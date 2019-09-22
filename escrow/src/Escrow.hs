{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

-- | A multisig contract written as a state machine.
--   $multisig
module Escrow(
      Payment(..)
    , State
    , mkValidator
    , scriptInstance
    , initialise
    , lock
    , cancelPayment
    , addSignature
    , makePayment
    ) where

import           Data.Functor                 (void)
import qualified Ledger.Interval              as Interval
import           Ledger.Validation            (PendingTx, PendingTx'(..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Tx              as Typed
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import           Wallet
import qualified Wallet                       as WAPI
import qualified Wallet.Typed.API             as WAPITyped

import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude     hiding (check)
import           Language.PlutusTx.StateMachine (StateMachine(..))
import qualified Language.PlutusTx.StateMachine as SM
import qualified Wallet.Typed.StateMachine as SM

data Payment = Payment
    { paymentAmount    :: Value
    -- ^ How much to pay out
    , paymentSender    :: PubKey
    -- ^ The sender of payment
    , paymentRecipient :: PubKey
    -- ^ Address to pay the value to
    , arbitrator       :: PubKey
    -- ^ Escrow guy
    , paymentDeadline  :: Slot
    -- ^ Time until the required amount of signatures has to be collected.
    }
    deriving (Show)

instance Eq Payment where
    {-# INLINABLE (==) #-}
    (Payment vl spk rpk apk sl) == (Payment vl' spk' rpk' apk' sl') = vl == vl' && spk == spk' && apk == apk' && rpk == rpk' && sl == sl'

PlutusTx.makeLift ''Payment

-- | State of the escrow contract
data State =
    CollectingSignatures Value Payment [PubKey]
    | Paid
    deriving (Show)

instance Eq State where
    {-# INLINABLE (==) #-}
    (CollectingSignatures vl pmt pks) == (CollectingSignatures vl' pmt' pks') =
        vl == vl' && pmt == pmt' && pks == pks'
    Paid == Paid = True
    _ == _ = False

PlutusTx.makeLift ''State

data Input = 
    AddSignature PubKey
    | Cancel
    | Pay

PlutusTx.makeLift ''Input

{-# INLINABLE isSignatory #-}
-- | Check if a public key is one of the signatories of the multisig contract.
isSignatory :: PubKey -> Payment -> Bool
isSignatory pk (Payment _ spk rpk apk  _) = any (\pk' -> pk == pk') [spk,rpk,apk]

{-# INLINABLE containsPk #-}
-- | Check whether a list of public keys contains a given key.
containsPk :: PubKey -> [PubKey] -> Bool
containsPk pk = any (\pk' -> pk' == pk)

{-# INLINABLE proposalExpired #-}
-- | Check whether a proposed 'Payment' has expired.
proposalExpired :: PendingTx -> Payment -> Bool
proposalExpired PendingTx{pendingTxValidRange} Payment{paymentDeadline} =
    paymentDeadline `Interval.before` pendingTxValidRange

{-# INLINABLE proposalAccepted #-}
-- | Check whether enough signatories (represented as a list of public keys)
--   have signed a proposed payment.
proposalAccepted :: Payment -> [PubKey] -> Bool
proposalAccepted (Payment _ spk rpk apk _) pks =
    let numSigned = length (filter (\pk -> containsPk pk pks) [spk,rpk,apk])
    -- * Hehehehehe
    in numSigned >= 2

{-# INLINABLE valuePreserved #-}
-- | @valuePreserved v p@ is true if the pending transaction @p@ pays the amount
--   @v@ to this script's address. It does not assert the number of such outputs:
--   this is handled in the generic state machine validator.
valuePreserved :: Value -> PendingTx -> Bool
valuePreserved vl ptx = vl == Validation.valueLockedBy ptx (Validation.ownHash ptx)

{-# INLINABLE valuePaid #-}
-- | @valuePaid pm ptx@ is true if the pending transaction @ptx@ pays
--   the amount specified in @pm@ to the public key address specified in @pm@
valuePaid :: Payment -> PendingTx -> Bool
valuePaid (Payment vl _ rpk apk _) ptx = vl == (Validation.valuePaidTo ptx rpk)

{-# INLINABLE step #-}
-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'check' below.
step :: State -> Input -> Maybe State
step s i = case (s, i) of
    (CollectingSignatures vl pmt pks, AddSignature pk) ->
        Just $ CollectingSignatures vl pmt (pk:pks)
    (CollectingSignatures vl _ _, Cancel) ->
        Just $ Paid
    (CollectingSignatures vl (Payment vp _ _ _ _) _, Pay) ->
        Just $ Paid
    _ -> Nothing

{-# INLINABLE check #-}
-- | @check params ptx state input@ checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses.
check :: State -> Input -> PendingTx -> Bool
check s i ptx = case (s, i) of
    (CollectingSignatures vl pmt pks, AddSignature pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk pmt &&
            not (containsPk pk pks) &&
            valuePreserved vl ptx
    (CollectingSignatures vl pmt _, Cancel) ->
        proposalExpired ptx pmt && valuePreserved vl ptx
    (CollectingSignatures vl pmt@(Payment vp _ _ _ _) pks, Pay) ->
        let vl' = vl - vp in
        not (proposalExpired ptx pmt) &&
            proposalAccepted pmt pks &&
            valuePreserved vl' ptx &&
            valuePaid pmt ptx
    _ -> False

{-# INLINABLE final #-}
-- | The machine is in a final state if we are holding no money.
final :: State -> Bool
final Paid = True
final _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: SM.StateMachineValidator State Input
mkValidator = SM.mkValidator $ StateMachine step check final

validatorCode :: PlutusTx.CompiledCode (Typed.ValidatorType EscrowSym)
validatorCode = $$(PlutusTx.compile [|| mkValidator ||])

type EscrowSym = StateMachine State Input
scriptInstance :: Typed.ScriptInstance EscrowSym
scriptInstance = Typed.Validator $ validatorCode

machineInstance :: SM.StateMachineInstance State Input
machineInstance =
    SM.StateMachineInstance
    (StateMachine step check final)
    scriptInstance
    stepRedeemerCode
    haltRedeemerCode

-- | Start watching the contract address
initialise :: WalletAPI m => () -> m ()
initialise () = WAPI.startWatching $ Typed.scriptAddress scriptInstance

-- | Lock some funds in a multisig contract.
lock
    :: (WalletAPI m, WalletDiagnostics m)
    =>
    Value
    ->
    PubKey
    ->
    PubKey
    ->
    Slot
    -- ^ The funds we want to lock
    -> m State
    -- ^ The initial state of the contract
lock vl rpk apk dl = do
    spk <- WAPI.ownPubKey
    (tx, state) <- SM.mkInitialise machineInstance (CollectingSignatures vl (Payment vl spk rpk apk dl) []) vl

    void $ WAPITyped.signTxAndSubmit tx

    pure state

-- | Cancel a proposed payment
cancelPayment
    :: (WalletAPI m, WalletDiagnostics m)
    => State
    -> m State
cancelPayment st = runStep st Cancel

-- | Add a signature to a proposed payment
addSignature
    :: (WalletAPI m, WalletDiagnostics m)
    => State
    -> m State
addSignature st = WAPI.ownPubKey >>= runStep st . AddSignature

-- | Make a payment after enough signatures have been collected.
makePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => State
    -> m State
makePayment currentState = do
    -- we can't use 'runStep' because the outputs of the transaction are
    -- different from the other transitions: We need two outputs, a public
    -- key output with the payment, and the script output with the remaining
    -- funds.
    (value, recipient) <- case currentState of
        CollectingSignatures vl' (Payment vl _ rpk _ _) _ -> pure (vl, rpk)
        _ -> WAPI.throwOtherError "Cannot make payment because no payment has been proposed. Run the 'lock' action first."
        -- Need to match to get the existential type out
    let addOutAndPay (Typed.TypedTxSomeIns tx) = do
            let pkOut = Typed.makePubKeyTxOut value recipient
                withPubKeyOut = tx { Typed.tyTxPubKeyTxOuts = [pkOut] }
            void $ WAPITyped.signTxAndSubmit withPubKeyOut

    (scriptTx, newState) <- SM.mkHalt machineInstance currentState Pay
    addOutAndPay scriptTx
    pure newState

stepRedeemerCode :: PlutusTx.CompiledCode (Input -> Typed.RedeemerFunctionType '[EscrowSym] EscrowSym)
stepRedeemerCode = $$(PlutusTx.compile [|| SM.mkStepRedeemer @State @Input ||])

haltRedeemerCode :: PlutusTx.CompiledCode (Input -> Typed.RedeemerFunctionType '[] EscrowSym)
haltRedeemerCode = $$(PlutusTx.compile [|| SM.mkHaltRedeemer @State @Input ||])

-- | Advance a running multisig contract. This applies the transition function
--   'SM.transition' to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
--
runStep
    :: (WalletAPI m, WalletDiagnostics m)
    => State
    -- ^ Current state of the instance
    -> Input
    -- ^ Input to be applied to the contract
    -> m State
    -- ^ New state after applying the input
runStep currentState input = do
    (scriptTx, newState) <- SM.mkStep machineInstance currentState input id

    -- Need to match to get the existential type out
    case scriptTx of
        (Typed.TypedTxSomeIns tx) -> void $ WAPITyped.signTxAndSubmit tx

    pure newState

--  Note [Current state of the contract]
--  The 'mkStep' function takes the current state of the contract and returns the
--  new state. Both values are placed on the chain, so technically we don't have to
--  pass them around like this, but we currently can't decode 'State' values from
--  PLC back to Haskell.
