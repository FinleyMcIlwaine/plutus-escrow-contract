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
    , dispute
    , makePayment
    ) where

import           Data.Functor                 (void)
import qualified Ledger.Interval              as Interval
import           Ledger.Validation            (PendingTx, PendingTx'(..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Tx              as Typed
import qualified Ledger.Typed.Scripts         as Scripts
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
    CollectingSignatures Payment [PubKey] [PubKey]
    | Paid
    deriving (Show)

instance Eq State where
    {-# INLINABLE (==) #-}
    (CollectingSignatures pmt pks dpks) == (CollectingSignatures pmt' pks' dpks') =
        pmt == pmt' && pks == pks' && dpks == dpks'
    Paid == Paid = True
    _ == _ = False

PlutusTx.makeLift ''State

data Input = 
    AddSignature PubKey
    | Dispute PubKey
    | Cancel
    | Pay

PlutusTx.makeLift ''Input

{-# INLINABLE isSignatory #-}
-- | Check if a public key is one of the signatories of the escrow contract.
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
-- | Check whether enough signatories have approved or disputed the contract
proposalAccepted :: Payment -> [PubKey] -> Bool
proposalAccepted (Payment _ spk rpk apk _) pks =
    let numSigned = length (filter (\pk -> containsPk pk pks) [spk,rpk,apk])
    in numSigned >= 2

{-# INLINABLE valuePreserved #-}
-- Value stays locked
valuePreserved :: Value -> PendingTx -> Bool
valuePreserved vl ptx = vl == Validation.valueLockedBy ptx (Validation.ownHash ptx)

{-# INLINABLE valuePaid #-}
-- | True if the pending transaction pays
--   the amount specified to the buyer or seller in the payment specified 
valuePaid :: Payment -> PendingTx -> Bool
valuePaid (Payment vl spk rpk apk _) ptx = (vl == (Validation.valuePaidTo ptx rpk)) || (vl == (Validation.valuePaidTo ptx spk))

{-# INLINABLE step #-}
-- | Computes the next state given current state
--   'step' does not perform any checks of the preconditions. This is done in
--   'check' below.
step :: State -> Input -> Maybe State
step s i = case (s, i) of
    (CollectingSignatures pmt pks dpks, AddSignature pk) ->
        Just $ CollectingSignatures pmt (pk:pks) (filter (\dpk -> dpk /= pk) dpks)
    (CollectingSignatures pmt pks dpks, Dispute dpk) ->
        Just $ CollectingSignatures pmt (filter (\pk' -> pk' /= dpk) pks) (dpk:dpks)
    (CollectingSignatures _ _ _, Cancel) ->
        Just $ Paid
    (CollectingSignatures (Payment vp _ _ _ _) _ _, Pay) ->
        Just $ Paid
    _ -> Nothing

{-# INLINABLE check #-}
-- | Checks whether the pending transaction pays the expected amounts to script and public key addresses.
check :: State -> Input -> PendingTx -> Bool
check s i ptx = case (s, i) of
    (CollectingSignatures pmt@(Payment vl _ _ _ _) pks dpks, AddSignature pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk pmt &&
            not (containsPk pk pks) &&
            valuePreserved vl ptx
    (CollectingSignatures pmt@(Payment vl _ _ _ _) pks dpks, Dispute dpk) ->
        Validation.txSignedBy ptx dpk &&
        isSignatory dpk pmt &&
        not (containsPk dpk dpks) &&
        valuePreserved vl ptx
    (CollectingSignatures pmt@(Payment vl _ _ _ _) _ _, Cancel) ->
        proposalExpired ptx pmt && valuePreserved vl ptx
    (CollectingSignatures pmt@(Payment vl _ _ _ _) pks dpks, Pay) ->
        not (proposalExpired ptx pmt) &&
            ((proposalAccepted pmt pks) || (proposalAccepted pmt dpks))  &&
            valuePreserved (vl - vl) ptx &&
            valuePaid pmt ptx
    _ -> False

{-# INLINABLE final #-}
-- | The machine is in a final state if we are paid.
final :: State -> Bool
final Paid = True
final _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Scripts.ValidatorType (SM.StateMachine State Input)
mkValidator = SM.mkValidator (StateMachine step check final)

validatorCode :: PlutusTx.CompiledCode (Scripts.ValidatorType EscrowSym)
validatorCode = $$(PlutusTx.compile [|| mkValidator ||])

type EscrowSym = StateMachine State Input
scriptInstance :: Scripts.ScriptInstance EscrowSym
--scriptInstance = Scripts.validator $ validatorCode
scriptInstance = Scripts.validator @EscrowSym (validatorCode) $$(PlutusTx.compile[|| wrap ||])
    where
        wrap = Scripts.wrapValidator @State @Input

machineInstance :: SM.StateMachineInstance State Input
machineInstance =
    SM.StateMachineInstance
    (StateMachine step check final)
    scriptInstance

-- | Start watching the contract address
initialise :: WalletAPI m => () -> m ()
initialise () = WAPI.startWatching $ Scripts.scriptAddress scriptInstance

-- | Lock some funds in an contract.
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
    (tx, state) <- SM.mkInitialise machineInstance (CollectingSignatures (Payment vl spk rpk apk dl) [] []) vl

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

-- | Dispute the contract fulfillment
dispute
    :: (WalletAPI m, WalletDiagnostics m)
    => State
    -> m State
dispute st = WAPI.ownPubKey >>= runStep st . Dispute

-- | Make a payment after enough signatures or disputes have been collected.
makePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => State
    -> m State
makePayment currentState = do
    -- we can't use 'runStep' because the outputs of the transaction are
    -- different from the other transitions: We need two outputs, a public
    -- key output with the payment, and the script output
    (value, recipient) <- case currentState of
        CollectingSignatures (Payment vl spk rpk _ _) pks dpks -> pure (vl, (if (length pks) > (length dpks) then rpk else spk))
        _ -> WAPI.throwOtherError "Cannot make payment because no payment has been proposed. Run the 'lock' action first."
        -- Need to match to get the existential type out
    let addOutAndPay (Typed.TypedTxSomeIns tx) = do
            let pkOut = Typed.makePubKeyTxOut value recipient
                withPubKeyOut = tx { Typed.tyTxPubKeyTxOuts = [pkOut] }
            void $ WAPITyped.signTxAndSubmit withPubKeyOut

    (scriptTx, newState) <- SM.mkHalt machineInstance currentState Pay
    addOutAndPay scriptTx
    pure newState

-- | Advance a running escrow contract. This applies the transition function
--   'SM.transition' to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
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
