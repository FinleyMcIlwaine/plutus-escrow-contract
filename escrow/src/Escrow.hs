{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
-- | A multisig contract written as a state machine.
--   $multisig
module Escrow(
    , Payment(..)
    , State
    , mkValidator
    , scriptInstance
    , MultiSigError(..)
    , MultiSigSchema
    , contract
    ) where

import           Control.Lens                 (makeClassyPrisms)
import qualified Ledger.Interval              as Interval
import           Ledger.Validation            (PendingTx, PendingTx'(..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import           Ledger                       (PubKey, Slot)

import qualified Language.PlutusTx            as PlutusTx
import           Language.Plutus.Contract
import           Language.Plutus.Contract.StateMachine (ValueAllocation(..), AsSMContractError, StateMachine(..))
import qualified Language.Plutus.Contract.StateMachine as SM
import qualified Language.Plutus.Contract.Tx       as Tx
import           Language.PlutusTx.Prelude         hiding (check, Applicative (..), (<>))
import qualified Prelude as Haskell

--   $multisig
--   The n-out-of-m multisig contract works like a joint account of
--   m people, requiring the consent of n people for any payments.
--   In the smart contract the signatories are represented by public keys,
--   and approval takes the form of signatures on transactions.
--
--   The multisig contract in
--   'Language.PlutusTx.Coordination.Contracts.MultiSig' expects n signatures on
--   a single transaction. This requires an off-chain communication channel. The
--   multisig contract implemented in this module uses a proposal system that
--   allows participants to propose payments and attach their signatures to
--   proposals over a period of time, using separate transactions. All contract
--   state is kept on the chain so there is no need for off-chain communication.

-- | A proposal for making a payment under the multisig scheme.
data Contract = Contract
    { paymentAmount    :: Value
    -- ^ How much to pay out
    , depositor :: PubKey
    -- ^ Address the payment comes from
    , beneficiary :: PubKey
    -- ^ Address the payment will go to
    , escrowAgent :: PubKey
    -- ^ Address of the escrow agent
    , expirationSlot  :: Slot
    -- ^ Time until the required amount of signatures has to be collected.
    }
    deriving (Show)

instance Eq Payment where
    {-# INLINABLE (==) #-}
    (Payment vl dep ben agent sl) == (Payment vl' dep' ben' agent' sl') = vl == vl' && dep == dep' && ben == ben' && agent == agent' && sl == sl'

-- | State of the multisig contract.
data State =
    CollectingSignatures Contract [PubKey] [PubKey]
    -- ^ A payment has been proposed and is awaiting signatures.
    | Paid
    -- ^ Contract has been paid out or refunded
    deriving (Show)

instance Eq State where
    {-# INLINABLE (==) #-}
    (Paid) == (Paid) = True
    (CollectingSignatures contract approvers disputers) == (CollectingSignatures contract' approvers' disputers') =
        contract == contract' && approvers == approvers' && disputers == disputers'
    _ == _ = False

data Input =
    Approve PubKey
    -- ^ Add a signature to the sigs. that have been collected for the
    --   current proposal.

    | Dispute PubKey
    -- ^ Cancel the current proposal if the deadline has passed
    deriving Show

data EscrowError =
    EContractError ContractError
    | EStateMachineError (SM.SMContractError State Input)
    deriving Show
makeClassyPrisms ''EscrowError

instance AsContractError EscrowError where
    _ContractError = _EContractError

instance AsSMContractError EscrowError State Input where
    _SMContractError = _EStateMachineError
    
type EscrowSchema =
    BlockchainActions
        .\/ Endpoint "create-contract" Contract
        .\/ Endpoint "sign-approve" ()
        .\/ Endpoint "sign-dispute" ()

{-# INLINABLE isSignatory #-}
-- | Check if a public key is one of the signatories of the multisig contract.
isSignatory :: PubKey -> Contract -> Bool
isSignatory pk (Contract _ d b e _) = containsPk pk [d, b, e] --any (\pk' -> pk == pk') [d, b, e]

{-# INLINABLE containsPk #-}
-- | Check whether a list of public keys contains a given key.
containsPk :: PubKey -> [PubKey] -> Bool
containsPk pk = any (\pk' -> pk' == pk)

{-# INLINABLE isValidProposal #-}
-- | Check whether a proposed 'Payment' is valid given the total
--   amount of funds currently locked in the contract.
-- we should not need isValidProposal :: Value -> Payment -> Bool
--isValidProposal vl (Payment amt _ _) = amt `Value.leq` vl

{-# INLINABLE proposalExpired #-}
-- | Check whether a proposed 'Contract' has expired.
contractExpired :: PendingTx -> Contract -> Bool
contractExpired PendingTx{pendingTxValidRange} Contract{expirationSlot} =
    expirationSlot `Interval.before` pendingTxValidRange

{-# INLINABLE proposalAccepted #-}
-- | Check whether enough signatories (represented as a list of public keys)
--   have signed a proposed payment.
contractAccepted :: Contract -> [PubKey] -> Bool
contractAccepted (Contract _ d b e _) pks =
    let numSigned = length (filter (\pk -> containsPk pk pks) [d, b, e])
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
valuePaid :: Contract -> PendingTx -> Bool
valuePaid (Contract vl d b e _) ptx = vl == (Validation.valuePaidTo ptx b)

{-# INLINABLE valuePaid #-}
-- | @valuePaid pm ptx@ is true if the pending transaction @ptx@ pays
--   the amount specified in @pm@ to the public key address specified in @pm@
valueRefunded :: Contract -> PendingTx -> Bool
valueRefunded (Contract vl d b e _) ptx = vl == (Validation.valuePaidTo ptx d)

{-# INLINABLE step #-}
-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'check' below.
step :: State -> Input -> Maybe State
step s i = case (s, i) of
    (CollectingSignatures contract approvers disputers, Approve pk) ->
        Just $ CollectingSignatures contract (pk:approvers) (filter (\disputer -> disputer \= pk) disputers)
    (CollectingSignatures contract approvers disputers, Dispute pk) ->
        Just $ CollectingSignatures contract (filter (\approver -> approver \= pk) approvers) (pk:disputers)
    --(CollectingSignatures vl (Payment vp _ _) _, Pay) ->
    --    let vl' = vl - vp in
    --    Just $ Holding vl'
    _ -> Nothing

{-# INLINABLE check #-}
-- | @check params ptx state input@ checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses.
--   p is params and needs to be dealt with
check :: State -> Input -> PendingTx -> Bool
check s i ptx = case (s, i) of
    (CollectingSignatures contract approvers _, Approve pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk contract &&
            not (containsPk pk approvers) &&
            valuePreserved (paymentAmount contract) ptx
    (CollectingSignatures contract _ disputers, Dispute pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk contract &&
            not (containsPk pk disputers) &&
            valuePreserved (paymentAmount contract) ptx
    --(CollectingSignatures vl pmt _, Cancel) ->
    --    proposalExpired ptx pmt && valuePreserved vl ptx
   -- (CollectingSignatures vl pmt@(Payment vp _ _) pks, Pay) ->
   --     let vl' = vl - vp in
   --     not (proposalExpired ptx pmt) &&
   --         proposalAccepted p pks &&
   --         valuePreserved vl' ptx &&
   --         valuePaid pmt ptx
    _ -> False

{-# INLINABLE final #-}
-- | The machine is in a final state if we are holding no money.
final :: State -> Bool
final (Paid) = True
final _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Scripts.ValidatorType EscrowSym
mkValidator = SM.mkValidator $ StateMachine step check final

validatorCode :: PlutusTx.CompiledCode (Scripts.ValidatorType MultiSigSym)
validatorCode = $$(PlutusTx.compile [|| mkValidator ||])

type EscrowSym = StateMachine State Input
scriptInstance :: Scripts.ScriptInstance EscrowSym
scriptInstance = Scripts.validator @EscrowSym
    (validatorCode)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @State @Input

machineInstance :: SM.StateMachineInstance State Input
machineInstance =
    SM.StateMachineInstance
    (StateMachine step check final)
    (scriptInstance)

allocate :: State -> Input -> Value -> ValueAllocation
allocate (CollectingSignatures (Contract vp b d e _) approvers _) (Approve _) vl =
    if (length approvers >= 2) then ValueAllocation{vaOwnAddress=0, vaOtherPayments=Tx.payToPubKey vl b}
    else ValueAllocation{vaOwnAddress = vl, vaOtherPayments = Haskell.mempty}
allocate (CollectingSignatures (Contract vp b d e _) _ disputers) (Dispute _) vl =
    if (length disputers >= 2) then ValueAllocation{vaOwnAddress=0, vaOtherPayments=Tx.payToPubKey vl b}
    else ValueAllocation{vaOwnAddress = vl, vaOtherPayments = Haskell.mempty}
allocate _ _ vl =
    ValueAllocation{vaOwnAddress = vl, vaOtherPayments = Haskell.mempty}

client :: SM.StateMachineClient State Input
client = SM.mkStateMachineClient (machineInstance) allocate

contract :: 
    ( AsContractError e
    , AsSMContractError e State Input
    )
    => Contract MultiSigSchema e ()
contract = go where
    theClient = client
    go = endpoints >> go -- TODO fix this next
    endpoints = lock <|> propose <|> cancel <|> addSignature <|> pay
    propose = endpoint @"propose-payment" >>= SM.runStep theClient . ProposePayment
    cancel  = endpoint @"cancel-payment" >> SM.runStep theClient Cancel
    addSignature = endpoint @"add-signature" >> ownPubKey >>= SM.runStep theClient . AddSignature
    lock = do
        value <- endpoint @"lock"
        SM.runInitialise theClient (Holding value) value
    pay = endpoint @"pay" >> SM.runStep theClient Pay

PlutusTx.makeIsData ''Contract
PlutusTx.makeLift ''Contract
PlutusTx.makeIsData ''State
PlutusTx.makeLift ''State
PlutusTx.makeIsData ''Input
PlutusTx.makeLift ''Input
