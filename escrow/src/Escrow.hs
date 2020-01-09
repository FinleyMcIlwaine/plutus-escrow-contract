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
module Escrow(Contract(..)
    , State
    , mkValidator
    , scriptInstance
    , EscrowError(..)
    , EscrowSchema
    , contract
    ) where

import           Control.Lens                 (makeClassyPrisms)
import qualified Ledger.Interval              as Interval
import           Ledger.Validation            (PendingTx, PendingTx'(..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value                 (Value)
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
data EscrowContract = EscrowContract
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

instance Eq EscrowContract where
    {-# INLINABLE (==) #-}
    (EscrowContract vl dep ben agent sl) == (EscrowContract vl' dep' ben' agent' sl') = vl == vl' && dep == dep' && ben == ben' && agent == agent' && sl == sl'

-- | State of the multisig contract.
data State =
    CollectingSignatures EscrowContract [PubKey] [PubKey]
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
        .\/ Endpoint "create-contract" EscrowContract
        .\/ Endpoint "sign-approve" ()
        .\/ Endpoint "sign-dispute" ()

{-# INLINABLE isSignatory #-}
-- | Check if a public key is one of the signatories of the multisig contract.
isSignatory :: PubKey -> EscrowContract -> Bool
isSignatory pk (EscrowContract _ d b e _) = containsPk pk [d, b, e] --any (\pk' -> pk == pk') [d, b, e]

{-# INLINABLE containsPk #-}
-- | Check whether a list of public keys contains a given key.
containsPk :: PubKey -> [PubKey] -> Bool
containsPk pk = any (\pk' -> pk' == pk)

{-# INLINABLE contractExpired #-}
-- | Check whether a proposed 'Contract' has expired.
contractExpired :: PendingTx -> EscrowContract -> Bool
contractExpired PendingTx{pendingTxValidRange} EscrowContract{expirationSlot} =
    expirationSlot `Interval.before` pendingTxValidRange

{-# INLINABLE contractAccepted #-}
-- | Check whether enough signatories (represented as a list of public keys)
--   have signed a proposed payment.
contractAccepted :: EscrowContract -> [PubKey] -> Bool
contractAccepted (EscrowContract _ d b e _) pks =
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
valuePaid :: EscrowContract -> PendingTx -> Bool
valuePaid (EscrowContract vl _ b _ _) ptx = vl == (Validation.valuePaidTo ptx b)

{-# INLINABLE valueRefunded #-}
-- | @valuePaid pm ptx@ is true if the pending transaction @ptx@ pays
--   the amount specified in @pm@ to the public key address specified in @pm@
valueRefunded :: EscrowContract -> PendingTx -> Bool
valueRefunded (EscrowContract vl d _ _ _) ptx = vl == (Validation.valuePaidTo ptx d)

{-# INLINABLE step #-}
-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'check' below.
step :: State -> Input -> Maybe State
step s i = case (s, i) of
    (CollectingSignatures escrowContract approvers disputers, Approve pk) ->
        Just $ CollectingSignatures escrowContract (pk:approvers) (filter (\disputer -> disputer /= pk) disputers)
    (CollectingSignatures escrowContract approvers disputers, Dispute pk) ->
        Just $ CollectingSignatures escrowContract (filter (\approver -> approver /= pk) approvers) (pk:disputers)
    _ -> Nothing

{-# INLINABLE check #-}
-- | @check params ptx state input@ checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses.
--   p is params and needs to be dealt with
check :: State -> Input -> PendingTx -> Bool
check s i ptx = case (s, i) of
    (CollectingSignatures escrowContract approvers _, Approve pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk escrowContract &&
            not (containsPk pk approvers) &&
            valuePreserved (paymentAmount escrowContract) ptx
    (CollectingSignatures escrowContract _ disputers, Dispute pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk escrowContract &&
            not (containsPk pk disputers) &&
            valuePreserved (paymentAmount escrowContract) ptx
    _ -> False

{-# INLINABLE final #-}
-- | The machine is in a final state if we are holding no money.
final :: State -> Bool
final (Paid) = True
final _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Scripts.ValidatorType EscrowSym
mkValidator = SM.mkValidator $ StateMachine step check final

validatorCode :: PlutusTx.CompiledCode (Scripts.ValidatorType EscrowSym)
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
allocate (CollectingSignatures (EscrowContract _ b _ _ _) approvers _) (Approve _) vl =
    if (length approvers >= 2) then ValueAllocation{vaOwnAddress=(vl - vl), vaOtherPayments=Tx.payToPubKey vl b}
    else ValueAllocation{vaOwnAddress = vl, vaOtherPayments = Haskell.mempty}
allocate (CollectingSignatures (EscrowContract _ b _ _ _) _ disputers) (Dispute _) vl =
    if (length disputers >= 2) then ValueAllocation{vaOwnAddress=(vl - vl), vaOtherPayments=Tx.payToPubKey vl b}
    else ValueAllocation{vaOwnAddress = vl, vaOtherPayments = Haskell.mempty}
allocate _ _ vl =
    ValueAllocation{vaOwnAddress = vl, vaOtherPayments = Haskell.mempty}

client :: SM.StateMachineClient State Input
client = SM.mkStateMachineClient (machineInstance) allocate

contract :: 
    ( AsContractError e
    , AsSMContractError e State Input
    )
    => Contract EscrowSchema e ()
contract = go where
    theClient = client
    go = endpoints >> go
    endpoints = createContract <|> signApprove <|> signDispute
    signApprove = endpoint @"sign-approve" >> ownPubKey >>= SM.runStep theClient . Approve
    signDispute = endpoint @"sign-dispute" >> ownPubKey >>= SM.runStep theClient . Dispute
    createContract = do
        escrowContract <- endpoint @"create-contract"
        SM.runInitialise theClient (CollectingSignatures escrowContract [] []) (paymentAmount escrowContract)

PlutusTx.makeIsData ''EscrowContract
PlutusTx.makeLift ''EscrowContract
PlutusTx.makeIsData ''State
PlutusTx.makeLift ''State
PlutusTx.makeIsData ''Input
PlutusTx.makeLift ''Input
