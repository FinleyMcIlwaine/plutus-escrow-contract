{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# LANGUAGE TemplateHaskell #-}
module EscrowTests(tests) where

import           Ledger.Crypto
import           Ledger.Slot
import           Control.Monad                                                 (foldM, foldM_, void, (>=>))
import           Data.Either                                                   (isLeft, isRight)
import           Data.Foldable                                                 (traverse_)
import qualified Data.Map                                                      as Map
import           Test.Tasty                                                    (TestTree, testGroup)
import qualified Test.Tasty.HUnit                                              as HUnit

import qualified Ledger.Ada                                                    as Ada
import qualified Ledger.Typed.Tx                                               as Typed
import           Ledger.Value                                                  (Value, scale)
import           Wallet.API                                                    (WalletAPI,
                                                                                WalletDiagnostics)
import qualified Wallet.Emulator                                               as EM

import qualified Language.PlutusTx as PlutusTx

import           Escrow (Payment, State)
import qualified Escrow as ESM

tests :: TestTree
tests = testGroup "escrow state machine tests" [
    HUnit.testCaseSteps "lock, sign - SUCCESS" (runTrace (lockSignPay 3 1) isRight),
    HUnit.testCaseSteps "lock, propose, sign 2x, pay - FAILURE" (runTrace (lockSignPay 2 1) isLeft),
    HUnit.testCaseSteps "lock, propose, sign 3x, pay x2 - SUCCESS" (runTrace (lockSignPay 3 2) isRight),
    HUnit.testCaseSteps "lock, propose, sign 3x, pay x3 - FAILURE" (runTrace (lockSignPay 3 3) isLeft)
    ]

runTrace :: EM.EmulatorAction a -> (Either EM.AssertionError a -> Bool) -> (String -> IO ()) -> IO ()
runTrace t f step = do
    let initialState = EM.emulatorStateInitialDist (Map.singleton (EM.walletPubKey (EM.Wallet 1)) (Ada.adaValueOf 10))
        (result, st) = EM.runEmulator initialState t
    if f result
    then pure ()
    else do
        step (show $ EM.emLog st)
        HUnit.assertFailure "transaction failed to validate"

processAndNotify :: EM.Trace m ()
processAndNotify = void (EM.addBlocksAndNotify [w1, w2, w3] 1)

w1, w2, w3 :: EM.Wallet
w1 = EM.Wallet 1
w2 = EM.Wallet 2
w3 = EM.Wallet 3


-- | A payment of 5 Ada to the public key address of wallet 2
payment :: ESM.Payment
payment =
    ESM.Payment
        { ESM.paymentAmount    = Ada.adaValueOf 5
        , ESM.paymentSender    = EM.walletPubKey w1
        , ESM.paymentRecipient = EM.walletPubKey w2
        , ESM.arbitrator       = EM.walletPubKey w3
        , ESM.paymentDeadline  = 20
        }

initialise' :: WalletAPI m => m ()
initialise' = ESM.initialise

-- State machine transitions partially applied to the 'payment' multisig contract
-- 
lock' :: (WalletAPI m, WalletDiagnostics m) => Value -> PubKey -> PubKey -> Slot -> m State
lock' = ESM.lock 
-- 
-- 
addSignature' :: (WalletAPI m, WalletDiagnostics m) => State -> m State
addSignature' = ESM.addSignature

makePayment' :: (WalletAPI m, WalletDiagnostics m) => State -> m State
makePayment' = ESM.makePayment
 
initialise'' :: WalletAPI m => EM.Trace m ()
initialise'' =
-- instruct all three wallets to start watching the contract address
    traverse_ (\w -> EM.walletAction w initialise') [w1, w2, w3]
-- 
lock'' :: (WalletAPI m, WalletDiagnostics m) => Value -> EM.Trace m State
-- wallet 1 locks the funds
lock'' value = processAndNotify >> fst <$> EM.walletAction w1 (lock' value (EM.walletPubKey w2) (EM.walletPubKey w3) 10)
-- 
-- proposePayment'' :: (WalletAPI m, WalletDiagnostics m) => State -> EM.Trace m State
-- proposePayment'' st = processAndNotify >> fst <$> EM.walletAction w2 (proposePayment' st payment)
-- 
addSignature'' :: (WalletAPI m, WalletDiagnostics m) => Integer -> State -> EM.Trace m State
addSignature'' i inSt = foldM (\st w -> (processAndNotify >> fst <$> EM.walletAction w (addSignature' st))) inSt (take (fromIntegral i) [w1, w2, w3])
-- 
makePayment'' :: (WalletAPI m, WalletDiagnostics m) => State -> EM.Trace m State
makePayment'' st = processAndNotify >> fst <$> EM.walletAction w3 (makePayment' st)
-- 
signPay :: (WalletAPI m, WalletDiagnostics m) => Integer -> State -> EM.Trace m State
signPay i = addSignature'' i >=> makePayment''

lockSignPay :: forall m . (EM.MonadEmulator m) => Integer -> Integer -> m ()
lockSignPay i j = EM.processEmulated $ do

    -- stX contain the state of the contract. See note [Current state of the
    -- contract] in
    -- Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine
    initialise''
    st1 <- lock'' (Ada.adaValueOf 10)

    foldM_ (\st _ -> signPay i st) st1 [1..j]

    processAndNotify
    EM.assertOwnFundsEq w2 (scale j (Ada.adaValueOf 5))
