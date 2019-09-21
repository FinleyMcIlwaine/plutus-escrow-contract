module Lib
    ( someFunc
    ) where

import           Language.PlutusCore
import qualified Language.PlutusTx.StateMachine as SM
import           Language.PlutusTx.StateMachine ()
import qualified Data.Map                     as Map
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import qualified Data.Text                    as Text
import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude    hiding (check)
import           Ledger                       hiding (to)
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import qualified Ledger.Validation            as Validation
import           Wallet
import qualified Wallet                       as WAPI


someFunc :: IO ()
someFunc = putStrLn "someFunc"

data ContractState =
    Initialised
