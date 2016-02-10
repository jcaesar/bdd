import Prelude
import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe)
import IBDD (emptyci,tci,fci,ifci,andci,orci,nandci,norci,biimpci,xorci,notci,litci,tautci,graphifyci)
import qualified IBDD
import ToPreludeChar (isToHs)
import Control.Monad (liftM,liftM2,(>=>))
import Control.Monad.ST (stToIO)
import Data.Map.Strict ((!));
import qualified Data.Map.Strict as Map
import System.Environment (getArgs)

uqh_r 0 r bdd = return (r,bdd)
uqh_r n r bdd = do
	(k,bdd) <- litci (IBDD.Nat n) bdd
	(k,bdd) <- biimpci k r bdd
	uqh_r (n-1) k bdd

urquhart n = do
	bdd <- emptyci
	(s,bdd) <- litci (IBDD.Nat n) bdd
	uqh_r (n-1) s bdd

main = do
	n <- (read . head) `liftM` getArgs
	_ <- stToIO $ urquhart n
	return ()
