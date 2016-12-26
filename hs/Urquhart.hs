import Prelude
import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe)
import IBDD (emptyci,tci,fci,ifci,andci,orci,nandci,norci,biimpci,xorci,notci,litci,tautci,graphifyci)
import qualified IBDD
import Control.Monad (liftM,liftM2,(>=>))
import Control.Monad.ST (stToIO)
import Data.Map.Strict ((!));
import qualified Data.Map.Strict as Map
import System.Environment (getArgs)

uqh_r _ 0 0 r bdd = return (r,bdd)
uqh_r n 0 i r bdd = uqh_r n n (i-1) r bdd
uqh_r n v i r bdd = do
	(k,bdd) <- litci (IBDD.Nat v) bdd
	(k,bdd) <- biimpci k r bdd
	uqh_r n (v-1) i k bdd

urquhart n = do
	bdd <- emptyci
	(s,bdd) <- tci bdd
	(s,bdd) <- uqh_r n n 1 s bdd
	(\t-> "Formula is " ++ (if t then "" else "not ") ++ "a tautology" ++ (if t then " as expected." else ". Buuuuuugg!")) `liftM` tautci s bdd

main = putStrLn =<< stToIO . urquhart =<< (read . head) `liftM` getArgs
