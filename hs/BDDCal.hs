import Prelude
import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe)
import IBDD (emptyci,tci,fci,ifci,iteci,andci,orci,nandci,norci,biimpci,xorci,notci,litci,tautci,graphifyci)
import qualified IBDD
import ToPreludeChar (isToHs)
import Control.Monad (liftM,liftM2,(>=>))
import Control.Monad.ST (stToIO)
import Data.Map.Strict ((!));
import qualified Data.Map.Strict as Map

kw_inp = "input"
kw_act = "actions"

dropUntil _ [] = []
dropUntil f as = if f as then as else dropUntil f (tail as)

startFrom s = drop (length s) . dropUntil (isPrefixOf s)

splitOn s ss = takeWhile (/=s) ss : (let d = dropWhile (/=s) ss in if null d then [] else splitOn s (tail d))

checkTaut v bdd ids = liftM (\t-> v ++ " is " ++ (if t then "" else "not ") ++ "a tautology.") (tautci (ids ! v) bdd)

bops = [
	("and",andci),
	("or",orci),
	("nand",nandci),
	("nor",norci),
	("biimp",biimpci),
	("xor",xorci)]

doAction (ids, bdd) line =
	if null wl || head wl == "autoreorder" then return ((ids, bdd), Nothing) else
	if length wl < 2 then cnp "Too few tokens" else
	if head wl == "tautology" then liftM (\r-> ((ids,bdd),Just r)) (checkTaut (wl !! 1) bdd ids) else
	if head wl == "graph" then liftM (\r-> ((ids,bdd),Just $ isToHs r)) (graphifyci [] (ga 1) bdd) else
	if length wl < 3 || wl !! 1 /= "=" then cnp "'=' expected"  else
	let f = 
		if length wl == 3 then return . (,) (ga 2) else
		if wl !! 2 == "not" then notci (ga 3) else
		if length wl /= 5 then cnp "Expected _ = _ op _" else
		(fromMaybe (cnp ("Unknown operator " ++ (wl !! 3))) (lookup (wl !! 3) bops)) (ga 2) (ga 4)
	in (\(np,bdd)-> ((Map.insert (wl!!0) np ids,bdd),Nothing)) `liftM` f bdd
	where
		wl = words line
		cnp x = error (x ++ " - could not parse " ++ unwords wl ++ ";")
		ga ind = fromMaybe (cnp ("Unknown identifier " ++ (wl !! ind))) . flip Map.lookup ids $ wl !! ind

assignInputs [] bdd = return (Map.empty,bdd)
assignInputs (a:is) bdd = let (i,n) = a in do
	(nn,bdd) <- litci (IBDD.Nat n) bdd
	(ids,bdd) <- assignInputs is bdd
	return (Map.insert i nn ids,bdd)

actionChain [] _ = return []
actionChain (a:as) s = do
	(s,r) <- doAction s a
	rec <- actionChain as s
	return (fromMaybe rec (liftM (:rec) r))
	
progs i a = do
	bdd <- emptyci
	s <- assignInputs i bdd
	actionChain a s

progi p = do
	let inputs = flip zip [0..] . words . takeWhile (/=';') . startFrom kw_inp $ p
	let actions = splitOn ';' . startFrom kw_act $ p
	stToIO $ progs inputs actions

main = do
	p <- getContents
	o <- progi p
	putStr $ unlines o
	return ()
