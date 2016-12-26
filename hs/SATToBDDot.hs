{-# OPTIONS_GHC -fno-warn-tabs #-}
{- Tab masterrace -}

import Prelude
import Data.List (isPrefixOf)
import IBDD (emptyci,tci,fci,iteci,andci,orci,notci,litci,graphifyci)
import qualified IBDD
import Control.Monad (liftM)
import Control.Monad.ST (stToIO)

parseLiteral :: String -> Either Integer Integer
parseLiteral l = (if isp then Left else Right) . read $ np
	where
		isp = isPrefixOf "-" l
		np = if isp then tail l else l

parseFile = map (map parseLiteral) . map words . lines

toLit (Right v) s = litci (IBDD.Nat v) s
toLit (Left v) s = do
	(l,s) <- litci (IBDD.Nat v) s
	notci l s

toDisj [] s = fci s
toDisj (a:as) s = do
	(d,s) <- toDisj as s
	(p,s) <- toLit a s
	orci p d s

toConj [] s = tci s
toConj (a:as) s = do
	(c,s) <- toConj as s
	(p,s) <- toDisj a s
	andci p c s

toBdd l = emptyci >>= toConj l

toGraphS s = do
	(ep,d) <- toBdd s
	graphifyci [] ep d
toGraph :: String -> IO String
toGraph s = stToIO . toGraphS . parseFile $ s

main :: IO ()
main = do
	inp <- getContents
	g <- toGraph inp
	putStr g
	return ()
