{-# OPTIONS_GHC -fno-warn-tabs #-}
{- Tab masterrace -}

import Prelude
import Data.List (isPrefixOf)
import IBDD (emptyci,tci,fci,ifci,iteci,andci,orci,notci,litci,graphifyci)
import qualified IBDD
import ToPreludeChar (isToHs)
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

toConj [] s = tci s
toConj (a:as) s = do
	(c,s) <- toConj as s
	(p,s) <- toLit a s
	andci p c s

toDisj [] s = fci s
toDisj (a:as) s = do
	(d,s) <- toDisj as s
	(p,s) <- toConj a s
	orci p d s

toBdd l = emptyci >>= toDisj l
toGraph s = do
	(ep,d) <- toBdd s
	graphifyci [] ep d

main :: IO ()
main = do
	inp <- getContents
	gvz <- stToIO . toGraph . parseFile $ inp
	putStrLn $ isToHs gvz
	return ()
