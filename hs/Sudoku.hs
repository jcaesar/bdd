import Prelude
import IBDD (emptyci,tci,fci,iteci,andci,orci,nandci,norci,biimpci,xorci,notci,litci,tautci,graphifyci,sat_list_coverci)
import qualified IBDD
import qualified Heap
import Data.Maybe
import Data.List
import ToPreludeChar (isToHs)

{- a Sudoku is coded into three figure numbers. First figure is the row index, the second the column, and the third the number that is noted in that cell -}

parseSudoku i =
	let a = lines i;
	    b = if length a == 9 then a else error "Need 9 lines in the input";
	    c = (\d -> if d == ' ' then Nothing else Just (read [d] :: Integer));
	    e = map (\f -> if length f == 9 then map c f else error "Need 9 characters in each line") b;
	in e

buildBdd = undefined

crossWith f a b = concat $ map (\c -> map (f c) b) a
cross = crossWith (,)

cell = [1..9]
row = map (*10) [1..9]
column = map (*100) [1..9]
group = [110,120,130,210,220,230,310,320,330]
allCells = crossWith (+) column row

onlyOne a bdd = do
	(b,_,bdd) <- onlyOne' (sort a) bdd
	return (b,bdd)

onlyOne' [e] bdd = do
	(eb,bdd) <- litci (IBDD.Nat e) bdd;
	(ne,bdd) <- notci eb bdd;
	return (eb,ne,bdd)
onlyOne' (a:b) bdd = do
	(ab,bdd) <- litci (IBDD.Nat a) bdd;
	(bn,bh,bdd) <- onlyOne' b bdd
	(an,bdd) <- iteci ab bh bn bdd;
	(f,bdd) <- fci bdd;
	(ah,bdd) <- iteci ab f bh bdd;
	return (an,ah,bdd)

mapBdd _ [] bdd = return ([], bdd)
mapBdd f (a:as) bdd = do
	(r,bdd) <- f a bdd
	(rs,bdd) <- mapBdd f as bdd
	return (r:rs,bdd)
{- I need a proper monad for this stuff. But I'm so afraid of the type. -}
foldrBdd :: (a -> b -> IBDD.Bddi_ext () -> Heap.ST Heap.RealWorld (b, IBDD.Bddi_ext ())) -> b -> [a] -> IBDD.Bddi_ext () -> Heap.ST Heap.RealWorld (b, IBDD.Bddi_ext ())
foldrBdd f b [] bdd = return (b,bdd)
foldrBdd f b (a:as) bdd = do
	(bn,bdd) <- foldrBdd f b as bdd
	f a bn bdd
compBdd g f a bdd = do
	(fr,bdd) <- f a bdd
	(gr,bdd) <- g fr bdd
	return (gr,bdd)
appBdd f a bdd = do
	(ar,bdd) <- a bdd
	f ar bdd
bigAnd l bdd = do
	(t,bdd) <- tci bdd
	foldrBdd andci t l bdd
bigOr l bdd = do
	(f,bdd) <- fci bdd
	foldrBdd orci f l bdd

one_per_cell = bigAnd `appBdd` (mapBdd onlyOne . map (\c -> map (c+) cell) $ allCells) 

pcl v bdd = do
	let ps = \v p -> (if p then "" else "-") ++ show (IBDD.integer_of_nat v)
	let pl = intercalate "," . map (uncurry ps)
	let pf = intercalate "\n" . map pl
	(r,s) <- sat_list_coverci v bdd
	return $ (pf r,s)

is2hs = isToHs 

solve = undefined

main = getContents >>= (solve . buildBdd . parseSudoku)

{- This is immensely slow, but not because of the bdd operations… putStrLn =<< is2hs <$> stToIO (emptyci >>= (bigOr `appBdd` (mapBdd onlyOne . map (\c -> map (c+) cell) $ reverse . take 3 $ allCells)) >>= uncurry (graphifyci [])) -}
