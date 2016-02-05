module ToPreludeChar where {

import qualified IBDD;
import Prelude ((*), (+), (.), (++)); 
import qualified Prelude;
import qualified Data.Char (chr);

nibbleToInt :: IBDD.Nibble -> Prelude.Int;
nibbleToInt IBDD.Nibble0 =  0;
nibbleToInt IBDD.Nibble1 =  1;
nibbleToInt IBDD.Nibble2 =  2;
nibbleToInt IBDD.Nibble3 =  3;
nibbleToInt IBDD.Nibble4 =  4;
nibbleToInt IBDD.Nibble5 =  5;
nibbleToInt IBDD.Nibble6 =  6;
nibbleToInt IBDD.Nibble7 =  7;
nibbleToInt IBDD.Nibble8 =  8;
nibbleToInt IBDD.Nibble9 =  9;
nibbleToInt IBDD.NibbleA = 10;
nibbleToInt IBDD.NibbleB = 11;
nibbleToInt IBDD.NibbleC = 12;
nibbleToInt IBDD.NibbleD = 13;
nibbleToInt IBDD.NibbleE = 14;
nibbleToInt IBDD.NibbleF = 15;


charToInt :: IBDD.Char -> Prelude.Int;
charToInt (IBDD.Char n1 n2) = nibbleToInt n1 * 16 + nibbleToInt n2;

charToChar :: IBDD.Char -> Prelude.Char;
charToChar = Data.Char.chr . charToInt;

isToHs = Prelude.map charToChar;

{-(instance Prelude.Show [IBDD.Char] where
	show s = "ISB\"" ++ isToHs s ++ "\""
-}
}
