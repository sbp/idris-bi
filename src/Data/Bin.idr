module Data.Bin

import public Data.Bi
import public Data.Bip

%default total
%access public export

-- basic properties of constructors

binPInj : BinP p = BinP q -> p = q
binPInj Refl = Refl

-- Following Coq.NArith.BinNatDef

-- Operation x -> 2*x+1
-- TODO

||| Operation x -> 2*x
binD : (a: Bin) -> Bin
binD BinO = BinO
binD (BinP a') = BinP (O a')

||| Successor
binSucc : (a: Bin) -> Bin
binSucc BinO = BinP U
binSucc (BinP a') = BinP (bipSucc a')

-- Predecessor
-- The successor of Bin seen as a Bip

||| Addition
binPlus : (a: Bin) -> (b: Bin) -> Bin
binPlus BinO BinO = BinO
binPlus BinO (BinP b') = BinP b'
binPlus (BinP a') BinO = BinP a'
binPlus (BinP a') (BinP b') = BinP (bipPlus a' b')

||| Subtraction
binMinus : (a: Bin) -> (b: Bin) -> Bin
binMinus BinO BinO = BinO
binMinus BinO (BinP b') = BinO
binMinus (BinP a') BinO = BinP a'
binMinus (BinP a') (BinP b') = if a' > b'
                                 then BinP (bipMinus a' b')
                                 else BinO

||| Multiplication
binMult : (a: Bin) -> (b: Bin) -> Bin
binMult BinO BinO = BinO
binMult BinO (BinP b') = BinO
binMult (BinP a') BinO = BinO
binMult (BinP a') (BinP b') = BinP (bipMult a' b')

||| Order
binCompare : (a: Bin) -> (b: Bin) -> Ordering
binCompare BinO BinO = EQ
binCompare BinO (BinP b) = LT
binCompare (BinP a) BinO = GT
binCompare (BinP a) (BinP b) = bipCompare a b EQ

-- Boolean equality and comparison
-- Min and max
-- Dividing by 2
-- Parity
-- Power
-- Square
-- Base-2 logarithm
-- Digits in number
-- Euclidean division
-- GCD
-- Square root
-- or, and, diff, xor, shifts
-- Checking whether a bit is set
-- Same but with index in Bin
-- TODO

-- Translation from Bin to Nat

toNatBin : (a: Bin) -> Nat
toNatBin BinO = 0
toNatBin (BinP a') = toNatBip a'

-- Nat to Bin
-- TODO

-- Iteration of a function

-- Idris specific

fromIntegerBin : Integer -> Bin
fromIntegerBin 0 = BinO
fromIntegerBin n =
  if (n > 1)
    then BinP (fromIntegerBip n)
    else BinP U

Eq Bin where
  BinO == BinO = True
  BinO == (BinP b) = False
  (BinP a) == BinO = False
  (BinP a) == (BinP b) = (a == b)

Cast Bin Nat where
  cast = toNatBin

Cast Bin Integer where
  cast = (cast {to=Integer}) . toNatBin

Ord Bin where
  compare = binCompare

Num Bin where
  (+) = binPlus
  (*) = binMult
  fromInteger = fromIntegerBin

-- TODO: Where does this come from?
||| Modulo
binMod : (a: Bip) -> (b: Bip) -> Bin
binMod U b = if (O U) <= b
               then BinP U
               else BinO
binMod (O a') b = let r = binMod a' b in
                  let r' = binD r in
                    if r' < (BinP b)
                      then r'
                      else binMinus r' (BinP b)
binMod (I a') b = let r = binMod a' b in
                  let r' = binSucc (binD r) in
                    if r' < (BinP b)
                      then r'
                      else binMinus r' (BinP b)
