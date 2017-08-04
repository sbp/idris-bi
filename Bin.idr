module Bin

import public Bi
import public Bip

%default total
%access public export

-- Following Coq.NArith.BinNatDef

-- Operation x -> 2*x+1
-- TODO

||| Operation x -> 2*x
binD : (a: Bin) -> Bin
binD BinZ = BinZ
binD (BinP a') = BinP (O a')

||| Successor
binSucc : (a: Bin) -> Bin
binSucc BinZ = BinP U
binSucc (BinP a') = BinP (bipSucc a')

-- Predecessor
-- The successor of Bin seen as a Bip

||| Addition
binPlus : (a: Bin) -> (b: Bin) -> Bin
binPlus BinZ BinZ = BinZ
binPlus BinZ (BinP b') = BinP b'
binPlus (BinP a') BinZ = BinP a'
binPlus (BinP a') (BinP b') = BinP (bipPlus a' b')

||| Subtraction
binMinus : (a: Bin) -> (b: Bin) -> Bin
binMinus BinZ BinZ = BinZ
binMinus BinZ (BinP b') = BinZ
binMinus (BinP a') BinZ = BinP a'
binMinus (BinP a') (BinP b') = if a' > b'
                                 then BinP (bipMinus a' b')
                                 else BinZ

||| Multiplication
binMult : (a: Bin) -> (b: Bin) -> Bin
binMult BinZ BinZ = BinZ
binMult BinZ (BinP b') = BinZ
binMult (BinP a') BinZ = BinZ
binMult (BinP a') (BinP b') = BinP (bipMult a' b')

||| Order
binCompare : (a: Bin) -> (b: Bin) -> Ordering
binCompare BinZ BinZ = EQ
binCompare BinZ (BinP b) = LT
binCompare (BinP a) BinZ = GT
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
toNatBin BinZ = 0
toNatBin (BinP a') = toNatBip a'

-- Nat to Bin
-- TODO

-- Iteration of a function

-- Idris specific

fromIntegerBin : Integer -> Bin
fromIntegerBin 0 = BinZ
fromIntegerBin n =
  if (n > 1)
    then BinP (fromIntegerBip n)
    else BinP U

Eq Bin where
  BinZ == BinZ = True
  BinZ == (BinP b) = False
  (BinP a) == BinZ = False
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
               else BinZ
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
