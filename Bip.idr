module Bip

import public Bi

%default total
%access public export

-- Following Coq.PArith.BinPosDef

||| Successor
bipSucc : (a: Bip) -> Bip
bipSucc U = O U
bipSucc (O a') = I a'
bipSucc (I a') = O (bipSucc a')

||| Addition
-- TODO: bipAdd?
bipPlus : (a: Bip) -> (b: Bip) -> Bip
bipPlus U U = O U
bipPlus U (O b') = I b'
bipPlus U (I b') = O (bipSucc b')
bipPlus (O a') U = I a'
bipPlus (O a') (O b') = O (bipPlus a' b')
bipPlus (O a') (I b') = I (bipPlus a' b')
bipPlus (I a') U = O (bipSucc a')
bipPlus (I a') (O b') = I (bipPlus a' b')
bipPlus (I a') (I b') = O (carry a' b')
  where
    carry : (a: Bip) -> (b: Bip) -> Bip
    carry U U = I U
    carry U (O b') = O (bipSucc b')
    carry U (I b') = I (bipSucc b')
    carry (O a') U = O (bipSucc a')
    carry (O a') (O b') = I (bipPlus a' b')
    carry (O a') (I b') = O (carry a' b')
    carry (I a') U = I (bipSucc a')
    carry (I a') (O b') = O (carry a' b')
    carry (I a') (I b') = I (carry a' b')

||| Operation x -> 2*x-1
bipDMO : (a: Bip) -> Bip
bipDMO U = U
bipDMO (O a') = I (bipDMO a')
bipDMO (I a') = I (O a')

||| Predecessor
bipPred : (a: Bip) -> Bip
bipPred U = U
bipPred (O a') = bipDMO a'
bipPred (I a') = O a'

-- Predecessor seen as Bin
-- TODO: bipPredN?

||| Auxiliary type for subtraction
data Bim =
   ||| Zero
   BimO |
   ||| Plus signed number
   BimP Bip |
   ||| Minus signed number
   BimM

%name Bim k,j,l,m,n

||| Operation x -> 2*x+1
bimDPO : (a: Bim) -> Bim
bimDPO BimO = BimP U
bimDPO (BimP a') = BimP (I a')
bimDPO BimM = BimM

||| Operation x -> 2*x
bimD : (a: Bim) -> Bim
bimD BimO = BimO
bimD (BimP a') = BimP (O a')
bimD BimM = BimM

||| Operation x -> 2*x-2
bimDMT : (a: Bip) -> Bim
bimDMT U = BimO
bimDMT (O a') = BimP (O (bipDMO a'))
bimDMT (I a') = BimP (O (O a'))

-- Predecessor with mask
-- TODO

||| Subtraction, result as a mask
bimMinus : (a: Bip) -> (b: Bip) -> Bim
bimMinus U U = BimO
bimMinus U _ = BimM
bimMinus (O a') U = BimP (bipDMO a')
bimMinus (O a') (O b') = bimD (bimMinus a' b')
bimMinus (O a') (I b') = bimDPO (carry a' b')
  where
    carry : (a: Bip) -> (b: Bip) -> Bim
    carry U _ = BimM
    carry (O a') U = bimDMT a'
    carry (O a') (O b') = bimDPO (carry a' b')
    carry (O a') (I b') = bimD (carry a' b')
    carry (I a') U = BimP (bipDMO a')
    carry (I a') (O b') = bimD (bimMinus a' b')
    carry (I a') (I b') = bimDPO (carry a' b')
bimMinus (I a') U = BimP (O a')
bimMinus (I a') (O b') = bimDPO (bimMinus a' b')
bimMinus (I a') (I b') = bimD (bimMinus a' b')

||| Subtraction, result as a Bip, and 1 if a <= b
bipMinus : (a: Bip) -> (b: Bip) -> Bip
bipMinus a b = case bimMinus a b of
                 BimP c => c
                 _ => U

||| Multiplication
bipMult : (a: Bip) -> (b: Bip) -> Bip
bipMult U b = b
bipMult (O a') b = O (bipMult a' b)
bipMult (I a') b = bipPlus b (O (bipMult a' b))

-- Iteration over a positive number
-- Power
-- Square
-- Division by 2 rounded below but for 1
-- Number of digits in a positive number
-- TODO

||| Comparison on binary positive numbers
bipCompare : (a: Bip) -> (b: Bip) -> (c: Ordering) -> Ordering
bipCompare U U c = c
bipCompare U (O a') _ = LT
bipCompare U (I a') _ = LT
bipCompare (O a') U _ = GT
bipCompare (O a') (O b') c = bipCompare a' b' c
bipCompare (O a') (I b') c = bipCompare a' b' LT
bipCompare (I a') U c = GT
bipCompare (I a') (O b') c = bipCompare a' b' GT
bipCompare (I a') (I b') c = bipCompare a' b' c

-- Min max
-- TODO

-- Boolean equality and comparisons
-- ABOVE

-- Square root for positive numbers
-- GCD
-- or, and, diff, xor, shifts
-- Checking whether a bit is set
-- Same, but with index in Bin (move to Bin?)
-- TODO

||| From Bip to Nat
toNatBip : (a: Bip) -> Nat
toNatBip a = bipMultNat a 1
  where
    bipMultNat : (a: Bip) -> (pow2: Nat) -> Nat
    bipMultNat U pow2 = pow2
    bipMultNat (O a') pow2 = bipMultNat a' (pow2 + pow2)
    bipMultNat (I a') pow2 = pow2 + (bipMultNat a' (pow2 + pow2))

-- From Nat to Bip
-- TODO

-- Idris specific

Uninhabited (O a = I a) where
  uninhabited Refl impossible

Uninhabited (O a = U) where
  uninhabited Refl impossible

Uninhabited (I a = U) where
  uninhabited Refl impossible

data Parity = Even | Odd

integerParity : Integer -> Parity
integerParity n =
  -- prim__sremBigInt is total with divisor /= 0 as here
  -- abs is not necessary since we're checking on 0 or _
  -- without abs, _ can be 1 or -1
  let remainder = assert_total (prim__sremBigInt n 2) in
    if remainder == 0
      then Even
      else Odd

fromIntegerBip : Integer -> Bip
fromIntegerBip n =
  if (n > 1)
    -- prim__sdivBigInt is total with divisor /= 0 as here
    -- quotient is n / 2, hence quotient and quotient' are < n
    -- this is true because n / 2 floors
    then let quotient = (assert_total (prim__sdivBigInt n 2))
             quotient' = (assert_smaller n quotient) in
               case integerParity n of
                 Even => O (fromIntegerBip quotient')
                 Odd => I (fromIntegerBip quotient')
    else U

Eq Bip where
  U == U = True
  (O a) == (O b) = (a == b)
  (I a) == (I b) = (a == b)
  _ == _ = False

Cast Bip Nat where
  cast = toNatBip

Cast Bip Integer where
  cast = (cast {to=Integer}) . toNatBip

Ord Bip where
  compare a b = bipCompare a b EQ

Num Bip where
  (+) = bipPlus
  (*) = bipMult
  fromInteger = fromIntegerBip
