module Bi

import Prelude.Interfaces

%default total
%access public export

||| Little endian positive binary number
data Bip =
  ||| One, acting like a most-significant one digit.
  ||| (Mnemonic: U for Unit)
  U |
  ||| Twice the inner term, acting like a zero digit.
  ||| (Mnemonic: O for digit 0)
  O Bip |
  ||| Twice the inner term plus one, acting like a non-most-sig one digit.
  ||| (Mnemonic: I for digit 1)
  I Bip

-- Name hints for interactive editing
%name Bip a,b,c,d,e

Uninhabited (O a = I a) where
  uninhabited Refl impossible

Uninhabited (O a = U) where
  uninhabited Refl impossible

Uninhabited (I a = U) where
  uninhabited Refl impossible

||| Natural binary number
data Bin =
  ||| Zero
  BZero |
  ||| Positive binary number
  BPos Bip

%name Bin k,j,l,m,n

||| Binary number mask
data BinM =
   ||| Zero mask
   BZeroM |
   ||| Positive mask, containing a positive binary number
   BPosM Bip |
   ||| Negative mask
   BNegM

%name BinM k,j,l,m,n

||| Binary number
data Bi =
  ||| Zero or positive binary number
  BNat Bin |
  ||| Negative binary number
  BNeg Bip

%name Bi p,q,r,s,t

isOne : Bip -> Bool
isOne U = True
isOne _ = False

bipSucc : (a: Bip) -> Bip
bipSucc U = O U
bipSucc (O a') = I a'
bipSucc (I a') = O (bipSucc a')

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

bipMultNat : (a: Bip) -> (pow2: Nat) -> Nat
bipMultNat U pow2 = pow2
bipMultNat (O a') pow2 = bipMultNat a' (pow2 + pow2)
bipMultNat (I a') pow2 = pow2 + (bipMultNat a' (pow2 + pow2))

toNatBip : (a: Bip) -> Nat
toNatBip a = bipMultNat a 1

toBipNatSucc : (n: Nat) -> Bip
toBipNatSucc Z = U
toBipNatSucc (S k) = bipSucc (toBipNatSucc k)

toBipNat : (n: Nat) -> Not (n = Z) -> Bip
toBipNat Z prf = void (prf Refl)
toBipNat (S k) _ = toBipNatSucc k

-- Double Minus One, 2*a-1
bipDMO : (a: Bip) -> Bip
bipDMO U = U
bipDMO (O a') = I (bipDMO a')
bipDMO (I a') = I (O a')

-- bipPred U is U
bipPred : (a: Bip) -> Bip
bipPred U = U
bipPred (O a') = bipDMO a'
bipPred (I a') = O a'

-- Auxiliary functions for subtraction, using BinM

-- Double Plus One, 2*a+1
bimDPO : (a: BinM) -> BinM
bimDPO BZeroM = BPosM U
bimDPO (BPosM a') = BPosM (I a')
bimDPO BNegM = BNegM

-- Double, 2*a
bimD : (a: BinM) -> BinM
bimD BZeroM = BZeroM
bimD (BPosM a') = BPosM (O a')
bimD BNegM = BNegM

-- Double Minus Two, 2*a-2
bimDMT : (a: Bip) -> BinM
bimDMT U = BZeroM
bimDMT (O a') = BPosM (O (bipDMO a'))
bimDMT (I a') = BPosM (O (O a'))

bimMinus : (a: Bip) -> (b: Bip) -> BinM
bimMinus U U = BZeroM
bimMinus U _ = BNegM
bimMinus (O a') U = BPosM (bipDMO a')
bimMinus (O a') (O b') = bimD (bimMinus a' b')
bimMinus (O a') (I b') = bimDPO (carry a' b')
  where
    carry : (a: Bip) -> (b: Bip) -> BinM
    carry U _ = BNegM
    carry (O a') U = bimDMT a'
    carry (O a') (O b') = bimDPO (carry a' b')
    carry (O a') (I b') = bimD (carry a' b')
    carry (I a') U = BPosM (bipDMO a')
    carry (I a') (O b') = bimD (bimMinus a' b')
    carry (I a') (I b') = bimDPO (carry a' b')
bimMinus (I a') U = BPosM (O a')
bimMinus (I a') (O b') = bimDPO (bimMinus a' b')
bimMinus (I a') (I b') = bimD (bimMinus a' b')

bipMinus : (a: Bip) -> (b: Bip) -> Bip
bipMinus a b = case bimMinus a b of
                 BPosM c => c
                 _ => U

bipMult : (a: Bip) -> (b: Bip) -> Bip
bipMult U b = b
bipMult (O a') b = O (bipMult a' b)
bipMult (I a') b = bipPlus b (O (bipMult a' b))

bipMult' : (a: Bip) -> (b: Bip) -> Bip
bipMult' a b = U -- ?bipMult'_rhs

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

binSucc : (a: Bin) -> Bin
binSucc BZero = BPos U
binSucc (BPos a') = BPos (bipSucc a')

binD : (a: Bin) -> Bin
binD BZero = BZero
binD (BPos a') = BPos (O a')

binPlus : (a: Bin) -> (b: Bin) -> Bin
binPlus BZero BZero = BZero
binPlus BZero (BPos b') = BPos b'
binPlus (BPos a') BZero = BPos a'
binPlus (BPos a') (BPos b') = BPos (bipPlus a' b')

binMult : (a: Bin) -> (b: Bin) -> Bin
binMult BZero BZero = BZero
binMult BZero (BPos b') = BZero
binMult (BPos a') BZero = BZero
binMult (BPos a') (BPos b') = BPos (bipMult a' b')

-- Conversions, needed for the interfaces

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

{- -- Slower, with fewer assertions
fromIntegerBip' 0 = U
fromIntegerBip' n =
  if (n > 1)
    then bipSucc (fromIntegerBip' (assert_smaller n (n - 1)))
    else U
-}

fromIntegerBin : Integer -> Bin
fromIntegerBin 0 = BZero
fromIntegerBin n =
  if (n > 1)
    then BPos (fromIntegerBip n)
    else BPos U

toNatBin : (a: Bin) -> Nat
toNatBin BZero = 0
toNatBin (BPos a') = toNatBip a'

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

binMinus : (a: Bin) -> (b: Bin) -> Bin
binMinus BZero BZero = BZero
binMinus BZero (BPos b') = BZero
binMinus (BPos a') BZero = BPos a'
binMinus (BPos a') (BPos b') = if a' > b'
                                 then BPos (bipMinus a' b')
                                 else BZero

Num Bip where
  (+) = bipPlus
  (*) = bipMult
  fromInteger = fromIntegerBip

Eq Bin where
  BZero == BZero = True
  BZero == (BPos b) = False
  (BPos a) == BZero = False
  (BPos a) == (BPos b) = (a == b)

Cast Bin Nat where
  cast = toNatBin

Cast Bin Integer where
  cast = (cast {to=Integer}) . toNatBin

Ord Bin where
  compare BZero BZero = EQ
  compare BZero (BPos b) = LT
  compare (BPos a) BZero = GT
  compare (BPos a) (BPos b) = compare a b

Num Bin where
  (+) = binPlus
  (*) = binMult
  fromInteger = fromIntegerBin

binMod : (a: Bip) -> (b: Bip) -> Bin
binMod U b = if (O U) <= b
               then BPos U
               else BZero
binMod (O a') b = let r = binMod a' b in
                  let r' = binD r in
                    if r' < (BPos b)
                      then r'
                      else binMinus r' (BPos b)
binMod (I a') b = let r = binMod a' b in
                  let r' = binSucc (binD r) in
                    if r' < (BPos b)
                      then r'
                      else binMinus r' (BPos b)
                      
