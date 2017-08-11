module Data.Bip

import public Data.Bi

%default total
%access public export

-- Basic properties of constructors

Uninhabited (U = O _) where
  uninhabited Refl impossible

Uninhabited (O _ = U) where
  uninhabited Refl impossible

Uninhabited (U = I _) where
  uninhabited Refl impossible

Uninhabited (I _ = U) where
  uninhabited Refl impossible

Uninhabited (I _ = O _) where
  uninhabited Refl impossible

Uninhabited (O _ = I _) where
  uninhabited Refl impossible

OInj : O p = O q -> p = q
OInj Refl = Refl

IInj : Bi.I p = Bi.I q -> p = q
IInj Refl = Refl

-- Following Coq.PArith.BinPosDef

||| Successor
bipSucc : (a: Bip) -> Bip
bipSucc  U     = O U
bipSucc (O a') = I a'
bipSucc (I a') = O (bipSucc a')

mutual
  ||| Addition
  -- TODO: bipAdd?
  bipPlus : (a, b: Bip) -> Bip
  bipPlus  U      U     = O U
  bipPlus  U     (O b') = I b'
  bipPlus  U     (I b') = O (bipSucc b')
  bipPlus (O a')  U     = I a'
  bipPlus (O a') (O b') = O (bipPlus a' b')
  bipPlus (O a') (I b') = I (bipPlus a' b')
  bipPlus (I a')  U     = O (bipSucc a')
  bipPlus (I a') (O b') = I (bipPlus a' b')
  bipPlus (I a') (I b') = O (bipCarry a' b')

  bipCarry : (a, b: Bip) -> Bip
  bipCarry  U      U     = I U
  bipCarry  U     (O b') = O (bipSucc b')
  bipCarry  U     (I b') = I (bipSucc b')
  bipCarry (O a')  U     = O (bipSucc a')
  bipCarry (O a') (O b') = I (bipPlus a' b')
  bipCarry (O a') (I b') = O (bipCarry a' b')
  bipCarry (I a')  U     = I (bipSucc a')
  bipCarry (I a') (O b') = O (bipCarry a' b')
  bipCarry (I a') (I b') = I (bipCarry a' b')

||| Operation x -> 2*x-1
bipDMO : (a: Bip) -> Bip
bipDMO  U     = U
bipDMO (O a') = I (bipDMO a')
bipDMO (I a') = I (O a')

||| Predecessor
bipPred : (a: Bip) -> Bip
bipPred  U     = U
bipPred (O a') = bipDMO a'
bipPred (I a') = O a'

||| Predecessor seen as Bin
bipPredBin : (a: Bip) -> Bin
bipPredBin  U     = BinO
bipPredBin (O a') = BinP (bipDMO a')
bipPredBin (I a') = BinP (O a')

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
bimDPO  BimO     = BimP U
bimDPO (BimP a') = BimP (I a')
bimDPO  BimM     = BimM

||| Operation x -> 2*x
bimD : (a: Bim) -> Bim
bimD  BimO     = BimO
bimD (BimP a') = BimP (O a')
bimD  BimM     = BimM

||| Operation x -> 2*x-2
bimDMT : (a: Bip) -> Bim
bimDMT  U     = BimO
bimDMT (O a') = BimP (O (bipDMO a'))
bimDMT (I a') = BimP (O (O a'))

||| Predecessor with mask
bimPred : (p: Bim) -> Bim
bimPred (BimP U) = BimO
bimPred (BimP a) = BimP (bipPred a)
bimPred  BimO    = BimM
bimPred  BimM    = BimM

||| Subtraction, result as a mask
bimMinus : (a, b: Bip) -> Bim
bimMinus  U      U     = BimO
bimMinus  U      _     = BimM
bimMinus (O a')  U     = BimP (bipDMO a')
bimMinus (O a') (O b') = bimD (bimMinus a' b')
bimMinus (O a') (I b') = bimDPO (carry a' b')
  where
    carry : (a, b: Bip) -> Bim
    carry  U      _     = BimM
    carry (O a')  U     = bimDMT a'
    carry (O a') (O b') = bimDPO (carry a' b')
    carry (O a') (I b') = bimD (carry a' b')
    carry (I a')  U     = BimP (bipDMO a')
    carry (I a') (O b') = bimD (bimMinus a' b')
    carry (I a') (I b') = bimDPO (carry a' b')
bimMinus (I a')  U     = BimP (O a')
bimMinus (I a') (O b') = bimDPO (bimMinus a' b')
bimMinus (I a') (I b') = bimD (bimMinus a' b')

||| Subtraction, result as a Bip, and 1 if a <= b
bipMinus : (a, b: Bip) -> Bip
bipMinus a b = case bimMinus a b of
                 BimP c => c
                 _ => U

||| Multiplication
bipMult : (a, b: Bip) -> Bip
bipMult  U     b = b
bipMult (O a') b = O (bipMult a' b)
bipMult (I a') b = bipPlus b (O (bipMult a' b))

||| Iteration over a positive number
bipIter : {ty: Type} -> (f: ty -> ty) -> (a: ty) -> (b: Bip) -> ty
bipIter f a  U     = f a
bipIter f a (O b') = bipIter f (bipIter f a b') b'
bipIter f a (I b') = f (bipIter f (bipIter f a b') b')

||| Power
bipPow : (a, b: Bip) -> Bip
bipPow a = bipIter (bipMult a) U

||| Square
bipSquare : (a: Bip) -> Bip
bipSquare  U     = U
bipSquare (O a') = O (O (bipSquare a'))
bipSquare (I a') = I (O (bipPlus (bipSquare a') a'))

||| Division by 2 rounded below but for 1
bipDivTwo : (a: Bip) -> Bip
bipDivTwo  U     = U
bipDivTwo (O a') = a'
bipDivTwo (I a') = a'

||| Division by 2 rounded up
bipDivTwoCeil : (a: Bip) -> Bip
bipDivTwoCeil  U     = U
bipDivTwoCeil (O a') = a'
bipDivTwoCeil (I a') = bipSucc a'

||| Number of digits in Bip, into Nat
bipDigitsNat : (a: Bip) -> Nat
bipDigitsNat  U     = S Z
bipDigitsNat (O a') = S (bipDigitsNat a')
bipDigitsNat (I a') = S (bipDigitsNat a')

||| Number of digits in a positive number
bipDigits : (a: Bip) -> Bip
bipDigits  U     = U
bipDigits (O a') = bipSucc (bipDigits a')
bipDigits (I a') = bipSucc (bipDigits a')

||| Comparison on binary positive numbers
bipCompare : (a, b: Bip) -> (c: Ordering) -> Ordering
bipCompare  U      U     c = c
bipCompare  U     (O a') _ = LT
bipCompare  U     (I a') _ = LT
bipCompare (O a')  U     _ = GT
bipCompare (O a') (O b') c = bipCompare a' b' c
bipCompare (O a') (I b') c = bipCompare a' b' LT
bipCompare (I a')  U     c = GT
bipCompare (I a') (O b') c = bipCompare a' b' GT
bipCompare (I a') (I b') c = bipCompare a' b' c

||| Min
bipMin : (a, b: Bip) -> Bip
bipMin a b =
  case bipCompare a b EQ of
    GT => b
    _  => a

||| Max
bipMax : (a, b: Bip) -> Bip
bipMax a b =
  case bipCompare a b EQ of
    GT => a
    _  => b

-- Boolean equality and comparisons
-- Defined in Ord below

-- Square root helper function
bipSqrtRemStep : (f, g: Bip -> Bip) -> (Bip, Bim) -> (Bip, Bim)
bipSqrtRemStep f g (s, BimP r) =
  let s' = I (O s)
      r' = g (f r)
  in
    case bipCompare s' r' EQ of
      LT => (I s, bimMinus r' s')
      EQ => (I s, bimMinus r' s')
      _  => (O s, BimP r')
bipSqrtRemStep f g (s, _) = (O s, bimMinus (g (f U)) (O (O U)))

||| Square root with remainder
bipSqrtRem : (a: Bip) -> (Bip, Bim)
bipSqrtRem  U         = (U, BimO)
bipSqrtRem (O  U)     = (U, BimP U)
bipSqrtRem (I  U)     = (U, BimP (O U))
bipSqrtRem (O (O a')) = bipSqrtRemStep O O (bipSqrtRem a')
bipSqrtRem (I (O a')) = bipSqrtRemStep O I (bipSqrtRem a')
bipSqrtRem (O (I a')) = bipSqrtRemStep I O (bipSqrtRem a')
bipSqrtRem (I (I a')) = bipSqrtRemStep I I (bipSqrtRem a')

||| Square root
bipSqrt : (a: Bip) -> Bip
bipSqrt = fst . bipSqrtRem

-- Divide
-- TODO

||| GCD, with Nat of total combined digits
bipGCDN : (n: Nat) -> (a, b: Bip) -> Bip
bipGCDN  Z     _ _ = U
bipGCDN (S n') a b =
  case (a, b) of
    (U   , _   ) => U
    (_   , U   ) => U
    (O a', O b') => O (bipGCDN n' a' b')
    (_   , O b') => bipGCDN n' a b'
    (O a', _   ) => bipGCDN n' a' b
    (I a', I b') =>
      case bipCompare a' b' EQ of
        EQ => a
        LT => bipGCDN n' (bipMinus b' a') a
        GT => bipGCDN n' (bipMinus a' b') b

||| GCD, using the Stein binary algorithm
bipGCD : (a, b: Bip) -> Bip
bipGCD a b = bipGCDN ((bipDigitsNat a) + (bipDigitsNat b)) a b

||| Generalised GCD, with Nat of total combined digits
bipGGCDN : (n: Nat) -> (a, b: Bip) -> (Bip, (Bip, Bip))
bipGGCDN  Z     a b = (U, (a, b))
bipGGCDN (S n') a b =
  case (a, b) of
    (U   , _   ) => (U, (U, b))
    (_   , U   ) => (U, (a, U))
    (O a', O b') =>
      let (g, p) = bipGGCDN n' a' b' in
                    (O g, p)
    (_   , O b') =>
      let (g, (aa, bb)) = bipGGCDN n' a b' in
                    (g, (aa, O bb))
    (O a', _   ) =>
      let (g, (aa, bb)) = bipGGCDN n' a' b in
                    (g, (O aa, bb))
    (I a', I b') =>
      case bipCompare a' b' EQ of
        EQ => (a, (U, U))
        LT =>
          let a'' = bipMinus b' a'
              (g, (ba, aa)) = bipGGCDN n' a'' a in
              (g, (aa, bipPlus aa (O ba)))
        GT =>
          let a'' = bipMinus a' b'
              (g, (ab, bb)) = bipGGCDN n' a'' b in
              (g, (bipPlus bb (O ab), bb))

||| Generalised GCD
bipGGCD : (a, b: Bip) -> (Bip, (Bip, Bip))
bipGGCD a b = bipGGCDN ((bipDigitsNat a) + (bipDigitsNat b)) a b

||| Logical OR
bipOr : (a, b: Bip) -> Bip
bipOr  U     (O b') = I b'
bipOr  U      b     = b
bipOr (O a')  U     = I a'
bipOr  a      U     = a
bipOr (O a') (O b') = O (bipOr a' b')
bipOr (O a') (I b') = I (bipOr a' b')
bipOr (I a') (O b') = I (bipOr a' b')
bipOr (I a') (I b') = I (bipOr a' b')

binDoubleSucc : (a: Bin) -> Bin
binDoubleSucc  BinO     = BinP U
binDoubleSucc (BinP a') = BinP (I a')

binDouble : (a: Bin) -> Bin
binDouble  BinO     = BinO
binDouble (BinP a') = BinP (O a')

||| Logical AND
bipAnd : (a, b: Bip) -> Bin
bipAnd  U     (O _)  = BinO
bipAnd  U      _     = BinP U
bipAnd (O a')  U     = BinO
bipAnd  a      U     = BinP U
bipAnd (O a') (O b') = binDouble (bipAnd a' b')
bipAnd (O a') (I b') = binDouble (bipAnd a' b')
bipAnd (I a') (O b') = binDouble (bipAnd a' b')
bipAnd (I a') (I b') = binDoubleSucc (bipAnd a' b')

||| Logical DIFF
bipDiff : (a, b: Bip) -> Bin
bipDiff  U     (O _)  = BinP U
bipDiff  U      _     = BinO
bipDiff (O a')  U     = BinP (O a')
bipDiff (I a')  U     = BinP (O a')
bipDiff (O a') (O b') = binDouble (bipDiff a' b')
bipDiff (O a') (I b') = binDouble (bipDiff a' b')
bipDiff (I a') (O b') = binDouble (bipDiff a' b')
bipDiff (I a') (I b') = binDoubleSucc (bipDiff a' b')

||| Logical XOR
bipXor : (a, b: Bip) -> Bin
bipXor  U      U     = BinO
bipXor  U     (O b') = BinP (I b')
bipXor  U     (I b') = BinP (O b')
bipXor (O a')  U     = BinP (O a')
bipXor (O a') (O b') = binDouble (bipXor a' b')
bipXor (O a') (I b') = binDoubleSucc (bipXor a' b')
bipXor (I a')  U     = BinP (O a')
bipXor (I a') (O b') = binDoubleSucc (bipXor a' b')
bipXor (I a') (I b') = binDouble (bipXor a' b')

-- ShiftL and ShiftR into Nat
-- TODO

||| Shift left
bipShiftL : (a: Bip) -> (b: Bin) -> Bip
bipShiftL a  BinO     = a
bipShiftL a (BinP b') = bipIter O a b'

||| Shift right
bipShiftR : (a: Bip) -> (b: Bin) -> Bip
bipShiftR a  BinO     = a
bipShiftR a (BinP b') = bipIter bipDivTwo a b'

||| Checking whether a bit is set, with Nat
bipTestBitNat : (a: Bip) -> (n: Nat) -> Bool
bipTestBitNat  U      Z     = True
bipTestBitNat  U     (S _)  = False
bipTestBitNat (O a')  Z     = False
bipTestBitNat (O a') (S n') = bipTestBitNat a' n'
bipTestBitNat (I a')  Z     = True
bipTestBitNat (I a') (S n') = bipTestBitNat a' n'

||| Checking whether a bit is set, with Bin
bipTestBit : (a: Bip) -> (b: Bin) -> Bool
bipTestBit (O a')  BinO     = False
bipTestBit  _      BinO     = True
bipTestBit  U      _        = False
bipTestBit (O a') (BinP b') = bipTestBit a' (bipPredBin b')
bipTestBit (I a') (BinP b') = bipTestBit a' (bipPredBin b')

-- Defined in a different way in Coq.PArith.BinPosDef
-- iter_op and to_nat
||| From Bip to Nat
toNatBip : (a: Bip) -> Nat
toNatBip a = bipMultNat a 1
  where
    bipMultNat : (a: Bip) -> (pow2: Nat) -> Nat
    bipMultNat  U     pow2 = pow2
    bipMultNat (O a') pow2 = bipMultNat a' (pow2 + pow2)
    bipMultNat (I a') pow2 = pow2 + (bipMultNat a' (pow2 + pow2))

||| From Nat to Bip, with Z mapping to O
toBipNat : (n: Nat) -> Bip
toBipNat  Z     = U
toBipNat (S Z)  = U
toBipNat (S n') = bipSucc (toBipNat n')

||| From successor of Nat to Bip
toBipNatSucc : (n: Nat) -> Bip
toBipNatSucc  Z     = U
toBipNatSucc (S n') = bipSucc (toBipNatSucc n')

-- Idris specific

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
  if n > 1
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
  U     ==  U    = True
  (O a) == (O b) = (a == b)
  (I a) == (I b) = (a == b)
  _     ==  _    = False

Cast Bip Nat where
  cast = toNatBip

Cast Bip Integer where
  cast = cast {to=Integer} . toNatBip

Ord Bip where
  compare a b = bipCompare a b EQ

Num Bip where
  (+) = bipPlus
  (*) = bipMult
  fromInteger = fromIntegerBip
