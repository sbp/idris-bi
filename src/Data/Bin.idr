module Data.Bin

import public Data.Bip

%default total
%access public export

-- Basic properties of constructors

Uninhabited (BinO = BinP _) where
  uninhabited Refl impossible

Uninhabited (BinP _ = BinO) where
 uninhabited Refl impossible

binPInj : BinP p = BinP q -> p = q
binPInj Refl = Refl

-- Following Coq.NArith.BinNatDef

||| Operation x -> 2*x+1
binDPO : (a : Bin) -> Bin
binDPO  BinO     = BinP U
binDPO (BinP a') = BinP (I a')

||| Operation x -> 2*x
binD : (a : Bin) -> Bin
binD  BinO     = BinO
binD (BinP a') = BinP (O a')

||| Successor
binSucc : (a : Bin) -> Bin
binSucc  BinO     = BinP U
binSucc (BinP a') = BinP (bipSucc a')

||| Predecessor
binPred : (a : Bin) -> Bin
binPred  BinO     = BinO
binPred (BinP a') = bipPredBin a'

||| The successor of Bin seen as a Bip
binSuccBip : (a : Bin) -> Bip
binSuccBip  BinO     = U
binSuccBip (BinP a') = bipSucc a'

||| Addition
binPlus : (a, b : Bin) -> Bin
binPlus  BinO      BinO     = BinO
binPlus  BinO     (BinP b') = BinP b'
binPlus (BinP a')  BinO     = BinP a'
binPlus (BinP a') (BinP b') = BinP (bipPlus a' b')

bimToBin : (a : Bim) -> Bin
bimToBin (BimP a') = BinP a'
bimToBin  _        = BinO

||| Subtraction
binMinus : (a, b : Bin) -> Bin
binMinus  BinO      BinO     = BinO
binMinus  BinO     (BinP b') = BinO
binMinus (BinP a')  BinO     = BinP a'
binMinus (BinP a') (BinP b') = bimToBin (bimMinus a' b')

||| Multiplication
binMult : (a, b : Bin) -> Bin
binMult  BinO      BinO     = BinO
binMult  BinO     (BinP b') = BinO
binMult (BinP a')  BinO     = BinO
binMult (BinP a') (BinP b') = BinP (bipMult a' b')

||| Order
binCompare : (a, b : Bin) -> Ordering
binCompare  BinO     BinO    = EQ
binCompare  BinO    (BinP b) = LT
binCompare (BinP a)  BinO    = GT
binCompare (BinP a) (BinP b) = bipCompare a b EQ

-- Boolean equality and comparison
-- Implemented below in Ord

||| Min
binMin : (a, b : Bin) -> Bin
binMin a b = case binCompare a b of
               LT => a
               EQ => a
               GT => b

||| Max
binMax : (a, b : Bin) -> Bin
binMax a b = case binCompare a b of
               LT => b
               EQ => b
               GT => a

||| Dividing by 2
binDivTwo : (a : Bin) -> Bin
binDivTwo  BinO         = BinO
binDivTwo (BinP  U)     = BinO
binDivTwo (BinP (O a')) = BinP a'
binDivTwo (BinP (I a')) = BinP a'

||| Even parity
binEven : (a : Bin) -> Bool
binEven  BinO        = True
binEven (BinP (O _)) = True
binEven  _           = False

||| Odd parity
binOdd : (a : Bin) -> Bool
binOdd = not . binEven

||| Power
binPow : (a, b : Bin) -> Bin
binPow  _         BinO     = BinP U
binPow  BinO      _        = BinO
binPow (BinP a') (BinP b') = BinP (bipPow a' b')

||| Square
binSquare : (a : Bin) -> Bin
binSquare  BinO     = BinO
binSquare (BinP a') = BinP (bipSquare a')

||| Base-2 logarithm
binLogTwo : (a : Bin) -> Bin
binLogTwo  BinO         = BinO
binLogTwo (BinP  U)     = BinO
binLogTwo (BinP (O a')) = BinP (bipDigits a')
binLogTwo (BinP (I a')) = BinP (bipDigits a')

||| Digits in number
binDigits : (a : Bin) -> Bin
binDigits  BinO     = BinO
binDigits (BinP a') = BinP (bipDigits a')

||| Digits in number, as Nat
binDigitsNat : (a : Bin) -> Nat
binDigitsNat  BinO     = Z
binDigitsNat (BinP a') = bipDigitsNat a'

-- Helper for bipDivEuclid, to work around #4001
bipDivEuclidHelp : (q, r, b : Bin) -> (o : Ordering) -> (Bin, Bin)
bipDivEuclidHelp q r b LT = (binDPO q, binMinus r b)
bipDivEuclidHelp q r b EQ = (binDPO q, binMinus r b)
bipDivEuclidHelp q r b GT = (binD q, r)

||| Euclidean division on Bip and Bin
bipDivEuclid : (a : Bip) -> (b : Bin) -> (Bin, Bin)
bipDivEuclid  U     (BinP U) = (BinP U, BinO)
bipDivEuclid  U      _       = (BinO, BinP U)
bipDivEuclid (O a')  b       =
  let qr = bipDivEuclid a' b
      q = fst qr
      r = snd qr
      r' = binD r in
     bipDivEuclidHelp q r' b (binCompare b r')
bipDivEuclid (I a')  b       =
  let qr = bipDivEuclid a' b
      q = fst qr
      r = snd qr
      r' = binDPO r in
     bipDivEuclidHelp q r' b (binCompare b r')

||| Euclidean division into remainder and modulo
binDivEuclid : (a, b : Bin) -> (Bin, Bin)
binDivEuclid  BinO     _    = (BinO, BinO)
binDivEuclid  a        BinO = (BinO, a)
binDivEuclid (BinP a') b    = bipDivEuclid a' b

||| Euclidean division
binDiv : (a, b : Bin) -> Bin
binDiv a b = fst (binDivEuclid a b)

||| Euclidean modulo
binModulo : (a, b : Bin) -> Bin
binModulo a b = snd (binDivEuclid a b)

||| GCD
binGCD : (a, b: Bin) -> Bin
binGCD  BinO      b        = b
binGCD  a         BinO     = a
binGCD (BinP a') (BinP b') = BinP (bipGCD a' b')

||| Generalised GCD
binGGCD : (a, b: Bin) -> (Bin, (Bin, Bin))
binGGCD  BinO      b        = (b, (BinO, BinP U))
binGGCD  a         BinO     = (a, (BinP U, BinO))
binGGCD (BinP a') (BinP b') =
  let gaabb = bipGGCD a' b'
      g = fst gaabb
      aa = fst $ snd gaabb
      bb = snd $ snd gaabb
  in
      (BinP g, (BinP aa, BinP bb))

-- Helper for binSqrtRem, to work around #4001
bipSqrtRemHelp : Bip -> Bim -> (Bin, Bin)
bipSqrtRemHelp s (BimP r) = (BinP s, BinP r)
bipSqrtRemHelp s  _       = (BinP s, BinO)

||| Square root with remainder
binSqrtRem : (a : Bin) -> (Bin, Bin)
binSqrtRem  BinO     = (BinO, BinO)
binSqrtRem (BinP a') = let qr = bipSqrtRem a' in
                       bipSqrtRemHelp (fst qr) (snd qr)

||| Square root
binSqrt : (a : Bin) -> Bin
binSqrt  BinO     = BinO
binSqrt (BinP a') = BinP (bipSqrt a')

||| Logical OR
binOr : (a, b : Bin) -> Bin
binOr  BinO      b        = b
binOr  a         BinO     = a
binOr (BinP a') (BinP b') = BinP (bipOr a' b')

||| Logical AND
binAnd : (a, b : Bin) -> Bin
binAnd  BinO      b        = BinO
binAnd  a         BinO     = BinO
binAnd (BinP a') (BinP b') = bipAnd a' b'

||| Logical DIFF
binDiff : (a, b : Bin) -> Bin
binDiff  BinO      b        = BinO
binDiff  a         BinO     = a
binDiff (BinP a') (BinP b') = bipDiff a' b'

||| Logical XOR
binXor : (a, b : Bin) -> Bin
binXor  BinO      b        = b
binXor  a         BinO     = a
binXor (BinP a') (BinP b') = bipXor a' b'

||| Shift left
binShiftL : (a, b : Bin) -> Bin
binShiftL  BinO     _ = BinO
binShiftL (BinP a') b = BinP (bipShiftL a' b)

||| Shift right
binShiftR : (a, b : Bin) -> Bin
binShiftR a  BinO     = a
binShiftR a (BinP b') = bipIter binDivTwo a b'

||| Checking whether a bit is set
binTestBitNat : (a : Bin) -> (b : Nat) -> Bool
binTestBitNat  BinO     _ = False
binTestBitNat (BinP a') b = bipTestBitNat a' b

||| Checking whether a bit is set, with index in Bin
binTestBit : (a, b : Bin) -> Bool
binTestBit  BinO     _ = False
binTestBit (BinP a') b = bipTestBit a' b

||| Translation from Bin to Nat
toNatBin : (a : Bin) -> Nat
toNatBin  BinO     = Z
toNatBin (BinP a') = toNatBip a'

||| Nat to Bin
toBinNat : (a : Nat) -> Bin
toBinNat  Z     = BinO
toBinNat (S a') = BinP (toBipNatSucc a')

-- Seems to be reversed from bipIter for no reason
||| Iteration of a function
binIter : {ty : Type} -> (f : ty -> ty) -> (a : Bin) -> (b : ty) -> ty
binIter f  BinO     b = b
binIter f (BinP a') b = bipIter f b a'

-- Idris specific

fromIntegerBin : Integer -> Bin
fromIntegerBin 0 = BinO
fromIntegerBin n =
  if (n > 1)
    then BinP (fromIntegerBip n)
    else BinP U

Eq Bin where
  BinO     ==  BinO    = True
  BinO     == (BinP b) = False
  (BinP a) ==  BinO    = False
  (BinP a) == (BinP b) = (a == b)

Cast Bin Nat where
  cast = toNatBin

Cast Bin Integer where
  cast = (cast {to=Integer}) . toNatBin

Ord Bin where
  compare = binCompare

Num Bin where
  (+)         = binPlus
  (*)         = binMult
  fromInteger = fromIntegerBin

-- negate and abs don't make much sense here, but it's syntactically convenient
Neg Bin where
  negate = const BinO
  (-) = binMinus
  abs = id

Integral Bin where
  div = binDiv
  mod = binModulo

DecEq Bin where
  decEq  BinO     BinO    = Yes Refl
  decEq  BinO    (BinP _) = No absurd
  decEq (BinP _)  BinO    = No absurd
  decEq (BinP a) (BinP b) = case decEq a b of
    Yes prf => Yes $ cong prf
    No contra => No $ contra . binPInj

-- TODO: Where does this come from?
||| Modulo
binMod : (a, b : Bip) -> Bin
binMod U b =
  if (O U) <= b
    then BinP U
    else BinO
binMod (O a') b =
  let r = binMod a' b
      r' = binD r in
      if r' < (BinP b)
        then r'
        else binMinus r' (BinP b)
binMod (I a') b =
  let r = binMod a' b
      r' = binSucc (binD r) in
      if r' < (BinP b)
        then r'
        else binMinus r' (BinP b)
