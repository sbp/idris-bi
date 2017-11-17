module Data.Biz

import public Data.Bin

%default total
%access public export

-- Basic properties of constructors

Uninhabited (BizO = BizP _) where
  uninhabited Refl impossible

Uninhabited (BizP _ = BizO) where
  uninhabited Refl impossible

Uninhabited (BizO = BizM _) where
  uninhabited Refl impossible

Uninhabited (BizM _ = BizO) where
  uninhabited Refl impossible

Uninhabited (BizM _ = BizP _) where
  uninhabited Refl impossible

Uninhabited (BizP _ = BizM _) where
  uninhabited Refl impossible

bizPInj : BizP p = BizP q -> p = q
bizPInj Refl = Refl

bizMInj : BizM p = BizM q -> p = q
bizMInj Refl = Refl

-- Following Coq.ZArith.BinIntDef

||| Double
bizD : (a : Biz) -> Biz
bizD  BizO     = BizO
bizD (BizP a') = BizP (O a')
bizD (BizM a') = BizM (O a')

||| Succ double
bizDPO : (a : Biz) -> Biz
bizDPO  BizO     = BizP U
bizDPO (BizP a') = BizP (I a')
bizDPO (BizM a') = BizM (bipDMO a')

||| Pred double
bizDMO : (a : Biz) -> Biz
bizDMO  BizO     = BizM U
bizDMO (BizM a') = BizM (I a')
bizDMO (BizP a') = BizP (bipDMO a')

-- TODO: Does "bipMinuzBiz" sound too much like Bip -> Biz -> Biz?
||| Subtraction of Bip into Biz
bipMinusBiz : (a, b : Bip) -> Biz
bipMinusBiz (I a') (I b') = bizD (bipMinusBiz a' b')
bipMinusBiz (I a') (O b') = bizDPO (bipMinusBiz a' b')
bipMinusBiz (I a')  U     = BizP (O a')
bipMinusBiz (O a') (I b') = bizDMO (bipMinusBiz a' b')
bipMinusBiz (O a') (O b') = bizD (bipMinusBiz a' b')
bipMinusBiz (O a')  U     = BizP (bipDMO a')
bipMinusBiz  U     (I b') = BizM (O b')
bipMinusBiz  U     (O b') = BizM (bipDMO b')
bipMinusBiz  U      U     = BizO

||| Addition
bizPlus : (a, b : Biz) -> Biz
bizPlus  BizO      b        = b
bizPlus  a         BizO     = a
bizPlus (BizP a') (BizP b') = BizP (bipPlus a' b')
bizPlus (BizP a') (BizM b') = bipMinusBiz a' b'
bizPlus (BizM a') (BizP b') = bipMinusBiz b' a'
bizPlus (BizM a') (BizM b') = BizM (bipPlus a' b')

||| Opposite
bizOpp : (a : Biz) -> Biz
bizOpp  BizO     = BizO
bizOpp (BizP a') = BizM a'
bizOpp (BizM a') = BizP a'

||| Successor
bizSucc : (a : Biz) -> Biz
bizSucc a = bizPlus a (BizP U)

||| Predecessor
bizPred : (a : Biz) -> Biz
bizPred a = bizPlus a (BizM U)

||| Subtraction
bizMinus : (a, b : Biz) -> Biz
bizMinus a b = bizPlus a (bizOpp b)

||| Multiplication
bizMult : (a, b : Biz) -> Biz
bizMult  BizO      _        = BizO
bizMult  _         BizO     = BizO
bizMult (BizP a') (BizP b') = BizP (bipMult a' b')
bizMult (BizP a') (BizM b') = BizM (bipMult a' b')
bizMult (BizM a') (BizP b') = BizM (bipMult a' b')
bizMult (BizM a') (BizM b') = BizP (bipMult a' b')

||| Power

bizPowBip : (a : Biz) -> (b : Bip) -> Biz
bizPowBip a b = bipIter (bizMult a) (BizP U) b

bizPow : (a, b : Biz) -> Biz
bizPow a (BizP b') = bizPowBip a b'
bizPow _  BizO     = BizP U
bizPow _ (BizM _)  = BizO

||| Square
bizSquare : (a : Biz) -> Biz
bizSquare  BizO     = BizO
bizSquare (BizP a') = BizP (bipSquare a')
bizSquare (BizM a') = BizP (bipSquare a')

||| Comparison
bizCompare : (a, b : Biz) -> Ordering
bizCompare  BizO      BizO     = EQ
bizCompare  BizO     (BizP _)  = LT
bizCompare  BizO     (BizM _)  = GT
bizCompare (BizP _)   BizO     = GT
bizCompare (BizP a') (BizP b') = bipCompare a' b' EQ
bizCompare (BizP _)  (BizM _)  = GT
bizCompare (BizM _)   BizO     = LT
bizCompare (BizM _)  (BizP _)  = LT
bizCompare (BizM a') (BizM b') = bipCompare b' a' EQ

||| Sign
bizSign : (a : Biz) -> Biz
bizSign  BizO    = BizO
bizSign (BizP _) = BizP U
bizSign (BizM _) = BizM U

-- Boolean comparisons are implemented in Ord

-- Helper for bizMin and bizMax, to work around #4001
bizMinMaxHelp : (a, b : Biz) -> Ordering -> Biz
bizMinMaxHelp _ b LT = b
bizMinMaxHelp a _ _  = a

||| Max
bizMax : (a, b : Biz) -> Biz
bizMax a b = bizMinMaxHelp a b (bizCompare a b)

||| Min
bizMin : (a, b : Biz) -> Biz
bizMin a b = bizMinMaxHelp b a (bizCompare a b)

||| Absolute value
bizAbs : (a : Biz) -> Biz
bizAbs  BizO     = BizO
bizAbs (BizP a') = BizP a'
bizAbs (BizM a') = BizP a'

||| Biz to Nat via absolute
bizAbsNat : (a : Biz) -> Nat
bizAbsNat  BizO     = Z
bizAbsNat (BizP a') = toNatBip a'
bizAbsNat (BizM a') = toNatBip a'

||| Biz to Bin via absolute
bizAbsBin : (a : Biz) -> Bin
bizAbsBin  BizO     = BinO
bizAbsBin (BizP a') = BinP a'
bizAbsBin (BizM a') = BinP a'

||| Biz to Nat, rounding negative numbers to zero
toNatBiz : (a : Biz) -> Nat
toNatBiz (BizP a') = toNatBip a'
toNatBiz  _        = Z

||| Biz to Bin, rounding negative numbers to zero
toBinBiz : (a : Biz) -> Bin
toBinBiz (BizP a') = BinP a'
toBinBiz  _        = BinO

||| Nat to Biz
toBizNat : (n : Nat) -> Biz
toBizNat  Z     = BizO
toBizNat (S n') = BizP (toBipNatSucc n')

||| Bin to Biz
toBizBin : (a : Bin) -> Biz
toBizBin  BinO     = BizO
toBizBin (BinP a') = BizP a'

||| Biz to Bip, rounding non-positive numbers to one
toBipBiz : (a: Biz) -> Bip
toBipBiz (BizP a') = a'
toBipBiz  _        = U

||| Iteration
bizIter : (f : ty -> ty) -> (a : Biz) -> (b : ty) -> ty
bizIter f (BizP a') b = bipIter f b a'
bizIter _  _        b = b

||| Euclidean division on Biz and Bin

-- Helper for bipzDivEuclid, to work around #4001
bipzDivEuclidHelp : (q,r,s : Biz) -> (o : Ordering) -> (Biz, Biz)
bipzDivEuclidHelp q r _ LT = (bizD q, r)
bipzDivEuclidHelp q r s EQ = (bizDPO q, bizMinus r s)
bipzDivEuclidHelp q r s GT = (bizDPO q, bizMinus r s)

bipzDivEuclid : (a : Bip) -> (b : Biz) -> (Biz, Biz)
bipzDivEuclid U b =
  case bizCompare (BizP (O U)) b of
    LT => (BizO, BizP U)
    EQ => (BizO, BizP U)
    GT => (BizP U, BizO)
bipzDivEuclid (O a') b =
  let qr = bipzDivEuclid a' b
      r' = bizD $ snd qr in
    bipzDivEuclidHelp (fst qr) r' b (bizCompare r' b)
bipzDivEuclid (I a') b =
  let qr = bipzDivEuclid a' b
      r' = bizDPO $ snd qr in
    bipzDivEuclidHelp (fst qr) r' b (bizCompare r' b)

||| Euclidean division into remainder and modulo

-- Helpers for bizDivEuclid, to work around #4001
bizDivEuclidHelp1 : (q, r, s : Biz) -> (Biz, Biz)
bizDivEuclidHelp1 q BizO _ = (bizOpp q, BizO)
bizDivEuclidHelp1 q r    s = (bizOpp (bizSucc q), bizMinus s r)

bizDivEuclidHelp2 : (q, r, s : Biz) -> (Biz, Biz)
bizDivEuclidHelp2 q BizO _ = (bizOpp q, BizO)
bizDivEuclidHelp2 q r    s = (bizOpp (bizSucc q), bizMinus r s)

bizDivEuclid : (a, b : Biz) -> (Biz, Biz)
bizDivEuclid  BizO      _        = (BizO, BizO)
bizDivEuclid  _         BizO     = (BizO, BizO)
bizDivEuclid (BizP a') (BizP b') = bipzDivEuclid a' (BizP b')
bizDivEuclid (BizM a') (BizP b') =
  let qr = bipzDivEuclid a' (BizP b') in
  bizDivEuclidHelp1 (fst qr) (snd qr) (BizP b')
bizDivEuclid (BizM a') (BizM b') =
  let qr = bipzDivEuclid a' (BizP b') in
  (fst qr, bizOpp $ snd qr)
bizDivEuclid (BizP a') (BizM b') =
  let qr = bipzDivEuclid a' (BizP b') in
  bizDivEuclidHelp2 (fst qr) (snd qr) (BizP b')

||| Division
bizDiv : (a, b : Biz) -> Biz
bizDiv a b = fst $ bizDivEuclid a b

||| Modulo
bizMod : (a, b : Biz) -> Biz
bizMod a b = snd $ bizDivEuclid a b

||| Truncated towards zero Euclidean division
bizQuotRem : (a, b : Biz) -> (Biz, Biz)
bizQuotRem  BizO      _        = (BizO, BizO)
bizQuotRem  a         BizO     = (BizO, a)
bizQuotRem (BizP a') (BizP b') =
  let qr = bipDivEuclid a' (BinP b') in
  (toBizBin $ fst qr, toBizBin $ snd qr)
bizQuotRem (BizM a') (BizP b') =
  let qr = bipDivEuclid a' (BinP b') in
  (bizOpp $ toBizBin $ fst qr, bizOpp $ toBizBin $ snd qr)
bizQuotRem (BizP a') (BizM b') =
  let qr = bipDivEuclid a' (BinP b') in
  (bizOpp $ toBizBin $ fst qr, toBizBin $ snd qr)
bizQuotRem (BizM a') (BizM b') =
  let qr = bipDivEuclid a' (BinP b') in
  (toBizBin $ fst qr, bizOpp $ toBizBin $ snd qr)

||| TTZ Euclidean division
bizQuot : (a, b : Biz) -> Biz
bizQuot a b = fst $ bizQuotRem a b

||| TTZ Euclidean remainder
bizRem : (a, b : Biz) -> Biz
bizRem a b = snd $ bizQuotRem a b

||| Even parity
bizEven : (a : Biz) -> Bool
bizEven  BizO        = True
bizEven (BizP (O _)) = True
bizEven (BizM (O _)) = True
bizEven  _           = False

||| Odd parity
bizOdd : (a : Biz) -> Bool
bizOdd  BizO        = False
bizOdd (BizP (O _)) = False
bizOdd (BizM (O _)) = False
bizOdd  _           = True

||| Division by two
bizDivTwo : (a : Biz) -> Biz
bizDivTwo  BizO     = BizO
bizDivTwo (BizP U)  = BizO
bizDivTwo (BizP a') = BizP (bipDivTwo a')
bizDivTwo (BizM a') = BizM (bipDivTwoCeil a')

||| Quot by two
bizQuotTwo : (a : Biz) -> Biz
bizQuotTwo  BizO     = BizO
bizQuotTwo (BizP U)  = BizO
bizQuotTwo (BizP a') = BizP (bipDivTwo a')
bizQuotTwo (BizM U)  = BizO
bizQuotTwo (BizM a') = BizM (bipDivTwo a')

-- TODO: Call the others "log2" too?
-- TODO: Rename -Two functions -2?
||| Log2
bizLog2 : (a : Biz) -> Biz
bizLog2 (BizP (I a')) = BizP (bipDigits a')
bizLog2 (BizP (O a')) = BizP (bipDigits a')
bizLog2  _            = BizO

||| Square root with remainder

-- Helper for bizSqrtRem, to work around #4001
bizSqrtRemHelp : Bip -> Bim -> (Biz, Biz)
bizSqrtRemHelp s (BimP r) = (BizP s, BizP r)
bizSqrtRemHelp s _        = (BizP s, BizO)

bizSqrtRem : (a : Biz) -> (Biz, Biz)
bizSqrtRem  BizO     = (BizO, BizO)
bizSqrtRem (BizP a') = let sr = bipSqrtRem a' in bizSqrtRemHelp (fst sr) (snd sr)
bizSqrtRem (BizM _)  = (BizO, BizO)

||| Square root
bizSqrt : (a : Biz) -> Biz
bizSqrt (BizP a') = BizP (bipSqrt a')
bizSqrt  _        = BizO

||| GCD
bizGCD : (a, b : Biz) -> Biz
bizGCD  BizO      b        = bizAbs b
bizGCD  a         BizO     = bizAbs a
bizGCD (BizP a') (BizP b') = BizP (bipGCD a' b')
bizGCD (BizP a') (BizM b') = BizP (bipGCD a' b')
bizGCD (BizM a') (BizP b') = BizP (bipGCD a' b')
bizGCD (BizM a') (BizM b') = BizP (bipGCD a' b')

||| Generalised GCD
bizGGCD : (a, b : Biz) -> (Biz, (Biz, Biz))
bizGGCD  BizO      b        = (bizAbs b, (BizO, bizSign b))
bizGGCD  a         BizO     = (bizAbs a, (bizSign a, BizO))
bizGGCD (BizP a') (BizP b') =
  let gaabb = bipGGCD a' b'
      g = fst gaabb
      aa = fst $ snd gaabb
      bb = snd $ snd gaabb in
  (BizP g, (BizP aa, BizP bb))
bizGGCD (BizP a') (BizM b') =
  let gaabb = bipGGCD a' b'
      g = fst gaabb
      aa = fst $ snd gaabb
      bb = snd $ snd gaabb in
  (BizP g, (BizP aa, BizM bb))
bizGGCD (BizM a') (BizP b') =
  let gaabb = bipGGCD a' b'
      g = fst gaabb
      aa = fst $ snd gaabb
      bb = snd $ snd gaabb in
  (BizP g, (BizM aa, BizP bb))
bizGGCD (BizM a') (BizM b') =
  let gaabb = bipGGCD a' b'
      g = fst gaabb
      aa = fst $ snd gaabb
      bb = snd $ snd gaabb in
  (BizP g, (BizM aa, BizM bb))

-- TODO: Should be a Biz -> Bin -> Biz version of this
||| Test bit
bizTestBit : (a, b : Biz) -> Bool
bizTestBit  a         BizO     = bizOdd a
bizTestBit  BizO     (BizP _ ) = False
bizTestBit (BizP a') (BizP b') = bipTestBit a' (BinP b')
bizTestBit (BizM a') (BizP b') = not (binTestBit (bipPredBin a') (BinP b'))
bizTestBit  _        (BizM _ ) = False

||| Shift left
bizShiftL : (a, b : Biz) -> Biz
bizShiftL a  BizO     = a
bizShiftL a (BizP b') = bipIter (bizMult (BizP (O U))) a b'  -- TODO should this be just `bizD`?
bizShiftL a (BizM b') = bipIter bizDivTwo a b'

||| Shift right
bizShiftR : (a, b : Biz) -> Biz
bizShiftR a b = bizShiftL a (bizOpp b)

bizShiftin : (b : Bool) -> (x : Biz) -> Biz
bizShiftin True  x = bizDPO x
bizShiftin False x = bizD x

bizZeroExt : (n, x : Biz) -> Biz
bizZeroExt n = bizIter (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) n (\_ => BizO)

bizSignExt : (n, x : Biz) -> Biz
bizSignExt n = bizIter (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) (bizPred n) (\x => if bizOdd x then BizM U else BizO)

||| Logical OR
bizOr : (a, b : Biz) -> Biz
bizOr  BizO      b        = b
bizOr  a         BizO     = a
bizOr (BizP a') (BizP b') = BizP (bipOr a' b')
bizOr (BizM a') (BizP b') =
  BizM (binSuccBip (binDiff (bipPredBin a') (BinP b')))
bizOr (BizP a') (BizM b') =
  BizM (binSuccBip (binDiff (bipPredBin b') (BinP a')))
bizOr (BizM a') (BizM b') =
  BizM (binSuccBip (binAnd (bipPredBin a') (bipPredBin b')))

||| Logical AND
bizAnd : (a, b : Biz) -> Biz
bizAnd  BizO      _        = BizO
bizAnd  _         BizO     = BizO
bizAnd (BizP a') (BizP b') = toBizBin (bipAnd a' b')
bizAnd (BizM a') (BizP b') = toBizBin (binDiff (BinP b') (bipPredBin a'))
bizAnd (BizP a') (BizM b') = toBizBin (binDiff (BinP a') (bipPredBin b'))
bizAnd (BizM a') (BizM b') =
  BizM (binSuccBip (binOr (bipPredBin a') (bipPredBin b')))

||| Logical DIFF
bizDiff : (a, b : Biz) -> Biz
bizDiff  BizO      _        = BizO
bizDiff  a         BizO     = a
bizDiff (BizP a') (BizP b') = toBizBin (bipDiff a' b')
bizDiff (BizM a') (BizP b') =
  BizM (binSuccBip (binOr (bipPredBin a') (BinP b')))
bizDiff (BizP a') (BizM b') = toBizBin (binAnd (BinP a') (bipPredBin b'))
bizDiff (BizM a') (BizM b') = toBizBin (binDiff (bipPredBin b') (bipPredBin a'))

||| Logical OR
bizXor : (a, b : Biz) -> Biz
bizXor  BizO      b        = b
bizXor  a         BizO     = a
bizXor (BizP a') (BizP b') = toBizBin (bipXor a' b')
bizXor (BizM a') (BizP b') =
  BizM (binSuccBip (binXor (bipPredBin a') (BinP b')))
bizXor (BizP a') (BizM b') =
  BizM (binSuccBip (binXor (BinP a') (bipPredBin b')))
bizXor (BizM a') (BizM b') =
  toBizBin (binXor (bipPredBin a') (bipPredBin b'))

-- Idris specific

fromIntegerBiz : Integer -> Biz
fromIntegerBiz 0 = BizO
fromIntegerBiz n =
  if n > 0
    then BizP (fromIntegerBip n)
    else BizM (fromIntegerBip (-n))

-- TODO something faster
toIntegerBiz : Biz -> Integer
toIntegerBiz  BizO    = 0
toIntegerBiz (BizP a) = cast {to=Integer} $ toNatBip a
toIntegerBiz (BizM a) = -(cast {to=Integer} $ toNatBip a)
Eq Biz where
  BizO     ==  BizO    = True
  BizO     == (BizP _) = False
  BizO     == (BizM _) = False
  (BizP _) ==  BizO    = False
  (BizM _) ==  BizO    = False
  (BizM _) == (BizP _) = False
  (BizP _) == (BizM _) = False
  (BizP a) == (BizP b) = a == b
  (BizM a) == (BizM b) = a == b

Cast Nat Biz where
  cast = toBizNat

Cast Biz Nat where
  cast = toNatBiz

-- TODO something better
Cast Biz Int where
  cast = (cast {to=Int}) . (cast {to=String}) . toIntegerBiz

Cast Biz Integer where
  cast = toIntegerBiz

Cast Biz Bip where
  cast = toBipBiz

Cast Biz Bin where
  cast = toBinBiz

-- Cast Bip Biz where
--   cast = ?

Cast Bin Biz where
  cast = toBizBin

Ord Biz where
  compare = bizCompare
  max = bizMax
  min = bizMin

Num Biz where
  (+)         = bizPlus
  (*)         = bizMult
  fromInteger = fromIntegerBiz

Neg Biz where
  negate = bizOpp
  abs    = bizAbs
  (-)    = bizMinus

-- TODO Integral instance? which div+mod to use?

DecEq Biz where
  decEq  BizO     BizO    = Yes Refl
  decEq  BizO    (BizP _) = No uninhabited
  decEq  BizO    (BizM _) = No uninhabited
  decEq (BizP _)  BizO    = No uninhabited
  decEq (BizP a) (BizP b) = case decEq a b of
    Yes prf   => Yes $ cong prf
    No contra => No $ contra . bizPInj
  decEq (BizP _) (BizM _) = No uninhabited
  decEq (BizM _)  BizO    = No uninhabited
  decEq (BizM _) (BizP _) = No uninhabited
  decEq (BizM a) (BizM b) = case decEq a b of
    Yes prf   => Yes $ cong prf
    No contra => No $ contra . bizMInj
