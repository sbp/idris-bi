module Data.BizMod2.Bitwise

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.DivMod
import Data.Biz.Bitwise
import Data.Biz.Nat

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.AddSubMul

%access export
%default total

-- Bit-level properties

-- TODO eqmod -> eqm
eqmodSameBits : (n : Nat) -> (x, y : Biz)
             -> ((i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> bizTestBit x i = bizTestBit y i)
             -> eqmod x y (modulus n)
eqmodSameBits  Z    x y _ =
  (x-y ** rewrite mul1R (x-y) in
          rewrite sym $ addAssoc x (-y) y in
          rewrite addOppDiagL y in
          sym $ add0R x)
eqmodSameBits (S k) x y f =
  let (z**prf) = eqmodSameBits k (bizDivTwo x) (bizDivTwo y) $
                 \i,i0,ik =>
                   rewrite sym $ zTestbitSucc x i i0 in
                   rewrite sym $ zTestbitSucc y i i0 in
                   f (i+1)
                     (ltLeIncl 0 (i+1) $ leLtTrans 0 i (i+1) i0 $ ltSuccRFro i i $ leRefl i)
                     (rewrite toBizNatInjSucc k in
                      rewrite addCompareMonoR i (toBizNat k) 1 in
                      ik)
  in
  (z ** rewrite zDecomp x in
        rewrite zDecomp y in
        rewrite bizShiftinSpec (bizOdd x) (bizDivTwo x) in
        rewrite bizShiftinSpec (bizOdd y) (bizDivTwo y) in
        rewrite f 0 uninhabited Refl in    -- bizOdd x = bizOdd y
        -- TODO bug: can't simply write `if bizOdd y then ..` - INTERNAL ERROR: Unelaboratable syntactic form
        rewrite addAssoc (z*modulus (S k)) (2*bizDivTwo y) (ifThenElse (bizOdd y) (Delay (BizP U)) (Delay BizO)) in
        rewrite mulAssoc z 2 (modulus k) in
        rewrite mulComm z 2 in
        rewrite sym $ mulAssoc 2 z (modulus k) in
        rewrite sym $ mulAddDistrL 2 (z*modulus k) (bizDivTwo y) in
        cong {f = \a => 2*a + (ifThenElse (bizOdd y) (Delay (BizP U)) (Delay BizO))} prf)

sameBitsEqmod : (n : Nat) -> (x, y, i : Biz) -> eqmod x y (modulus n) -> 0 `Le` i -> i `Lt` toBizNat n
            -> bizTestBit x i = bizTestBit y i
sameBitsEqmod  Z    _ _ i    _       zlei iltn = absurd $ zlei $ ltGt i 0 iltn
sameBitsEqmod (S k) x y i (z**xy) zlei iltn    =
  case decEq i 0 of
    Yes i0 =>
      rewrite i0 in
      case evenOrOdd x of
        Left (a**eprf) =>
          let evy = xy
                 |> replace {P=\q=>x=q+y} (mulAssoc z 2 (modulus k))
                 |> replace {P=\q=>x=q*(modulus k)+y} (mulComm z 2)
                 |> replace {P=\q=>x=q+y} (sym $ mulAssoc 2 z (modulus k))
                 |> trans (sym eprf)
                 |> addTransferLZ (2*a) (2*(z*(modulus k))) y
                 |> replace {P=\q=>y=2*a+q} (sym $ mulOppR 2 (z*(modulus k)))
                 |> replace {P=\q=>y=q} (sym $ mulAddDistrL 2 a (-(z*(modulus k))))
          in
          rewrite oddNotEven x in
          rewrite oddNotEven y in
          rewrite evenSpecFro x (a**eprf) in
          rewrite evenSpecFro y (a-z*(modulus k)**evy) in
          Refl
        Right (a**oprf) =>
          let ody = xy
                 |> replace {P=\q=>x=q+y} (mulAssoc z 2 (modulus k))
                 |> replace {P=\q=>x=q*(modulus k)+y} (mulComm z 2)
                 |> replace {P=\q=>x=q+y} (sym $ mulAssoc 2 z (modulus k))
                 |> trans (sym oprf)
                 |> addTransferLZ (2*a+1) (2*(z*(modulus k))) y
                 |> replace {P=\q=>y=2*a+1+q} (sym $ mulOppR 2 (z*(modulus k)))
                 |> replace {P=\q=>y=q} (addComm (2*a+1) (2*(-(z*(modulus k)))))
                 |> replace {P=\q=>y=q} (addAssoc (2*(-(z*(modulus k)))) (2*a) 1)
                 |> replace {P=\q=>y=q+1} (sym $ mulAddDistrL 2 (-(z*(modulus k))) a)
          in
          rewrite oddSpecFro x (a**oprf) in
          rewrite oddSpecFro y (-(z*(modulus k))+a**ody) in
          Refl
    No in0 =>
      rewrite succPredZ i in
      let zleip = ltPredRTo 0 i $ leNeqLt i 0 zlei in0
          ih = sameBitsEqmod k (bizDivTwo x) (bizDivTwo y) (i-1)
                 (z ** snd $ bizShiftinInj (bizOdd x) (bizOdd y) (bizDivTwo x) (z * (modulus k) + bizDivTwo y) aux)
                 zleip
                 (rewrite sym $ addCompareMonoR (i-1) (toBizNat k) 1 in
                  rewrite sym $ addAssoc i (-1) 1 in
                  rewrite add0R i in
                  rewrite sym $ toBizNatInjSucc k in
                  iltn)
      in
      rewrite zTestbitSucc x (bizPred i) zleip in
      rewrite zTestbitSucc y (bizPred i) zleip in
      ih
  where
  aux : bizShiftin (bizOdd x) (bizDivTwo x) = bizShiftin (bizOdd y) (z * (modulus k) + bizDivTwo y)
  aux =
    rewrite sym $ zDecomp x in
    rewrite bizShiftinSpec (bizOdd y) (z * (modulus k) + bizDivTwo y) in
    rewrite mulAddDistrL 2 (z*(modulus k)) (bizDivTwo y) in
    rewrite sym $ addAssoc (2*(z*(modulus k))) (2*(bizDivTwo y)) (ifThenElse (bizOdd y) (Delay 1) (Delay 0)) in
    rewrite sym $ bizShiftinSpec (bizOdd y) (bizDivTwo y) in
    rewrite sym $ zDecomp y in
    rewrite mulAssoc 2 z (modulus k) in
    rewrite mulComm 2 z in
    rewrite sym $ mulAssoc z 2 (modulus k) in
    xy

equalSameBits : (x, y : Biz) -> ((i : Biz) -> 0 `Le` i -> bizTestBit x i = bizTestBit y i) -> x = y
equalSameBits x y f with (x `compare` y) proof xy
  | LT =
    let zltyx = replace {P = \a => a = LT} (compareSubR x y) (sym xy)
        zleyx = ltLeIncl 0 (y-x) zltyx
        (n ** yxltm) = modulusInfinity (y-x) zleyx
        yxeqm0 = eqmodSameBits n x y (\i,zlei,_ => f i zlei)
              |> eqmodSub y y x y (modulus n) (eqmodRefl y (modulus n))
              |> replace {P = \a => eqmod (y-x) a (modulus n)} (addOppDiagR y)
        yx0 = eqmodSmallEq (y-x) 0 (modulus n) yxeqm0 zleyx yxltm uninhabited Refl
        contra = replace {P = \a => 0 `Lt` a} yx0 zltyx
    in absurd contra
  | EQ = compareEqIffTo x y (sym xy)
  | GT =
    let zltxy = replace {P = \a => a = LT} (compareSubR y x) (gtLt x y $ sym xy)
        zlexy = ltLeIncl 0 (x-y) zltxy
        (n ** xyltm) = modulusInfinity (x-y) zlexy
        xyeqm0 = eqmodSameBits n y x (\i,zlei,_ => sym $ f i zlei)
              |> eqmodSub x x y x (modulus n) (eqmodRefl x (modulus n))
              |> replace {P = \a => eqmod (x-y) a (modulus n)} (addOppDiagR x)
        xy0 = eqmodSmallEq (x-y) 0 (modulus n) xyeqm0 zlexy xyltm uninhabited Refl
        contra = replace {P = \a => 0 `Lt` a} xy0 zltxy
    in absurd contra

-- TODO can't move these because of dependency on `modulus`

zTestbitAbove : (n : Nat) -> (x, i : Biz) -> 0 `Le` x -> x `Lt` modulus n -> toBizNat n `Le` i -> bizTestBit x i = False
zTestbitAbove  Z     BizO    i _    _    _    = testbit0L i
zTestbitAbove  Z    (BizP a) _ _    xltm _    = absurd $ le1L a $ ltGt a 1 xltm
zTestbitAbove  Z    (BizM _) _ zlex _    _    = absurd $ zlex Refl
zTestbitAbove (S k)  x       i zlex xltm nlei =
  let zlti = ltLeTrans 0 (toBizNat (S k)) i Refl nlei in
  rewrite zTestbitEq x i $ ltLeIncl 0 i zlti in
  rewrite neqbNeqFro i 0 $ ltNotEq i 0 zlti in
  zTestbitAbove k (bizDivTwo x) (i-1)
    (div2Pos x zlex)
    (rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus k) Refl in
     leLtTrans (2*(bizDivTwo x)) x (modulus (S k))
       (dDiv2Le x zlex)
        xltm
    )
    (rewrite sym $ addCompareMonoR (toBizNat k) (i-1) 1 in
     rewrite sym $ succPredZ i in
     rewrite sym $ toBizNatInjSucc k in
     nlei)

zTestbitAboveNeg : (n : Nat) -> (x, i : Biz) -> -(modulus n) `Le` x -> x `Lt` 0 -> toBizNat n `Le` i -> bizTestBit x i = True
zTestbitAboveNeg n x i mmlex xlt0 nlei =
  let notmxm1 = sym $ zOneComplement i x $ leTrans 0 (toBizNat n) i (toBizNatIsNonneg n) nlei
      mxm1false = zTestbitAbove n (-x-1) i
                    (ltPredRTo 0 (-x) $
                     rewrite sym $ compareOpp x 0 in
                     xlt0)
                    (ltPredLTo (-x) (modulus n) $
                     rewrite compareOpp (-x) (modulus n) in
                     rewrite oppInvolutive x in
                     mmlex)
                    nlei
  in
  rewrite sym $ notNot (bizTestBit x i) in
  rewrite trans notmxm1 mxm1false in
  Refl

-- TODO reformulate RHS as `modulus n <= x`
zSignBit : (n : Nat) -> (x : Biz) -> 0 `Le` x -> x `Lt` modulus (S n)
        -> bizTestBit x (toBizNat n) = if x < modulus n then False else True
zSignBit  Z     BizO        _    _     = Refl
zSignBit  Z    (BizP  U)    _    _     = Refl
zSignBit  Z    (BizP (O a)) _    xltsm = absurd $ nlt1R a xltsm
zSignBit  Z    (BizP (I a)) _    xltsm = absurd $ nlt1R a $ compareContGtLtTo a U xltsm
zSignBit  Z    (BizM _)     zlex _     = absurd $ zlex Refl
zSignBit (S k)  x           zlex xltsm =
  rewrite toBizNatInjSucc k in
  rewrite zTestbitSucc x (toBizNat k) (toBizNatIsNonneg k) in
  rewrite zSignBit k (bizDivTwo x)
            (div2Pos x zlex)
            (rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus (S k)) Refl in
             leLtTrans (2*(bizDivTwo x)) x (modulus (S (S k)))
               (dDiv2Le x zlex)
                xltsm
            ) in
  aux2
  where
  aux : (x : Biz) -> (k : Bip) -> BizP (O k) `Lt` x -> BizP k `Le` bizDivTwo x
  aux  BizO        _ dkltx = absurd dkltx
  aux (BizP  U)    _ dkltx = absurd dkltx
  aux (BizP (O a)) k dkltx = ltLeIncl k a dkltx
  aux (BizP (I a)) k dkltx = compareContLtLtTo k a dkltx
  aux (BizM  _)    _ dkltx = absurd dkltx
  aux2 : (if bizDivTwo x < modulus k then False else True) = (if x < modulus (S k) then False else True)
  aux2 with (x `compare` modulus (S k)) proof xsm
    | LT = rewrite ltbLtFro (bizDivTwo x) (modulus k) $
                     rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus k) Refl in
                     leLtTrans (2*(bizDivTwo x)) x (modulus (S k))
                       (dDiv2Le x zlex)
                       (sym xsm)
                   in
           Refl
    | EQ = rewrite compareEqIffTo x (modulus (S k)) (sym xsm) in
           rewrite compareContRefl (bipPow2 k) EQ in
           Refl
    | GT = let mlex2 = aux x (bipPow2 k) $ gtLt x (modulus (S k)) (sym xsm) in
           rewrite nltbLeFro (modulus k) (bizDivTwo x) mlex2 in
           Refl

zTestbitLe : (x, y : Biz) -> 0 `Le` y -> ((i : Biz) -> 0 `Le` i -> bizTestBit x i = True -> bizTestBit y i = True) -> x `Le` y
zTestbitLe x y zley =
  bizShiftinInd
    (\q => (p : Biz) -> ((i : Biz) -> 0 `Le` i -> bizTestBit p i = True -> bizTestBit q i = True) -> p `Le` q)
    (\p, fInd =>
     rewrite equalSameBits p 0 $ \i, zlei =>
               rewrite testbit0L i in
               notTrueIsFalse (bizTestBit p i) $
               \btb => absurd $ trans (sym $ testbit0L i) (fInd i zlei btb)
     in
     uninhabited)
    (\b,q,zleq,ih,p,fInd =>
      rewrite zDecomp p in
      rewrite bizShiftinSpec (bizOdd p) (bizDivTwo p) in
      rewrite bizShiftinSpec b q in
      let p2leq = ih (bizDivTwo p) $ \i, zlei, btb2 =>
                    rewrite sym $ zTestbitShiftinSucc b q i zlei in
                    fInd (i+1)
                      (leTrans 0 i (i+1) zlei $ ltLeIncl i (i+1) $ ltSuccRFro i i $ leRefl i)
                      (rewrite zTestbitSucc p i zlei in
                       btb2)
      in
      case trueOrFalse (bizOdd p) of
        Left nod =>
          rewrite nod in
          rewrite add0R (2*(bizDivTwo p)) in
          leTrans (2*(bizDivTwo p)) (2*q) (2*q + (ifThenElse b (Delay 1) (Delay 0)))
            (rewrite mulCompareMonoL 2 (bizDivTwo p) q Refl in
             p2leq)
            (case b of
               False =>
                 rewrite add0R (2*q) in
                 leRefl (2*q)
               True =>
                 ltLeIncl (2*q) ((2*q)+1) $ ltSuccRFro (2*q) (2*q) $ leRefl (2*q)
            )
        Right od =>
          rewrite od in
          rewrite trans (sym $ zTestbitShiftinBase b q) (fInd 0 uninhabited od) in   -- b = True
          rewrite addCompareMonoR (2*(bizDivTwo p)) (2*q) 1 in
          rewrite mulCompareMonoL 2 (bizDivTwo p) q Refl in
          p2leq
    )
    y zley x

-- Bit-level reasoning over type [int]
public export
testbit : (x : BizMod2 n) -> (i : Biz) -> Bool
testbit x i = bizTestBit (unsigned x) i

testbitRepr : (n : Nat) -> (x : Biz) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (repr x n) i = bizTestBit x i
testbitRepr n x i zlei iltn =
  sameBitsEqmod n (unsigned (repr x n)) x i (eqmUnsignedRepr' x n) zlei iltn

sameBitsEq : (x, y : BizMod2 n) -> ((i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit x i = testbit y i) -> x = y
sameBitsEq {n} x y f =
  rewrite sym $ reprUnsigned x in
  rewrite sym $ reprUnsigned y in
  eqmSamerepr (unsigned x) (unsigned y) n $
  eqmodSameBits n (unsigned x) (unsigned y) f

bitsAbove : (x : BizMod2 n) -> (i : Biz) -> toBizNat n `Le` i -> testbit x i = False
bitsAbove {n} x i nlei =
  let ur = unsignedRange x in
  zTestbitAbove n (unsigned x) i (fst ur) (snd ur) nlei

bitsZero : (i : Biz) -> testbit (repr 0 n) i = False
bitsZero {n} i = rewrite unsignedZero n in
                 testbit0L i

bitsOne : (n : Nat) -> (i : Biz) -> Not (n=0) -> testbit (repr 1 n) i = i == 0
bitsOne  Z    _ nz = absurd $ nz Refl
bitsOne (S _) i _  = testbit1L i

bitsMone : (n : Nat) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (repr (-1) n) i = True
bitsMone n i zlei iltn =
  rewrite testbitRepr n (-1) i zlei iltn in
  testbitM1L i zlei

-- TODO reformulate RHS as `halfModulus n <= unsigned x`
-- when `n=0` this becomes `bizTestBit 0 (-1) = True` which is wrong
signBitOfUnsigned : (x : BizMod2 n) -> Not (n=0) -> testbit x (toBizNat n - 1) = if unsigned x < halfModulus n then False else True
signBitOfUnsigned {n=Z}   _ nz = absurd $ nz Refl
signBitOfUnsigned {n=S n} x _  =
  rewrite aux n in
  let ur = unsignedRange x in
  zSignBit n (unsigned x) (fst ur) (snd ur)
  where
  aux : (n : Nat) -> bipMinusBiz (toBipNatSucc n) U = toBizNat n
  aux  Z    = Refl
  aux (S n) =
    rewrite sym $ add1R (toBipNatSucc n) in
    rewrite posSubAdd (toBipNatSucc n) 1 1 in
    Refl

-- when `n=0` this becomes `bizTestBit (-1) i = False` which is wrong
bitsSigned : (x : BizMod2 n) -> (i : Biz) -> Not (n=0) -> 0 `Le` i -> bizTestBit (signed x) i = testbit x (if i < toBizNat n then i else toBizNat n - 1)
bitsSigned {n} x i nz zlei =
  case decEq (i `compare` toBizNat n) LT of
    Yes iltn =>
      rewrite ltbLtFro i (toBizNat n) iltn in
      sameBitsEqmod n (signed x) (unsigned x) i (eqmSignedUnsigned x) zlei iltn
    No igen =>
      let nlei = geLe i (toBizNat n) igen in
      rewrite nltbLeFro (toBizNat n) i nlei in
      rewrite signBitOfUnsigned x nz in
      case decEq ((unsigned x) `compare` (halfModulus n)) LT of
        Yes xltm2 =>
          rewrite ltbLtFro (unsigned x) (halfModulus n) xltm2 in
          bitsAbove x i nlei
        No xgem2 =>
          rewrite nltbLeFro (halfModulus n) (unsigned x) $ geLe (unsigned x) (halfModulus n) xgem2 in
          zTestbitAboveNeg n (unsigned x - modulus n) i
            (rewrite addCompareMonoR 0 (unsigned x) (-(modulus n)) in
             fst $ unsignedRange x)
            (rewrite sym $ compareSub (unsigned x) (modulus n) in
             snd $ unsignedRange x)
            nlei

bitsLe : (x, y : BizMod2 n) -> ((i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit x i = True -> testbit y i = True) -> unsigned x `Le` unsigned y
bitsLe {n} x y f =
  zTestbitLe (unsigned x) (unsigned y) (fst $ unsignedRange y) $ \i, zlei, tbxt =>
  case decEq (i `compare` toBizNat n) LT of
    Yes iltn =>
      f i zlei iltn tbxt
    No igen =>
      let tbxf = bitsAbove x i $ geLe i (toBizNat n) igen in
      absurd $ trans (sym tbxt) tbxf

-- Properties of bitwise and, or, xor

bitsAnd : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (x `and` y) i = testbit x i && testbit y i
bitsAnd {n} x y i zlei iltn =
  rewrite testbitRepr n ((unsigned x) `bizAnd` (unsigned y)) i zlei iltn in
  landSpec (unsigned x) (unsigned y) i

bitsOr : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (x `or` y) i = testbit x i || testbit y i
bitsOr {n} x y i zlei iltn =
  rewrite testbitRepr n ((unsigned x) `bizOr` (unsigned y)) i zlei iltn in
  lorSpec (unsigned x) (unsigned y) i

bitsXor : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (x `xor` y) i = testbit x i `xor` testbit y i
bitsXor {n} x y i zlei iltn =
  rewrite testbitRepr n ((unsigned x) `bizXor` (unsigned y)) i zlei iltn in
  lxorSpec (unsigned x) (unsigned y) i

bitsNot : (x : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (not x) i = not (testbit x i)
bitsNot {n} x i zlei iltn =
  rewrite bitsXor x (-1) i zlei iltn in
  rewrite negRepr 1 n in
  rewrite bitsMone n i zlei iltn in
  xorTrueR (testbit x i)

andCommut : (x, y : BizMod2 n) -> x `and` y = y `and` x
andCommut x y =
  sameBitsEq (x `and` y) (y `and` x) $ \i, zlei, iltn =>
  rewrite bitsAnd x y i zlei iltn in
  rewrite bitsAnd y x i zlei iltn in
  andComm (testbit x i) (testbit y i)

andAssoc : (x, y, z : BizMod2 n) -> (x `and` y) `and` z = x `and` (y `and` z)
andAssoc x y z =
  sameBitsEq ((x `and` y) `and` z) (x `and` (y `and` z)) $ \i, zlei, iltn =>
  rewrite bitsAnd (x `and` y) z i zlei iltn in
  rewrite bitsAnd x y i zlei iltn in
  rewrite bitsAnd x (y `and` z) i zlei iltn in
  rewrite bitsAnd y z i zlei iltn in
  andbAssoc (testbit x i) (testbit y i) (testbit z i)

andZero : (x : BizMod2 n) -> x `and` 0 = 0
andZero {n} x =
  sameBitsEq (x `and` 0) 0 $ \i, zlei, iltn =>
  rewrite bitsAnd x 0 i zlei iltn in
  rewrite bitsZero {n} i in
  andFalse (testbit x i)

andZeroL : (x : BizMod2 n) -> 0 `and` x = 0
andZeroL x = rewrite andCommut 0 x in
             andZero x

andMone : (x : BizMod2 n) -> x `and` (-1) = x
andMone {n} x =
  sameBitsEq (x `and` (-1)) x $ \i, zlei, iltn =>
  rewrite bitsAnd x (-1) i zlei iltn in
  rewrite negRepr 1 n in
  rewrite bitsMone n i zlei iltn in
  andTrue (testbit x i)

andMoneL : (x : BizMod2 n) -> (-1) `and` x = x
andMoneL x = rewrite andCommut (-1) x in
             andMone x

andIdem : (x : BizMod2 n) -> x `and` x = x
andIdem x =
  sameBitsEq (x `and` x) x $ \i, zlei, iltn =>
  rewrite bitsAnd x x i zlei iltn in
  andbIdem (testbit x i)

orCommut : (x, y : BizMod2 n) -> x `or` y = y `or` x
orCommut x y =
  sameBitsEq (x `or` y) (y `or` x) $ \i, zlei, iltn =>
  rewrite bitsOr x y i zlei iltn in
  rewrite bitsOr y x i zlei iltn in
  orComm (testbit x i) (testbit y i)

orAssoc : (x, y, z : BizMod2 n) -> (x `or` y) `or` z = x `or` (y `or` z)
orAssoc x y z =
  sameBitsEq ((x `or` y) `or` z) (x `or` (y `or` z)) $ \i, zlei, iltn =>
  rewrite bitsOr (x `or` y) z i zlei iltn in
  rewrite bitsOr x y i zlei iltn in
  rewrite bitsOr x (y `or` z) i zlei iltn in
  rewrite bitsOr y z i zlei iltn in
  orbAssoc (testbit x i) (testbit y i) (testbit z i)

orZero : (x : BizMod2 n) -> x `or` 0 = x
orZero {n} x =
  sameBitsEq (x `or` 0) x $ \i, zlei, iltn =>
  rewrite bitsOr x 0 i zlei iltn in
  rewrite bitsZero {n} i in
  orFalse (testbit x i)

orZeroL : (x : BizMod2 n) -> 0 `or` x = x
orZeroL x = rewrite orCommut 0 x in
             orZero x

orMone : (x : BizMod2 n) -> x `or` (-1) = -1
orMone {n} x =
  sameBitsEq (x `or` (-1)) (-1) $ \i, zlei, iltn =>
  rewrite bitsOr x (-1) i zlei iltn in
  rewrite negRepr 1 n in
  rewrite bitsMone n i zlei iltn in
  orbTrue (testbit x i)

orIdem : (x : BizMod2 n) -> x `or` x = x
orIdem x =
  sameBitsEq (x `or` x) x $ \i, zlei, iltn =>
  rewrite bitsOr x x i zlei iltn in
  orbIdem (testbit x i)

andOrDistrib : (x, y, z : BizMod2 n) -> x `and` (y `or` z) = (x `and` y) `or` (x `and` z)
andOrDistrib x y z =
  sameBitsEq (x `and` (y `or` z)) ((x `and` y) `or` (x `and` z)) $ \i, zlei, iltn =>
  rewrite bitsAnd x (y `or` z) i zlei iltn in
  rewrite bitsOr y z i zlei iltn in
  rewrite bitsOr (x `and` y) (x `and` z) i zlei iltn in
  rewrite bitsAnd x y i zlei iltn in
  rewrite bitsAnd x z i zlei iltn in
  andbOrbDistribR (testbit x i) (testbit y i) (testbit z i)

andOrDistribL : (x, y, z : BizMod2 n) -> (x `or` y) `and` z = (x `and` z) `or` (y `and` z)
andOrDistribL x y z =
  rewrite andCommut (x `or` y) z in
  rewrite andCommut x z in
  rewrite andCommut y z in
  andOrDistrib z x y

orAndDistrib : (x, y, z : BizMod2 n) -> x `or` (y `and` z) = (x `or` y) `and` (x `or` z)
orAndDistrib x y z =
  sameBitsEq (x `or` (y `and` z)) ((x `or` y) `and` (x `or` z)) $ \i, zlei, iltn =>
  rewrite bitsOr x (y `and` z) i zlei iltn in
  rewrite bitsAnd y z i zlei iltn in
  rewrite bitsAnd (x `or` y) (x `or` z) i zlei iltn in
  rewrite bitsOr x y i zlei iltn in
  rewrite bitsOr x z i zlei iltn in
  orbAndbDistribR (testbit x i) (testbit y i) (testbit z i)

orAndDistribL : (x, y, z : BizMod2 n) -> (x `and` y) `or` z = (x `or` z) `and` (y `or` z)
orAndDistribL x y z =
  rewrite orCommut (x `and` y) z in
  rewrite orCommut x z in
  rewrite orCommut y z in
  orAndDistrib z x y

andOrAbsorb : (x, y : BizMod2 n) -> x `and` (x `or` y) = x
andOrAbsorb x y =
  sameBitsEq (x `and` (x `or` y)) x $ \i, zlei, iltn =>
  rewrite bitsAnd x (x `or` y) i zlei iltn in
  rewrite bitsOr x y i zlei iltn in
  aux (testbit x i) (testbit y i)
  where
  aux : (a, b : Bool) -> a && (a || b) = a
  aux False _ = Refl
  aux True  _ = Refl

orAndAbsorb : (x, y : BizMod2 n) -> x `or` (x `and` y) = x
orAndAbsorb x y =
  sameBitsEq (x `or` (x `and` y)) x $ \i, zlei, iltn =>
  rewrite bitsOr x (x `and` y) i zlei iltn in
  rewrite bitsAnd x y i zlei iltn in
  aux (testbit x i) (testbit y i)
  where
  aux : (a, b : Bool) -> a || (a && b) = a
  aux False _ = Refl
  aux True  _ = Refl

xorCommut : (x, y : BizMod2 n) -> x `xor` y = y `xor` x
xorCommut x y =
  sameBitsEq (x `xor` y) (y `xor` x) $ \i, zlei, iltn =>
  rewrite bitsXor x y i zlei iltn in
  rewrite bitsXor y x i zlei iltn in
  xorComm (testbit x i) (testbit y i)

xorAssoc : (x, y, z : BizMod2 n) -> (x `xor` y) `xor` z = x `xor` (y `xor` z)
xorAssoc x y z =
  sameBitsEq ((x `xor` y) `xor` z) (x `xor` (y `xor` z)) $ \i, zlei, iltn =>
  rewrite bitsXor (x `xor` y) z i zlei iltn in
  rewrite bitsXor x y i zlei iltn in
  rewrite bitsXor x (y `xor` z) i zlei iltn in
  rewrite bitsXor y z i zlei iltn in
  xorbAssoc (testbit x i) (testbit y i) (testbit z i)

xorZeroL : (x : BizMod2 n) -> 0 `xor` x = x
xorZeroL x =
  sameBitsEq (0 `xor` x) x $ \i, zlei, iltn =>
  rewrite bitsXor 0 x i zlei iltn in
  rewrite bitsZero {n} i in
  xorFalse (testbit x i)

xorZero : (x : BizMod2 n) -> x `xor` 0 = x
xorZero {n} x =
  rewrite xorCommut x 0 in
  xorZeroL x

xorIdem : (x : BizMod2 n) -> x `xor` x = 0
xorIdem x =
  sameBitsEq (x `xor` x) 0 $ \i, zlei, iltn =>
  rewrite bitsXor x x i zlei iltn in
  rewrite bitsZero {n} i in
  xorDiag (testbit x i)

xorZeroEqual : (x, y : BizMod2 n) -> x `xor` y = 0 -> x = y
xorZeroEqual x y prf =
  sameBitsEq x y $ \i, zlei, iltn =>
  xorbFalseEqual (testbit x i) (testbit y i) $ aux i zlei iltn
  where
  aux : (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit x i `xor` testbit y i = False
  aux i zlei iltn =
    rewrite sym $ bitsXor x y i zlei iltn in
    rewrite prf in
    bitsZero i
  xorbFalseEqual : (a, b : Bool) -> a `xor` b = False -> a = b
  xorbFalseEqual False False Refl = Refl
  xorbFalseEqual False True  prf  = absurd prf
  xorbFalseEqual True  False prf  = absurd prf
  xorbFalseEqual True  True  Refl = Refl

xorIsZero : (x, y : BizMod2 n) -> (x `xor` y) == 0 = x == y
xorIsZero x y with ((x `xor` y)==0) proof xorzb
  | False with (x==y) proof xyb
    | False = Refl
    | True = let xorz = replace {P = \z => if z then x `xor` y = 0 else Not (x `xor` y = 0)} (sym xorzb) (eqSpec (x `xor` y) 0)
                 xy = replace {P = \z => if z then x = y else Not (x = y)} (sym xyb) (eqSpec x y)
                 contra = xorz
                       |> replace {P = \z => Not (z `xor` y = 0)} xy
                       |> replace {P = \z => Not (z = 0)} (xorIdem y)
             in
             absurd $ contra Refl
  | True =
    let xorz = replace {P = \z => if z then x `xor` y = 0 else Not (x `xor` y = 0)} (sym xorzb) (eqSpec (x `xor` y) 0) in
    rewrite xorZeroEqual x y xorz in
    sym $ eqTrue y

andXorDistrib : (x, y, z : BizMod2 n) -> x `and` (y `xor` z) = (x `and` y) `xor` (x `and` z)
andXorDistrib x y z =
  sameBitsEq (x `and` (y `xor` z)) ((x `and` y) `xor` (x `and` z)) $ \i, zlei, iltn =>
  rewrite bitsAnd x (y `xor` z) i zlei iltn in
  rewrite bitsXor y z i zlei iltn in
  rewrite bitsXor (x `and` y) (x `and` z) i zlei iltn in
  rewrite bitsAnd x y i zlei iltn in
  rewrite bitsAnd x z i zlei iltn in
  aux (testbit x i) (testbit y i) (testbit z i)
  where
  aux : (a, b, c : Bool) -> a && (b `xor` c) = (a && b) `xor` (a && c)
  aux False _ _ = Refl
  aux True  _ _ = Refl

andLe : (x, y : BizMod2 n) -> unsigned (x `and` y) `Le` unsigned x
andLe x y =
  bitsLe (x `and` y) x $ \i, zlei, iltn, tbxy =>
  let tbxtby = trans (sym $ bitsAnd x y i zlei iltn) tbxy in
  fst $ andbTrueIffTo (testbit x i) (testbit y i) tbxtby

orLe : (x, y : BizMod2 n) -> unsigned x `Le` unsigned (x `or` y)
orLe x y =
  bitsLe x (x `or` y) $ \i, zlei, iltn, tbx =>
  rewrite bitsOr x y i zlei iltn in
  rewrite tbx in
  Refl

-- Properties of bitwise complement.

notInvolutive : (x : BizMod2 n) -> not (not x) = x
notInvolutive {n} x =
  rewrite xorAssoc x (-1) (-1) in
  rewrite negRepr 1 n in
  rewrite xorIdem (repr (-1) n) in
  xorZero x

-- De Morgan's laws

notOrAndNot : (x, y : BizMod2 n) -> not (x `or` y) = (not x) `and` (not y)
notOrAndNot {n} x y =
  sameBitsEq (not (x `or` y)) ((not x) `and` (not y)) $ \i, zlei, iltn =>
  rewrite bitsNot (x `or` y) i zlei iltn in
  rewrite bitsOr x y i zlei iltn in
  rewrite bitsAnd (not x) (not y) i zlei iltn in
  rewrite bitsNot x i zlei iltn in
  rewrite bitsNot y i zlei iltn in
  negbOrb (testbit x i) (testbit y i)

notAndOrNot : (x, y : BizMod2 n) -> not (x `and` y) = (not x) `or` (not y)
notAndOrNot {n} x y =
  sameBitsEq (not (x `and` y)) ((not x) `or` (not y)) $ \i, zlei, iltn =>
  rewrite bitsNot (x `and` y) i zlei iltn in
  rewrite bitsAnd x y i zlei iltn in
  rewrite bitsOr (not x) (not y) i zlei iltn in
  rewrite bitsNot x i zlei iltn in
  rewrite bitsNot y i zlei iltn in
  negbAndb (testbit x i) (testbit y i)

andNotSelf : (x : BizMod2 n) -> x `and` (not x) = 0
andNotSelf {n} x =
  sameBitsEq (x `and` (not x)) 0 $ \i, zlei, iltn =>
  rewrite bitsAnd x (not x) i zlei iltn in
  rewrite bitsNot x i zlei iltn in
  rewrite bitsZero {n} i in
  andbNotSelf (testbit x i)

orNotSelf : (x : BizMod2 n) -> x `or` (not x) = -1
orNotSelf {n} x =
  sameBitsEq (x `or` (not x)) (-1) $ \i, zlei, iltn =>
  rewrite bitsOr x (not x) i zlei iltn in
  rewrite bitsNot x i zlei iltn in
  rewrite negRepr 1 n in	
  rewrite bitsMone n i zlei iltn in
  orbNotSelf (testbit x i)

xorNotSelf : (x : BizMod2 n) -> x `xor` (not x) = -1
xorNotSelf {n} x =
  sameBitsEq (x `xor` (not x)) (-1) $ \i, zlei, iltn =>
  rewrite bitsXor x (not x) i zlei iltn in
  rewrite bitsNot x i zlei iltn in
  rewrite negRepr 1 n in	
  rewrite bitsMone n i zlei iltn in
  xorbNotSelf (testbit x i)

unsignedNot : (x : BizMod2 n) -> unsigned (not x) = maxUnsigned n - unsigned x
unsignedNot {n} x = trans aux1 aux2
  where
  aux1 : unsigned (not x) = unsigned (repr (-(unsigned x)-1) n)
  aux1 =
    cong {f=unsigned} $ sameBitsEq (not x) (repr (-(unsigned x)-1) n) $ \i, zlei, iltn =>
    rewrite bitsNot x i zlei iltn in
    rewrite testbitRepr n (-(unsigned x)-1) i zlei iltn in
    sym $ zOneComplement i (unsigned x) zlei
  aux2 : unsigned (repr (-(unsigned x)-1) n) = maxUnsigned n - unsigned x
  aux2 =
    rewrite unsignedReprEq (-(unsigned x)-1) n in
    sym $ snd $ divModPos (-(unsigned x)-1) (modulus n) (-1) (maxUnsigned n - unsigned x)
      (rewrite sym $ compareSubR (unsigned x) (maxUnsigned n) in
       ltPredRTo (unsigned x) (modulus n) (snd $ unsignedRange x))
      (rewrite sym $ addAssoc (modulus n) (-1) (-(unsigned x)) in
       rewrite addCompareMonoL (modulus n) (-1-(unsigned x)) 0 in
       rewrite sym $ compareSub (-1) (unsigned x) in
       leSuccLTo (-1) (unsigned x) (fst $ unsignedRange x))
      (rewrite sym $ addAssoc (modulus n) (-1) (-(unsigned x)) in
       rewrite addAssoc (-(modulus n)) (modulus n) (-1-(unsigned x)) in
       rewrite posSubDiag (bipPow2 n) in
       addComm (-(unsigned x)) (-1))

notNeg : (x : BizMod2 n) -> not x = (-x)-1
notNeg {n} x =
  case decEq n 0 of
    Yes nz => rewrite nz in
              Refl
    No nnz =>
      sameBitsEq (not x) (-x-1) $ \i, zlei, iltn =>
      rewrite bitsNot x i zlei iltn in
      rewrite testbitRepr n ((unsigned $ repr (-(unsigned x)) n) - (unsigned $ repr 1 n)) i zlei iltn in
      trans (aux1 i zlei) (aux2 i zlei iltn nnz)
  where
  aux : (n : Nat) -> Not (n=0) -> U `Lt` bipPow2 n
  aux  Z    nz = absurd $ nz Refl
  aux (S _) _  = Refl
  aux1 : (i : Biz) -> 0 `Le` i -> not (bizTestBit (unsigned x) i) = bizTestBit (-(unsigned x)-1) i
  aux1 i zlei = sym $ zOneComplement i (unsigned x) zlei
  aux2 : (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> Not (n=0)
      -> bizTestBit (-(unsigned x)-1) i = bizTestBit ((unsigned $ repr (-(unsigned x)) n) - (unsigned $ repr 1 n)) i
  aux2 i zlei iltn nnz =
    sameBitsEqmod n (-(unsigned x)-1) ((unsigned $ repr (-(unsigned x)) n) - (unsigned $ repr 1 n)) i
      (eqmodAdd (-(unsigned x)) (unsigned $ repr (-(unsigned x)) n) (-1) (-(unsigned $ repr 1 n)) (modulus n)
         (eqmUnsignedRepr (-(unsigned x)) n)
         (rewrite unsignedRepr 1 n uninhabited $
                  ltPredRTo 1 (modulus n) (aux n nnz)
          in
          eqmodRefl (-1) (modulus n))
      )
      zlei iltn

negNot : (x : BizMod2 n) -> -x = (not x) + 1
negNot {n} x =
  rewrite notNeg x in
  rewrite subAddNeg (-x) 1 in
  rewrite sym $ addAssoc (-x) (-1) 1 in
  rewrite negRepr 1 n in	                       -- a lot of ceremony just to prove (-1)+1=0 :(
  rewrite addComm (repr (-1) n) (repr 1 n) in
  rewrite sym $ negRepr 1 n in	
  rewrite sym $ subAddNeg (repr 1 n) (repr 1 n) in
  rewrite subIdem (repr 1 n) in
  sym $ add0R (-x)

subAddNot : (x, y : BizMod2 n) -> x - y = (x + (not y)) + 1
subAddNot x y =
  rewrite subAddNeg x y in
  rewrite negNot y in
  addAssoc x (not y) 1

subAddNot3 : (x, y : BizMod2 n) -> Either (b = 0) (b = 1) -> (x - y) - b = (x + (not y)) + (b `xor` 1)
subAddNot3 {n} x y (Left b0) =
  rewrite b0 in
  rewrite unsignedZero n in
  rewrite add0R (unsigned (x-y)) in
  rewrite reprUnsigned (repr 1 n) in
  rewrite reprUnsigned (x-y) in
  subAddNot x y
subAddNot3 {n} x y (Right b1) =
  rewrite b1 in
  rewrite xorIdem (repr 1 n) in
  rewrite unsignedZero n in
  rewrite add0R (unsigned (x+(not y))) in
  rewrite reprUnsigned (x+(not y)) in
  rewrite subAddNot x y in
  rewrite subAddNeg ((x+(not y))+1) 1 in
  rewrite sym $ addAssoc (x+(not y)) (repr 1 n) (-(repr 1 n)) in
  rewrite addNegZero (repr 1 n) in
  add0R (x+(not y))

-- we can't have a common helper for several `with` branches
subBorrowAddCarryAux : (n : Nat) -> (x, y, b : BizMod2 n) -> Not (n=0) -> Either (b = 0) (b = 1) ->
                       (unsigned x + unsigned (not y) + unsigned (b `xor` 1)) `compare` modulus n = unsigned x - unsigned y - unsigned b `compare` 0
subBorrowAddCarryAux n x y b nz b01 =
  rewrite unsignedNot y in
  rewrite aux in
  rewrite addComm (maxUnsigned n) (-(unsigned y)) in
  rewrite addAssoc (unsigned x) (-(unsigned y)) (maxUnsigned n) in
  rewrite sym $ addAssoc (unsigned x - unsigned y) (maxUnsigned n) (1 - unsigned b) in
  rewrite addAssoc (maxUnsigned n) 1 (-(unsigned b)) in
  rewrite sym $ addAssoc (modulus n) (-1) 1 in
  rewrite addComm (modulus n) (-(unsigned b)) in
  rewrite addAssoc (unsigned x - unsigned y) (-(unsigned b)) (modulus n) in
  addCompareMonoR (unsigned x - unsigned y - unsigned b) 0 (modulus n)
  where
  aux : unsigned (b `xor` (repr 1 n)) = 1 - unsigned b
  aux = case b01 of
    Left b0 =>
      rewrite b0 in
      rewrite unsignedZero n in
      rewrite reprUnsigned (repr 1 n) in
      unsignedOne n nz
    Right b1 =>
      rewrite b1 in
      rewrite xorIdem (repr 1 n) in
      rewrite unsignedOne n nz in
      unsignedZero n

subBorrowAddCarry : (x, y : BizMod2 n) -> Either (b = 0) (b = 1) -> subBorrow x y b = (addCarry x (not y) (b `xor` 1)) `xor` 1
subBorrowAddCarry {n} {b} x y b01 with (decEq n 0)
  subBorrowAddCarry {n} {b} x y b01 | Yes n0 =
    rewrite n0 in
    aux0 (MkBizMod2 BizO (Refl, Refl)) (unsigned x - unsigned y - unsigned b < 0)
    where
    aux0 : (x : a) -> (b : Bool) -> (if b then x else x) = x
    aux0 _ True = Refl
    aux0 _ False = Refl
  subBorrowAddCarry {n} {b} x y b01 | No nz with (bizCompare (unsigned x - unsigned y - unsigned b) 0) proof cmp
    subBorrowAddCarry {n} {b} x y b01 | No nz | LT =
      rewrite subBorrowAddCarryAux n x y b nz b01 in
      rewrite sym cmp in
      rewrite unsignedZero n in
      sym $ reprUnsigned (repr 1 n)
    subBorrowAddCarry {n} {b} x y b01 | No nz | EQ =
      rewrite subBorrowAddCarryAux n x y b nz b01 in
      rewrite sym cmp in
      sym $ xorIdem (repr 1 n)
    subBorrowAddCarry {n} {b} x y b01 | No nz | GT =
      rewrite subBorrowAddCarryAux n x y b nz b01 in
      rewrite sym cmp in
      sym $ xorIdem (repr 1 n)

-- Connections between [add] and bitwise logical operations.

addIsOr : (x, y : BizMod2 n) -> x `and` y = 0 -> x + y = x `or` y
addIsOr {n} x y prf =
  sameBitsEq (x+y) (x `or` y) $ \i, zlei, iltn =>
  rewrite testbitRepr n (unsigned x + unsigned y) i zlei iltn in
  rewrite testbitRepr n (unsigned x `bizOr` unsigned y) i zlei iltn in
  rewrite lorSpec (unsigned x) (unsigned y) i in
  zAddIsOr (unsigned x) (unsigned y) i zlei $ \j, zlej, jlei =>
  rewrite sym $ landSpec (unsigned x) (unsigned y) j in
  rewrite sym $ testbitRepr n (unsigned x `bizAnd` unsigned y) j zlej (leLtTrans j i (toBizNat n) jlei iltn) in
  rewrite prf in
  bitsZero j

xorIsOr : (x, y : BizMod2 n) -> x `and` y = 0 -> x `xor` y = x `or` y
xorIsOr {n} x y prf =
  sameBitsEq (x `xor` y) (x `or` y) $ \i, zlei, iltn =>
  rewrite bitsOr x y i zlei iltn in
  rewrite bitsXor x y i zlei iltn in
  let tbxyf = trans (trans (sym $ bitsAnd x y i zlei iltn)
                           (cong {f=\z=>testbit z i} prf))
                    (bitsZero i)
  in
  aux (testbit x i) (testbit y i) tbxyf
  where
  aux : (b1, b2 : Bool) -> b1 && b2 = False -> b1 `xor` b2 = b1 || b2
  aux True  True  prf = absurd prf
  aux True  False _   = Refl
  aux False True  _   = Refl
  aux False False _   = Refl

addIsXor : (x, y : BizMod2 n) -> x `and` y = 0 -> x + y = x `xor` y
addIsXor x y prf =
  rewrite xorIsOr x y prf in
  addIsOr x y prf

addAnd : (x, y, z : BizMod2 n) -> y `and` z = 0 -> (x `and` y) + (x `and` z) = x `and` (y `or` z)
addAnd x y z prf =
  rewrite addIsOr (x `and` y) (x `and` z) $
    rewrite andCommut x z in
    rewrite sym $ andAssoc (x `and` y) z x in
    rewrite andAssoc x y z in
    rewrite prf in
    rewrite andZero x in
    andZeroL x
  in
  sym $ andOrDistrib x y z