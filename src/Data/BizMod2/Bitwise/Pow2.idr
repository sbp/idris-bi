module Data.BizMod2.Bitwise.Pow2

import Data.List

import Data.Util

import Data.Bip.Iter
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Bitwise
import Data.Biz.Nat
import Data.Biz.DivMod
import Data.Biz.PowSqrt

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.AddSubMul
import Data.BizMod2.Bitwise
import Data.BizMod2.Bitwise.Shift

%access export
%default total

-- Properties of [Z_one_bits] and [is_power2].

powerserie : List Biz -> Biz
powerserie []        = 0
powerserie (x :: xs) = bizPow2 x + powerserie xs

zOneBitsPowerserieI : (n : Nat) -> (x, i : Biz) -> 0 `Le` i -> 0 `Le` x -> x `Lt` modulus n
                   -> x * (bizPow2 i) = powerserie (zOneBits n x i)
zOneBitsPowerserieI  Z     BizO    _ _ _ _ = Refl
zOneBitsPowerserieI  Z    (BizP x) _ _ _ xltn = absurd $ nlt1R x xltn
zOneBitsPowerserieI  Z    (BizM _) _ _ zlex _ = absurd $ zlex Refl
zOneBitsPowerserieI (S k) x i zlei zlex xltn =
  let ih = zOneBitsPowerserieI k (bizDivTwo x) (i+1)
             (leSuccR 0 i zlei)
             (div2Pos x zlex)
             (rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus k) Refl in
              leLtTrans (2*(bizDivTwo x)) x (2*(modulus k))
                (dDiv2Le x zlex)
                xltn)
      rew = cong {f = \z => z * (bizPow2 i)} $ zDecomp x  -- workaround to rewrite only LHS
  in
  rewrite rew in
  rewrite bizShiftinSpec (bizOdd x) (bizDivTwo x) in
  case trueOrFalse (bizOdd x) of
    Left fprf =>
      rewrite fprf in
      rewrite add0R (2*(bizDivTwo x)) in
      rewrite sym ih in
      rewrite bizPow2IsExp i 1 zlei uninhabited in
      rewrite mulComm (bizPow2 i) 2 in
      rewrite mulAssoc (bizDivTwo x) 2 (bizPow2 i) in
      rewrite mulComm (bizDivTwo x) 2 in
      Refl
    Right tprf =>
      rewrite tprf in
      rewrite mulAddDistrR (2*(bizDivTwo x)) 1 (bizPow2 i) in
      rewrite mul1L (bizPow2 i) in
      rewrite sym ih in
      rewrite bizPow2IsExp i 1 zlei uninhabited in
      rewrite mulComm (bizPow2 i) 2 in
      rewrite mulAssoc (bizDivTwo x) 2 (bizPow2 i) in
      rewrite mulComm (bizDivTwo x) 2 in
      addComm (2*(bizDivTwo x)*(bizPow2 i)) (bizPow2 i)

zOneBitsPowerserie : (n : Nat) -> (x : Biz) -> 0 `Le` x -> x `Lt` modulus n
                   -> x = powerserie (zOneBits n x 0)
zOneBitsPowerserie n x zlex xltn =
  trans (sym $ mul1R x) (zOneBitsPowerserieI n x 0 uninhabited zlex xltn)

zOneBitsRangeJ : (n : Nat) -> (x, i, j : Biz) -> Elem j (zOneBits n x i) -> (i `Le` j, j `Lt` i + toBizNat n)
zOneBitsRangeJ Z x i j = absurd
zOneBitsRangeJ (S k) x i j =
  rewrite toBizNatInjSucc k in
  let ih = zOneBitsRangeJ k (bizDivTwo x) (i+1) j in
  case trueOrFalse (bizOdd x) of
    Left fprf =>
      rewrite fprf in
      \elem =>
        let ih2 = ih elem in
        ( ltLeIncl i j $ ltLeTrans i (i+1) j
            (rewrite addComm i 1 in
             rewrite addCompareMonoR 0 1 i in
             Refl)
            (fst ih2)
        , rewrite addComm (toBizNat k) 1 in
          rewrite addAssoc i 1 (toBizNat k) in
          snd ih2)
    Right tprf =>
      rewrite tprf in
      \elem =>
        case elem of
          Here =>
            ( leRefl i
            , rewrite addComm i (toBizNat k + 1) in
              rewrite addCompareMonoR 0 (toBizNat k + 1) i in
              ltSuccRFro 0 (toBizNat k) (toBizNatIsNonneg k))
          (There xs) =>
            let ih2 = ih xs in
            ( ltLeIncl i j $ ltLeTrans i (i+1) j
                (rewrite addComm i 1 in
                 rewrite addCompareMonoR 0 1 i in
                 Refl)
                (fst ih2)
            , rewrite addComm (toBizNat k) 1 in
              rewrite addAssoc i 1 (toBizNat k) in
              snd ih2)

zOneBitsRange : (n : Nat) -> (x, i : Biz) -> Elem i (zOneBits n x 0) -> (0 `Le` i, i `Lt` toBizNat n)
zOneBitsRange n x i elem = zOneBitsRangeJ n x 0 i elem

-- we can get `0 <= unsigned logx` from unsignedRange
isPower2Rng : (x, logx : BizMod2 n) -> isPower2 x = Just logx -> unsigned logx `Lt` toBizNat n
isPower2Rng {n} x logx prf with (zOneBits n (unsigned x) 0) proof zob
  | [] = absurd prf
  | (i :: []) =
      rewrite sym $ justInjective prf in
      let irng = zOneBitsRange n (unsigned x) i $
                   rewrite sym zob in
                   Here
               in
      rewrite unsignedRepr i n (fst irng) $
              ltLeIncl i (maxUnsigned n) $
              ltLeTrans i (toBizNat n) (maxUnsigned n) (snd irng) (wordsizeMaxUnsigned n)
             in
      snd irng
  | (_ :: _ :: _) = absurd prf

isPower2Range : (x, logx : BizMod2 n) -> isPower2 x = Just logx -> logx `ltu` iwordsize n = True
isPower2Range {n} x logx prf =
  ltbLtFro (unsigned logx) (unsigned $ iwordsize n) $
  rewrite unsignedReprWordsize n in
  isPower2Rng x logx prf

isPower2Correct : (x, logx : BizMod2 n) -> isPower2 x = Just logx -> unsigned x = bizPow2 (unsigned logx)
isPower2Correct {n} x logx prf with (zOneBits n (unsigned x) 0) proof zob
  | [] = absurd prf
  | (i :: []) =
      rewrite zOneBitsPowerserie n (unsigned x) (fst $ unsignedRange x) (snd $ unsignedRange x) in
      rewrite sym zob in
      rewrite sym $ justInjective prf in
      let irng = zOneBitsRange n (unsigned x) i $
                   rewrite sym zob in
                   Here
               in
      rewrite unsignedRepr i n (fst irng) $
              ltLeIncl i (maxUnsigned n) $
              ltLeTrans i (toBizNat n) (maxUnsigned n) (snd irng) (wordsizeMaxUnsigned n)
             in
      add0R (bizPow2 i)
  | (_ :: _ :: _) = absurd prf

-- TODO move to Biz.PowSqrt?
-- `0 <= bizPow2 x` is just `ltLeIncl bizPow2Pos`
bizPow2Range : (n : Nat) -> (x : Biz) -> 0 `Le` x -> x `Lt` toBizNat n -> bizPow2 x `Le` maxUnsigned n
bizPow2Range  Z    x zlex xltn = absurd $ zlex $ ltGt x 0 xltn
bizPow2Range (S k) x zlex xltn =
  let rew = cong {f = bizDMO} $ bipPow2Biz k in
  rewrite rew in
  rewrite predDoubleSpec (bizPow2 (toBizNat k)) in
  rewrite sym $ bizPow2IsExp 1 (toBizNat k) uninhabited (toBizNatIsNonneg k) in
  rewrite addComm 1 (toBizNat k) in
  rewrite sym $ toBizNatInjSucc k in
  ltPredRTo (bizPow2 x) (bizPow2 $ toBizNat (S k)) $
  bizPow2MonotoneStrict x (toBizNat (S k)) zlex xltn

zOneBitsZero : (n : Nat) -> (i : Biz) -> zOneBits n 0 i = []
zOneBitsZero Z     _ = Refl
zOneBitsZero (S k) i = zOneBitsZero k (i+1)

zOneBitsBizPow2 : (n : Nat) -> (x, i : Biz) -> 0 `Le` x -> x `Lt` toBizNat n -> zOneBits n (bizPow2 x) i = [i + x]
zOneBitsBizPow2  Z    x i zlex xltn = absurd $ zlex $ ltGt x 0 xltn
zOneBitsBizPow2 (S k) x i zlex xltn =
  case leLtOrEq 0 x zlex of
    Right zx =>
      rewrite sym zx in
      rewrite zOneBitsZero k (i+1) in
      rewrite add0R i in
      Refl
    Left zltx =>
      let zlex1 = ltPredRTo 0 x zltx
          (p2ev, p2d2) = bizShiftinInj (bizOdd (bizPow2 x)) False (bizDivTwo (bizPow2 x)) (bizPow2 (x-1)) $
                         rewrite sym $ zDecomp (bizPow2 x) in
                         rewrite sym $ bizPow2S (x-1) zlex1 in
                         rewrite sym $ addAssoc x (-1) 1 in
                         cong $ sym $ add0R x
         in
      rewrite p2ev in
      rewrite p2d2 in
      rewrite zOneBitsBizPow2 k (x-1) (i+1) zlex1 $
              rewrite addComm x (-1) in
              rewrite sym $ addCompareTransferL x 1 (toBizNat k) in
              rewrite addComm 1 (toBizNat k) in
              rewrite sym $ toBizNatInjSucc k in
              xltn
             in
      rewrite addComm x (-1) in
      rewrite addAssoc (i+1) (-1) x in
      rewrite sym $ addAssoc i 1 (-1) in
      rewrite add0R i in
      Refl

isPower2BizPow2 : (n : Nat) -> (x : Biz) -> 0 `Le` x -> x `Lt` toBizNat n -> isPower2 (repr (bizPow2 x) n) = Just (repr x n)
isPower2BizPow2 n x zlex xltn =
  rewrite unsignedRepr (bizPow2 x) n
            (ltLeIncl 0 (bizPow2 x) (bizPow2Pos x zlex))
            (bizPow2Range n x zlex xltn)
         in
  rewrite zOneBitsBizPow2 n x 0 zlex xltn in
  Refl

-- Relation between bitwise operations and multiplications / divisions by powers of 2

-- Left shifts and multiplications by powers of 2.

zShiftlMulBizPow2 : (x, n : Biz) -> 0 `Le` n -> bizShiftL x n = x * bizPow2 n
zShiftlMulBizPow2 x  BizO    _    = sym $ mul1R x
zShiftlMulBizPow2 x (BizP n) zlen =
  peanoRect
    (\z => bipIter (2*) x z = x*(BizP (bipIter O U z)))
    (mulComm 2 x)
    (\z, prf =>
     rewrite iterSucc (2*) x z in
     rewrite iterSucc O U z in
     rewrite mulAssoc x 2 (BizP (bipIter O U z)) in
     rewrite mulComm x 2 in
     rewrite sym $ mulAssoc 2 x (BizP (bipIter O U z)) in
     cong {f = (2*)} prf
    )
    n
zShiftlMulBizPow2 _ (BizM _) zlen = absurd $ zlen Refl

shlMulBizPow2 : (x, y : BizMod2 n) -> shl x y = x * (repr (bizPow2 (unsigned y)) n)
shlMulBizPow2 {n} x y =
  eqmSamerepr (bizShiftL (unsigned x) (unsigned y)) ((unsigned x)*(unsigned (repr (bizPow2 (unsigned y)) n))) n $
  let (zleuy, uyltn) = unsignedRange y in
  rewrite zShiftlMulBizPow2 (unsigned x) (unsigned y) zleuy in
  eqmodMult (unsigned x) (unsigned x) (bizPow2 (unsigned y)) (unsigned (repr (bizPow2 (unsigned y)) n)) (modulus n)
    (eqmodRefl (unsigned x) (modulus n))
    (eqmUnsignedRepr (bizPow2 (unsigned y)) n)

shlMul : (x, y : BizMod2 n) -> shl x y = x*(shl 1 y)
shlMul {n} x y =
  rewrite shlMulBizPow2 (repr 1 n) y in
  rewrite mul1L (repr (bizPow2 (unsigned y)) n) in
  shlMulBizPow2 x y

mulPow2 : (x, y, logy : BizMod2 n) -> isPower2 y = Just logy -> x*y = shl x logy
mulPow2 x y logy prf =
  rewrite shlMulBizPow2 x logy in
  rewrite sym $ isPower2Correct y logy prf in
  rewrite reprUnsigned y in
  Refl

shiftedOrIsAdd : (x, y : BizMod2 n) -> (m : Biz) -> 0 `Le` m -> m `Lt` toBizNat n -> unsigned y `Lt` bizPow2 m
              -> (shl x (repr m n)) `or` y = repr ((unsigned x) * (bizPow2 m) + unsigned y) n
shiftedOrIsAdd {n} x y m zlem mltn uylt2m =
  let urmn = unsignedRepr m n zlem $
             ltLeIncl m (maxUnsigned n) $
             ltLeTrans m (toBizNat n) (maxUnsigned n) mltn (wordsizeMaxUnsigned n)
     in
  rewrite sym $ addIsOr (shl x (repr m n)) y $
          sameBitsEq ((shl x (repr m n)) `and` y) (repr 0 n) $ \i, zlei, iltn =>
          rewrite bitsAnd (shl x (repr m n)) y i zlei iltn in
          rewrite bitsShl x (repr m n) i zlei iltn in
          rewrite urmn in
          trans {b=False}
            (case ltLeTotal i m of
               Left iltm =>
                 rewrite ltbLtFro i m iltm in
                 Refl
               Right mlei =>
                 rewrite nltbLeFro m i mlei in
                 rewrite zTestbitAbove (toNatBiz m) (unsigned y) i (fst $ unsignedRange y)
                           (rewrite bipPow2Biz (toNatBiz m) in
                            rewrite toNatBizId m zlem in
                            uylt2m)
                           (rewrite toNatBizId m zlem in
                            mlei)
                        in
                 andFalse (testbit x (i-m))
               )
            (sym $ bitsZero {n} i)
         in
  eqmSamerepr ((unsigned (shl x (repr m n))) + unsigned y) ((unsigned x)*(bizPow2 m) + unsigned y) n $
  eqmodAdd (unsigned (shl x (repr m n))) ((unsigned x)*(bizPow2 m)) (unsigned y) (unsigned y) (modulus n)
    (rewrite shlMulBizPow2 x (repr m n) in
     eqmUnsignedReprL ((unsigned x)*(unsigned (repr (bizPow2 (unsigned (repr m n))) n))) ((unsigned x)*(bizPow2 m)) n $
     eqmodMult (unsigned x) (unsigned x) (unsigned (repr (bizPow2 (unsigned (repr m n))) n)) (bizPow2 m) (modulus n)
       (eqmodRefl (unsigned x) (modulus n))
       (eqmUnsignedReprL (bizPow2 (unsigned (repr m n))) (bizPow2 m) n $
        eqmodRefl2 (bizPow2 (unsigned (repr m n))) (bizPow2 m) (modulus n) $
        rewrite urmn in
        Refl))
    (eqmodRefl (unsigned y) (modulus n))

-- Unsigned right shifts and unsigned divisions by powers of 2.

zShiftrDivBizPow2 : (x, y : Biz) -> 0 `Le` y -> bizShiftR x y = x `bizDiv` (bizPow2 y)
zShiftrDivBizPow2 x  BizO    _    = sym $ fst $ divMod1 x
zShiftrDivBizPow2 x (BizP p) _    =
  peanoRect
    (\z => bipIter bizDivTwo x z = x `bizDiv` (BizP (bipIter O U z)))
    (div2Div x)
    (\z, prf =>
      rewrite iterSucc bizDivTwo x z in
      rewrite iterSucc O U z in
      rewrite prf in
      rewrite mulComm 2 (BizP (bipIter O U z)) in
      rewrite sym $ divDivPos x (BizP (bipIter O U z)) 2 Refl Refl in
      div2Div (x `bizDiv` (BizP (bipIter O U z))))
    p
zShiftrDivBizPow2 _ (BizM _) zley = absurd $ zley Refl
