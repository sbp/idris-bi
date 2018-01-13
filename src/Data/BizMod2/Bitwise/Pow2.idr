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
import Data.BizMod2.Ord
import Data.BizMod2.AddSubMul
import Data.BizMod2.Bitwise
import Data.BizMod2.Bitwise.Shift

%access export
%default total

-- Properties of [Z_one_bits] and [is_power2].

-- TODO move to Biz?
public export
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
zOneBitsZero  Z    _ = Refl
zOneBitsZero (S k) i = zOneBitsZero k (i+1)

zOneBitsBizPow2 : (n : Nat) -> (x, i : Biz) -> 0 `Le` x -> x `Lt` toBizNat n -> zOneBits n (bizPow2 x) i = [i + x]
zOneBitsBizPow2  Z    x _ zlex xltn = absurd $ zlex $ ltGt x 0 xltn
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

shlMulBizPow2 : (x, y : BizMod2 n) -> shl x y = x * (repr (bizPow2 (unsigned y)) n)
shlMulBizPow2 {n} x y =
  eqmSamerepr (bizShiftL (unsigned x) (unsigned y)) ((unsigned x)*(unsigned (repr (bizPow2 (unsigned y)) n))) n $
  let (zleuy, uyltn) = unsignedRange y in
  rewrite zShiftlMulBizPow2 (unsigned x) (unsigned y) zleuy in
  eqmodMult (unsigned x) (unsigned x) (bizPow2 (unsigned y)) (unsigned (repr (bizPow2 (unsigned y)) n)) (modulus n)
    (eqmodRefl (unsigned x) (modulus n))
    (eqmUnsignedRepr (bizPow2 (unsigned y)) n)

shl1BizPow2 : (y : BizMod2 n) -> shl 1 y = repr (bizPow2 (unsigned y)) n
shl1BizPow2 {n} y =
  rewrite shlMulBizPow2 (repr 1 n) y in
  mul1L (repr (bizPow2 (unsigned y)) n)

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

-- TODO move to Biz.DivMod?
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

shruDivBizPow2 : (x, y : BizMod2 n) -> shru x y = repr ((unsigned x) `bizDiv` (bizPow2 (unsigned y))) n
shruDivBizPow2 x y = rewrite zShiftrDivBizPow2 (unsigned x) (unsigned y) (fst $ unsignedRange y) in
                     Refl

divuPow2 : (x, y, logy : BizMod2 n) -> isPower2 y = Just logy -> x `divu` y = shru x logy
divuPow2 x y logy prf = rewrite isPower2Correct y logy prf in
                        sym $ shruDivBizPow2 x logy

-- Signed right shifts and signed divisions by powers of 2.

shrDivBizPow2 : (x, y : BizMod2 n) -> shr x y = repr ((signed x) `bizDiv` (bizPow2 (unsigned y))) n
shrDivBizPow2 x y = rewrite zShiftrDivBizPow2 (signed x) (unsigned y) (fst $ unsignedRange y) in
                    Refl

divsBizPow2 : (x, y, logy : BizMod2 n) -> isPower2 y = Just logy -> x `divs` y = shrx x logy
divsBizPow2 {n} x y logy prf =
  rewrite shlMulBizPow2 (repr 1 n) logy in
  rewrite mul1L (repr (bizPow2 (unsigned logy)) n) in
  rewrite sym $ isPower2Correct y logy prf in
  rewrite reprUnsigned y in
  Refl

-- Unsigned modulus over [2^n] is masking with [2^n-1].

zTestbitModBizPow2 : (n, x, i : Biz) -> 0 `Le` n -> 0 `Le` i -> bizTestBit (x `bizMod` (bizPow2 n)) i = if i < n then bizTestBit x i else False
zTestbitModBizPow2 n x i zlen zlei =
  natlikeInd
    (\m => (y, j : Biz) -> 0 `Le` j -> bizTestBit (y `bizMod` (bizPow2 m)) j = if j < m then bizTestBit y j else False)
    (\y, j, zlej =>
     rewrite snd $ divMod1 y in
     rewrite testbit0L j in
     rewrite nltbLeFro 0 j zlej in
     Refl)
    (\m, zlem, prf, y, j, zlej =>
     rewrite bizPow2S m zlem in
     rewrite doubleSpec (bizPow2 m) in
     rewrite aux y m zlem in
     rewrite zTestbitShiftin (bizOdd y) ((bizDivTwo y) `bizMod` (bizPow2 m)) j zlej in
     case leLtOrEq 0 j zlej of
       Right j0 =>
         rewrite sym j0 in
         rewrite ltbLtFro 0 (bizSucc m) $
                 ltSuccRFro 0 m zlem
                in
         Refl
       Left zltj =>
         rewrite neqbNeqFro j 0 $ ltNotEq j 0 zltj in
         rewrite prf (bizDivTwo y) (j-1) (ltPredRTo 0 j zltj) in
         really_believe_me zltj
-- TODO bug: if we uncomment either of the branches it checks fine, but checking the whole thing seems to hang
       -- case ltLeTotal (j-1) m of
       --   Left j1ltm =>
       --     rewrite ltbLtFro (j-1) m j1ltm in
       --     rewrite ltbLtFro j (m+1) $
       --             rewrite addComm m 1 in
       --             rewrite addCompareTransferL j 1 m in
       --             rewrite addComm (-1) j in
       --             j1ltm
       --            in
       --     rewrite sym $ zTestbitSucc y (j-1) (ltPredRTo 0 j zltj) in
       --     rewrite sym $ addAssoc j (-1) 1 in
       --     rewrite add0R j in
       --     Refl
       --   Right mlej1 =>
       --     rewrite nltbLeFro m (j-1) mlej1 in
       --     rewrite nltbLeFro (m+1) j $
       --             rewrite sym $ addCompareMonoR (m+1) j (-1) in
       --             rewrite sym $ addAssoc m 1 (-1) in
       --             rewrite add0R m in
       --             mlej1
       --           in
       --     Refl
    )
    n zlen
    x i zlei
  where
  auxIf : (b : Bool) -> let ifb = if b then BizP U else BizO in (0 `Le` ifb, ifb `Le` 1)
  auxIf True = (uninhabited, uninhabited)
  auxIf False = (uninhabited, uninhabited)
  aux : (p, q : Biz) -> 0 `Le` q -> p `bizMod` (2*(bizPow2 q)) = bizShiftin (bizOdd p) ((bizDivTwo p) `bizMod` (bizPow2 q))
  aux p q zleq =
    let rew = cong {f=\z=>z `bizMod` (2*(bizPow2 q))} $ zDecomp p in
    rewrite rew in
    rewrite bizShiftinSpec (bizOdd p) (bizDivTwo p) in
    rewrite bizShiftinSpec (bizOdd p) ((bizDivTwo p) `bizMod` (bizPow2 q)) in
    let (zlep2m2q, p2m2qlt2q) = modPosBound (bizDivTwo p) (bizPow2 q) (bizPow2Pos q zleq)
        (zleif, ifle1) = auxIf (bizOdd p)
       in
    sym $ snd $ divModPos (2*(bizDivTwo p)+(if bizOdd p then 1 else 0)) (2*(bizPow2 q))
                          ((bizDivTwo p) `bizDiv` (bizPow2 q)) (2*((bizDivTwo p) `bizMod` (bizPow2 q))+(if bizOdd p then 1 else 0))
      (leTrans 0 (2*((bizDivTwo p) `bizMod` (bizPow2 q))) (2*((bizDivTwo p) `bizMod` (bizPow2 q))+(if bizOdd p then 1 else 0))
         (rewrite mulComm 2 ((bizDivTwo p) `bizMod` (bizPow2 q)) in
          rewrite mulCompareMonoR 2 0 ((bizDivTwo p) `bizMod` (bizPow2 q)) Refl in
          zlep2m2q)
         (rewrite addComm (2*((bizDivTwo p) `bizMod` (bizPow2 q))) (ifThenElse (bizOdd p) (Delay 1) (Delay 0)) in
          rewrite addCompareMonoR 0 (ifThenElse (bizOdd p) (Delay 1) (Delay 0)) (2*((bizDivTwo p) `bizMod` (bizPow2 q))) in
          zleif))
      (ltLeTrans (2*((bizDivTwo p) `bizMod` (bizPow2 q))+(if bizOdd p then 1 else 0)) (2*(((bizDivTwo p) `bizMod` (bizPow2 q))+1)) (2*(bizPow2 q))
         (rewrite mulAddDistrL 2 ((bizDivTwo p) `bizMod` (bizPow2 q)) 1 in
          rewrite addCompareMonoL (2*((bizDivTwo p) `bizMod` (bizPow2 q))) (ifThenElse (bizOdd p) (Delay 1) (Delay 0)) 2 in
          ltSuccRFro (if bizOdd p then 1 else 0) 1 ifle1)
         (rewrite mulCompareMonoL 2 (((bizDivTwo p) `bizMod` (bizPow2 q))+1) (bizPow2 q) Refl in
          leSuccLFro ((bizDivTwo p) `bizMod` (bizPow2 q)) (bizPow2 q) p2m2qlt2q))
      (rewrite mulAssoc ((bizDivTwo p) `bizDiv` (bizPow2 q)) 2 (bizPow2 q) in
       rewrite mulComm ((bizDivTwo p) `bizDiv` (bizPow2 q)) 2 in
       rewrite sym $ mulAssoc 2 ((bizDivTwo p) `bizDiv` (bizPow2 q)) (bizPow2 q) in
       rewrite addAssoc (2*(((bizDivTwo p) `bizDiv` (bizPow2 q))*(bizPow2 q))) (2*((bizDivTwo p) `bizMod` (bizPow2 q))) (ifThenElse (bizOdd p) (Delay 1) (Delay 0)) in
       rewrite sym $ mulAddDistrL 2 (((bizDivTwo p) `bizDiv` (bizPow2 q))*(bizPow2 q)) ((bizDivTwo p) `bizMod` (bizPow2 q)) in
       cong {f=\r=>2*r+(ifThenElse (bizOdd p) (Delay 1) (Delay 0))} $
       divEuclEq (bizDivTwo p) (bizPow2 q) (ltNotEq (bizPow2 q) 0 $ bizPow2Pos q zleq))

zTestbitBizPow2M1 : (n, i : Biz) -> 0 `Le` n -> 0 `Le` i -> bizTestBit (bizPow2 n - 1) i = if i < n then True else False
zTestbitBizPow2M1 n i zlen zlei =
  rewrite aux in
  rewrite zTestbitModBizPow2 n (-1) i zlen zlei in
  rewrite testbitM1L i zlei in
  Refl
  where
  aux : bizPow2 n - 1 = (-1) `bizMod` (bizPow2 n)
  aux =
    snd $ divModPos (-1) (bizPow2 n) (-1) (bizPow2 n - 1)
      (ltPredRTo 0 (bizPow2 n) $
       bizPow2Pos n zlen)
      (rewrite addComm (bizPow2 n) (-1) in
       rewrite addCompareMonoR (-1) 0 (bizPow2 n) in
       Refl)
      (rewrite sym $ oppEqMulM1L (bizPow2 n) in
       rewrite addAssoc (-bizPow2 n) (bizPow2 n) (-1) in
       rewrite addOppDiagL (bizPow2 n) in
       Refl)

moduAnd : (x, y, logy : BizMod2 n) -> isPower2 y = Just logy -> x `modu` y = x `and` (y-1)
moduAnd {n} x y logy prf =
  case decEq n 0 of
    Yes nz =>
      rewrite nz in
      Refl
    No nnz =>
      sameBitsEq (x `modu` y) (x `and` (y-1)) $ \i, zlei, iltn =>
      rewrite bitsAnd x (y-1) i zlei iltn in
      rewrite testbitRepr n ((unsigned x) `bizMod` (unsigned y)) i zlei iltn in
      rewrite unsignedOne n nnz in
      rewrite testbitRepr n (unsigned y - 1) i zlei iltn in
      rewrite isPower2Correct y logy prf in
      rewrite zTestbitModBizPow2 (unsigned logy) (unsigned x) i (fst $ unsignedRange logy) zlei in
      rewrite zTestbitBizPow2M1 (unsigned logy) i (fst $ unsignedRange logy) zlei in
      case ltLeTotal i (unsigned logy) of
        Left iltuly =>
          rewrite ltbLtFro i (unsigned logy) iltuly in
          sym $ andTrue (bizTestBit (unsigned x) i)
        Right ulylei =>
          rewrite nltbLeFro (unsigned logy) i ulylei in
          sym $ andFalse (bizTestBit (unsigned x) i)

-- Properties of [shrx] (signed division by a power of 2)

shrxZero : (x : BizMod2 n) -> 1 `Lt` toBizNat n -> shrx x 0 = x
shrxZero {n} x ultn =
  rewrite shlZero (repr 1 n) in
  rewrite signedOne n ultn in
  rewrite quot1R (signed x) in
  reprSigned x

-- shared lemma, move to Biz.PowSqrt for 0 `Le` y?
unsignedPowHalfMod : (y : BizMod2 n) -> unsigned y `Lt` toBizNat n - 1 -> bizPow2 (unsigned y) `Lt` halfModulus n
unsignedPowHalfMod {n} y yltn1 =
  rewrite halfModulusPower n in
  bizPow2MonotoneStrict (unsigned y) (toBizNat n - 1) (fst $ unsignedRange y) yltn1

shrxShr : (x, y : BizMod2 n) -> y `ltu` (repr (toBizNat n - 1) n) = True -> shrx x y = shr (if x < 0 then x+((shl 1 y)-1) else x) y
shrxShr {n} x y yltun =
  case decEq n 0 of
    Yes nz =>
      rewrite bizMod2P0N x nz in
      rewrite nz in
      Refl
    No nnz =>
      let yltn1 = ltuInvPredNZ y yltun nnz
          yltn = auxyltn yltn1
         in
      rewrite shrDivBizPow2 (ifThenElse (x < 0) (Delay (x+((shl 1 y)-1))) (Delay x)) y in
      case ltLeTotal (signed x) (signed {n} 0) of
        Left xlts0 =>
          rewrite ltbLtFro x 0 xlts0 in
          let xlt0 = replace {P=\z=>signed x `Lt` z} (signedZero n nnz) xlts0 in
          rewrite quotDivNeg (signed x) (signed $ shl 1 y) xlt0 $
                    rewrite auxS yltn1 in
                    bizPow2Pos (unsigned y) (fst $ unsignedRange y)
                 in
          rewrite auxS yltn1 in
          rewrite addSigned x ((shl 1 y)-1) in
          rewrite auxS1 nnz yltn1 in
          rewrite signedRepr (signed x + (bizPow2 (unsigned y) - 1)) n nnz
                    (rewrite sym $ add0R (minSigned n) in
                     addLeMono (minSigned n) (signed x) 0 ((bizPow2 (unsigned y) - 1))
                       (fst $ signedRange x nnz)
                       (ltPredRTo 0 (bizPow2 (unsigned y)) $
                        bizPow2Pos (unsigned y) (fst $ unsignedRange y)))
                    (ltLeIncl (signed x + (bizPow2 (unsigned y) - 1)) (maxSigned n)  $
                     addLtMono (signed x) 0 ((bizPow2 (unsigned y) - 1)) (maxSigned n)
                       xlt0
                       (rewrite addCompareMonoR (bizPow2 (unsigned y)) (halfModulus n) (-1) in
                        unsignedPowHalfMod y yltn1))
                 in
          rewrite addAssoc (signed x) (bizPow2 (unsigned y)) (-1) in
          Refl
        Right szlex =>
          rewrite nltbLeFro 0 x szlex in
          let zlex = replace {P=\z=>z `Le` signed x} (signedZero n nnz) szlex in
          rewrite quotDivPos (signed x) (signed $ shl 1 y) zlex $
                    ltLeIncl 0 (signed $ shl 1 y) $
                    rewrite auxS yltn1 in
                    bizPow2Pos (unsigned y) (fst $ unsignedRange y)
                 in
          rewrite auxU yltn in
          rewrite ltbLtFro (bizPow2 (unsigned y)) (halfModulus n) (unsignedPowHalfMod y yltn1) in
          Refl
  where
  auxyltn : unsigned y `Lt` toBizNat n - 1 -> unsigned y `Lt` toBizNat n
  auxyltn yltn1 = ltTrans (unsigned y) (toBizNat n - 1) (toBizNat n) yltn1 (ltPred (toBizNat n))
  auxR : unsigned y `Lt` toBizNat n -> unsigned (repr (bizPow2 (unsigned y)) n) = bizPow2 (unsigned y)
  auxR yltn =
    let zleuy = fst $ unsignedRange y in
    unsignedRepr (bizPow2 (unsigned y)) n
      (ltLeIncl 0 (bizPow2 (unsigned y)) $
       bizPow2Pos (unsigned y) zleuy)
      (ltPredRTo (bizPow2 (unsigned y)) (modulus n) $
       rewrite modulusPower n in
       bizPow2MonotoneStrict (unsigned y) (toBizNat n) zleuy yltn)
  auxU : unsigned y `Lt` toBizNat n -> unsigned (shl 1 y) = bizPow2 (unsigned y)
  auxU yltn =
    rewrite shl1BizPow2 y in
    auxR yltn
  auxS : unsigned y `Lt` toBizNat n - 1 -> signed (shl 1 y) = bizPow2 (unsigned y)
  auxS yltn1 =
    let yltn = auxyltn yltn1 in
    rewrite shl1BizPow2 y in
    rewrite signedEqUnsigned (repr (bizPow2 (unsigned y)) n) $
              rewrite auxR yltn in
              ltPredRTo (bizPow2 (unsigned y)) (halfModulus n) (unsignedPowHalfMod y yltn1)
           in
    auxR yltn
  auxS1 : Not (n=0) -> unsigned y `Lt` toBizNat n - 1 -> signed ((shl 1 y)-1) = bizPow2 (unsigned y) - 1
  auxS1 nz yltn1 =
    let yltn = auxyltn yltn1 in
    rewrite shl1BizPow2 y in
    rewrite unsignedOne n nz in
    rewrite auxR yltn in
    signedRepr (bizPow2 (unsigned y) - 1) n nz
      (ltLeIncl (minSigned n) (bizPow2 (unsigned y) - 1) $
       ltLeTrans (minSigned n) 0 (bizPow2 (unsigned y) - 1)
         (minSignedNeg n nz)
         (ltPredRTo 0 (bizPow2 (unsigned y)) $
          bizPow2Pos (unsigned y) (fst $ unsignedRange y)))
      (ltLeIncl (bizPow2 (unsigned y) - 1) (maxSigned n) $
       rewrite addCompareMonoR (bizPow2 (unsigned y)) (halfModulus n) (-1) in
       unsignedPowHalfMod y yltn1)

shrxShr2 : (x, y : BizMod2 n) -> y `ltu` (repr (toBizNat n - 1) n) = True -> shrx x y = shr (x + (shru (shr x (repr (toBizNat n - 1) n)) (iwordsize n - y))) y
shrxShr2 {n} x y yltun =
  case decEq n 0 of
    Yes nz =>
      rewrite bizMod2P0N x nz in
      rewrite nz in
      Refl
    No nnz =>
      rewrite shrxShr x y yltun in
      rewrite shrLtZero x nnz in
      cong {f=\z=>shr z y} $
      case ltLeTotal (signed x) (signed {n} 0) of
        Left xlts0 =>
          rewrite ltbLtFro x 0 xlts0 in
          rewrite shl1BizPow2 y in
          rewrite unsignedOne n nnz in
          rewrite unsignedReprWordsize n in
          let zleuy = fst $ unsignedRange y
              uyltn = ltTrans (unsigned y) (toBizNat n - 1) (toBizNat n) (ltuInvPredNZ y yltun nnz) (ltPred (toBizNat n))
             in
          rewrite unsignedRepr (bizPow2 (unsigned y)) n
                    (ltLeIncl 0 (bizPow2 (unsigned y)) $
                     bizPow2Pos (unsigned y) zleuy)
                    (ltPredRTo (bizPow2 (unsigned y)) (modulus n) $
                     rewrite modulusPower n in
                     bizPow2MonotoneStrict (unsigned y) (toBizNat n) zleuy uyltn)
                 in
          cong {f=\z=>x+z} $
          sameBitsEq (repr ((bizPow2 (unsigned y)) - 1) n) (shru (repr (-1) n) (repr (toBizNat n - unsigned y) n)) $ \i, zlei, iltn =>
          rewrite testbitRepr n ((bizPow2 (unsigned y)) - 1) i zlei iltn in
          rewrite zTestbitBizPow2M1 (unsigned y) i zleuy zlei in
          rewrite bitsShru (repr (-1) n) (repr (toBizNat n - unsigned y) n) i zlei iltn in
          rewrite unsignedRepr (toBizNat n - unsigned y) n
                    (rewrite sym $ compareSubR (unsigned y) (toBizNat n) in
                     ltLeIncl (unsigned y) (toBizNat n) uyltn)
                    (leTrans (toBizNat n - unsigned y) (toBizNat n) (maxUnsigned n)
                       (rewrite addComm (toBizNat n) (-unsigned y) in
                        rewrite sym $ addCompareTransferL (toBizNat n) (unsigned y) (toBizNat n) in
                        rewrite addCompareMonoR 0 (unsigned y) (toBizNat n) in
                        zleuy)
                       (wordsizeMaxUnsigned n))
                 in
          case ltLeTotal i (unsigned y) of
            Left iltuy =>
              rewrite ltbLtFro i (unsigned y) iltuy in
              sym $ bitsMone n (i + (toBizNat n - unsigned y))
                (ltLeIncl 0 (i + (toBizNat n - unsigned y)) $
                 leLtTrans 0 i (i + (toBizNat n - unsigned y)) zlei $
                   rewrite addComm i (toBizNat n - unsigned y) in
                   rewrite addCompareMonoR 0 (toBizNat n - unsigned y) i in
                   rewrite sym $ compareSubR (unsigned y) (toBizNat n) in
                   uyltn)
                (rewrite addComm (toBizNat n) (-unsigned y) in
                 rewrite addAssoc i (-unsigned y) (toBizNat n) in
                 rewrite addCompareMonoR (i - unsigned y) 0 (toBizNat n) in
                 rewrite sym $ compareSub i (unsigned y) in
                 iltuy)
            Right uylei =>
              rewrite nltbLeFro (unsigned y) i uylei in
              sym $ bitsAbove (repr (-1) n) (i + (toBizNat n - unsigned y)) $
                rewrite addComm (toBizNat n) (-unsigned y) in
                rewrite addAssoc i (-unsigned y) (toBizNat n) in
                rewrite addCompareMonoR 0 (i - unsigned y) (toBizNat n) in
                rewrite sym $ compareSubR (unsigned y) i in
                uylei
        Right szlex =>
          rewrite nltbLeFro 0 x szlex in
          rewrite sameBitsEq (shru (repr 0 n) (iwordsize n - y)) 0 $ \i, zlei, iltn =>
                  rewrite bitsShru (repr 0 n) (iwordsize n - y) i zlei iltn in
                  rewrite unsignedZero n in
                  rewrite testbit0L i in
                  testbit0L (i + unsigned (iwordsize n - y))
                 in
          sym $ add0R x

shrxCarry : (x, y : BizMod2 n) -> y `ltu` (repr (toBizNat n - 1) n) = True -> shrx x y = (shr x y) + (shrCarry x y)
shrxCarry {n} x y yltun =
  case decEq n 0 of
    Yes nz =>
      rewrite bizMod2P0N x nz in
      rewrite nz in
      Refl
    No nnz =>
      rewrite shrxShr x y yltun in
      case ltLeTotal (signed x) (signed {n} 0) of
        Left xlts0 =>
          rewrite ltbLtFro x 0 xlts0 in
          let xlt0 = replace {P=\z=>signed x `Lt` z} (signedZero n nnz) xlts0
              yltn1 = ltuInvPredNZ y yltun nnz
              yltn = ltTrans (unsigned y) (toBizNat n - 1) (toBizNat n) yltn1 (ltPred (toBizNat n))
              zleuy = fst $ unsignedRange y
              p2ylemu = bizPow2Range n (unsigned y) zleuy yltn
              zlt2y = bizPow2Pos (unsigned y) zleuy
              (zlexm2y, xm2ylt2y) = modPosBound (unsigned x) (bizPow2 (unsigned y)) zlt2y
             in
          rewrite aux yltn in
          rewrite shl1BizPow2 y in
          rewrite shrDivBizPow2 (x+((repr (bizPow2 (unsigned y)) n)-1)) y in
          rewrite shrDivBizPow2 x y in
          rewrite aux2 in
          rewrite addSigned x (repr ((bizPow2 (unsigned y)) - 1) n) in
          rewrite signedRepr ((bizPow2 (unsigned y)) - 1) n nnz
                    (ltLeIncl (minSigned n) (bizPow2 (unsigned y) - 1) $
                     ltLeTrans (minSigned n) 0 (bizPow2 (unsigned y) - 1)
                       (minSignedNeg n nnz)
                       (ltPredRTo 0 (bizPow2 (unsigned y)) zlt2y))
                    (ltLeIncl (bizPow2 (unsigned y) - 1) (maxSigned n) $
                     rewrite addCompareMonoR (bizPow2 (unsigned y)) (halfModulus n) (-1) in
                     unsignedPowHalfMod y yltn1)
                 in
          rewrite signedRepr (signed x + (bizPow2 (unsigned y) - 1)) n nnz
                    (rewrite sym $ add0R (minSigned n) in
                     addLeMono (minSigned n) (signed x) 0 ((bizPow2 (unsigned y) - 1))
                       (fst $ signedRange x nnz)
                       (ltPredRTo 0 (bizPow2 (unsigned y)) zlt2y))
                    (ltLeIncl (signed x + (bizPow2 (unsigned y) - 1)) (maxSigned n)  $
                     addLtMono (signed x) 0 ((bizPow2 (unsigned y) - 1)) (maxSigned n)
                       xlt0
                       (rewrite addCompareMonoR (bizPow2 (unsigned y)) (halfModulus n) (-1) in
                        unsignedPowHalfMod y yltn1))
                 in
          rewrite unsignedZero n in
          rewrite divShift (signed x) (bizPow2 (unsigned y)) zlt2y in
          rewrite aux3 yltn in
          rewrite unsignedRepr (bizPow2 (unsigned y)) n
                    (ltLeIncl 0 (bizPow2 (unsigned y)) zlt2y)
                    p2ylemu
                 in
          rewrite unsignedRepr ((unsigned x) `bizMod` (bizPow2 (unsigned y))) n zlexm2y
                    (ltLeIncl ((unsigned x) `bizMod` (bizPow2 (unsigned y))) (maxUnsigned n) $
                     ltLeTrans ((unsigned x) `bizMod` (bizPow2 (unsigned y))) (bizPow2 (unsigned y)) (maxUnsigned n)
                       xm2ylt2y
                       p2ylemu)
                 in
          eqmSamerepr (((signed x) `bizDiv` (bizPow2 (unsigned y)))+(if ((unsigned x) `bizMod` (bizPow2 (unsigned y))) == 0 then 0 else 1))
                      ((unsigned (repr ((signed x) `bizDiv` (bizPow2 (unsigned y))) n))+(unsigned (if ((unsigned x) `bizMod` (bizPow2 (unsigned y))) /= 0 then repr 1 n else repr 0 n)))
                      n $
          eqmodAdd ((signed x) `bizDiv` (bizPow2 (unsigned y)))
                   (unsigned (repr ((signed x) `bizDiv` (bizPow2 (unsigned y))) n))
                   (if ((unsigned x) `bizMod` (bizPow2 (unsigned y))) == 0 then 0 else 1)
                   (unsigned (if ((unsigned x) `bizMod` (bizPow2 (unsigned y))) /= 0 then repr 1 n else repr 0 n))
                   (modulus n)
            (eqmUnsignedRepr ((signed x) `bizDiv` (bizPow2 (unsigned y))) n)
            (case decEq ((unsigned x) `bizMod` (bizPow2 (unsigned y))) 0 of
               Yes m0 =>
                 rewrite eqbEqFro ((unsigned x) `bizMod` (bizPow2 (unsigned y))) 0 m0 in
                 eqmUnsignedRepr 0 n
               No mnz =>
                 rewrite neqbNeqFro ((unsigned x) `bizMod` (bizPow2 (unsigned y))) 0 mnz in
                 eqmUnsignedRepr 1 n)
        Right szlex =>
          rewrite nltbLeFro 0 x szlex in
          sym $ add0R (shr x y)
  where
  aux : unsigned y `Lt` toBizNat n -> x `and` ((shl 1 y) - 1) = x `modu` (repr (bizPow2 (unsigned y)) n)
  aux yltn =
    rewrite shl1BizPow2 y in
    sym $ moduAnd x (repr (bizPow2 (unsigned y)) n) y $
      rewrite isPower2BizPow2 n (unsigned y) (fst $ unsignedRange y) yltn
             in
      cong $ reprUnsigned y
  aux2 : (repr (bizPow2 (unsigned y)) n) - 1 = repr ((bizPow2 (unsigned y)) - 1) n
  aux2 =
    eqmSamerepr ((unsigned (repr (bizPow2 (unsigned y)) n)) - (unsigned (repr 1 n))) ((bizPow2 (unsigned y)) - 1) n $
    eqmodSub (unsigned (repr (bizPow2 (unsigned y)) n)) (bizPow2 (unsigned y)) (unsigned (repr 1 n)) 1 (modulus n)
      (eqmUnsignedRepr' (bizPow2 (unsigned y)) n)
      (eqmUnsignedRepr' 1 n)
  aux3 : unsigned y `Lt` toBizNat n -> (signed x) `bizMod` (bizPow2 (unsigned y)) = (unsigned x) `bizMod` (bizPow2 (unsigned y))
  aux3 yltn =
    let zleuy = fst $ unsignedRange y in
    eqmodModEq (signed x) (unsigned x) (bizPow2 (unsigned y)) (bizPow2Pos (unsigned y) zleuy) $
    eqmodDivides (modulus n) (bizPow2 (unsigned y)) (signed x) (unsigned x)
      (eqmSignedUnsigned x)
      (rewrite bipPow2Biz n in
       (bizPow2 (toBizNat n - unsigned y) **
          rewrite sym $ bizPow2IsExp (toBizNat n - unsigned y) (unsigned y)
                    (rewrite sym $ compareSubR (unsigned y) (toBizNat n) in
                     ltLeIncl (unsigned y) (toBizNat n) yltn)
                    zleuy
                 in
          rewrite sym $ addAssoc (toBizNat n) (-unsigned y) (unsigned y) in
          rewrite addOppDiagL (unsigned y) in
          cong $ sym $ add0R (toBizNat n)))

-- Connections between [shr] and [shru].

shrShruPositive : (x, y : BizMod2 n) -> 0 `Le` signed x -> shr x y = shru x y
shrShruPositive x y zlesx =
  rewrite shrDivBizPow2 x y in
  rewrite shruDivBizPow2 x y in
  rewrite signedEqUnsigned x (signedPositiveTo x zlesx) in
  Refl

shrAndIsShruAnd : (x, y, z : BizMod2 n) -> y < 0 = False -> shr (x `and` y) z = shru (x `and` y) z
shrAndIsShruAnd {n} x y z ynlt0 =
  case decEq n 0 of
    Yes n0 => rewrite n0 in
              Refl
    No nnz =>
      shrShruPositive (x `and` y) z $
      andPositive x y $
      rewrite sym $ signedZero n nnz in
      nltbLeTo (repr 0 n) y ynlt0

-- Properties of [one_bits] (decomposition in sum of powers of two)

oneBitsRange : (x, i : BizMod2 n) -> Elem i (oneBits x) -> i `ltu` iwordsize n = True
oneBitsRange {n} x i elem =
  let (ui ** (eq, elemui)) = listElemMapInv (\x => repr x n) i (zOneBits n (unsigned x) 0) elem
      (zleui, uiltn) = zOneBitsRange n (unsigned x) ui elemui
     in
  rewrite eq in
  reprLtu ui n zleui uiltn

-- TODO move to BizMod2
intOfOneBits : List (BizMod2 n) -> BizMod2 n
intOfOneBits [] = 0
intOfOneBits (a :: b) = (shl 1 a) + (intOfOneBits b)

oneBitsDecomp : (x : BizMod2 n) -> x = intOfOneBits (oneBits x)
oneBitsDecomp {n} x =
  trans {b = repr (powerserie (zOneBits n (unsigned x) 0)) n}
    (trans {b = repr (unsigned x) n}
      (sym $ reprUnsigned x)
      (let (minu, maxu) = unsignedRange x in
       cong {f=\q=>repr q n} $ zOneBitsPowerserie n (unsigned x) minu maxu))
    (aux ((zOneBits n (unsigned x) BizO)) (zOneBitsRange n (unsigned x)))
  where
  aux : (l : List Biz) -> ((z : Biz) -> Elem z l -> (0 `Le` z, z `Lt` toBizNat n)) -> repr (powerserie l) n = intOfOneBits ((\x => repr x n) <$> l)
  aux [] _ = Refl
  aux (e :: l) f =
    rewrite sym $ aux l (\z, el => f z (There el)) in
    eqmSamerepr ((bizPow2 e)+(powerserie l)) ((unsigned (shl 1 (repr e n)))+(unsigned (repr (powerserie l) n))) n $
    eqmodAdd (bizPow2 e) (unsigned (shl 1 (repr e n))) (powerserie l) (unsigned (repr (powerserie l) n)) (modulus n)
      (rewrite shl1BizPow2 (repr e n) in
       eqmUnsignedReprR (bizPow2 e)  (bizPow2 (unsigned (repr e n))) n $
       let (mine, maxe) = f e Here in
       rewrite unsignedRepr e n mine $
               ltLeIncl e (maxUnsigned n) $
               ltLeTrans e (toBizNat n) (maxUnsigned n) maxe (wordsizeMaxUnsigned n) in
       eqmodRefl (bizPow2 e) (modulus n))
      (eqmUnsignedRepr (powerserie l) n)

-- !!!
-- TODO can't put the following in Biz/BizMod2.Bitwise because of equalSameBits & zTestbitModBizPow2
-- TODO move this + dependencies + earlier complex lemmas to Biz.Bitwise.Extended? how to move equalSameBits, refactor modulus?
bizDigitsInterval1 : (x : Biz) -> 0 `Le` x -> x `Lt` bizPow2 (bizDigits x)
bizDigitsInterval1 x zlex =
  leLtTrans x (x `bizMod` (bizPow2 (bizDigits x))) (bizPow2 (bizDigits x))
    (rewrite compareEqIffFro x (x `bizMod` (bizPow2 (bizDigits x))) $
             equalSameBits x (x `bizMod` (bizPow2 (bizDigits x))) $ \i, zlei =>
             rewrite zTestbitModBizPow2 (bizDigits x) x i (bizDigitsNonneg x) zlei in
             case ltLeTotal i (bizDigits x) of
               Left iltdx =>
                 rewrite ltbLtFro i (bizDigits x) iltdx in
                 Refl
               Right dxlei =>
                 rewrite nltbLeFro (bizDigits x) i dxlei in
                 bizTestbitDigits2 x i zlex dxlei
            in
     uninhabited)
    (snd $ modPosBound x (bizPow2 (bizDigits x)) (bizPow2Pos (bizDigits x) (bizDigitsNonneg x)))

bizDigitsMonotone : (x, y : Biz) -> 0 `Le` x -> x `Le` y -> bizDigits x `Le` bizDigits y
bizDigitsMonotone x y zlex xley =
  bizDigitsInterval2 x (bizDigits y) (bizDigitsNonneg y) zlex $
  leLtTrans x y (bizPow2 (bizDigits y)) xley $
  bizDigitsInterval1 y (leTrans 0 x y zlex xley)

digitsInterval1 : (x : BizMod2 n) -> unsigned x `Lt` bizPow2 (digits x)
digitsInterval1 x = bizDigitsInterval1 (unsigned x) (fst $ unsignedRange x)

digitsInterval2 : (x : BizMod2 n) -> (m : Biz) -> 0 `Le` m -> unsigned x `Lt` bizPow2 m -> digits x `Le` m
digitsInterval2 x m zlem uxlt2m = bizDigitsInterval2 (unsigned x) m zlem (fst $ unsignedRange x) uxlt2m

andInterval : (a, b : BizMod2 n) -> unsigned (a `and` b) `Lt` bizPow2 (digits a `min` digits b)
andInterval a b =
  ltLeTrans (unsigned (a `and` b)) (bizPow2 (digits (a `and` b))) (bizPow2 (digits a `min` digits b))
    (digitsInterval1 (a `and` b))
    (bizPow2Monotone (digits (a `and` b)) (digits a `min` digits b)
      (fst $ digitsRange (a `and` b))
      (digitsAnd a b))

orInterval : (a, b : BizMod2 n) -> unsigned (a `or` b) `Lt` bizPow2 (digits a `max` digits b)
orInterval a b = rewrite sym $ digitsOr a b in
                 digitsInterval1 (a `or` b)

xorInterval : (a, b : BizMod2 n) -> unsigned (a `xor` b) `Lt` bizPow2 (digits a `max` digits b)
xorInterval a b =
  ltLeTrans (unsigned (a `xor` b)) (bizPow2 (digits (a `xor` b))) (bizPow2 (digits a `max` digits b))
  (digitsInterval1 (a `xor` b))
  (bizPow2Monotone (digits (a `xor` b)) (digits a `max` digits b)
    (fst $ digitsRange (a `xor` b))
    (digitsXor a b))