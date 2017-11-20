module Data.BizMod2.Bitwise.Pow2

import Data.List
import Data.Util

import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Bitwise
import Data.Biz.Nat
import Data.Biz.PowSqrt

import Data.BizMod2

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