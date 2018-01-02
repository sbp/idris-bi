module Data.Biz.PowSqrt

import Control.Pipeline

import Data.Util

import Data.Bip.AddMul
import Data.Bip.Iter
import Data.Bip.OrdSub
import Data.Bip.PowSqrt

import Data.Bin.AddSubMul
import Data.Bin.Ord
import Data.Bin.PowSqrt

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Bitwise

%access export
%default total

-- Specification of power

-- pow_Zpos

powZpos : (p, q : Bip) -> bizPow (BizP p) (BizP q) = BizP (bipPow p q)
powZpos p q = sym $ iterSwapGen BizP (bipMult p) (bizMult $ BizP p) (\_ => Refl) U q

-- pow_0_r is trivial

-- pow_0_l

pow0L : (a : Biz) -> Not (a=0) -> bizPow 0 a = 0
pow0L  BizO    anz = absurd $ anz Refl
pow0L (BizP a) _   =
  case succPredOr a of
    Left equ  => rewrite equ in
                 Refl
    Right eqs =>
      rewrite sym eqs in
      rewrite iterSucc (bizMult 0) 1 (bipPred a) in
      Refl
pow0L (BizM _) _   = Refl

-- pow_succ_r

powSuccR : (n, m : Biz) -> 0 `Le` m -> bizPow n (bizSucc m) = n * bizPow n m
powSuccR _  BizO    _    = Refl
powSuccR n (BizP a) _    = rewrite addComm a 1 in
                           iterAdd (bizMult n) 1 1 a
powSuccR _ (BizM _) zlem = absurd $ zlem Refl

-- pow_neg_r

powNegR : (n, m : Biz) -> m `Lt` 0 -> bizPow n m = 0
powNegR _  BizO    = absurd
powNegR _ (BizP _) = absurd
powNegR _ (BizM _) = const Refl

-- For folding back a [pow_pos] into a [pow]

-- pow_pos_fold is trivial

powDoubleOpp : (a : Biz) -> (b : Bip) -> bizPow (-a) (BizP (O b)) = bizPow a (BizP (O b))
powDoubleOpp a b =
  peanoRect
    (\x => bizPow (-a) (BizP (O x)) = bizPow a (BizP (O x)))
    (rewrite mul1R a in
     rewrite mul1R (-a) in
     mulOppOpp a a
    )
    (\x, prf =>
      rewrite iterSucc (bizMult a) 1 x in
      rewrite iterSwap (bizMult a) (bizPow a (BizP x)) (bipSucc x) in
      rewrite iterSucc (bizMult a) (bizPow a (BizP x)) x in
      rewrite mulAssoc a a (bizPow a (BizP (O x))) in
      rewrite iterSucc (bizMult (-a)) 1 x in
      rewrite iterSwap (bizMult (-a)) (bizPow (-a) (BizP x)) (bipSucc x) in
      rewrite iterSucc (bizMult (-a)) (bizPow (-a) (BizP x)) x in
      rewrite mulAssoc (-a) (-a) (bizPow (-a) (BizP (O x))) in
      rewrite mulOppOpp a a in
      cong prf
    )
    b

-- pow_opp_even

powOppEven : (a, b : Biz) -> Even b -> bizPow (-a) b = bizPow a b
powOppEven _  BizO     _              = Refl
powOppEven _ (BizP _) (BizO   ** prf) = absurd prf
powOppEven a (BizP b) (BizP x ** prf) =
  rewrite bizPInj prf in
  powDoubleOpp a x
powOppEven _ (BizP _) (BizM _ ** prf) = absurd prf
powOppEven _ (BizM _)  _              = Refl

-- pow_opp_odd

powOppOdd : (a, b : Biz) -> Odd b -> bizPow (-a) b = -bizPow a b
powOppOdd _  BizO    (BizO   ** prf) = absurd prf
powOppOdd _  BizO    (BizP _ ** prf) = absurd prf
powOppOdd _  BizO    (BizM _ ** prf) = absurd prf
powOppOdd a (BizP _) (BizO   ** prf) = rewrite bizPInj prf in
                                       mulOppL a 1
powOppOdd a (BizP _) (BizP x ** prf) =
  rewrite bizPInj prf in
  rewrite powDoubleOpp a x in
  mulOppL a (bizPow a (BizP (O x)))
powOppOdd _ (BizP _) (BizM _ ** prf) = absurd prf
powOppOdd _ (BizM _)  _              = Refl

-- abs_pow

absPowPos : (a, b : Bip) -> bizAbs (bizPow (BizP a) (BizP b)) = bizPow (BizP a) (BizP b)
absPowPos a b =
  absEq (bizPow (BizP a) (BizP b)) $
  ltLeIncl 0 (bizPow (BizP a) (BizP b)) $
  iterInvariant (bizMult (BizP a)) (\x => 0 `Lt` x) b
    (\x,prf => rewrite mulCompareMonoL (BizP a) 0 x Refl in
               prf) 1 Refl

absPow : (a, b : Biz) -> bizAbs (bizPow a b) = bizPow (bizAbs a) b
absPow  _        BizO    = Refl
absPow  BizO    (BizP b) = rewrite pow0L (BizP b) uninhabited in
                           Refl
absPow (BizP a) (BizP b) = absPowPos a b
absPow (BizM a) (BizP b) =
  case evenOrOdd (BizP b) of
    Left  eprf => rewrite sym $ powOppEven (BizM a) (BizP b) eprf in
                  absPowPos a b
    Right oprf => let absM = powOppOdd (BizM a) (BizP b) oprf
                          |> cong {f=bizOpp}
                          |> replace (oppInvolutive (bizPow (BizM a) (BizP b)))
                   in
                  rewrite sym absM in
                  rewrite absOpp (bizPow (BizP a) (BizP b)) in
                  absPowPos a b
absPow  _       (BizM _) = Refl

powAddR : (a, b, c : Biz) -> 0 `Le` b -> 0 `Le` c -> bizPow a (b+c) = (bizPow a b) * (bizPow a c)
powAddR a b c zleb zlec =
  natlikeInd
    (\x => bizPow a (x+c) = (bizPow a x) * (bizPow a c))
    (sym $ mul1L (bizPow a c))
    (\x,zlex,prf =>
      rewrite sym $ addAssoc x 1 c in
      rewrite addComm 1 c in
      rewrite addAssoc x c 1 in
      rewrite powSuccR a (x+c) (addLeMono 0 x 0 c zlex zlec) in
      rewrite powSuccR a x zlex in
      rewrite sym $ mulAssoc a (bizPow a x) (bizPow a c) in
      cong {f=bizMult a} prf)
    b zleb

-- Power of 2

bizPow2Equiv : (x : Biz) -> bizPow2 x = bizPow 2 x
bizPow2Equiv  BizO    = Refl
bizPow2Equiv (BizP p) = iterSwapGen BizP O (bizMult 2) (\_ => Refl) U p
bizPow2Equiv (BizM _) = Refl

bipPow2Biz : (x : Nat) -> BizP (bipPow2 x) = bizPow2 (toBizNat x)
bipPow2Biz  Z        = Refl
bipPow2Biz (S  Z)    = Refl
bipPow2Biz (S (S k)) = rewrite iterSucc O U (toBipNatSucc k) in
                       cong {f = BizP . O} $ bizPInj $ bipPow2Biz (S k)

bizPow2Pos : (x : Biz) -> 0 `Le` x -> 0 `Lt` bizPow2 x
bizPow2Pos  BizO    _    = Refl
bizPow2Pos (BizP _) _    = Refl
bizPow2Pos (BizM _) zlex = absurd $ zlex Refl

bizPow2S : (x : Biz) -> 0 `Le` x -> bizPow2 (bizSucc x) = bizD (bizPow2 x)
bizPow2S x zlex =
  rewrite bizPow2Equiv (bizSucc x) in
  rewrite bizPow2Equiv x in
  rewrite powSuccR 2 x zlex in
  sym $ doubleSpec (bizPow 2 x)

bizPow2IsExp : (x, y : Biz) -> 0 `Le` x -> 0 `Le` y -> bizPow2 (x + y) = bizPow2 x * bizPow2 y
bizPow2IsExp x y zlex zley =
  rewrite bizPow2Equiv (x+y) in
  rewrite bizPow2Equiv x in
  rewrite bizPow2Equiv y in
  powAddR 2 x y zlex zley

pow2Le : (n : Biz) -> n `Le` bizPow2 n
pow2Le  BizO     = uninhabited
pow2Le (BizP a)  =
  peanoRect
    (\x => x `Le` bipIter O U x)
    uninhabited
    (\p, prf =>
      rewrite iterSucc O U p in
      rewrite sym $ succPredDouble (bipIter O U p) in
      rewrite compareSuccSucc p (bipDMO (bipIter O U p)) in
      leTrans p (bipIter O U p) (bipDMO (bipIter O U p)) prf (leDMO (bipIter O U p))
    )
    a
pow2Le (BizM _)  = uninhabited

bizPow2Monotone : (x, y : Biz) -> 0 `Le` x -> x `Le` y -> bizPow2 x `Le` bizPow2 y
bizPow2Monotone x y zlex xley =
  rewrite sym $ add0R y in
  rewrite sym $ addOppDiagR x in
  rewrite addAssoc y x (-x) in
  rewrite addComm y x in
  rewrite sym $ addAssoc x y (-x) in
  rewrite bizPow2IsExp x (y-x) zlex $
            rewrite sym $ compareSubR x y in
            xley
         in
  rewrite sym $ mul1R (bizPow2 x) in
  rewrite sym $ mulAssoc (bizPow2 x) 1 (bizPow2 (y-x)) in
  rewrite mul1L (bizPow2 (y-x)) in
  rewrite mulCompareMonoL (bizPow2 x) 1 (bizPow2 (y-x)) (bizPow2Pos x zlex) in
  leSuccLFro 0 (bizPow2 (y-x)) $
  bizPow2Pos (y-x) $
    rewrite sym $ compareSubR x y in
    xley

bizPow2MonotoneStrict : (x, y : Biz) -> 0 `Le` x -> x `Lt` y -> bizPow2 x `Lt` bizPow2 y
bizPow2MonotoneStrict x y zlex xlty =
  rewrite sym $ add0R y in
  rewrite addAssoc y (-1) 1 in
  let xley1 = ltPredRTo x y xlty
      zley1 = leTrans 0 x (y-1) zlex xley1
     in
  rewrite bizPow2IsExp (y-1) 1 zley1 uninhabited in
  leLtTrans (bizPow2 x) (bizPow2 (y-1)) ((bizPow2 (y-1))*2)
    (bizPow2Monotone x (y-1) zlex xley1)
    (rewrite sym $ mul1R (bizPow2 (y-1)) in
     rewrite sym $ mulAssoc (bizPow2 (y-1)) 1 2 in
     rewrite mulCompareMonoL (bizPow2 (y-1)) 1 2 (bizPow2Pos (y-1) zley1) in
     Refl)

-- Specification of square

-- square_spec

squareSpec : (n : Biz) -> bizSquare n = n * n
squareSpec  BizO    = Refl
squareSpec (BizP a) = cong $ squareSpec a
squareSpec (BizM a) = cong $ squareSpec a

-- Specification of square root

-- sqrtrem_spec

sqrtremSpec : (n : Biz) -> 0 `Le` n -> let sr = bizSqrtRem n
                                           s = fst sr
                                           r = snd sr
                                         in (n = s*s + r, 0 `Le` r, r `Le` 2*s)
sqrtremSpec  BizO    _    = (Refl, uninhabited, uninhabited)
sqrtremSpec (BizP a) zlen =
  case sqrtremSpec a of
    SqrtExact  prf      prfa => rewrite prfa in
                                (cong prf, uninhabited, uninhabited)
    SqrtApprox prf prf1 prfa => rewrite prfa in
                                (cong prf, uninhabited, prf1)
sqrtremSpec (BizM a) zlen = absurd $ zlen Refl

-- sqrt_spec

sqrtSpec : (n : Biz) -> 0 `Le` n -> let s = bizSqrt n
                                      in (s*s `Le` n, n `Lt` (bizSucc s)*(bizSucc s))
sqrtSpec  BizO    zlen = (zlen, Refl)
sqrtSpec (BizP a) zlen = rewrite add1R $ bipSqrt a in
                         sqrtSpec a
sqrtSpec (BizM a) zlen = absurd $ zlen Refl

-- sqrt_neg

sqrtNeg : (n : Biz) -> n `Lt` 0 -> bizSqrt n = 0
sqrtNeg  BizO    = absurd
sqrtNeg (BizP _) = absurd
sqrtNeg (BizM _) = const Refl

-- sqrtrem_sqrt

sqrtremSqrt : (n : Biz) -> fst (bizSqrtRem n) = bizSqrt n
sqrtremSqrt  BizO    = Refl
sqrtremSqrt (BizP a) with (bipSqrtRem a)
  | (_,BimO)   = Refl
  | (_,BimP _) = Refl
  | (_,BimM)   = Refl
sqrtremSqrt (BizM _) = Refl

-- Specification of logarithm

-- log2_spec

log2Spec : (n : Biz) -> 0 `Lt` n -> (bizPow 2 (bizLog2 n) `Le` n, n `Lt` bizPow 2 (bizSucc (bizLog2 n)))
log2Spec  BizO        zltn = absurd zltn
log2Spec (BizP  U   ) _    = (uninhabited, Refl)
log2Spec (BizP (O a)) _    = rewrite powZpos 2 (bipDigits a) in
                             rewrite powZpos 2 ((bipDigits a)+1) in
                             ( sizeLe a
                             , rewrite addComm (bipDigits a) 1 in
                               rewrite iterAdd (bipMult 2) 1 1 (bipDigits a) in
                               sizeGt a
                             )
log2Spec (BizP (I a)) _    = rewrite powZpos 2 (bipDigits a) in
                             rewrite powZpos 2 ((bipDigits a)+1) in
                             ( leTrans (bipPow 2 (bipDigits a)) (O a) (I a) (sizeLe a) $
                                 rewrite compareContSpec a a LT in
                                 rewrite compareContRefl a EQ in
                                 uninhabited
                             , rewrite addComm (bipDigits a) 1 in
                               rewrite iterAdd (bipMult 2) 1 1 (bipDigits a) in
                               compareContGtLtFro a (bipPow 2 (bipDigits a)) (sizeGt a)
                             )
log2Spec (BizM _)     zltn = absurd zltn

-- log2_nonpos

log2Nonpos : (n : Biz) -> n `Le` 0 -> bizLog2 n = 0
log2Nonpos  BizO    _    = Refl
log2Nonpos (BizP _) nle0 = absurd $ nle0 Refl
log2Nonpos (BizM _) _    = Refl