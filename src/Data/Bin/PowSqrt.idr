module Data.Bin.PowSqrt

import Data.Util

--import Data.Bip.Iter
import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.PowSqrt

import Data.Bin
import Data.Bin.AddSubMul
import Data.Bin.Ord

%access public export
%default total

-- Specifications of power

-- pow_0_r is trivial

-- pow_succ_r
-- dropped the `0<=p` requirement as it's trivial
powSuccR : (n, p : Bin) -> binPow n (binSucc p) = n * binPow n p
powSuccR  BinO     BinO    = Refl
powSuccR (BinP _)  BinO    = Refl
powSuccR  BinO    (BinP _) = Refl
powSuccR (BinP a) (BinP b) = cong $ powSuccR a b

-- pow_neg_r doesn't make sense: as Bin, p can't ever be <0

-- Specification of square

-- square_spec

squareSpec : (n : Bin) -> binSquare n = n * n
squareSpec  BinO    = Refl
squareSpec (BinP a) = cong $ squareSpec a

-- Specification of Base-2 logarithm

-- size_log2

sizeLog2 : (n : Bin) -> Not (n=0) -> binDigits n = binSucc (binLogTwo n)
sizeLog2  BinO        nz = absurd $ nz Refl
sizeLog2 (BinP  U   ) _  = Refl
sizeLog2 (BinP (O _)) _  = Refl
sizeLog2 (BinP (I _)) _  = Refl

-- size_gt

sizeGt : (n : Bin) -> n `Lt` binPow 2 (binDigits n)
sizeGt  BinO    = Refl
sizeGt (BinP a) = sizeGt a

-- size_le

sizeLe : (n : Bin) -> binPow 2 (binDigits n) `Le` binDPO n
sizeLe  BinO    = uninhabited
sizeLe (BinP a) =
  ltLeIncl (bipPow 2 (bipDigits a)) (I a) $
  ltSuccRFro (bipPow 2 (bipDigits a)) (O a) $
  sizeLe a

-- log2_spec
-- TODO replace requirement with `Not (n=0)`?
log2Spec : (n : Bin) -> 0 `Lt` n -> ( binPow 2 (binLogTwo n) `Le` n
                                    , n `Lt` binPow 2 (binSucc (binLogTwo n))
                                    )
log2Spec  BinO        zltn = absurd zltn
log2Spec (BinP  U   ) _    = (uninhabited, Refl)
log2Spec (BinP (O a)) _    = (sizeLe a, sizeGt $ BinP $ O a)
log2Spec (BinP (I a)) _    = (sizeLe $ BinP a, sizeGt $ BinP $ I a)

-- log2_nonpos doesn't make sense too (and is trivial when n=0)

-- Specification of square root

-- sqrtrem_sqrt

sqrtremSqrt : (n : Bin) -> fst (binSqrtRem n) = binSqrt n
sqrtremSqrt  BinO    = Refl
sqrtremSqrt (BinP a) with (snd $ bipSqrtRem a)
  | BimP _ = Refl
  | BimO   = Refl
  | BimM   = Refl

-- sqrtrem_spec

sqrtremSpec : (n : Bin) -> let sr = binSqrtRem n
                               s = fst sr
                               r = snd sr
                           in (n = s*s + r, r `Le` 2*s)
sqrtremSpec  BinO    = (Refl, uninhabited)
sqrtremSpec (BinP a) = case sqrtremSpec a of
  SqrtExact  prf     srprf =>
    rewrite srprf in
    (cong prf, uninhabited)
  SqrtApprox prf rle srprf =>
    rewrite srprf in
    (cong prf, rle)

-- sqrt_spec
-- removed redundant constraint on `n`
sqrtSpec : (n : Bin) -> let s = binSqrt n in
  (s*s `Le` n, n `Lt` (binSucc s)*(binSucc s))
sqrtSpec BinO = (uninhabited, Refl)
sqrtSpec (BinP a) = sqrtSpec a

-- sqrt_neg doesn't make sense