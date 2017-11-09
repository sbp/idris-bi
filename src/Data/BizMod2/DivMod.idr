module Data.BizMod2.DivMod

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.DivMod

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.AddSubMul

%access public export
%default total

-- Properties of division and modulus

moduDivuEuclid : (x, y : BizMod2 n) -> Not (y = 0) -> x = ((x `divu` y)*y)+(x `modu` y)
moduDivuEuclid {n} x y yz =
  let ux = unsigned x
      uy = unsigned y in
  trans (sym $ reprUnsigned x) $
  eqmSamerepr ux ((unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)+(unsigned $ repr (ux `bizMod` uy) n)) n $
  eqmodTrans ux ((ux `bizDiv` uy)*uy + (ux `bizMod` uy))
             ((unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)+(unsigned $ repr (ux `bizMod` uy) n))
             (modulus n)
    (eqmodRefl2 ux ((ux `bizDiv` uy)*uy + (ux `bizMod` uy)) (modulus n) $
     divEuclEq ux uy $
     yz . replace {P=\z=>z=0} (reprUnsigned y) . cong {f=\z=>repr z n})
    (eqmodAdd ((ux `bizDiv` uy)*uy) (unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)
              (ux `bizMod` uy) (unsigned $ repr (ux `bizMod` uy) n)
              (modulus n)
       (eqmodTrans ((ux `bizDiv` uy)*uy) ((unsigned $ repr (ux `bizDiv` uy) n)*uy)
                   (unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)
                   (modulus n)
          (eqmodMult (ux `bizDiv` uy) (unsigned $ repr (ux `bizDiv` uy) n) uy uy (modulus n)
             (eqmUnsignedRepr (ux `bizDiv` uy) n)
             (eqmodRefl uy (modulus n)))
          (eqmUnsignedRepr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n))
       (eqmUnsignedRepr (ux `bizMod` uy) n))

moduDivu : (x, y : BizMod2 n) -> Not (y = 0) -> x `modu` y = x - ((x `divu` y)*y)
moduDivu x y yz = addTransferL x ((x `divu` y)*y) (x `modu` y) $
                  moduDivuEuclid x y yz

modsDivsEuclid : (x, y : BizMod2 n) -> x = ((x `divs` y)*y)+(x `mods` y)
modsDivsEuclid {n} x y =
  let uy = unsigned y
      sx = signed x
      sy = signed y in
  trans (sym $ reprSigned x) $
  eqmSamerepr sx ((unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)+(unsigned $ repr (sx `bizRem` sy) n)) n $
  eqmodTrans sx ((sx `bizQuot` sy)*sy + (sx `bizRem` sy))
             ((unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)+(unsigned $ repr (sx `bizRem` sy) n))
             (modulus n)
    (eqmodRefl2 sx ((sx `bizQuot` sy)*sy + (sx `bizRem` sy)) (modulus n) $
     quotremEq sx sy)
    (eqmodAdd ((sx `bizQuot` sy)*sy) (unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)
              (sx `bizRem` sy) (unsigned $ repr (sx `bizRem` sy) n)
              (modulus n)
       (eqmodTrans ((sx `bizQuot` sy)*sy) ((unsigned $ repr (sx `bizQuot` sy) n)*uy)
                   (unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)
                   (modulus n)
          (eqmodMult (sx `bizQuot` sy) (unsigned $ repr (sx `bizQuot` sy) n) sy uy (modulus n)
             (eqmUnsignedRepr (sx `bizQuot` sy) n)
             (eqmSignedUnsigned y))
          (eqmUnsignedRepr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n))
       (eqmUnsignedRepr (sx `bizRem` sy) n))

modsDivs : (x, y : BizMod2 n) -> x `mods` y = x - ((x `divs` y)*y)
modsDivs x y = addTransferL x ((x `divs` y)*y) (x `mods` y) $
               modsDivsEuclid x y

divu1 : (x : BizMod2 n) -> x `divu` 1 = x
divu1 {n=Z}   x = sym $ bizMod2P0 x
divu1 {n=S n} x = rewrite fst $ divMod1 (unsigned x) in
                  reprUnsigned x

-- there are some weird problems if you just split n
modu1 : (x : BizMod2 n) -> x `modu` 1 = 0
modu1 {n} x with (decEq n 0)
  | Yes z = rewrite z in
            Refl
  | No nz =
    rewrite moduDivu x 1 (oneNotZero n nz) in
    rewrite divu1 x in
    rewrite mul1R x in
    subIdem x

divsM1 : (x : BizMod2 n) -> x `divs` (-1) = -x
divsM1 {n} x =
  rewrite signedMone n in
  rewrite quotOppR (signed x) 1 uninhabited in
  rewrite quot1R (signed x) in
  eqmSamerepr (-(signed x)) (-(unsigned x)) n $
  eqmodNeg (signed x) (unsigned x) (modulus n) $
  eqmSignedUnsigned x

modsM1 : (x : BizMod2 n) -> x `mods` (-1) = 0
modsM1 x =
  rewrite modsDivs x (-1) in
  rewrite divsM1 x in
  rewrite mulNegL x (-1) in
  rewrite mulM1R x in
  rewrite negInvolutive x in
  subIdem x

divmodu2DivuModu : (nl, d : BizMod2 n) -> Not (d = 0) -> divmodu2 0 nl d = Just (nl `divu` d, nl `modu` d)
divmodu2DivuModu {n} nl d dz =
  rewrite neqbNeqFro (unsigned d) (unsigned $ repr 0 n) (dz . unsignedInj d 0) in
  rewrite unsignedZero n in
  rewrite lebLeFro ((unsigned nl) `bizDiv` (unsigned d)) (maxUnsigned n) $
            ltPredRTo ((unsigned nl) `bizDiv` (unsigned d)) (modulus n) $
            leLtTrans ((unsigned nl) `bizDiv` (unsigned d)) (unsigned nl) (modulus n)
              (divLe (unsigned nl) (unsigned d)
                 (case leLtOrEq 0 (unsigned d) (fst $ unsignedRange d) of
                    Left zltd => zltd
                    Right zd => absurd $ aux d dz $ sym zd
                 )
                 (fst $ unsignedRange nl))
              (snd $ unsignedRange nl)
              in
  Refl
  where
  aux : (x : BizMod2 n) -> Not (x = 0) -> Not (unsigned x = 0)
  aux x xz = rewrite sym $ unsignedZero n in
             xz . unsignedInj x 0

-- TODO the normalized types explode so fast that it doesn't seem realistic to
-- prove manually in current Idris (1.1.1)
{-
-- when n=0 the condition in divmods2 becomes 0 <= q <= -1 so this won't hold
divmods2DivsMods : (nl, d : BizMod2 n) -> Not (n=0) -> Not (d = 0) -> Either (Not (nl = repr (minSigned n) n)) (Not (d = -1))
                 -> divmods2 (if nl < 0 then -1 else 0) nl d = Just (nl `divs` d, nl `mods` d)
divmods2DivsMods {n} nl d nz dz nlord =
  rewrite neqbNeqFro (unsigned d) (unsigned $ repr 0 n) (dz . unsignedInj d 0) in
  rewrite unsignedZero n in
  rewrite ltbLtFro 0 (halfModulus n) $ halfModulusPos n nz in
  rewrite aux nl nz in
  ?divmods2DivsMods
  where
  aux : (x : BizMod2 n) -> Not (n=0) -> signed (if x < 0 then -1 else 0) * (modulus n) + unsigned x = signed x
-}
