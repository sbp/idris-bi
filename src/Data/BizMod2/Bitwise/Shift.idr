module Data.BizMod2.Bitwise.Shift

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.DivMod
import Data.Biz.Bitwise
import Data.Biz.PowSqrt
import Data.Biz.Nat

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.AddSubMul
import Data.BizMod2.Bitwise

%access export
%default total

-- Properties of shifts

bitsShl : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
       -> testbit (shl x y) i = if i < unsigned y then False else testbit x (i - unsigned y)
bitsShl {n} x y i zlei iltn with (i < unsigned y) proof iy
  | True =
    rewrite testbitRepr n (bizShiftL (unsigned x) (unsigned y)) i zlei iltn in
    shiftlSpecLow (unsigned x) (unsigned y) i (ltbLtTo i (unsigned y) (sym iy))
  | False =
    rewrite testbitRepr n (bizShiftL (unsigned x) (unsigned y)) i zlei iltn in
    shiftlSpecHigh (unsigned x) (unsigned y) i zlei (nltbLeTo (unsigned y) i (sym iy))

-- the original has `if i + unsigned y < toBizNat n then testbit x (i + unsigned y) else False` here
-- this seems redundant: we can simply use bitsAbove after using this
bitsShru : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
        -> testbit (shru x y) i = testbit x (i + unsigned y)
bitsShru {n} x y i zlei iltn =
  rewrite testbitRepr n (bizShiftR (unsigned x) (unsigned y)) i zlei iltn in
  shiftrSpec (unsigned x) (unsigned y) i zlei

bitsShr : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
      -> testbit (shr x y) i = testbit x (if i + unsigned y < toBizNat n then i + unsigned y else toBizNat n - 1)
bitsShr {n=Z}   x y i _    _    =
  rewrite bizMod2P0 x in
  rewrite testbit0L (ifThenElse (i + unsigned y < 0) (Delay (i + unsigned y)) (Delay (-1))) in
  testbit0L i
bitsShr {n=S n} x y i zlei iltn =
  rewrite testbitRepr (S n) (bizShiftR (signed x) (unsigned y)) i zlei iltn in
  rewrite shiftrSpec (signed x) (unsigned y) i zlei in
  bitsSigned x (i+unsigned y) uninhabited $
    leTrans 0 i (i+unsigned y) zlei $
      rewrite addComm i (unsigned y) in
      rewrite addCompareMonoR 0 (unsigned y) i in
      fst $ unsignedRange y

shlZero : (x : BizMod2 n) -> shl x 0 = x
shlZero {n} x =
  sameBitsEq (shl x 0) x $ \i, zlei, iltn =>
  rewrite unsignedZero n in
  rewrite reprUnsigned x in
  Refl

bitwiseBinopShl : (f : BizMod2 n -> BizMod2 n -> BizMod2 n) -> (fb : Bool -> Bool -> Bool) -> (x, y, k : BizMod2 n)
               -> ((a, b : BizMod2 n) -> (j : Biz) -> 0 `Le` j -> j `Lt` toBizNat n -> testbit (f a b) j = fb (testbit a j) (testbit b j))
               -> fb False False = False -> f (shl x k) (shl y k) = shl (f x y) k
bitwiseBinopShl {n} f fb x y k ftest fbprf =
  sameBitsEq (f (shl x k) (shl y k)) (shl (f x y) k) $ \i, zlei, iltn =>
  rewrite ftest (shl x k) (shl y k) i zlei iltn in
  rewrite bitsShl (f x y) k i zlei iltn in
  rewrite bitsShl x k i zlei iltn in
  rewrite bitsShl y k i zlei iltn in
  aux i zlei iltn
  where
  aux : (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
     -> fb (if i < unsigned k then False else testbit x (i - unsigned k))
           (if i < unsigned k then False else testbit y (i - unsigned k)) =
          if i < unsigned k then False else testbit (f x y) (i - unsigned k)
  aux i zlei iltn with (i < unsigned k) proof ik
    | True = fbprf
    | False = sym $ ftest x y (i - unsigned k)
                (rewrite sym $ compareSubR (unsigned k) i in
                 nltbLeTo (unsigned k) i (sym ik))
                (leLtTrans (i - unsigned k) i (toBizNat n)
                   (rewrite addComm i (-unsigned k) in
                    rewrite addCompareMonoR (-unsigned k) 0 i in
                    rewrite sym $ compareOpp 0 (unsigned k) in
                    fst $ unsignedRange k)
                   iltn)

andShl : (x, y, k : BizMod2 n) -> (shl x k) `and` (shl y k) = shl (x `and` y) k
andShl x y k = bitwiseBinopShl and (\a, b => a && b) x y k bitsAnd Refl

orShl : (x, y, k : BizMod2 n) -> (shl x k) `or` (shl y k) = shl (x `or` y) k
orShl x y k = bitwiseBinopShl or (\a, b => a || b) x y k bitsOr Refl

xorShl : (x, y, k : BizMod2 n) -> (shl x k) `xor` (shl y k) = shl (x `xor` y) k
xorShl x y k = bitwiseBinopShl xor xor x y k bitsXor Refl

-- TODO put in Ord
-- `0 <= unsigned x` is just unsignedRange
ltuInv : (x, y : BizMod2 n) -> x `ltu` y = True -> unsigned x `Lt` unsigned y
ltuInv x y = ltbLtTo (unsigned x) (unsigned y)

ltuIwordsizeInv : (x : BizMod2 n) -> x `ltu` iwordsize n = True -> unsigned x `Lt` toBizNat n
ltuIwordsizeInv {n} x prf =
  rewrite sym $ unsignedReprWordsize n in
  ltuInv x (iwordsize n) prf

ltuSum : (x, y : BizMod2 n) -> x `ltu` iwordsize n = True -> y `ltu` iwordsize n = True
      -> unsigned (x+y) = unsigned x + unsigned y
ltuSum {n} x y xn yn =
  unsignedRepr (unsigned x + unsigned y) n
    (addLeMono 0 (unsigned x) 0 (unsigned y) (fst $ unsignedRange x) (fst $ unsignedRange y))
    (leTrans (unsigned x + unsigned y) (bizDMO (toBizNat n)) (maxUnsigned n)
      (rewrite predDoubleSpec (toBizNat n) in
       ltPredRTo (unsigned x + unsigned y) (2*(toBizNat n)) $
       rewrite mulAddDistrR 1 1 (toBizNat n) in
       rewrite mul1L (toBizNat n) in
       addLtMono (unsigned x) (toBizNat n) (unsigned y) (toBizNat n) (ltuIwordsizeInv x xn) (ltuIwordsizeInv y yn))
      (twoWordsizeMaxUnsigned n)
    )

-- A helper to avoid dependent pattern matching on comparisons
compareTotal : (p, q : Biz) -> Either (Either (p `Lt` q) (p `Gt` q)) (bizCompare p q = EQ)
compareTotal p q with (p `compare` q)
  | LT = Left $ Left Refl
  | EQ = Right Refl
  | GT = Left $ Right Refl

-- TODO requirements on y and z look far stronger than necessary, this seems to hold for y+z < 2^n
shlShl : (x, y, z : BizMod2 n)
      -> y `ltu` iwordsize n = True -> z `ltu` iwordsize n = True
      -> shl (shl x y) z = shl x (y+z)
shlShl {n} x y z yn zn =
  sameBitsEq (shl (shl x y) z) (shl x (y+z)) $ \i, zlei, iltn =>
  rewrite bitsShl (shl x y) z i zlei iltn in
  rewrite bitsShl x (y+z) i zlei iltn in
  rewrite ltuSum y z yn zn in
  aux i zlei iltn
  where
  aux : (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
      -> (if i < unsigned z then False else testbit (shl x y) (i - unsigned z)) =
           (if i < unsigned y + unsigned z then False else testbit x (i - (unsigned y + unsigned z)))
  aux i zlei iltn with (i < unsigned z) proof iz
    | True =
      rewrite ltbLtFro i (unsigned y + unsigned z) $
         ltLeTrans i (unsigned z) (unsigned y + unsigned z)
           (ltbLtTo i (unsigned z) (sym iz))
           (rewrite addCompareMonoR 0 (unsigned y) (unsigned z) in
            fst $ unsignedRange y)
      in Refl
    | False =
      rewrite bitsShl x y (i - unsigned z)
               (rewrite sym $ compareSubR (unsigned z) i in
                nltbLeTo (unsigned z) i (sym iz))
               (leLtTrans (i - unsigned z) i (toBizNat n)
                  (rewrite addComm i (-unsigned z) in
                    rewrite addCompareMonoR (-unsigned z) 0 i in
                    rewrite sym $ compareOpp 0 (unsigned z) in
                    fst $ unsignedRange z)
                  iltn)
            in
      rewrite addComm (unsigned y) (unsigned z) in
      rewrite addCompareTransferL i (unsigned z) (unsigned y) in
      rewrite addComm (-unsigned z) i in
      rewrite oppAddDistr (unsigned z) (unsigned y) in
      rewrite addAssoc i (-unsigned z) (-unsigned y) in
      case compareTotal (i - unsigned z) (unsigned y) of
        Left (Left izylt)  => rewrite izylt in Refl
        Right izyeq        => rewrite izyeq in Refl
        Left (Right izygt) => rewrite izygt in Refl

shruZero : (x : BizMod2 n) -> shru x 0 = x
shruZero {n} x =
  sameBitsEq (shru x 0) x $ \i, zlei, iltn =>
  rewrite unsignedZero n in
  rewrite reprUnsigned x in
  Refl

bitwiseBinopShru : (f : BizMod2 n -> BizMod2 n -> BizMod2 n) -> (fb : Bool -> Bool -> Bool) -> (x, y, k : BizMod2 n)
                -> ((a, b : BizMod2 n) -> (j : Biz) -> 0 `Le` j -> j `Lt` toBizNat n -> testbit (f a b) j = fb (testbit a j) (testbit b j))
                -> fb False False = False -> f (shru x k) (shru y k) = shru (f x y) k
bitwiseBinopShru {n} f fb x y k ftest fbprf =
  sameBitsEq (f (shru x k) (shru y k)) (shru (f x y) k) $ \i, zlei, iltn =>
  rewrite ftest (shru x k) (shru y k) i zlei iltn in
  rewrite bitsShru (f x y) k i zlei iltn in
  rewrite bitsShru x k i zlei iltn in
  rewrite bitsShru y k i zlei iltn in
  case ltLeTotal (i + unsigned k) (toBizNat n) of
    Left ikltn =>
      sym $ ftest x y (i + unsigned k)
       (leTrans 0 i (i + unsigned k)
          zlei
          (rewrite addComm i (unsigned k) in
           rewrite addCompareMonoR 0 (unsigned k) i in
           fst $ unsignedRange k))
       ikltn
    Right nleik =>
      rewrite bitsAbove x (i + unsigned k) nleik in
      rewrite bitsAbove y (i + unsigned k) nleik in
      rewrite bitsAbove (f x y) (i + unsigned k) nleik in
      fbprf

andShru : (x, y, k : BizMod2 n) -> (shru x k) `and` (shru y k) = shru (x `and` y) k
andShru x y k = bitwiseBinopShru and (\a, b => a && b) x y k bitsAnd Refl

orShru : (x, y, k : BizMod2 n) -> (shru x k) `or` (shru y k) = shru (x `or` y) k
orShru x y k = bitwiseBinopShru or (\a, b => a || b) x y k bitsOr Refl

xorShru : (x, y, k : BizMod2 n) -> (shru x k) `xor` (shru y k) = shru (x `xor` y) k
xorShru x y k = bitwiseBinopShru xor xor x y k bitsXor Refl

-- TODO requirements on y and z look far stronger than necessary, this seems to hold for y+z < 2^n
shruShru : (x, y, z : BizMod2 n)
        -> y `ltu` iwordsize n = True -> z `ltu` iwordsize n = True
        -> shru (shru x y) z = shru x (y+z)
shruShru {n} x y z yn zn =
  sameBitsEq (shru (shru x y) z) (shru x (y+z)) $ \i, zlei, iltn =>
  rewrite bitsShru (shru x y) z i zlei iltn in
  rewrite bitsShru x (y+z) i zlei iltn in
  rewrite ltuSum y z yn zn in
  case ltLeTotal (i + unsigned z) (toBizNat n) of
    Left izltn =>
      rewrite bitsShru x y (i + unsigned z)
                (leTrans 0 i (i + unsigned z)
                   zlei
                   (rewrite addComm i (unsigned z) in
                    rewrite addCompareMonoR 0 (unsigned z) i in
                    fst $ unsignedRange z))
                izltn
              in
      rewrite addComm (unsigned y) (unsigned z) in
      rewrite addAssoc i (unsigned z) (unsigned y) in
      Refl
    Right nleiz =>
      rewrite bitsAbove (shru x y) (i + unsigned z) nleiz in
      sym $ bitsAbove x (i + (unsigned y + unsigned z)) $
      leTrans (toBizNat n) (i + unsigned z) (i + (unsigned y + unsigned z))
        nleiz
        (rewrite addAssoc i (unsigned y) (unsigned z) in
         rewrite addComm i (unsigned y) in
         rewrite sym $ addAssoc (unsigned y) i (unsigned z) in
         rewrite addCompareMonoR 0 (unsigned y) (i + unsigned z) in
         fst $ unsignedRange y)

shrZero : (x : BizMod2 n) -> shr x 0 = x
shrZero {n} x =
  sameBitsEq (shr x 0) x $ \i, zlei, iltn =>
  rewrite unsignedZero n in
  rewrite reprSigned x in
  Refl

bitwiseBinopShr : (f : BizMod2 n -> BizMod2 n -> BizMod2 n) -> (fb : Bool -> Bool -> Bool) -> (x, y, k : BizMod2 n)
               -> ((a, b : BizMod2 n) -> (j : Biz) -> 0 `Le` j -> j `Lt` toBizNat n -> testbit (f a b) j = fb (testbit a j) (testbit b j))
               -> f (shr x k) (shr y k) = shr (f x y) k
bitwiseBinopShr {n=Z}   f _  _ _ _ _     = bizMod2P0 (f (MkBizMod2 BizO (Refl, Refl)) (MkBizMod2 BizO (Refl, Refl)))
bitwiseBinopShr {n=S n} f fb x y k ftest =
  sameBitsEq (f (shr x k) (shr y k)) (shr (f x y) k) $ \i, zlei, iltn =>
  rewrite ftest (shr x k) (shr y k) i zlei iltn in
  rewrite bitsShr (f x y) k i zlei iltn in
  rewrite bitsShr x k i zlei iltn in
  rewrite bitsShr y k i zlei iltn in
  case ltLeTotal (i + unsigned k) (toBizNat (S n)) of
    Left ikltn =>
      rewrite ltbLtFro (i + unsigned k) (toBizNat (S n)) ikltn in
      sym $ ftest x y (i + unsigned k)
        (leTrans 0 i (i + unsigned k)
           zlei
           (rewrite addComm i (unsigned k) in
            rewrite addCompareMonoR 0 (unsigned k) i in
            fst $ unsignedRange k))
        ikltn
    Right nleik =>
      rewrite nltbLeFro (toBizNat (S n)) (i + unsigned k) nleik in
      sym $ ftest x y (toBizNat (S n) - 1)
        (ltPredRTo 0 (toBizNat (S n)) Refl)
        (ltPredLTo (toBizNat (S n)) (toBizNat (S n)) $
         leRefl (toBizNat (S n)))

andShr : (x, y, k : BizMod2 n) -> (shr x k) `and` (shr y k) = shr (x `and` y) k
andShr x y k = bitwiseBinopShr and (\a, b => a && b) x y k bitsAnd

orShr : (x, y, k : BizMod2 n) -> (shr x k) `or` (shr y k) = shr (x `or` y) k
orShr x y k = bitwiseBinopShr or (\a, b => a || b) x y k bitsOr

xorShr : (x, y, k : BizMod2 n) -> (shr x k) `xor` (shr y k) = shr (x `xor` y) k
xorShr x y k = bitwiseBinopShr xor xor x y k bitsXor

-- TODO requirements on y and z look far stronger than necessary, this seems to hold for y+z < 2^n
shrShr : (x, y, z : BizMod2 n)
      -> y `ltu` iwordsize n = True -> z `ltu` iwordsize n = True
      -> shr (shr x y) z = shr x (y+z)
shrShr {n=Z}   _ _ _ _  _  = Refl
shrShr {n=S n} x y z yn zn =
  sameBitsEq (shr (shr x y) z) (shr x (y+z)) $ \i, zlei, iltn =>
  rewrite bitsShr (shr x y) z i zlei iltn in
  rewrite bitsShr x (y+z) i zlei iltn in
  rewrite ltuSum y z yn zn in
  case ltLeTotal (i + unsigned z) (toBizNat (S n)) of
    Left izltn =>
      rewrite ltbLtFro (i + unsigned z) (toBizNat (S n)) izltn in
      rewrite bitsShr x y (i + unsigned z)
                (leTrans 0 i (i + unsigned z)
                   zlei
                   (rewrite addComm i (unsigned z) in
                    rewrite addCompareMonoR 0 (unsigned z) i in
                    fst $ unsignedRange z))
                izltn
        in
      rewrite addComm (unsigned y) (unsigned z) in
      rewrite addAssoc i (unsigned z) (unsigned y) in
      case compareTotal (i + unsigned z + unsigned y) (toBizNat (S n)) of
        Left (Left izylt)  => rewrite izylt in Refl
        Right izyeq        => rewrite izyeq in Refl
        Left (Right izygt) => rewrite izygt in Refl
    Right nleiz =>
      rewrite nltbLeFro (toBizNat (S n)) (i + unsigned z) nleiz in
      rewrite bitsShr x y (toBizNat (S n) - 1)
                (ltPredRTo 0 (toBizNat (S n)) Refl)
                (ltPredLTo (toBizNat (S n)) (toBizNat (S n)) $
                 leRefl (toBizNat (S n)))
              in
      rewrite nltbLeFro (toBizNat (S n)) (i + (unsigned y + unsigned z)) $
                leTrans (toBizNat (S n)) (i + unsigned z) (i + (unsigned y + unsigned z))
                  nleiz
                  (rewrite addAssoc i (unsigned y) (unsigned z) in
                   rewrite addComm i (unsigned y) in
                   rewrite sym $ addAssoc (unsigned y) i (unsigned z) in
                   rewrite addCompareMonoR 0 (unsigned y) (i + unsigned z) in
                   fst $ unsignedRange y)
              in
      case leLtOrEq 0 (unsigned y) (fst $ unsignedRange y) of
        Left zlty =>
          rewrite nltbLeFro (toBizNat (S n)) (toBizNat (S n) - 1 + unsigned y) $
                     rewrite sym $ addAssoc (toBizNat (S n)) (-1) (unsigned y) in
                     rewrite addComm (toBizNat (S n)) (-1+unsigned y) in
                     rewrite addCompareMonoR 0 (-1+unsigned y) (toBizNat (S n)) in
                     rewrite addCompareTransferL 0 (-1) (unsigned y) in
                     leSuccLFro 0 (unsigned y) zlty
                 in
          Refl
        Right zeqy =>
          rewrite sym zeqy in
          rewrite add0R (toBizNat (S n) - 1) in
          rewrite ltbLtFro (toBizNat (S n) - 1) (toBizNat (S n)) $
                   ltPredLTo (toBizNat (S n)) (toBizNat (S n)) $
                   leRefl (toBizNat (S n))
                 in
          Refl

andShrShru : (x, y, z : BizMod2 n) -> (shr x z) `and` (shru y z) = shru (x `and` y) z
andShrShru {n} x y z =
  sameBitsEq ((shr x z) `and` (shru y z)) (shru (x `and` y) z) $ \i, zlei, iltn =>
  rewrite bitsAnd (shr x z) (shru y z) i zlei iltn in
  rewrite bitsShr x z i zlei iltn in
  rewrite bitsShru y z i zlei iltn in
  rewrite bitsShru (x `and` y) z i zlei iltn in
  case ltLeTotal (i + unsigned z) (toBizNat n) of
    Left izltn =>
      rewrite ltbLtFro (i + unsigned z) (toBizNat n) izltn in
      sym $ bitsAnd x y (i + unsigned z)
        (leTrans 0 i (i + unsigned z)
           zlei
           (rewrite addComm i (unsigned z) in
            rewrite addCompareMonoR 0 (unsigned z) i in
            fst $ unsignedRange z))
        izltn
    Right nleiz =>
      rewrite nltbLeFro (toBizNat n) (i + unsigned z) nleiz in
      rewrite bitsAbove y (i + unsigned z) nleiz in
      rewrite bitsAbove (x `and` y) (i + unsigned z) nleiz in
      andFalse (testbit x (toBizNat n - 1))

shrAndShruAnd : (x, y, z : BizMod2 n) -> shru (shl z y) y = z -> (shr x y) `and` z = (shru x y) `and` z
shrAndShruAnd x y z prf =
  rewrite sym prf in
  rewrite andShru x (shl z y) y in
  andShrShru x (shl z y) y

-- TODO this actually holds for n=0 but we run into issues with rewrite
-- TODO we could also reformulate the RHS condition as `halfModulus n <= unsigned x'
shruLtZero : (x : BizMod2 n) -> Not (n=0) -> shru x (repr (toBizNat n - 1) n) = if x < repr 0 n then repr 1 n else repr 0 n
shruLtZero {n} x nz =
  sameBitsEq (shru x (repr (toBizNat n - 1) n)) (if x < 0 then 1 else 0) $ \i, zlei, iltn =>
  rewrite bitsShru x (repr (toBizNat n - 1) n) i zlei iltn in
  rewrite unsignedRepr (toBizNat n - 1) n
            (rewrite sym $ compareSubR 1 (toBizNat n) in
             leSuccLFro 0 (toBizNat n) $
             leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) $
             nz . toBizNatInj n 0)
            (rewrite addCompareMonoR (toBizNat n) (modulus n) (-1) in
             rewrite modulusPower n in
             pow2Le (toBizNat n))
    in
  rewrite signedZero n nz in
  case leLtOrEq 0 i zlei of
    Right i0 =>
      rewrite sym i0 in
      rewrite signBitOfUnsigned x nz in
      case ltLeTotal (unsigned x) (halfModulus n) of
        Left uxltn2 =>
          rewrite ltbLtFro (unsigned x) (halfModulus n) uxltn2 in
          case geGtOrEq (unsigned x) 0 (leGe 0 (unsigned x) $ fst $ unsignedRange x) of
            Left gt => rewrite gt in
                       rewrite unsignedZero n in
                       Refl
            Right eq => rewrite eq in
                        rewrite unsignedZero n in
                        Refl
        Right n2leux =>
          rewrite nltbLeFro (halfModulus n) (unsigned x) n2leux in
          rewrite sym $ compareSub (unsigned x) (modulus n) in
          rewrite snd $ unsignedRange x in
          rewrite unsignedOne n nz in
          Refl
    Left zlti =>
      rewrite bitsAbove x (i + (toBizNat n - 1)) $
            rewrite addComm (toBizNat n) (-1) in
            rewrite addAssoc i (-1) (toBizNat n) in
            rewrite addCompareMonoR 0 (i-1) (toBizNat n) in
            rewrite sym $ compareSubR 1 i in
            leSuccLFro 0 i zlti
          in
      case ltLeTotal (unsigned x) (halfModulus n) of
        Left uxltn2 =>
          rewrite ltbLtFro (unsigned x) (halfModulus n) uxltn2 in
          case geGtOrEq (unsigned x) 0 (leGe 0 (unsigned x) $ fst $ unsignedRange x) of
            Left gt => rewrite gt in
                       sym $ bitsZero i
            Right eq => rewrite eq in
                        sym $ bitsZero i
        Right n2leux =>
          rewrite nltbLeFro (halfModulus n) (unsigned x) n2leux in
          rewrite sym $ compareSub (unsigned x) (modulus n) in
          rewrite snd $ unsignedRange x in
          rewrite unsignedOne n nz in
          rewrite testbit1L i in
          sym $ neqbNeqFro i 0 $
          \i0 => absurd $ replace i0 zlti

-- TODO this should also hold for n=0
shrLtZero : (x : BizMod2 n) -> Not (n=0) -> shr x (repr (toBizNat n - 1) n) = if x < repr 0 n then repr (-1) n else repr 0 n
shrLtZero {n} x nz =
  sameBitsEq (shr x (repr (toBizNat n - 1) n)) (if x < 0 then repr (-1) n else 0) $ \i, zlei, iltn =>
  rewrite bitsShr x (repr (toBizNat n - 1) n) i zlei iltn in
  rewrite unsignedRepr (toBizNat n - 1) n
            (rewrite sym $ compareSubR 1 (toBizNat n) in
             leSuccLFro 0 (toBizNat n) $
             leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) $
             nz . toBizNatInj n 0)
            (rewrite addCompareMonoR (toBizNat n) (modulus n) (-1) in
             rewrite modulusPower n in
             pow2Le (toBizNat n))
         in
  rewrite signedZero n nz in
  trans {b = testbit x (toBizNat n - 1)}
    (case ltLeTotal (i + (toBizNat n - 1)) (toBizNat n) of
       Left in1ltn =>
         rewrite ltbLtFro (i + (toBizNat n - 1)) (toBizNat n) in1ltn in
         case leLtOrEq 0 i zlei of
           Right i0 => rewrite sym i0 in
                       Refl
           Left zlti =>
             let olei = leSuccLFro 0 i zlti
                 ogti = in1ltn
                     |> replace {P=\z=>i+z `Lt` toBizNat n} (addComm (toBizNat n) (-1))
                     |> replace {P=\z=>z `Lt` toBizNat n} (addAssoc i (-1) (toBizNat n))
                     |> replace {P=\z=>z=LT} (addCompareMonoR (i-1) 0 (toBizNat n))
                     |> replace {P=\z=>z=LT} (sym $ compareSub i 1)
                     |> ltGt i 1
                in
             absurd $ olei ogti
       Right nlein1 =>
         rewrite nltbLeFro (toBizNat n) (i + (toBizNat n - 1)) nlein1 in
         Refl
    )
    (rewrite signBitOfUnsigned x nz in
     case ltLeTotal (unsigned x) (halfModulus n) of
       Left uxltn2 =>
         rewrite ltbLtFro (unsigned x) (halfModulus n) uxltn2 in
         case geGtOrEq (unsigned x) 0 (leGe 0 (unsigned x) $ fst $ unsignedRange x) of
           Left gt => rewrite gt in
                      sym $ bitsZero i
           Right eq => rewrite eq in
                       sym $ bitsZero i
       Right n2leux =>
         rewrite nltbLeFro (halfModulus n) (unsigned x) n2leux in
         rewrite sym $ compareSub (unsigned x) (modulus n) in
         rewrite snd $ unsignedRange x in
         sym $ bitsMone n i zlei iltn
    )

-- Properties of rotations

bitsRol : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
      -> testbit (rol x y) i = testbit x ((i - unsigned y) `bizMod` (toBizNat n))
bitsRol {n} x y i zlei iltn =
  case decEq n 0 of
    Yes n0 =>
      rewrite n0 in
      rewrite bizMod2P0N x n0 in
      rewrite testbit0L i in
      sym $ testbit0L ((i - unsigned y) `bizMod` 0)
    No nz =>
      rewrite testbitRepr n (bizOr (bizShiftL (unsigned x) (unsigned y `bizMod` toBizNat n))
                                   (bizShiftR (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n)))) i zlei iltn in
      rewrite lorSpec (bizShiftL (unsigned x) (unsigned y `bizMod` toBizNat n))
                      (bizShiftR (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n))) i in
      rewrite shiftrSpec (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n)) i zlei in
      let ymnrange = modPosBound (unsigned y) (toBizNat n) $
                     leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) $
                     nz . toBizNatInj n 0
          ydivmodn = divEuclEq (unsigned y) (toBizNat n) (nz . toBizNatInj n 0)
          in
      case ltLeTotal i (unsigned y `bizMod` toBizNat n) of
        Left iltymn =>
          rewrite shiftlSpecLow (unsigned x) (unsigned y `bizMod` toBizNat n) i iltymn in
          cong {f = testbit x} $
          snd $ divModPos (i - unsigned y) (toBizNat n) (-(unsigned y `bizDiv` toBizNat n)-1) (i + (toBizNat n - (unsigned y `bizMod` toBizNat n)))
           (rewrite addAssoc i (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
            rewrite sym $ compareSubR (unsigned y `bizMod` toBizNat n) (i+(toBizNat n)) in
            ltLeIncl (unsigned y `bizMod` toBizNat n) (i+(toBizNat n)) $
            ltLeTrans (unsigned y `bizMod` toBizNat n) (toBizNat n) (i+(toBizNat n))
              (snd ymnrange)
              (rewrite addCompareMonoR 0 i (toBizNat n) in
               zlei))
           (rewrite addComm (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
            rewrite addAssoc i (-(unsigned y `bizMod` toBizNat n)) (toBizNat n) in
            rewrite addCompareMonoR (i-(unsigned y `bizMod` toBizNat n)) 0 (toBizNat n) in
            rewrite sym $ compareSub i (unsigned y `bizMod` toBizNat n) in
            iltymn)
           (rewrite addAssoc i (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
            rewrite addAssoc ((-(unsigned y `bizDiv` toBizNat n)-1)*(toBizNat n)) (i + toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
            rewrite addComm i (toBizNat n) in
            rewrite addAssoc ((-(unsigned y `bizDiv` toBizNat n)-1)*(toBizNat n)) (toBizNat n) i in
            rewrite mulAddDistrR (-(unsigned y `bizDiv` toBizNat n)) (-1) (toBizNat n) in
            rewrite sym $ oppEqMulM1L (toBizNat n) in
            rewrite sym $ addAssoc ((-(unsigned y `bizDiv` toBizNat n))*(toBizNat n)) (-toBizNat n) (toBizNat n) in
            rewrite addOppDiagL (toBizNat n) in
            rewrite add0R ((-(unsigned y `bizDiv` toBizNat n))*(toBizNat n)) in
            rewrite addComm ((-(unsigned y `bizDiv` toBizNat n))*(toBizNat n)) i in
            rewrite sym $ addAssoc i ((-(unsigned y `bizDiv` toBizNat n))*(toBizNat n)) (-(unsigned y `bizMod` toBizNat n)) in
            rewrite mulOppL (unsigned y `bizDiv` toBizNat n) (toBizNat n) in
            rewrite sym $ oppAddDistr ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) (unsigned y `bizMod` toBizNat n) in
            cong {f=\z=> i - z} ydivmodn)
        Right ymnlei =>
          rewrite shiftlSpecHigh (unsigned x) (unsigned y `bizMod` toBizNat n) i zlei ymnlei in
          rewrite bitsAbove x (i + (toBizNat n - (unsigned y `bizMod` toBizNat n))) $
                    rewrite addComm (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
                    rewrite addAssoc i (-(unsigned y `bizMod` toBizNat n)) (toBizNat n) in
                    rewrite addCompareMonoR 0 (i-(unsigned y `bizMod` toBizNat n)) (toBizNat n) in
                    rewrite sym $ compareSubR (unsigned y `bizMod` toBizNat n) i in
                    ymnlei
                  in
          rewrite orFalse $ testbit x (i - (unsigned y `bizMod` toBizNat n)) in
          cong {f = testbit x} $
          snd $ divModPos (i - unsigned y) (toBizNat n) (-(unsigned y `bizDiv` toBizNat n)) (i - (unsigned y `bizMod` toBizNat n))
            (rewrite sym $ compareSubR (unsigned y `bizMod` toBizNat n) i in
             ymnlei)
            (leLtTrans (i - (unsigned y `bizMod` toBizNat n)) i (toBizNat n)
              (rewrite addComm i (-(unsigned y `bizMod` toBizNat n)) in
               rewrite addCompareMonoR (-(unsigned y `bizMod` toBizNat n)) 0 i in
               rewrite sym $ compareOpp 0 (unsigned y `bizMod` toBizNat n) in
               fst ymnrange)
              iltn)
            (rewrite mulOppL (unsigned y `bizDiv` toBizNat n) (toBizNat n) in
             rewrite addAssoc (-((unsigned y `bizDiv` toBizNat n)*(toBizNat n))) i (-(unsigned y `bizMod` toBizNat n)) in
             rewrite addComm (-((unsigned y `bizDiv` toBizNat n)*(toBizNat n))) i in
             rewrite sym $ addAssoc i (-((unsigned y `bizDiv` toBizNat n)*(toBizNat n))) (-(unsigned y `bizMod` toBizNat n)) in
             rewrite sym $ oppAddDistr ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) (unsigned y `bizMod` toBizNat n) in
             cong {f=\z=> i - z} ydivmodn)

bitsRor : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
      -> testbit (ror x y) i = testbit x ((i + unsigned y) `bizMod` (toBizNat n))
bitsRor {n} x y i zlei iltn =
  case decEq n 0 of
    Yes n0 =>
      rewrite n0 in
      rewrite bizMod2P0N x n0 in
      rewrite testbit0L i in
      sym $ testbit0L ((i + unsigned y) `bizMod` 0)
    No nz =>
      rewrite testbitRepr n (bizOr (bizShiftR (unsigned x) (unsigned y `bizMod` toBizNat n))
                                   (bizShiftL (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n)))) i zlei iltn in
      rewrite lorSpec (bizShiftR (unsigned x) (unsigned y `bizMod` toBizNat n))
                      (bizShiftL (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n))) i in
      rewrite shiftrSpec (unsigned x) (unsigned y `bizMod` toBizNat n) i zlei in
      let ymnrange = modPosBound (unsigned y) (toBizNat n) $
                     leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) $
                     nz . toBizNatInj n 0
          ydivmodn = divEuclEq (unsigned y) (toBizNat n) (nz . toBizNatInj n 0)
          in
      case ltLeTotal (i+(unsigned y `bizMod` toBizNat n)) (toBizNat n) of
        Left iymnltn =>
          rewrite shiftlSpecLow (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n)) i $
                    rewrite addComm (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
                    rewrite addCompareTransferL i (-(unsigned y `bizMod` toBizNat n)) (toBizNat n) in
                    rewrite oppInvolutive (unsigned y `bizMod` toBizNat n) in
                    rewrite addComm (unsigned y `bizMod` toBizNat n) i in
                    iymnltn
                  in
          rewrite orFalse $ testbit x (i + (unsigned y `bizMod` toBizNat n)) in
          cong {f = testbit x} $
          snd $ divModPos (i + unsigned y) (toBizNat n) (unsigned y `bizDiv` toBizNat n) (i + (unsigned y `bizMod` toBizNat n))
            (addLeMono 0 i 0 (unsigned y `bizMod` toBizNat n) zlei (fst ymnrange))
            iymnltn
            (rewrite addAssoc ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) i (unsigned y `bizMod` toBizNat n) in
             rewrite addComm ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) i in
             rewrite sym $ addAssoc i ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) (unsigned y `bizMod` toBizNat n) in
             cong {f=bizPlus i} ydivmodn)
        Right ymnlei =>
          rewrite shiftlSpecHigh (unsigned x) ((toBizNat n) - (unsigned y `bizMod` toBizNat n)) i zlei $
                    rewrite addComm (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
                    rewrite sym $ addCompareTransferL (toBizNat n) (unsigned y `bizMod` toBizNat n) i in
                    rewrite addComm (unsigned y `bizMod` toBizNat n) i in
                    ymnlei
                 in
          rewrite bitsAbove x (i + (unsigned y `bizMod` toBizNat n)) ymnlei in
          cong {f = testbit x} $
          snd $ divModPos (i + unsigned y) (toBizNat n) ((unsigned y `bizDiv` toBizNat n)+1) (i - ((toBizNat n) - (unsigned y `bizMod` toBizNat n)))
            (rewrite oppAddDistr (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
             rewrite oppInvolutive (unsigned y `bizMod` toBizNat n) in
             rewrite addComm (-toBizNat n) (unsigned y `bizMod` toBizNat n) in
             rewrite addAssoc i (unsigned y `bizMod` toBizNat n) (-toBizNat n) in
             rewrite sym $ compareSubR (toBizNat n) (i+(unsigned y `bizMod` toBizNat n)) in
             ymnlei)
            (rewrite oppAddDistr (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
             rewrite oppInvolutive (unsigned y `bizMod` toBizNat n) in
             rewrite addAssoc i (-toBizNat n) (unsigned y `bizMod` toBizNat n) in
             rewrite addComm i (-toBizNat n) in
             rewrite sym $ addAssoc (-toBizNat n) i (unsigned y `bizMod` toBizNat n) in
             rewrite sym $ addCompareTransferL (i+(unsigned y `bizMod` toBizNat n)) (toBizNat n) (toBizNat n) in
             addLtMono i (toBizNat n) (unsigned y `bizMod` toBizNat n) (toBizNat n) iltn (snd ymnrange))
            (rewrite mulAddDistrR (unsigned y `bizDiv` toBizNat n) 1 (toBizNat n) in
             rewrite mul1L (toBizNat n) in
             rewrite oppAddDistr (toBizNat n) (-(unsigned y `bizMod` toBizNat n)) in
             rewrite oppInvolutive (unsigned y `bizMod` toBizNat n) in
             rewrite addAssoc i (-toBizNat n) (unsigned y `bizMod` toBizNat n) in
             rewrite addAssoc ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)+(toBizNat n)) (i-toBizNat n) (unsigned y `bizMod` toBizNat n) in
             rewrite addComm i (-toBizNat n) in
             rewrite addAssoc ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)+(toBizNat n)) (-toBizNat n) i in
             rewrite sym $ addAssoc ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) (toBizNat n) (-toBizNat n) in
             rewrite addOppDiagR (toBizNat n) in
             rewrite add0R ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) in
             rewrite addComm ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) i in
             rewrite sym $ addAssoc i ((unsigned y `bizDiv` toBizNat n)*(toBizNat n)) (unsigned y `bizMod` toBizNat n) in
             cong {f=bizPlus i} ydivmodn)

-- `ltu y iwordsize n = True` doesn't seem necessary
shlRolm : (x, y : BizMod2 n) -> shl x y = rolm x y (shl (repr (-1) n) y)
shlRolm {n} x y =
  sameBitsEq (shl x y) (rolm x y (shl (repr (-1) n) y)) $ \i, zlei, iltn =>
  rewrite bitsAnd (x `rol` y) (shl (repr (-1) n) y) i zlei iltn in
  rewrite bitsShl x y i zlei iltn in
  rewrite bitsShl (repr (-1) n) y i zlei iltn in
  rewrite bitsRol x y i zlei iltn in
  case ltLeTotal i (unsigned y) of
    Left ilty =>
      rewrite ltbLtFro i (unsigned y) ilty in
      sym $ andFalse (testbit x (i-unsigned y `bizMod` toBizNat n))
    Right ylei =>
      rewrite nltbLeFro (unsigned y) i ylei in
      rewrite bitsMone n (i - unsigned y)
                (rewrite sym $ compareSubR (unsigned y) i in
                 ylei)
                (leLtTrans (i - unsigned y) i (toBizNat n)
                  (rewrite addComm i (-unsigned y) in
                   rewrite addCompareMonoR (-unsigned y) 0 i in
                   rewrite sym $ compareOpp 0 (unsigned y) in
                   fst $ unsignedRange y)
                  iltn)
             in
      rewrite andTrue (testbit x (i-unsigned y `bizMod` toBizNat n)) in
      cong {f = testbit x} $
      sym $ snd $ divModSmall (i-unsigned y) (toBizNat n)
        (rewrite sym $ compareSubR (unsigned y) i in
         ylei)
        (leLtTrans (i - unsigned y) i (toBizNat n)
         (rewrite addComm i (-unsigned y) in
          rewrite addCompareMonoR (-unsigned y) 0 i in
          rewrite sym $ compareOpp 0 (unsigned y) in
          fst $ unsignedRange y)
         iltn)

-- TODO we actually can do with `y <= n` here
shruRolm : (x, y : BizMod2 n) -> y `ltu` iwordsize n = True -> shru x y = rolm x (iwordsize n - y) (shru (repr (-1) n) y)
shruRolm {n} x y yltun =
  sameBitsEq (shru x y) (rolm x (iwordsize n - y) (shru (repr (-1) n) y)) $ \i, zlei, iltn =>
  rewrite bitsAnd (x `rol` (iwordsize n - y)) (shru (repr (-1) n) y) i zlei iltn in
  rewrite bitsShru x y i zlei iltn in
  rewrite bitsShru (repr (-1) n) y i zlei iltn in
  rewrite bitsRol x (iwordsize n - y) i zlei iltn in
  let yltn = yltun
          |> ltbLtTo (unsigned y) (unsigned $ iwordsize n)
          |> replace {P=\z=>unsigned y `Lt` z} (unsignedReprWordsize n)
     in
  case ltLeTotal (i + unsigned y) (toBizNat n) of
    Left iyltn =>
      rewrite bitsMone n (i + unsigned y)
                (leTrans 0 i (i + unsigned y)
                  zlei
                  (rewrite addComm i (unsigned y) in
                   rewrite addCompareMonoR 0 (unsigned y) i in
                   fst $ unsignedRange y))
                iyltn
              in
      rewrite andTrue (testbit x ((i - (unsigned (iwordsize n - y))) `bizMod` (toBizNat n))) in
      rewrite unsignedReprWordsize n in
      rewrite unsignedRepr (toBizNat n - unsigned y) n
                (rewrite sym $ compareSubR (unsigned y) (toBizNat n) in
                 ltLeIncl (unsigned y) (toBizNat n) yltn)
                (leTrans (toBizNat n - unsigned y) (toBizNat n) (maxUnsigned n)
                  (rewrite addComm (toBizNat n) (-unsigned y) in
                   rewrite addCompareMonoR (-unsigned y) 0 (toBizNat n) in
                   rewrite sym $ compareOpp 0 (unsigned y) in
                   fst $ unsignedRange y)
                  (wordsizeMaxUnsigned n))
             in
      cong {f = testbit x} $
      snd $ divModPos (i - (toBizNat n - unsigned y)) (toBizNat n) (-1) (i + unsigned y)
        (leTrans 0 i (i + unsigned y)
          zlei
          (rewrite addComm i (unsigned y) in
           rewrite addCompareMonoR 0 (unsigned y) i in
           fst $ unsignedRange y))
        iyltn
        (rewrite sym $ oppEqMulM1L (toBizNat n) in
         rewrite oppAddDistr (toBizNat n) (-unsigned y) in
         rewrite oppInvolutive (unsigned y) in
         rewrite addAssoc i (-toBizNat n) (unsigned y) in
         rewrite addComm i (-toBizNat n) in
         sym $ addAssoc (-toBizNat n) i (unsigned y))
    Right nleiy =>
      rewrite bitsAbove x (i + unsigned y) nleiy in
      rewrite bitsAbove (repr (-1) n) (i + unsigned y) nleiy in
      sym $ andFalse (testbit x ((i - (unsigned (iwordsize n - y))) `bizMod` (toBizNat n)))

rolZero : (x : BizMod2 n) -> rol x 0 = x
rolZero {n} x =
  sameBitsEq (rol x 0) x $ \i, zlei, iltn =>
  rewrite bitsRol x 0 i zlei iltn in
  rewrite unsignedZero n in
  rewrite add0R i in
  cong {f = testbit x} $
  snd $ divModSmall i (toBizNat n) zlei iltn

bitwiseBinopRol : (f : BizMod2 n -> BizMod2 n -> BizMod2 n) -> (fb : Bool -> Bool -> Bool) -> (x, y, k : BizMod2 n)
               -> ((a, b : BizMod2 n) -> (j : Biz) -> 0 `Le` j -> j `Lt` toBizNat n -> testbit (f a b) j = fb (testbit a j) (testbit b j))
               -> f (rol x k) (rol y k) = rol (f x y) k
bitwiseBinopRol {n} f fb x y k ftest =
  case decEq n 0 of
    Yes n0 => rewrite bizMod2P0N (f (rol x k) (rol y k)) n0 in
              sym $ bizMod2P0N (rol (f x y) k) n0
    No nz =>
      sameBitsEq (f (rol x k) (rol y k)) (rol (f x y) k) $ \i, zlei, iltn =>
      rewrite ftest (rol x k) (rol y k) i zlei iltn in
      rewrite bitsRol (f x y) k i zlei iltn in
      rewrite bitsRol x k i zlei iltn in
      rewrite bitsRol y k i zlei iltn in
      let ikmnrange = modPosBound (i - unsigned k) (toBizNat n) $
                      leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) $
                      nz . toBizNatInj n 0
         in
      sym $ ftest x y ((i - unsigned k) `bizMod` toBizNat n)
        (fst ikmnrange)
        (snd ikmnrange)

andRol : (x, y, k : BizMod2 n) -> (rol x k) `and` (rol y k) = rol (x `and` y) k
andRol x y k = bitwiseBinopRol and (\a, b => a && b) x y k bitsAnd

orRol : (x, y, k : BizMod2 n) -> (rol x k) `or` (rol y k) = rol (x `or` y) k
orRol x y k = bitwiseBinopRol or (\a, b => a || b) x y k bitsOr

xorRol : (x, y, k : BizMod2 n) -> (rol x k) `xor` (rol y k) = rol (x `xor` y) k
xorRol x y k = bitwiseBinopRol xor xor x y k bitsXor

rolRol : (x, a, b : BizMod2 n) -> bizDivides (toBizNat n) (modulus n)
      -> rol (rol x a) b = rol x ((a+b) `modu` (iwordsize n))
rolRol {n} x a b ndiv2n =
  case decEq n 0 of
    Yes n0 => rewrite n0 in
              Refl
    No nz =>
      sameBitsEq (rol (rol x a) b) (rol x ((a+b) `modu` (iwordsize n))) $ \i, zlei, iltn =>
      rewrite bitsRol (rol x a) b i zlei iltn in
      rewrite bitsRol x ((a+b) `modu` (iwordsize n)) i zlei iltn in
      let znz = nz . toBizNatInj n 0
          zltn = leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) znz
          ibmnRange = modPosBound (i - unsigned b) (toBizNat n) zltn
         in
      rewrite bitsRol x a ((i - unsigned b) `bizMod` (toBizNat n)) (fst ibmnRange) (snd ibmnRange) in
      cong {f = testbit x} $
      eqmodModEq (((i - unsigned b) `bizMod` (toBizNat n)) - unsigned a)
                 (i - unsigned ((a+b) `modu` (iwordsize n)))
                 (toBizNat n) zltn $
      eqmodTrans (((i - unsigned b) `bizMod` (toBizNat n)) - unsigned a)
                 (i - unsigned b - unsigned a)
                 (i - unsigned ((a+b) `modu` (iwordsize n)))
                 (toBizNat n)
        (eqmodSub ((i - unsigned b) `bizMod` (toBizNat n)) (i - unsigned b)
                  (unsigned a) (unsigned a)
                  (toBizNat n)
           (eqmodSym (i - unsigned b) ((i - unsigned b) `bizMod` (toBizNat n)) (toBizNat n) $
            eqmodMod (i - unsigned b) (toBizNat n) znz)
           (eqmodRefl (unsigned a) (toBizNat n)))
        (rewrite sym $ addAssoc i (-unsigned b) (-unsigned a) in
         rewrite sym $ oppAddDistr (unsigned b) (unsigned a) in
         eqmodSub i i (unsigned b + unsigned a) (unsigned ((a+b) `modu` (iwordsize n))) (toBizNat n)
           (eqmodRefl i (toBizNat n))
           (eqmodTrans (unsigned b + unsigned a)
                       ((unsigned a + unsigned b) `bizMod` (toBizNat n))
                       (unsigned ((a+b) `modu` (iwordsize n)))
                       (toBizNat n)
              (rewrite addComm (unsigned b) (unsigned a) in
               eqmodMod (unsigned a + unsigned b) (toBizNat n) znz)
              (rewrite unsignedReprWordsize n in
               eqmodTrans ((unsigned a + unsigned b) `bizMod` (toBizNat n))
                          ((unsigned (repr (unsigned a + unsigned b) n)) `bizMod` (toBizNat n))
                          (unsigned (repr ((unsigned (repr (unsigned a + unsigned b) n)) `bizMod` (toBizNat n)) n))
                          (toBizNat n)
                 (eqmodRefl2 ((unsigned a + unsigned b) `bizMod` (toBizNat n))
                             ((unsigned (repr (unsigned a + unsigned b) n)) `bizMod` (toBizNat n))
                             (toBizNat n) $
                    eqmodModEq (unsigned a + unsigned b) (unsigned (repr (unsigned a + unsigned b) n)) (toBizNat n) zltn $
                    eqmodDivides (modulus n) (toBizNat n) (unsigned a + unsigned b) (unsigned (repr (unsigned a + unsigned b) n))
                      (eqmUnsignedRepr (unsigned a + unsigned b) n)
                      ndiv2n)
                 (eqmodDivides (modulus n) (toBizNat n)
                               ((unsigned (repr (unsigned a + unsigned b) n)) `bizMod` (toBizNat n))
                               (unsigned (repr ((unsigned (repr (unsigned a + unsigned b) n)) `bizMod` (toBizNat n)) n))
                      (eqmUnsignedRepr ((unsigned (repr (unsigned a + unsigned b) n)) `bizMod` (toBizNat n)) n)
                      ndiv2n))))

rolmZero : (x, m : BizMod2 n) -> rolm x 0 m = x `and` m
rolmZero x _ =
  rewrite rolZero x in
  Refl

rolmRolm : (x, a1, b1, a2, b2 : BizMod2 n) -> bizDivides (toBizNat n) (modulus n)
        -> rolm (rolm x a1 b1) a2 b2 = rolm x (modu (a1+a2) (iwordsize n)) ((rol b1 a2) `and` b2)
rolmRolm x a1 b1 a2 b2 ndiv2n =
  rewrite sym $ andRol (rol x a1) b1 a2 in
  rewrite andAssoc (rol (rol x a1) a2) (rol b1 a2) b2 in
  rewrite rolRol x a1 a2 ndiv2n in
  Refl

orRolm : (x, a, b1, b2 : BizMod2 n) -> (rolm x a b1) `or` (rolm x a b2) = rolm x a (b1 `or` b2)
orRolm x a b1 b2 = sym $ andOrDistrib (rol x a) b1 b2

-- TODO we actually can do with `y <= n` here
rorRol : (x, y : BizMod2 n) -> y `ltu` iwordsize n = True -> ror x y = rol x (iwordsize n - y)
rorRol {n} x y yltun =
  case decEq n 0 of
    Yes n0 => rewrite n0 in
              Refl
    No nz =>
      sameBitsEq (ror x y) (rol x (iwordsize n - y)) $ \i, zlei, iltn =>
      rewrite bitsRor x y i zlei iltn in
      rewrite bitsRol x (iwordsize n - y) i zlei iltn in
      rewrite unsignedReprWordsize n in
      let zltn = leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) (nz . toBizNatInj n 0)
          yltn = yltun
              |> ltbLtTo (unsigned y) (unsigned $ iwordsize n)
              |> replace {P=\z=>unsigned y `Lt` z} (unsignedReprWordsize n)
         in
      rewrite unsignedRepr (toBizNat n - unsigned y) n
                (rewrite sym $ compareSubR (unsigned y) (toBizNat n) in
                 ltLeIncl (unsigned y) (toBizNat n) yltn)
                (leTrans (toBizNat n - unsigned y) (toBizNat n) (maxUnsigned n)
                   (rewrite addComm (toBizNat n) (-unsigned y) in
                    rewrite addCompareMonoR (-unsigned y) 0 (toBizNat n) in
                    rewrite sym $ compareOpp 0 (unsigned y) in
                    fst $ unsignedRange y)
                   (wordsizeMaxUnsigned n))
             in
      cong {f = testbit x} $
      eqmodModEq (i + unsigned y) (i - (toBizNat n - unsigned y)) (toBizNat n) zltn $
      (1 **
         rewrite mul1L (toBizNat n) in
         rewrite oppAddDistr (toBizNat n) (-unsigned y) in
         rewrite oppInvolutive (unsigned y) in
         rewrite addAssoc (toBizNat n) i ((-toBizNat n) + unsigned y) in
         rewrite addComm (toBizNat n) i in
         rewrite sym $ addAssoc i (toBizNat n) ((-toBizNat n) + unsigned y) in
         rewrite addAssoc (toBizNat n) (-toBizNat n) (unsigned y) in
         rewrite addOppDiagR (toBizNat n) in
         Refl)

rorRolNeg : (x, y : BizMod2 n) -> bizDivides (toBizNat n) (modulus n) -> ror x y = rol x (-y)
rorRolNeg {n} x y ndiv2n =
  case decEq n 0 of
    Yes n0 => rewrite n0 in
              Refl
    No nz =>
      sameBitsEq (ror x y) (rol x (-y)) $ \i, zlei, iltn =>
      rewrite bitsRor x y i zlei iltn in
      rewrite bitsRol x (-y) i zlei iltn in
      cong {f = testbit x} $
      eqmodModEq (i + unsigned y) (i - (unsigned (repr (-unsigned y) n))) (toBizNat n)
                 (leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) (nz . toBizNatInj n 0)) $
        eqmodTrans (i + unsigned y)
                   (i - (-unsigned y))
                   (i - (unsigned (repr (-unsigned y) n)))
                   (toBizNat n)
          (eqmodRefl2 (i + unsigned y) (i - (-unsigned y)) (toBizNat n) $
           rewrite oppInvolutive (unsigned y) in
           Refl)
          (eqmodSub i i (-unsigned y) (unsigned (repr (-unsigned y) n)) (toBizNat n)
            (eqmodRefl i (toBizNat n))
            (eqmodDivides (modulus n) (toBizNat n) (-unsigned y) (unsigned (repr (-unsigned y) n))
               (eqmUnsignedRepr (-unsigned y) n)
               ndiv2n))

orRor : (x, y, z : BizMod2 n) -> y `ltu` iwordsize n = True -> z `ltu` iwordsize n = True -> y + z = iwordsize n
     -> ror x z = shl x y `or` shru x z
orRor {n} x y z yltun zltun yzn =
  let yltn = yltun
          |> ltbLtTo (unsigned y) (unsigned $ iwordsize n)
          |> replace {P=\q=>unsigned y `Lt` q} (unsignedReprWordsize n)
      zltn = zltun
          |> ltbLtTo (unsigned z) (unsigned $ iwordsize n)
          |> replace {P=\q=>unsigned z `Lt` q} (unsignedReprWordsize n)
      zleuz = fst $ unsignedRange z
      ynmz = trans
               (sym $ trans
                  (sym $ unsignedRepr (unsigned y + unsigned z) n
                    (addLeMono 0 (unsigned y) 0 (unsigned z) (fst $ unsignedRange y) zleuz)
                    (leTrans (unsigned y + unsigned z) (bizDMO (toBizNat n)) (maxUnsigned n)
                       (rewrite predDoubleSpec (toBizNat n) in
                        ltPredRTo (unsigned y + unsigned z) (2*(toBizNat n)) $
                        rewrite mulAddDistrR 1 1 (toBizNat n) in
                        rewrite mul1L (toBizNat n) in
                        addLtMono (unsigned y) (toBizNat n) (unsigned z) (toBizNat n) yltn zltn)
                       (twoWordsizeMaxUnsigned n)))
                  (trans (cong {f=unsigned} yzn) (unsignedReprWordsize n)))
               (addComm (unsigned y) (unsigned z))
          |> addTransferLZ (toBizNat n) (unsigned z) (unsigned y)
     in
  sameBitsEq (ror x z) (shl x y `or` shru x z) $ \i, zlei, iltn =>
  rewrite testbitRepr n ((bizShiftR (unsigned x) ((unsigned z) `bizMod` (toBizNat n))) `bizOr`
                         (bizShiftL (unsigned x) ((toBizNat n)-((unsigned z) `bizMod` (toBizNat n))))) i zlei iltn in
  rewrite testbitRepr n ((unsigned (repr (bizShiftL (unsigned x) (unsigned y)) n)) `bizOr`
                         (unsigned (repr (bizShiftR (unsigned x) (unsigned z)) n))) i zlei iltn in
  rewrite lorSpec (bizShiftR (unsigned x) ((unsigned z) `bizMod` (toBizNat n)))
                  (bizShiftL (unsigned x) ((toBizNat n)-((unsigned z) `bizMod` (toBizNat n)))) i in
  rewrite lorSpec (unsigned (repr (bizShiftL (unsigned x) (unsigned y)) n))
                  (unsigned (repr (bizShiftR (unsigned x) (unsigned z)) n)) i in
  rewrite testbitRepr n (bizShiftL (unsigned x) (unsigned y)) i zlei iltn in
  rewrite testbitRepr n (bizShiftR (unsigned x) (unsigned z)) i zlei iltn in
  rewrite orComm (bizTestBit (bizShiftL (unsigned x) (unsigned y)) i) (bizTestBit (bizShiftR (unsigned x) (unsigned z)) i) in
  cong2 {f = (||)}
    (sameBitsEqm n (bizShiftR (unsigned x) ((unsigned z) `bizMod` (toBizNat n)))
                   (bizShiftR (unsigned x) (unsigned z))
                   i
       (eqmodRefl2 (bizShiftR (unsigned x) ((unsigned z) `bizMod` (toBizNat n)))
                   (bizShiftR (unsigned x) (unsigned z))
                   (modulus n) $
        cong {f = bizShiftR (unsigned x)} $
        snd $ divModSmall (unsigned z) (toBizNat n) zleuz zltn)
       zlei iltn)
    (cong {f=Delay} $
     sameBitsEqm n (bizShiftL (unsigned x) ((toBizNat n)-((unsigned z) `bizMod` (toBizNat n))))
                   (bizShiftL (unsigned x) (unsigned y))
                   i
       (eqmodRefl2 (bizShiftL (unsigned x) ((toBizNat n)-((unsigned z) `bizMod` (toBizNat n))))
                   (bizShiftL (unsigned x) (unsigned y))
                   (modulus n) $
        rewrite snd $ divModSmall (unsigned z) (toBizNat n) zleuz zltn in
        cong {f = bizShiftL (unsigned x)} (sym ynmz))
       zlei iltn)
