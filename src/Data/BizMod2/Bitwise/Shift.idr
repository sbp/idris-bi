module Data.BizMod2.Bitwise.Shift

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
bitsShr {n=Z} x y i zlei iltn =
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

-- TODO requirements on y and z look far stronger than necessary, this seems to hold for y+z < 2^n
shlShl : (x, y, z : BizMod2 n)
      -> y `ltu` iwordsize n = True -> z `ltu` iwordsize n = True
      -> shl (shl x y) z = shl x (y+z)
shlShl {n} x y z yn zn =
  sameBitsEq (shl (shl x y) z) (shl x (y+z)) $ \i, zlei, iltn =>
  rewrite bitsShl (shl x y) z i zlei iltn in
  rewrite bitsShl x (y+z) i zlei iltn in
  rewrite ltuSum y z yn zn in
  aux2 i zlei iltn
  where
  auxCompare : (p, q : Biz) -> Either (Either (p `Lt` q) (p `Gt` q)) (bizCompare p q = EQ)
  auxCompare p q with (p `compare` q)
    | LT = Left $ Left Refl
    | EQ = Right Refl
    | GT = Left $ Right Refl
  aux2 : (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n
      -> (if i < unsigned z then False else testbit (shl x y) (i - unsigned z)) =
           (if i < unsigned y + unsigned z then False else testbit x (i - (unsigned y + unsigned z)))
  aux2 i zlei iltn with (i < unsigned z) proof iz
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
      case auxCompare (i - unsigned z) (unsigned y) of
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
