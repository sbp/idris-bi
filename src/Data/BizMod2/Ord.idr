module Data.BizMod2.Ord

import Data.Util

import Data.Biz
import Data.Biz.Ord
import Data.Biz.Nat

import Data.BizMod2
import Data.BizMod2.Core

%access export
%default total

ltbLtFro : (x, y : BizMod2 n) -> (signed x) `Lt` (signed y) -> x < y = True
ltbLtFro _ _ sxltsy = rewrite sxltsy in
                      Refl

nltbLeTo : (x, y : BizMod2 n) -> y < x = False -> (signed x) `Le` (signed y)
nltbLeTo x y prf xy with (y `compare` x) proof yx
  | LT = absurd prf
  | EQ = absurd $ trans yx (gtLt (signed x) (signed y) xy)
  | GT = absurd $ trans yx (gtLt (signed x) (signed y) xy)

nltbLeFro : (x, y : BizMod2 n) -> (signed x) `Le` (signed y) -> y < x = False
nltbLeFro x y sxlesy with (y `compare` x) proof yx
  | LT = absurd $ sxlesy $ ltGt (signed y) (signed x) (sym yx)
  | EQ = Refl
  | GT = Refl

reprLtu : (p : Biz) -> (n : Nat) -> 0 `Le` p -> p `Lt` toBizNat n -> (repr p n) `ltu` iwordsize n = True
reprLtu p n zlep pltn =
  rewrite unsignedRepr p n zlep $
          ltLeIncl p (maxUnsigned n) $
          ltLeTrans p (toBizNat n) (maxUnsigned n) pltn (wordsizeMaxUnsigned n)
         in
  rewrite unsignedReprWordsize n in
  ltbLtFro p (toBizNat n) pltn

-- `0 <= unsigned x` is just unsignedRange
ltuInv : (x, y : BizMod2 n) -> x `ltu` y = True -> unsigned x `Lt` unsigned y
ltuInv x y = ltbLtTo (unsigned x) (unsigned y)

ltuIwordsizeInv : (x : BizMod2 n) -> x `ltu` iwordsize n = True -> unsigned x `Lt` toBizNat n
ltuIwordsizeInv {n} x prf =
  rewrite sym $ unsignedReprWordsize n in
  ltuInv x (iwordsize n) prf

ltuInvPredNZ : (y : BizMod2 n) -> y `ltu` (repr (toBizNat n - 1) n) = True -> Not (n=0) -> unsigned y `Lt` toBizNat n - 1
ltuInvPredNZ {n} y yltun nz =
  rewrite sym $ unsignedRepr (toBizNat n - 1) n
                (case leLtOrEq 0 (toBizNat n) $ toBizNatIsNonneg n of   -- TODO use leNeqLt
                   Right n0 => absurd $ nz $ toBizNatInj n 0 $ sym n0
                   Left zltn => ltPredRTo 0 (toBizNat n) zltn)
                (leTrans (toBizNat n - 1) (toBizNat n) (maxUnsigned n)
                   (ltLeIncl (toBizNat n - 1) (toBizNat n) $ ltPred (toBizNat n))
                   (wordsizeMaxUnsigned n))
              in
  ltuInv y (repr (toBizNat n - 1) n) yltun

-- Properties of comparisons

negateCmp : (c : Comparison) -> (x, y : BizMod2 n) -> cmp (negateComparison c) x y = not (cmp c x y)
negateCmp Ceq _ _ = Refl
negateCmp Cne x y = sym $ notNot (x == y)
negateCmp Clt _ _ = Refl
negateCmp Cle x y = sym $ notNot (y < x)
negateCmp Cgt _ _ = Refl
negateCmp Cge x y = sym $ notNot (x < y)

negateCmpu : (c : Comparison) -> (x, y : BizMod2 n) -> cmpu (negateComparison c) x y = not (cmpu c x y)
negateCmpu Ceq _ _ = Refl
negateCmpu Cne x y = sym $ notNot (x == y)
negateCmpu Clt _ _ = Refl
negateCmpu Cle x y = sym $ notNot (y `ltu` x)
negateCmpu Cgt _ _ = Refl
negateCmpu Cge x y = sym $ notNot (x `ltu` y)

swapCmp : (c : Comparison) -> (x, y : BizMod2 n) -> cmp (swapComparison c) x y = cmp c y x
swapCmp Ceq x y = eqSym (unsigned x) (unsigned y)
swapCmp Cne x y = cong $ eqSym (unsigned x) (unsigned y)
swapCmp Clt _ _ = Refl
swapCmp Cle _ _ = Refl
swapCmp Cgt _ _ = Refl
swapCmp Cge _ _ = Refl

swapCmpu : (c : Comparison) -> (x, y : BizMod2 n) -> cmpu (swapComparison c) x y = cmpu c y x
swapCmpu Ceq x y = eqSym (unsigned x) (unsigned y)
swapCmpu Cne x y = cong $ eqSym (unsigned x) (unsigned y)
swapCmpu Clt _ _ = Refl
swapCmpu Cle _ _ = Refl
swapCmpu Cgt _ _ = Refl
swapCmpu Cge _ _ = Refl