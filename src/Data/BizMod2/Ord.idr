module Data.BizMod2.Ord

import Data.Util

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Nat

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.AddSubMul

%access export
%default total

-- TODO merge with Core?

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

-- TODO move translate* to AddSubMul? if merged with Core there'll be a cyclic dependency due to addSigned in translateLt
translateEq : (x, y, d : BizMod2 n) -> x + d == y + d = x == y
translateEq {n} x y d =
  case trueOrFalse ((unsigned x)==(unsigned y)) of
    Left neq =>
      rewrite neq in
      neqbNeqFro (unsigned (x + d)) (unsigned (y + d)) $ \xdyd =>
      let (xmin, xmax) = unsignedRange x
          (ymin, ymax) = unsignedRange y
          uxuy = eqmodSmallEq (unsigned x) (unsigned y) (modulus n)
                 (rewrite sym $ add0R (unsigned x) in
                  rewrite sym $ add0R (unsigned y) in
                  rewrite sym $ addOppDiagR (unsigned d) in
                  rewrite addAssoc (unsigned x) (unsigned d) (-unsigned d) in
                  rewrite addAssoc (unsigned y) (unsigned d) (-unsigned d) in
                  eqmodSub (unsigned x+unsigned d) (unsigned y+unsigned d) (unsigned d) (unsigned d) (modulus n)
                     (eqmodTrans (unsigned x+unsigned d) (unsigned (repr (unsigned x+unsigned d) n)) (unsigned y+unsigned d) (modulus n)
                       (eqmUnsignedRepr (unsigned x+unsigned d) n)
                       (eqmodTrans (unsigned (repr (unsigned x+unsigned d) n)) (unsigned (repr (unsigned y+unsigned d) n)) (unsigned y+unsigned d) (modulus n)
                        (eqmodRefl2 (unsigned (repr (unsigned x+unsigned d) n)) (unsigned (repr (unsigned y+unsigned d) n)) (modulus n) xdyd)
                        (eqmUnsignedRepr' (unsigned y+unsigned d) n)))
                     (eqmodRefl (unsigned d) (modulus n)))
                 xmin xmax ymin ymax
         in
      neqbNeqTo (unsigned x) (unsigned y) neq $ uxuy
    Right eq =>
      rewrite eq in
      rewrite eqbEqTo (unsigned x) (unsigned y) eq in
      eqbEqFro (unsigned (y + d)) (unsigned (y + d)) Refl

translateLtu : (x, y, d : BizMod2 n) -> (unsigned x + unsigned d) `Le` maxUnsigned n -> (unsigned y + unsigned d) `Le` maxUnsigned n
            -> (x + d) `ltu` (y + d) = x `ltu` y
translateLtu {n} x y d xdlen ydlen =
  let zleud = fst $ unsignedRange d in
  rewrite unsignedRepr (unsigned x + unsigned d) n
            (addLeMono 0 (unsigned x) 0 (unsigned d) (fst $ unsignedRange x) zleud)
            xdlen
         in
  rewrite unsignedRepr (unsigned y + unsigned d) n
            (addLeMono 0 (unsigned y) 0 (unsigned d) (fst $ unsignedRange y) zleud)
            ydlen
         in
  case ltLeTotal (unsigned x) (unsigned y) of
    Left xlty =>
      rewrite ltbLtFro (unsigned x) (unsigned y) xlty in
      ltbLtFro (unsigned x + unsigned d) (unsigned y + unsigned d) $
      rewrite addCompareMonoR (unsigned x) (unsigned y) (unsigned d) in
      xlty
    Right ylex =>
      rewrite nltbLeFro (unsigned y) (unsigned x) ylex in
      nltbLeFro (unsigned y + unsigned d) (unsigned x + unsigned d) $
      rewrite addCompareMonoR (unsigned y) (unsigned x) (unsigned d) in
      ylex

translateCmpu : (c : Comparison) -> (x, y, d : BizMod2 n)
            -> (unsigned x + unsigned d) `Le` maxUnsigned n -> (unsigned y + unsigned d) `Le` maxUnsigned n
             -> cmpu c (x + d) (y + d) = cmpu c x y
translateCmpu Ceq x y d _     _     = translateEq x y d
translateCmpu Cne x y d _     _     = cong $ translateEq x y d
translateCmpu Clt x y d xdlen ydlen = translateLtu x y d xdlen ydlen
translateCmpu Cle x y d xdlen ydlen = cong $ translateLtu y x d ydlen xdlen
translateCmpu Cgt x y d xdlen ydlen = translateLtu y x d ydlen xdlen
translateCmpu Cge x y d xdlen ydlen = cong $ translateLtu x y d xdlen ydlen

translateLt : (x, y, d : BizMod2 n)
           -> minSigned n `Le` (signed x + signed d) -> (signed x + signed d) `Le` maxSigned n
           -> minSigned n `Le` (signed y + signed d) -> (signed y + signed d) `Le` maxSigned n
           -> (x+d) < (y+d) = x < y
translateLt {n} x y d minxd xdmax minyd ydmax =
  case decEq n 0 of
    Yes n0 =>
      rewrite bizMod2P0Signed x n0 in
      rewrite bizMod2P0Signed (x+d) n0 in
      rewrite bizMod2P0Signed y n0 in
      rewrite bizMod2P0Signed (y+d) n0 in
      Refl
    No nnz =>
      case ltLeTotal (signed x) (signed y) of
        Left xlty =>
          rewrite ltbLtFro x y xlty in
          ltbLtFro (x+d) (y+d) $
          rewrite addSigned x d in
          rewrite addSigned y d in
          rewrite signedRepr (signed x + signed d) n nnz minxd xdmax in
          rewrite signedRepr (signed y + signed d) n nnz minyd ydmax in
          rewrite addCompareMonoR (signed x) (signed y) (signed d) in
          xlty
        Right ylex =>
          rewrite nltbLeFro y x ylex in
          nltbLeFro (y+d) (x+d) $
          rewrite addSigned x d in
          rewrite addSigned y d in
          rewrite signedRepr (signed x + signed d) n nnz minxd xdmax in
          rewrite signedRepr (signed y + signed d) n nnz minyd ydmax in
          rewrite addCompareMonoR (signed y) (signed x) (signed d) in
          ylex

translateCmp : (c : Comparison) -> (x, y, d : BizMod2 n)
            -> minSigned n `Le` (signed x + signed d) -> (signed x + signed d) `Le` maxSigned n
            -> minSigned n `Le` (signed y + signed d) -> (signed y + signed d) `Le` maxSigned n
            -> cmp c (x + d) (y + d) = cmp c x y
translateCmp Ceq x y d _     _     _     _     = translateEq x y d
translateCmp Cne x y d _     _     _     _     = cong $ translateEq x y d
translateCmp Clt x y d minxd xdmax minyd ydmax = translateLt x y d minxd xdmax minyd ydmax
translateCmp Cle x y d minxd xdmax minyd ydmax = cong $ translateLt y x d minyd ydmax minxd xdmax
translateCmp Cgt x y d minxd xdmax minyd ydmax = translateLt y x d minyd ydmax minxd xdmax
translateCmp Cge x y d minxd xdmax minyd ydmax = cong $ translateLt x y d minxd xdmax minyd ydmax

-- when n=0, isFalse ~ () and isTrue ~ Void
notboolIsFalseIsTrue : (x : BizMod2 n) -> Not (n=0) -> isFalse x -> isTrue (notbool x)
notboolIsFalseIsTrue {n} _ nnz fx =
  rewrite fx in
  rewrite unsignedZero n in
  oneNotZero n nnz

notboolIsTrueIsFalse : (x : BizMod2 n) -> isTrue x -> isFalse (notbool x)
notboolIsTrueIsFalse {n} x tx =
  rewrite eqFalse x (repr 0 n) tx in
  Refl

ltuRangeTest : (x, y : BizMod2 n) -> x `ltu` y = True -> unsigned y `Le` maxSigned n -> (0 `Le` signed x, signed x `Lt` unsigned y)
ltuRangeTest {n} x y xltuy uylems =
  let uxltuy = ltuInv x y xltuy
      uxltms = ltLeIncl (unsigned x) (maxSigned n) $
               ltLeTrans (unsigned x) (unsigned y) (maxSigned n) uxltuy uylems
     in
  ( signedPositiveFro x uxltms
  , rewrite signedEqUnsigned x uxltms in
    uxltuy
  )