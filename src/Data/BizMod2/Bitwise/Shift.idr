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

-- TODO the original has `if i + unsigned y < toBizNat n then testbit x (i + unsigned y) else False` here but this seems redundant?
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