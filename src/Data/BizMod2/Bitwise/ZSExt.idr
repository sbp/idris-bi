module Data.BizMod2.Bitwise.ZSExt

import Data.Util

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Nat
import Data.Biz.Bitwise

import Data.BizMod2
import Data.BizMod2.Bitwise
import Data.BizMod2.Bitwise.Pow2

%access export
%default total

-- Properties of integer zero extension and sign extension.

bitsZeroExt : (m, i : Biz) -> (x : BizMod2 n) -> 0 `Le` i -> testbit (zeroExt m x) i = if i < m then testbit x i else False
bitsZeroExt {n} m i x zlei =
  case ltLeTotal i (toBizNat n) of
    Left iltn =>
      rewrite testbitRepr n (bizZeroExt m (unsigned x)) i zlei iltn in
      zZeroExtSpec m (unsigned x) i zlei
    Right nlei =>
      rewrite bitsAbove (zeroExt m x) i nlei in
      rewrite bitsAbove x i nlei in
      sym $ ifSame False (i<m)

bitsSignExt : (m, i : Biz) -> (x : BizMod2 n) -> 0 `Le` i -> i `Lt` toBizNat n -> 0 `Lt` m -> testbit (signExt m x) i = testbit x (if i < m then i else m - 1)
bitsSignExt {n} m i x zlei iltn zltm =
  rewrite testbitRepr n (bizSignExt m (unsigned x)) i zlei iltn in
  zSignExtSpec m (unsigned x) i zlei zltm

zeroExtAbove : (m : Biz) -> (x : BizMod2 n) -> toBizNat n `Le` m -> zeroExt m x = x
zeroExtAbove {n} m x nlem =
  sameBitsEq (zeroExt m x) x $ \i, zlei, iltn =>
  rewrite bitsZeroExt m i x zlei in
  rewrite ltbLtFro i m $
          ltLeTrans i (toBizNat n) m iltn nlem
         in
  Refl

signExtAbove : (m : Biz) -> (x : BizMod2 n) -> toBizNat n `Le` m -> signExt m x = x
signExtAbove {n} m x nlem =
  case decEq n 0 of
    Yes n0 =>
      rewrite bizMod2P0N x n0 in
      rewrite n0 in
      Refl
    No nnz =>
      sameBitsEq (signExt m x) x $ \i, zlei, iltn =>
      rewrite bitsSignExt m i x zlei iltn $
              ltLeTrans 0 (toBizNat n) m (leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) (nnz . toBizNatInj n 0)) nlem
             in
      rewrite ltbLtFro i m $
              ltLeTrans i (toBizNat n) m iltn nlem
             in
      Refl

zeroExtAnd : (m : Biz) -> (x : BizMod2 n) -> 0 `Le` m -> zeroExt m x = x `and` (repr (bizPow2 m - 1) n)
zeroExtAnd m x zlem =
  sameBitsEq (zeroExt m x) (x `and` (repr (bizPow2 m - 1) n)) $ \i, zlei, iltn =>
  rewrite bitsZeroExt m i x zlei in
  rewrite bitsAnd x (repr (bizPow2 m - 1) n) i zlei iltn in
  rewrite testbitRepr n (bizPow2 m - 1) i zlei iltn in
  rewrite zTestbitBizPow2M1 m i zlem zlei in
  case ltLeTotal i m of
    Left iltm =>
      rewrite ltbLtFro i m iltm in
      sym $ andTrue (testbit x i)
    Right mlei =>
      rewrite nltbLeFro m i mlei in
      sym $ andFalse (testbit x i)

zeroExtMod : (m : Biz) -> (x : BizMod2 n) -> 0 `Le` m -> m `Lt` toBizNat n -> unsigned (zeroExt m x) = (unsigned x) `bizMod` (bizPow2 m)
zeroExtMod m x zlem mltn =
  equalSameBits (unsigned (zeroExt m x)) ((unsigned x) `bizMod` (bizPow2 m)) $ \i, zlei =>
  rewrite zTestbitModBizPow2 m (unsigned x) i zlem zlei in
  bitsZeroExt m i x zlei

zeroExtWiden : (x : BizMod2 n) -> (m, m1 : Biz) -> m `Le` m1 -> zeroExt m1 (zeroExt m x) = zeroExt m x
zeroExtWiden x m m1 mlem1 =
  sameBitsEq (zeroExt m1 (zeroExt m x)) (zeroExt m x) $ \i, zlei, _ =>
  rewrite bitsZeroExt m1 i (zeroExt m x) zlei in
  rewrite bitsZeroExt m i x zlei in
  case ltLeTotal i m1 of
    Left iltm1 =>
      rewrite ltbLtFro i m1 iltm1 in
      Refl
    Right m1lei =>
      rewrite nltbLeFro m1 i m1lei in
      rewrite nltbLeFro m i (leTrans m m1 i mlem1 m1lei) in
      Refl

-- TODO the next 2 can probably be simplified to use `signExtAbove`

signExtWiden : (x : BizMod2 n) -> (m, m1 : Biz) -> 0 `Lt` m -> m `Le` m1 -> signExt m1 (signExt m x) = signExt m x
signExtWiden x m m1 zltm mlem1 =
  sameBitsEq (signExt m1 (signExt m x)) (signExt m x) $ \i, zlei, iltn =>
  let zltm1 = ltLeTrans 0 m m1 zltm mlem1 in
  rewrite bitsSignExt m1 i (signExt m x) zlei iltn zltm1 in
  rewrite bitsSignExt m i x zlei iltn zltm in
  case ltLeTotal i m1 of
    Left iltm1 =>
      rewrite ltbLtFro i m1 iltm1 in
      bitsSignExt m i x zlei iltn zltm
    Right m1lei =>
      rewrite nltbLeFro m1 i m1lei in
      rewrite bitsSignExt m (m1-1) x (ltPredRTo 0 m1 zltm1) (ltTrans (m1-1) i (toBizNat n) (ltPredLTo m1 i m1lei) iltn) zltm in
      rewrite nltbLeFro m i (leTrans m m1 i mlem1 m1lei) in
      case decEq m1 m of
        Yes m1m =>
          rewrite m1m in
          rewrite ltbLtFro (m-1) m (ltPred m) in
          Refl
        No m1neqm =>
          rewrite nltbLeFro m (m1-1) $
                  ltPredRTo m m1 $
                  leNeqLt m1 m mlem1 m1neqm
                 in
          Refl

signZeroExtWiden : (x : BizMod2 n) -> (m, m1 : Biz) -> 0 `Le` m -> m `Lt` m1 -> signExt m1 (zeroExt m x) = zeroExt m x
signZeroExtWiden x m m1 zlem mltm1 =
  sameBitsEq (signExt m1 (zeroExt m x)) (zeroExt m x) $ \i, zlei, iltn =>
  let zltm1 = leLtTrans 0 m m1 zlem mltm1 in
  rewrite bitsSignExt m1 i (zeroExt m x) zlei iltn zltm1 in
  rewrite bitsZeroExt m i x zlei in
  case ltLeTotal i m1 of
    Left iltm1 =>
      rewrite ltbLtFro i m1 iltm1 in
      bitsZeroExt m i x zlei
    Right m1lei =>
      rewrite nltbLeFro m1 i m1lei in
      rewrite bitsZeroExt m (m1-1) x (ltPredRTo 0 m1 zltm1) in
      rewrite nltbLeFro m i (ltLeIncl m i $ ltLeTrans m m1 i mltm1 m1lei) in
      rewrite nltbLeFro m (m1-1) (ltPredRTo m m1 mltm1) in
      Refl

zeroExtNarrow : (x : BizMod2 n) -> (m, m1 : Biz) -> m `Le` m1 -> zeroExt m (zeroExt m1 x) = zeroExt m x
zeroExtNarrow x m m1 mlem1 =
  sameBitsEq (zeroExt m (zeroExt m1 x)) (zeroExt m x) $ \i, zlei, iltn =>
  rewrite bitsZeroExt m i (zeroExt m1 x) zlei in
  rewrite bitsZeroExt m i x zlei in
  rewrite bitsZeroExt m1 i x zlei in
  case ltLeTotal i m of
    Left iltm =>
      rewrite ltbLtFro i m iltm in
      rewrite ltbLtFro i m1 (ltLeTrans i m m1 iltm mlem1) in
      Refl
    Right mlei =>
      rewrite nltbLeFro m i mlei in
      Refl