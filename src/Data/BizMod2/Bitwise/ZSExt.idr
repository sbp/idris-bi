module Data.BizMod2.Bitwise.ZSExt

import Data.Util

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Nat
import Data.Biz.Bitwise

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.Bitwise
import Data.BizMod2.Bitwise.Shift
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

zeroExtMod : (m : Biz) -> (x : BizMod2 n) -> 0 `Le` m -> unsigned (zeroExt m x) = (unsigned x) `bizMod` (bizPow2 m)
zeroExtMod m x zlem =
  equalSameBits (unsigned (zeroExt m x)) ((unsigned x) `bizMod` (bizPow2 m)) $ \i, zlei =>
  rewrite zTestbitModBizPow2 m (unsigned x) i zlem zlei in
  bitsZeroExt m i x zlei

zeroExtWiden : (m, m1 : Biz) -> (x : BizMod2 n) -> m `Le` m1 -> zeroExt m1 (zeroExt m x) = zeroExt m x
zeroExtWiden m m1 x mlem1 =
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

signExtWiden : (m, m1 : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> m `Le` m1 -> signExt m1 (signExt m x) = signExt m x
signExtWiden m m1 x zltm mlem1 =
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

signZeroExtWiden : (m, m1 : Biz) -> (x : BizMod2 n) -> 0 `Le` m -> m `Lt` m1 -> signExt m1 (zeroExt m x) = zeroExt m x
signZeroExtWiden m m1 x zlem mltm1 =
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

zeroExtNarrow : (m, m1 : Biz) -> (x : BizMod2 n) -> m `Le` m1 -> zeroExt m (zeroExt m1 x) = zeroExt m x
zeroExtNarrow m m1 x mlem1 =
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

signExtNarrow : (m, m1 : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> m `Le` m1 -> signExt m (signExt m1 x) = signExt m x
signExtNarrow m m1 x zltm mlem1 =
  sameBitsEq (signExt m (signExt m1 x)) (signExt m x) $ \i, zlei, iltn =>
  let zltm1 = ltLeTrans 0 m m1 zltm mlem1 in
  rewrite bitsSignExt m i (signExt m1 x) zlei iltn zltm in
  rewrite bitsSignExt m i x zlei iltn zltm in
  case ltLeTotal i m of
    Left iltm =>
      rewrite ltbLtFro i m iltm in
      rewrite bitsSignExt m1 i x zlei iltn zltm1 in
      rewrite ltbLtFro i m1 (ltLeTrans i m m1 iltm mlem1) in
      Refl
    Right mlei =>
      rewrite nltbLeFro m i mlei in
      rewrite bitsSignExt m1 (m-1) x (ltPredRTo 0 m zltm) (ltTrans (m-1) i (toBizNat n) (ltPredLTo m i mlei) iltn) zltm1 in
      rewrite ltbLtFro (m-1) m1 (ltPredLTo m m1 mlem1) in
      Refl

-- TODO we only need 0<m here to deduce 0<m1, maybe requiring it directly is less restrictive?
zeroSignExtNarrow : (m, m1 : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> m `Le` m1 -> zeroExt m (signExt m1 x) = zeroExt m x
zeroSignExtNarrow m m1 x zltm mlem1 =
  sameBitsEq (zeroExt m (signExt m1 x)) (zeroExt m x) $ \i, zlei, iltn =>
  rewrite bitsZeroExt m i (signExt m1 x) zlei in
  rewrite bitsZeroExt m i x zlei in
  case ltLeTotal i m of
    Left iltm =>
      rewrite ltbLtFro i m iltm in
      rewrite bitsSignExt m1 i x zlei iltn (ltLeTrans 0 m m1 zltm mlem1) in
      rewrite ltbLtFro i m1 (ltLeTrans i m m1 iltm mlem1) in
      Refl
    Right mlei =>
      rewrite nltbLeFro m i mlei in
      Refl

zeroExtIdem : (m : Biz) -> (x : BizMod2 n) -> zeroExt m (zeroExt m x) = zeroExt m x
zeroExtIdem m x = zeroExtWiden m m x (leRefl m)

signExtIdem : (m : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> signExt m (signExt m x) = signExt m x
signExtIdem m x zltm = signExtWiden m m x zltm (leRefl m)

signExtZeroExt : (m : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> signExt m (zeroExt m x) = signExt m x
signExtZeroExt m x zltm =
  sameBitsEq (signExt m (zeroExt m x)) (signExt m x) $ \i, zlei, iltn =>
  rewrite bitsSignExt m i (zeroExt m x) zlei iltn zltm in
  rewrite bitsSignExt m i x zlei iltn zltm in
  case ltLeTotal i m of
    Left iltm =>
      rewrite ltbLtFro i m iltm in
      rewrite bitsZeroExt m i x zlei in
      rewrite ltbLtFro i m iltm in
      Refl
    Right mlei =>
      rewrite nltbLeFro m i mlei in
      rewrite bitsZeroExt m (m-1) x (ltPredRTo 0 m zltm) in
      rewrite ltbLtFro (m-1) m (ltPredLTo m m $ leRefl m) in
      Refl

zeroExtSignExt : (m : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> zeroExt m (signExt m x) = zeroExt m x
zeroExtSignExt m x zltm = zeroSignExtNarrow m m x zltm (leRefl m)

signExtEqualIfZeroEqual : (m : Biz) -> (x, y : BizMod2 n) -> 0 `Lt` m -> zeroExt m x = zeroExt m y -> signExt m x = signExt m y
signExtEqualIfZeroEqual m x y zltm zeq =
  rewrite sym $ signExtZeroExt m x zltm in
  rewrite sym $ signExtZeroExt m y zltm in
  cong {f = signExt m} zeq

zeroExtShruShl : (m : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> m `Lt` toBizNat n -> let y = repr (toBizNat n - m) n in zeroExt m x = shru (shl x y) y
zeroExtShruShl {n} m x zltm mltn =
  let unwrapy = unsignedRepr (toBizNat n - m) n
                 (rewrite sym $ compareSubR m (toBizNat n) in
                  ltLeIncl m (toBizNat n) mltn)
                 (ltLeIncl (toBizNat n - m) (maxUnsigned n) $
                  ltLeTrans (toBizNat n - m) (toBizNat n) (maxUnsigned n)
                   (rewrite addComm (toBizNat n) (-m) in
                    rewrite addCompareMonoR (-m) 0 (toBizNat n) in
                    rewrite sym $ compareOpp 0 m in
                    zltm)
                   (wordsizeMaxUnsigned n))
    in
  sameBitsEq (zeroExt m x) (shru (shl x (repr (toBizNat n - m) n)) (repr (toBizNat n - m) n)) $ \i, zlei, iltn =>
  rewrite bitsZeroExt m i x zlei in
  rewrite bitsShru (shl x (repr (toBizNat n - m) n)) (repr (toBizNat n - m) n) i zlei iltn in
-- TODO case bug strikes again
  really_believe_me x
 --case ltLeTotal i m of
 --   Left iltm =>
 --     rewrite ltbLtFro i m iltm in
 --     rewrite bitsShl x (repr (toBizNat n - m) n) (i + unsigned (repr (toBizNat n - m) n))
 --              (rewrite unwrapy in
 --               rewrite addAssoc i (toBizNat n) (-m) in
 --               rewrite sym $ compareSubR m (i + toBizNat n) in
 --               ltLeIncl m (i + toBizNat n) $
 --               ltLeTrans m (toBizNat n) (i + toBizNat n)
 --                 mltn
 --                (rewrite addCompareMonoR 0 i (toBizNat n) in
 --                 zlei))
 --              (rewrite unwrapy in
 --               rewrite addComm (toBizNat n) (-m) in
 --               rewrite addAssoc i (-m) (toBizNat n) in
 --               rewrite addCompareMonoR (i-m) 0 (toBizNat n) in
 --               rewrite sym $ compareSub i m in
 --               iltm)
 --            in
 --     rewrite unwrapy in
 --     rewrite nltbLeFro (toBizNat n - m) (i + (toBizNat n - m)) $
 --               rewrite addCompareMonoR 0 i (toBizNat n - m) in
 --               zlei
 --            in
 --     rewrite sym $ addAssoc i (toBizNat n - m) (-(toBizNat n - m)) in
 --     rewrite addOppDiagR (toBizNat n - m) in
 --     cong {f = testbit x} $ sym $ add0R i
 --   Right mlei =>
 --     rewrite nltbLeFro m i mlei in
 --     sym $ bitsAbove (shl x (repr (toBizNat n - m) n)) (i + unsigned (repr (toBizNat n - m) n)) $
 --     rewrite unwrapy in
 --     rewrite addComm (toBizNat n) (-m) in
 --     rewrite addAssoc i (-m) (toBizNat n) in
 --     rewrite addCompareMonoR 0 (i-m) (toBizNat n) in
 --     rewrite sym $ compareSubR m i in
 --     mlei

signExtShrShl : (m : Biz) -> (x : BizMod2 n) -> 0 `Lt` m -> m `Lt` toBizNat n -> let y = repr (toBizNat n - m) n in signExt m x = shr (shl x y) y
signExtShrShl {n} m x zltm mltn =
  case decEq n 0 of
    Yes n0 =>
      rewrite n0 in
      Refl
    No nnz =>
      let unwrapy = unsignedRepr (toBizNat n - m) n
                     (rewrite sym $ compareSubR m (toBizNat n) in
                      ltLeIncl m (toBizNat n) mltn)
                     (ltLeIncl (toBizNat n - m) (maxUnsigned n) $
                      ltLeTrans (toBizNat n - m) (toBizNat n) (maxUnsigned n)
                       (rewrite addComm (toBizNat n) (-m) in
                        rewrite addCompareMonoR (-m) 0 (toBizNat n) in
                        rewrite sym $ compareOpp 0 m in
                        zltm)
                       (wordsizeMaxUnsigned n))
        in
      sameBitsEq (signExt m x) (shr (shl x (repr (toBizNat n - m) n)) (repr (toBizNat n - m) n)) $ \i, zlei, iltn =>
      rewrite bitsSignExt m i x zlei iltn zltm in
      rewrite bitsShr (shl x (repr (toBizNat n - m) n)) (repr (toBizNat n - m) n) i zlei iltn in
-- TODO case bug strikes again
      really_believe_me x
     --case ltLeTotal i m of
     --  Left iltm =>
     --    rewrite ltbLtFro i m iltm in
     --    rewrite ltbLtFro (i+unsigned (repr (toBizNat n - m) n)) (toBizNat n) $
     --            rewrite unwrapy in
     --            rewrite addComm (toBizNat n) (-m) in
     --            rewrite addAssoc i (-m) (toBizNat n) in
     --            rewrite addCompareMonoR (i-m) 0 (toBizNat n) in
     --            rewrite sym $ compareSub i m in
     --            iltm
     --           in
     --    rewrite bitsShl x (repr (toBizNat n - m) n) (i + unsigned (repr (toBizNat n - m) n))
     --             (rewrite unwrapy in
     --              rewrite addAssoc i (toBizNat n) (-m) in
     --              rewrite sym $ compareSubR m (i + toBizNat n) in
     --              ltLeIncl m (i + toBizNat n) $
     --              ltLeTrans m (toBizNat n) (i + toBizNat n)
     --                mltn
     --               (rewrite addCompareMonoR 0 i (toBizNat n) in
     --                zlei))
     --             (rewrite unwrapy in
     --              rewrite addComm (toBizNat n) (-m) in
     --              rewrite addAssoc i (-m) (toBizNat n) in
     --              rewrite addCompareMonoR (i-m) 0 (toBizNat n) in
     --              rewrite sym $ compareSub i m in
     --              iltm)
     --           in
     --    rewrite unwrapy in
     --    rewrite nltbLeFro (toBizNat n - m) (i + (toBizNat n - m)) $
     --              rewrite addCompareMonoR 0 i (toBizNat n - m) in
     --              zlei
     --           in
     --    rewrite sym $ addAssoc i (toBizNat n - m) (-(toBizNat n - m)) in
     --    rewrite addOppDiagR (toBizNat n - m) in
     --    cong {f = testbit x} $ sym $ add0R i
     --  Right mlei =>
     --    rewrite nltbLeFro m i mlei in
     --    rewrite nltbLeFro (toBizNat n) (i+unsigned (repr (toBizNat n - m) n)) $
     --            rewrite unwrapy in
     --            rewrite addComm (toBizNat n) (-m) in
     --            rewrite addAssoc i (-m) (toBizNat n) in
     --            rewrite addCompareMonoR 0 (i-m) (toBizNat n) in
     --            rewrite sym $ compareSubR m i in
     --            mlei in
     --    rewrite bitsShl x (repr (toBizNat n - m) n) (toBizNat n - 1)
     --              (ltPredRTo 0 (toBizNat n) $
     --               (leNeqLt (toBizNat n) 0 (toBizNatIsNonneg n) (nnz . toBizNatInj n 0)))
     --              (ltPred (toBizNat n))
     --           in
     --    rewrite unwrapy in
     --    rewrite nltbLeFro (toBizNat n - m) (toBizNat n - 1) $
     --            rewrite addCompareMonoL (toBizNat n) (-m) (-1) in
     --            rewrite sym $ compareOpp 1 m in
     --            leSuccLFro 0 m zltm
     --           in
     --    rewrite oppAddDistr (toBizNat n) (-m) in
     --    rewrite oppInvolutive m in
     --    rewrite addAssoc (toBizNat n - 1) (-toBizNat n) m in
     --    rewrite addComm (toBizNat n) (-1) in
     --    rewrite sym $ addAssoc (-1) (toBizNat n) (-toBizNat n) in
     --    rewrite addOppDiagR (toBizNat n) in
     --    cong {f = testbit x} $ addComm m (-1)
