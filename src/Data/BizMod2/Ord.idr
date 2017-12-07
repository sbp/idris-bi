module Data.BizMod2.Ord

import Data.So

import Data.Util

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Nat
import Data.Biz.DivMod

import Data.BizMod2
import Data.BizMod2.Core
import Data.BizMod2.AddSubMul
import Data.BizMod2.Bitwise

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

notLt : (x, y : BizMod2 n) -> not (y < x) = (x <= y)
notLt x y =
  rewrite eqSigned x y in
  case ltLeTotal (signed y) (signed x) of
    Left syltsx =>
      rewrite ltbLtFro y x syltsx in
      rewrite nltbLeFro y x $
              ltLeIncl (signed y) (signed x) syltsx in
      sym $ neqbNeqFro (signed x) (signed y) $
      ltNotEq (signed x) (signed y) syltsx
    Right sxlesy =>
      rewrite nltbLeFro x y sxlesy in
      case leLtOrEq (signed x) (signed y) sxlesy of
        Left sxltsy =>
          rewrite ltbLtFro x y sxltsy in
          Refl
        Right sxeqsy =>
          rewrite eqbEqFro (signed x) (signed y) sxeqsy in
          sym $ orbTrue (x<y)

ltNot : (x, y : BizMod2 n) -> y < x = not (x < y) && not (x == y)
ltNot x y =
  rewrite sym $ notOr (x < y) (x == y) in
  rewrite sym $ notLt x y in
  sym $ notNot (y<x)

notLtu : (x, y : BizMod2 n) -> not (y `ltu` x) = ((x `ltu` y) || (x == y))
notLtu x y =
  case ltLeTotal (unsigned y) (unsigned x) of
    Left uyltux =>
      rewrite ltbLtFro (unsigned y) (unsigned x) uyltux in
      rewrite nltbLeFro (unsigned y) (unsigned x) $
              ltLeIncl (unsigned y) (unsigned x) uyltux in
      sym $ neqbNeqFro (unsigned x) (unsigned y) $
      ltNotEq (unsigned x) (unsigned y) uyltux
    Right uxleuy =>
      rewrite nltbLeFro (unsigned x) (unsigned y) uxleuy in
      case leLtOrEq (unsigned x) (unsigned y) uxleuy of
        Left uxltuy =>
          rewrite ltbLtFro (unsigned x) (unsigned y) uxltuy in
          Refl
        Right uxequy =>
          rewrite eqbEqFro (unsigned x) (unsigned y) uxequy in
          sym $ orbTrue (x `ltu` y)

ltuNot : (x, y : BizMod2 n) -> y `ltu` x = not (x `ltu` y) && not (x == y)
ltuNot x y =
  rewrite sym $ notOr (x `ltu` y) (x == y) in
  rewrite sym $ notLtu x y in
  sym $ notNot (y `ltu` x)

-- TODO move to Bitwise?
ltSubOverflow : (x, y : BizMod2 n) -> (subOverflow x y 0) `xor` (negative (x-y)) = if x<y then 1 else 0
ltSubOverflow {n} x y =
  case decEq n 0 of
    Yes n0 =>
      rewrite bizMod2P0Signed x n0 in
      rewrite bizMod2P0Signed y n0 in
      rewrite n0 in
      Refl
    No nnz =>
      let (minx, maxx) = signedRange x nnz
          (miny, maxy) = signedRange y nnz
          zlexypm = addLeMono (minSigned n) (signed x) (minSigned n + 1) (-signed y)
                      minx
                      (rewrite sym $ oppAddDistr (halfModulus n) (-1) in
                       rewrite sym $ compareOpp (signed y) (maxSigned n) in
                       maxy)
                 |> replace {P=\q=>q `Le` signed x - signed y} (addAssoc (minSigned n) (minSigned n) 1)
                 |> replace {P=\q=>q+1 `Le` signed x - signed y} (sym $ oppAddDistr (halfModulus n) (halfModulus n))
                 |> replace {P=\q=>-(q+q)+1 `Le` signed x - signed y} (sym $ mul1L (halfModulus n))
                 |> replace {P=\q=>-q+1 `Le` signed x - signed y} (sym $ mulAddDistrR 1 1 (halfModulus n))
                 |> replace {P=\q=>Not (q = GT)} (sym $ addCompareTransferL 1 (2*(halfModulus n)) (signed x - signed y))
                 |> replace {P=\q=>1 `Le` q + (signed x - signed y)} (sym $ halfModulusModulus n nnz)
                 |> replace {P=\q=>1 `Le` q} (addComm (modulus n) (signed x - signed y))
                 |> ltLeTrans 0 1 (signed x - signed y + modulus n) Refl
                 |> ltLeIncl 0 (signed x - signed y + modulus n)
          xyltm = addLeMono (signed x) (maxSigned n) (-signed y) (halfModulus n)
                    maxx
                    (rewrite compareOpp (-signed y) (halfModulus n) in
                     rewrite oppInvolutive (signed y) in
                     miny)
               |> replace {P=\q=>signed x - signed y `Le` q} (addComm (maxSigned n) (halfModulus n))
               |> replace {P=\q=>signed x - signed y `Le` q} (addAssoc (halfModulus n) (halfModulus n) (-1))
               |> replace {P=\q=>signed x - signed y `Le` (q+q)-1} (sym $ mul1L (halfModulus n))
               |> replace {P=\q=>signed x - signed y `Le` q-1} (sym $ mulAddDistrR 1 1 (halfModulus n))
               |> replace {P=\q=>signed x - signed y `Le` q-1} (sym $ halfModulusModulus n nnz)
               |> ltPredRFro (signed x - signed y) (modulus n)
         in
      rewrite subSigned x y in
      rewrite aux nnz in
      case ltLeTotal (signed x - signed y) (signed {n} 0) of
        Left xylts0 =>
          let xylt0 = replace {P=\z=>signed x - signed y `Lt` z} (signedZero n nnz) xylts0 in
          rewrite ltbLtFro x y $
                  rewrite compareSub (signed x) (signed y) in
                  xylt0
                 in
          let xyltmax = ltLeTrans (signed x - signed y) 0 (maxSigned n)
                          xylt0
                          (ltPredRTo 0 (halfModulus n) $
                           halfModulusPos n nnz)
             in
          rewrite ltbLtFro (signed x - signed y) (maxSigned n) xyltmax in
          rewrite andTrue (minSigned n <= (signed x - signed y)) in
          case ltLeTotal (signed x - signed y) (minSigned n) of
            Left xyltmin =>
              rewrite nlebLtFro (signed x - signed y) (minSigned n) xyltmin in
              rewrite nltbLeFro (repr 0 n) (repr (signed x - signed y) n) $
                      rewrite signedZero n nnz in
                      rewrite signedReprEq (signed x - signed y) n in
                      rewrite sym $ snd $ divModPos (signed x - signed y) (modulus n) (-1) (signed x - signed y + modulus n)
                                zlexypm
                                (rewrite addCompareMonoR (signed x - signed y) 0 (modulus n) in
                                 xylt0)
                                (rewrite addComm (-modulus n) (signed x - signed y + modulus n) in
                                 rewrite sym $ addAssoc (signed x - signed y) (modulus n) (-modulus n) in
                                 rewrite addOppDiagR (modulus n) in
                                 sym $ add0R (signed x - signed y))
                             in
                      rewrite ltbLtFro (signed x - signed y + modulus n) (halfModulus n) $
                              ltLeTrans (signed x - signed y + modulus n) (minSigned n + modulus n) (halfModulus n)
                                (rewrite addCompareMonoR (signed x - signed y) (minSigned n) (modulus n) in
                                 xyltmin)
                                (rewrite sym $ addCompareTransferL (modulus n) (halfModulus n) (halfModulus n) in
                                 rewrite sym $ mul1L (halfModulus n) in
                                 rewrite sym $ mulAddDistrR 1 1 (halfModulus n) in
                                 rewrite sym $ halfModulusModulus n nnz in
                                 leRefl (modulus n))
                             in
                      zlexypm
                     in
              xorZero 1
            Right minlexy =>
              rewrite lebLeFro (minSigned n) (signed x - signed y) minlexy in
              rewrite ltbLtFro (repr (signed x - signed y) n) 0 $
                      rewrite signedRepr (signed x - signed y) n nnz
                                minlexy
                                (ltLeIncl (signed x - signed y) (maxSigned n) xyltmax)
                             in
                      xylts0
                     in
              xorZeroL 1
        Right szlexy =>
          let zlexy = replace {P=\z=>z `Le` signed x - signed y} (signedZero n nnz) szlexy in
          rewrite nltbLeFro y x $
                  rewrite compareSubR (signed y) (signed x) in
                  zlexy
                 in
          let minltxy = ltLeTrans (minSigned n) 0 (signed x - signed y)
                          (rewrite sym $ compareOpp 0 (halfModulus n) in
                           halfModulusPos n nnz)
                          zlexy
             in
          rewrite ltbLtFro (minSigned n) (signed x - signed y) minltxy in
          case ltLeTotal (maxSigned n) (signed x - signed y) of
            Left maxltxy =>
              rewrite nlebLtFro (maxSigned n) (signed x - signed y) maxltxy in
              rewrite ltbLtFro (repr (signed x - signed y) n) (repr 0 n) $
                      rewrite signedZero n nnz in
                      rewrite signedReprEq (signed x - signed y) n in
                      rewrite snd $ divModSmall (signed x - signed y) (modulus n) zlexy xyltm in
                      rewrite nltbLeFro (halfModulus n) (signed x - signed y) $
                              ltPredLFro (halfModulus n) (signed x - signed y) maxltxy
                             in
                      rewrite addComm (signed x - signed y) (-modulus n) in
                      rewrite sym $ addCompareTransferL (signed x - signed y) (modulus n) 0 in
                      xyltm
                     in
              xorIdem 1
            Right xylemax =>
              rewrite lebLeFro (signed x - signed y) (maxSigned n) xylemax in
              rewrite nltbLeFro 0 (repr (signed x - signed y) n) $
                      rewrite signedRepr (signed x - signed y) n nnz
                               (ltLeIncl (minSigned n) (signed x - signed y) minltxy)
                                xylemax
                             in
                      szlexy
                     in
              xorIdem 0
  where
  aux : Not (n=0) -> signed x - signed y - signed (repr 0 n) = signed x - signed y
  aux nnz = rewrite signedZero n nnz in
            sub0R (signed x - signed y)

-- Non-overlapping test

noOverlap : (ofs1, ofs2 : BizMod2 n) -> (sz1, sz2 : Biz) -> Bool
noOverlap {n} ofs1 ofs2 sz1 sz2 =
  let x1 = unsigned ofs1
      x2 = unsigned ofs2
     in
  (x1 + sz1 <= modulus n) && ((x2 + sz2 <= modulus n) && ((x1 + sz1 <= x2) || (x2 + sz2 <= x1)))

noOverlapSound : (ofs1, ofs2, base : BizMod2 n) -> (sz1, sz2 : Biz) -> noOverlap ofs1 ofs2 sz1 sz2 = True
             -> Either (unsigned (base + ofs1) + sz1 `Le` unsigned (base + ofs2)) (unsigned (base + ofs2) + sz2 `Le` unsigned (base + ofs1))
noOverlapSound {n} ofs1 ofs2 base sz1 sz2 noov =
  let (p1, p2p3) = soAndSo $ eqToSo noov
      (p2, ep3) = soAndSo p2p3
      p3 = soOrSo ep3
     in
   case unsignedAddEither base ofs1 of
     Left under1 =>
       rewrite under1 in
       rewrite sym $ addAssoc (unsigned base) (unsigned ofs1) sz1 in
       case unsignedAddEither base ofs2 of
         Left under2 =>
           rewrite under2 in
           rewrite sym $ addAssoc (unsigned base) (unsigned ofs2) sz2 in
           rewrite addCompareMonoL (unsigned base) (unsigned ofs1 + sz1) (unsigned ofs2) in
           rewrite addCompareMonoL (unsigned base) (unsigned ofs2 + sz2) (unsigned ofs1) in
           case p3 of
             Left lprf =>
               Left $ lebLeTo (unsigned ofs1 + sz1) (unsigned ofs2) $ soToEq lprf
             Right rprf =>
               Right $ lebLeTo (unsigned ofs2 + sz2) (unsigned ofs1) $ soToEq rprf
         Right over2 =>
           rewrite over2 in
           rewrite sym $ addAssoc (unsigned base) (unsigned ofs2) (-modulus n) in
           rewrite sym $ addAssoc (unsigned base) (unsigned ofs2 - modulus n) sz2 in
           rewrite addCompareMonoL (unsigned base) (unsigned ofs2 - modulus n + sz2) (unsigned ofs1) in
           rewrite addComm (unsigned ofs2) (-modulus n) in
           rewrite sym $ addAssoc (-modulus n) (unsigned ofs2) sz2 in
           rewrite sym $ addCompareTransferL (unsigned ofs2 + sz2) (modulus n) (unsigned ofs1) in
           Right $ leTrans (unsigned ofs2 + sz2) (modulus n) (modulus n + unsigned ofs1)
                     (lebLeTo (unsigned ofs2 + sz2) (modulus n) $ soToEq p2)
                     (rewrite addComm (modulus n) (unsigned ofs1) in
                      rewrite addCompareMonoR 0 (unsigned ofs1) (modulus n) in
                      fst $ unsignedRange ofs1)
     Right over1 =>
       rewrite over1 in
       rewrite sym $ addAssoc (unsigned base) (unsigned ofs1) (-modulus n) in
       rewrite sym $ addAssoc (unsigned base) (unsigned ofs1 - modulus n) sz1 in
       case unsignedAddEither base ofs2 of
         Left under2 =>
           rewrite under2 in
           rewrite sym $ addAssoc (unsigned base) (unsigned ofs2) sz2 in
           rewrite addCompareMonoL (unsigned base) (unsigned ofs1 - modulus n + sz1) (unsigned ofs2) in
           rewrite addComm (unsigned ofs1) (-modulus n) in
           rewrite sym $ addAssoc (-modulus n) (unsigned ofs1) sz1 in
           rewrite sym $ addCompareTransferL (unsigned ofs1 + sz1) (modulus n) (unsigned ofs2) in
           Left $ leTrans (unsigned ofs1 + sz1) (modulus n) (modulus n + unsigned ofs2)
                    (lebLeTo (unsigned ofs1 + sz1) (modulus n) $ soToEq p1)
                    (rewrite addComm (modulus n) (unsigned ofs2) in
                     rewrite addCompareMonoR 0 (unsigned ofs2) (modulus n) in
                     fst $ unsignedRange ofs2)
         Right over2 =>
           rewrite over2 in
           rewrite addComm (unsigned ofs1) (-modulus n) in
           rewrite addAssoc (unsigned base) (-modulus n + unsigned ofs1) sz1 in
           rewrite addAssoc (unsigned base) (-modulus n) (unsigned ofs1) in
           rewrite sym$ addAssoc (unsigned base - modulus n) (unsigned ofs1) sz1 in
           rewrite sym $ addAssoc (unsigned base) (unsigned ofs2) (-modulus n) in
           rewrite addComm (unsigned ofs2) (-modulus n) in
           rewrite addAssoc (unsigned base) (-modulus n) (unsigned ofs2) in
           rewrite sym $ addAssoc (unsigned base - modulus n) (unsigned ofs2) sz2 in
           rewrite addCompareMonoL (unsigned base - modulus n) (unsigned ofs1 + sz1) (unsigned ofs2) in
           rewrite addCompareMonoL (unsigned base - modulus n) (unsigned ofs2 + sz2) (unsigned ofs1) in
           case p3 of
             Left lprf =>
               Left $ lebLeTo (unsigned ofs1 + sz1) (unsigned ofs2) $ soToEq lprf
             Right rprf =>
               Right $ lebLeTo (unsigned ofs2 + sz2) (unsigned ofs1) $ soToEq rprf
