module Data.BizMod2.Core

import Data.Util

import Data.Bip.AddMul
import Data.Bip.Iter
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.DivMod
import Data.Biz.Nat

import Data.BizMod2

%access export
%default total

-- Properties of [modulus], [max_unsigned], etc.

halfModulusPower : (n : Nat) -> halfModulus n = bizPow2 (toBizNat n - 1)
halfModulusPower n =
  rewrite modulusPower n in
  aux
  where
  aux : bizDivTwo (bizPow2 (toBizNat n)) = bizPow2 (toBizNat n - 1)
  aux with (toBizNat n) proof bn
    | BizO   = Refl
    | BizP a = case succPredOr a of
                 Left  lprf => rewrite lprf in
                               Refl
                 Right rprf => rewrite sym rprf in
                               rewrite iterSucc O U (bipPred a) in
                               rewrite sym $ add1R (bipPred a) in
                               rewrite posSubAdd (bipPred a) 1 1 in
                               Refl
    | BizM _ = let zneg = replace {P = \x => 0 `Le` x} (sym bn) (toBizNatIsNonneg n)
               in
               -- TODO bug: `zneg does not have a function type ((\x => ([__])) (BizM _))`
               -- absurd $ zneg Refl
               really_believe_me zneg

halfModulusModulus : (n : Nat) -> Not (n=0) -> modulus n = 2 * halfModulus n
halfModulusModulus n nz =
  rewrite halfModulusPower n in
  rewrite modulusPower n in
  aux
  where
  aux : bizPow2 (toBizNat n) = 2 * (bizPow2 (toBizNat n - 1))
  aux with (toBizNat n) proof bn
    | BizO   = absurd $ nz $ toBizNatInj n 0 $ sym bn
    | BizP a = case succPredOr a of
                 Left  lprf => rewrite lprf in
                               Refl
                 Right rprf => rewrite sym rprf in
                               rewrite iterSucc O U (bipPred a) in
                               rewrite sym $ add1R (bipPred a) in
                               rewrite posSubAdd (bipPred a) 1 1 in
                               Refl
    | BizM _ = let zneg = replace {P = \x => 0 `Le` x} (sym bn) (toBizNatIsNonneg n)
               in
               -- TODO bug: `zneg does not have a function type ((\x => ([__])) (BizM _))`
               -- absurd $ zneg Refl
               really_believe_me zneg

modulusInfinity : (x : Biz) -> 0 `Le` x -> (n ** x `Lt` modulus n)
modulusInfinity x zlex =
  natlikeInd
    (\y => (n ** y `Lt` modulus n))
    (0 ** Refl)
    (\y, zley, (n ** prf) =>
      (S n ** case decEq y 0 of
                Yes y0 =>
                  rewrite y0 in
                  Refl
                No yn0 =>
                  leLtTrans (y+1) (2*y) (modulus (S n))
                    (rewrite mulAddDistrR 1 1 y in
                     rewrite mul1L y in
                     rewrite addCompareMonoL y 1 y in
                     leSuccLFro 0 y $ leNeqLt y 0 zley yn0)
                    (rewrite mulCompareMonoL 2 y (modulus n) Refl in
                     prf)
      )
    )
    x
    zlex

{- Relative positions, from greatest to smallest:

      max_unsigned
      max_signed
      2*wordsize-1
      wordsize
      0
      min_signed
-}

halfModulusPos : (n : Nat) -> Not (n=0) -> 0 `Lt` halfModulus n
halfModulusPos  Z    nz = absurd $ nz Refl
halfModulusPos (S _) _  = Refl

minSignedNeg : (n : Nat) -> Not (n=0) -> minSigned n `Lt` 0
minSignedNeg  Z    nz = absurd $ nz Refl
minSignedNeg (S _) _  = Refl

maxSignedPos : (n : Nat) -> Not (n=0) -> 0 `Le` maxSigned n
maxSignedPos  Z        nz = absurd $ nz Refl
maxSignedPos (S  Z)    _  = uninhabited
maxSignedPos (S (S _)) _  = uninhabited

twoWordsizeMaxUnsigned : (n : Nat) -> bizDMO (toBizNat n) `Le` maxUnsigned n
twoWordsizeMaxUnsigned  Z = uninhabited
twoWordsizeMaxUnsigned (S Z) = uninhabited
twoWordsizeMaxUnsigned (S (S k)) =
  let ih = twoWordsizeMaxUnsigned (S k)
      bs = toBipNatSucc k
  in
  rewrite predDoubleSucc bs in
  leTrans bs (bipDMO bs) (bipDMO (bipPow2 k)) (leDMO bs) ih

wordsizeMaxUnsigned : (n : Nat) -> toBizNat n `Le` maxUnsigned n
wordsizeMaxUnsigned  Z     = uninhabited
wordsizeMaxUnsigned (S k) =
  leTrans (toBizNat (S k)) (bizDMO (toBizNat (S k))) (maxUnsigned (S k))
    (leDMO (toBipNatSucc k))
    (twoWordsizeMaxUnsigned (S k))

maxSignedUnsigned : (n : Nat) -> maxSigned n `Lt` maxUnsigned n
maxSignedUnsigned  Z    = Refl
maxSignedUnsigned (S k) =
  let pk = bipPow2 k in
  ltLeTrans (bipMinusBiz pk U) (BizP pk) (BizP (bipDMO pk))
    -- a proof of bizPred (BizP pk) `Lt` (BizP pk)
    (rewrite compareSub (BizP pk - 1) (BizP pk) in
     rewrite sym $ addAssoc (BizP pk) (-1) (BizM pk) in
     rewrite addComm 1 pk in
     rewrite addAssoc (BizP pk) (BizM pk) (-1) in
     rewrite posSubDiag pk in
     Refl)
    (leDMO pk)

unsignedReprEq : (x : Biz) -> (n : Nat) -> unsigned (repr x n) = x `bizMod` modulus n
unsignedReprEq x  Z    = sym $ snd $ divMod1 x
unsignedReprEq x (S k) = bizMod2Eq x (S k)

signedReprEq : (x : Biz) -> (n : Nat) -> let m = modulus n
                                             xm = x `bizMod` m
                                        in signed (repr x n) = if xm < halfModulus n then xm else xm - m
signedReprEq x n = rewrite unsignedReprEq x n in
                   Refl

-- TODO move to BizMod ?

-- Modulo arithmetic

-- We define and state properties of equality and arithmetic modulo a positive
-- integer.

public export
eqmod : (x, y, m : Biz) -> Type
eqmod x y m = (k ** x = k * m + y)

eqmodRefl : (x, m : Biz) -> eqmod x x m
eqmodRefl _ _ = (0 ** Refl)

eqmodRefl2 : (x, y, m : Biz) -> x = y -> eqmod x y m
eqmodRefl2 y y m Refl = eqmodRefl y m

eqmodSym : (x, y, m : Biz) -> eqmod x y m -> eqmod y x m
eqmodSym _ y m (k ** prf) =
  ((-k) ** rewrite prf in
           rewrite addAssoc ((-k)*m) (k*m) y in
           rewrite sym $ mulAddDistrR (-k) k m in
           rewrite addOppDiagL k in
           Refl)

eqmodTrans : (x, y, z, m : Biz) -> eqmod x y m -> eqmod y z m -> eqmod x z m
eqmodTrans _ _ z m (k1 ** prf1) (k2 ** prf2) =
  (k1+k2 ** rewrite prf1 in
            rewrite prf2 in
            rewrite addAssoc (k1*m) (k2*m) z in
            rewrite sym $ mulAddDistrR k1 k2 m in
            Refl)

eqmodSmallEq : (x, y, m : Biz) -> eqmod x y m -> 0 `Le` x -> x `Lt` m -> 0 `Le` y -> y `Lt` m -> x = y
eqmodSmallEq x y m (k ** prf) zlex xltm zley yltm =
  let dprf = fst $ divModPos x m k y zley yltm prf
      zdiv = fst $ divModSmall x m zlex xltm
      kz = trans dprf zdiv
  in
  replace kz prf

eqmodModEq : (x, y, m : Biz) -> 0 `Lt` m -> eqmod x y m -> x `bizMod` m = y `bizMod` m
eqmodModEq x y m zltm (k**prf) =
  rewrite prf in
  rewrite addComm (k*m) y in
  modPlus y k m zltm

eqmodMod : (x, m : Biz) -> Not (m=0) -> eqmod x (x `bizMod` m) m
eqmodMod x m mnz = (x `bizDiv` m ** divEuclEq x m mnz)

eqmodAdd : (a, b, c, d, m : Biz) -> eqmod a b m -> eqmod c d m -> eqmod (a + c) (b + d) m
eqmodAdd _ b _ d m (k1**prf1) (k2**prf2) =
  (k1+k2 ** rewrite prf1 in
            rewrite prf2 in
            rewrite addAssoc (k1*m+b) (k2*m) d in
            rewrite sym $ addAssoc (k1*m) b (k2*m) in
            rewrite addComm b (k2*m) in
            rewrite addAssoc (k1*m) (k2*m) b in
            rewrite sym $ mulAddDistrR k1 k2 m in
            rewrite sym $ addAssoc ((k1+k2)*m) b d in
            Refl)

eqmodNeg : (x, y, m : Biz) -> eqmod x y m -> eqmod (-x) (-y) m
eqmodNeg _ y m (k**prf) =
  (-k ** rewrite prf in
         rewrite oppAddDistr (k*m) y in
         rewrite sym $ mulOppL k m in
         Refl)

eqmodSub : (a, b, c, d, m : Biz) -> eqmod a b m -> eqmod c d m -> eqmod (a - c) (b - d) m
eqmodSub a b c d m eq1 eq2 = eqmodAdd a b (-c) (-d) m eq1 $ eqmodNeg c d m eq2

eqmodMult : (a, b, c, d, m : Biz) -> eqmod a b m -> eqmod c d m -> eqmod (a * c) (b * d) m
eqmodMult a b c d m (k1**prf1) (k2**prf2) =
  (k1*k2*m+k1*d+b*k2 ** rewrite prf1 in
                        rewrite prf2 in
                        rewrite mulAddDistrR (k1*m) b (k2*m+d) in
                        rewrite mulAddDistrL (k1*m) (k2*m) d in
                        rewrite mulAddDistrL b (k2*m) d in
                        rewrite mulAssoc (k1*m) k2 m in
                        rewrite sym $ mulAssoc k1 m k2 in
                        rewrite mulComm m k2 in
                        rewrite mulAssoc k1 k2 m in
                        rewrite sym $ mulAssoc k1 m d in
                        rewrite mulComm m d in
                        rewrite mulAssoc k1 d m in
                        rewrite sym $ mulAddDistrR (k1*k2*m) (k1*d) m in
                        rewrite mulAssoc b k2 m in
                        rewrite addAssoc ((k1*k2*m+k1*d)*m) ((b*k2)*m) (b*d) in
                        rewrite sym $ mulAddDistrR (k1*k2*m+k1*d) (b*k2) m in
                        Refl)

eqmodDivides : (n, m, x, y : Biz) -> eqmod x y n -> bizDivides m n -> eqmod x y m
eqmodDivides n m x y (k**prf1) (p**prf2) =
  (k*p ** rewrite sym $ mulAssoc k p m in
          rewrite sym prf2 in
          prf1)

public export
eqm : (x, y : Biz) -> (n : Nat) -> Type
eqm x y = eqmod x y . modulus

-- Properties of the coercions between [Z] and [int]

eqmSamerepr : (x, y : Biz) -> (n : Nat) -> eqm x y n -> repr x n = repr y n
eqmSamerepr _ _    Z    _  = Refl
eqmSamerepr x y n@(S _) em =
  mkintEq (x `bizMod2` n) (y `bizMod2` n) n
          (bizMod2Range x n) (bizMod2Range y n) $
  rewrite bizMod2Eq x n in
  rewrite bizMod2Eq y n in
  eqmodModEq x y (modulus n) Refl em

eqmUnsignedRepr : (x : Biz) -> (n : Nat) -> eqm x (unsigned (repr x n)) n
eqmUnsignedRepr x    Z    = (x ** rewrite mul1R x in
                                  sym $ add0R x)
eqmUnsignedRepr x n@(S _) =
  (x `bizDiv` modulus n ** rewrite bizMod2Eq x n in
                           divEuclEq x (modulus n) uninhabited)

eqmUnsignedRepr' : (x : Biz) -> (n : Nat) -> eqm (unsigned (repr x n)) x n
eqmUnsignedRepr' x n = eqmodSym x (unsigned $ repr x n) (modulus n) $ eqmUnsignedRepr x n

eqmUnsignedReprL : (a, b : Biz) -> (n : Nat) -> eqm a b n -> eqm (unsigned $ repr a n) b n
eqmUnsignedReprL a b n =
  eqmodTrans (unsigned $ repr a n) a b (modulus n) $
  eqmUnsignedRepr' a n

eqmUnsignedReprR : (a, b : Biz) -> (n : Nat) -> eqm a b n -> eqm a (unsigned $ repr b n) n
eqmUnsignedReprR a b n ab =
  eqmodTrans a b (unsigned $ repr b n) (modulus n) ab $
  eqmUnsignedRepr b n

eqmSignedUnsigned : (x : BizMod2 n) -> eqm (signed x) (unsigned x) n
eqmSignedUnsigned {n} x with (unsigned x < halfModulus n)
  | False = (-1 ** addComm (unsigned x) (-(modulus n)))
  | True  = (0  ** Refl)

eqmUnsignedSigned : (x : BizMod2 n) -> eqm (unsigned x) (signed x) n
eqmUnsignedSigned {n} x = eqmodSym (signed x) (unsigned x) (modulus n) (eqmSignedUnsigned x)

unsignedRange : (x : BizMod2 n) -> (0 `Le` unsigned x, unsigned x `Lt` modulus n)
unsignedRange (MkBizMod2 i r) =
  (ltSuccRTo 0 i $
   rewrite sym $ addCompareMonoR 0 (i+1) (-1) in
   rewrite sym $ addAssoc i 1 (-1) in
   rewrite add0R i in
   fst r, snd r)

unsignedRange2 : (x : BizMod2 n) -> (0 `Le` unsigned x, unsigned x `Le` maxUnsigned n)
unsignedRange2 {n} x =
  let (lo, hi) = unsignedRange x in
  (lo, ltSuccRTo (unsigned x) (maxUnsigned n) $
       rewrite sym $ addAssoc (modulus n) (-1) 1 in
       hi)

signedRange : (x : BizMod2 n) -> Not (n=0) -> (minSigned n `Le` signed x, signed x `Le` maxSigned n)
signedRange {n} x nz with (unsigned x < halfModulus n) proof hx
  | False = let hm = halfModulus n
                ux = unsigned x
                m2 = cong {f = bizOpp} $ halfModulusModulus n nz
            in
            rewrite m2 in
            ( rewrite sym $ addCompareMonoR (-hm) (ux-(2*hm)) (2*hm) in
              rewrite sym $ addAssoc ux (-(2*hm)) (2*hm) in
              rewrite addOppDiagL (2*hm) in
              rewrite add0R ux in
              rewrite oppEqMulM1 hm in
              rewrite mulComm hm (-1) in
              rewrite sym $ mulAddDistrR (-1) 2 hm in
              rewrite mul1L hm in
              nltbLeTo hm ux (sym hx)
            , rewrite sym $ addCompareMonoR (ux-(2*hm)) (hm-1) (2*hm) in
              rewrite sym $ addAssoc ux (-(2*hm)) (2*hm) in
              rewrite addOppDiagL (2*hm) in
              rewrite add0R ux in
              rewrite addComm (hm-1) (2*hm) in
              rewrite addComm hm (-1) in
              rewrite addAssoc (2*hm) (-1) hm in
              leTrans ux (2*hm-1) (2*hm-1+hm)
                (ltPredRTo ux (2*hm) $
                 rewrite sym $ halfModulusModulus n nz in
                 snd $ unsignedRange x)
                (rewrite sym $ addCompareMonoL (-(2*hm-1)) (2*hm-1) (2*hm-1+hm) in
                 rewrite addAssoc (-(2*hm-1)) (2*hm-1) hm in
                 rewrite addOppDiagL (2*hm-1) in
                 ltLeIncl 0 hm $
                 halfModulusPos n nz)
            )
  | True  = let hm = halfModulus n
                ux = unsigned x
            in
            ( leTrans (-hm) 0 ux
                (rewrite sym $ compareOpp 0 hm in
                 ltLeIncl 0 hm $
                 halfModulusPos n nz)
                (fst $ unsignedRange x)
            , ltPredRTo ux hm $
              ltbLtTo ux hm (sym hx)
            )

reprUnsigned : (x : BizMod2 n) -> repr (unsigned x) n = x
reprUnsigned {n=Z}    x              = sym $ bizMod2P0 x
reprUnsigned {n=S n} (MkBizMod2 i r) =
  mkintEq (i `bizMod2` (S n)) i (S n) (bizMod2Range i (S n)) r $
  rewrite bizMod2Eq i (S n) in
  snd $ divModSmall i (modulus (S n)) (leSuccLFro (-1) i (fst r)) (snd r)

unsignedInj : (x, y : BizMod2 n) -> unsigned x = unsigned y -> x = y
unsignedInj x y prf =
  rewrite sym $ reprUnsigned x in
  rewrite sym $ reprUnsigned y in
  cong {f = \z => repr z n} prf

reprSigned : (x : BizMod2 n) -> repr (signed x) n = x
reprSigned {n} x =
  trans
    (eqmSamerepr (signed x) (unsigned x) n (eqmSignedUnsigned x))
    (reprUnsigned x)

eqmReprEq : (x : Biz) -> (y : BizMod2 n) -> eqm x (unsigned y) n -> repr x n = y
eqmReprEq {n} x y eqxuy = rewrite sym $ reprUnsigned y in
                          eqmSamerepr x (unsigned y) n eqxuy

unsignedRepr : (x : Biz) -> (n : Nat) -> 0 `Le` x -> x `Le` maxUnsigned n -> unsigned (repr x n) = x
unsignedRepr  BizO       Z    _    _     = Refl
unsignedRepr (BizP _)    Z    _    xlemu = absurd $ xlemu Refl
unsignedRepr (BizM _)    Z    zlex _     = absurd $ zlex Refl
unsignedRepr  x       n@(S _) zlex xlemu =
  rewrite bizMod2Eq x n in
  snd $ divModSmall x (modulus n) zlex (ltPredRFro x (modulus n) xlemu)

signedRepr : (x : Biz) -> (n : Nat) -> Not (n=0) -> minSigned n `Le` x -> x `Le` maxSigned n -> signed (repr x n) = x
signedRepr    BizO     Z    nz _     _     = absurd $ nz Refl
signedRepr    BizO    (S _) _  _     _     = Refl
signedRepr x@(BizP _)  n    _  _     xlema =
  rewrite unsignedRepr x n uninhabited $
            ltLeIncl x (maxUnsigned n) $
            leLtTrans x (maxSigned n) (maxUnsigned n) xlema (maxSignedUnsigned n) in
  rewrite ltbLtFro x (halfModulus n) $
            ltPredRFro x (halfModulus n) xlema in
  Refl
signedRepr   (BizM a)  n    nz milex _     =
  -- prove that we can substitute `repr x n` with `repr (x+(modulus n)) n`
  let xm = cong {f=signed} $ eqmSamerepr (BizM a) ((BizM a)+(modulus n)) n $
           eqmodAdd (BizM a) (BizM a) 0 (modulus n) (modulus n) (eqmodRefl (BizM a) (modulus n)) $
           (-1 ** sym $ posSubDiag (bipPow2 n))
      mhm = cong {f=bizOpp} $ halfModulusModulus n nz
  in
  rewrite xm in
  rewrite unsignedRepr ((BizM a)+(modulus n)) n
            (rewrite addCompareTransferL 0 (modulus n) (BizM a) in
             leTrans (-(modulus n)) (-(halfModulus n)) (BizM a)
               (rewrite mhm in
                rewrite sym $ compareOpp (halfModulus n) (2*(halfModulus n)) in
                rewrite sym $ mul1L (halfModulus n) in
                rewrite mulAssoc 2 1 (halfModulus n) in
                rewrite mulCompareMonoR (halfModulus n) 1 2 (halfModulusPos n nz) in
                uninhabited)
               milex
            )
            (rewrite addCompareMonoL (modulus n) (BizM a) (-1) in
             le1L a)
  in
  rewrite nltbLeFro (halfModulus n) ((modulus n)+(BizM a)) $
            rewrite addCompareTransferL (halfModulus n) (modulus n) (BizM a) in
            rewrite mhm in
            rewrite sym $ mulOppL 2 (halfModulus n) in
            rewrite sym $ mulAddDistrR1 (-2) (halfModulus n) in
            rewrite mulOppL 1 (halfModulus n) in
            rewrite mul1L (halfModulus n) in
            milex
  in
  rewrite addComm ((modulus n)+(BizM a)) (-(modulus n)) in
  rewrite addAssoc (-(modulus n)) (modulus n) (BizM a)  in
  rewrite posSubDiag (bipPow2 n) in
  Refl

signedEqUnsigned : (x : BizMod2 n) -> unsigned x `Le` maxSigned n -> signed x = unsigned x
signedEqUnsigned {n} x uxlema with ((unsigned x) < (halfModulus n)) proof uxhm
  | False = let hmgtux = ltGt (unsigned x) (halfModulus n) $
                         ltPredRFro (unsigned x) (halfModulus n) uxlema
                hmleux = nltbLeTo (halfModulus n) (unsigned x) (sym uxhm)
            in
            absurd $ hmleux hmgtux
  | True = Refl

-- TODO split into `to` and `fro`

signedPositiveTo : (x : BizMod2 n) -> 0 `Le` signed x -> unsigned x `Le` maxSigned n
signedPositiveTo {n} x zles uxgtma with ((unsigned x) < (halfModulus n)) proof uxhm
  | False = let uxgem = zles
                     |> replace {P = \x => Not (x=GT)} (sym $ compareSubR (modulus n) (unsigned x))
                     |> leGe (modulus n) (unsigned x)
            in
            absurd $ uxgem $ snd (unsignedRange x)
  | True  = let hmleux = uxgtma
                      |> gtLt (unsigned x) ((halfModulus n)-1)
                      |> leSuccLFro ((halfModulus n)-1) (unsigned x)
                      |> replace {P = \y => y `Le` unsigned x} (sym $ addAssoc (halfModulus n) (-1) 1)
                      |> replace {P = \y => y `Le` unsigned x} (add0R (halfModulus n))
                hmgtux = ltGt (unsigned x) (halfModulus n) $ ltbLtTo (unsigned x) (halfModulus n) (sym uxhm)
            in
            absurd $ hmleux hmgtux

signedPositiveFro : (x : BizMod2 n) -> unsigned x `Le` maxSigned n -> 0 `Le` signed x
signedPositiveFro {n} x uxlema zgts with ((unsigned x) < (halfModulus n)) proof uxhm
  | False = let hmgtux = ltGt (unsigned x) (halfModulus n) $
                         ltPredRFro (unsigned x) (halfModulus n) uxlema
                hmleux = nltbLeTo (halfModulus n) (unsigned x) (sym uxhm)
            in
            absurd $ hmleux hmgtux
  | True = let zleux = fst $ unsignedRange x in
           absurd $ zleux zgts

-- Properties of zero, one, minus one

unsignedZero : (n : Nat) -> unsigned {n} 0 = 0
unsignedZero  Z    = Refl
unsignedZero (S _) = Refl

unsignedOne : (n : Nat) -> Not (n=0) -> unsigned {n} 1 = 1
unsignedOne  Z    nz = absurd $ nz Refl
unsignedOne (S _) _  = Refl

unsignedMone : (n : Nat) -> unsigned {n} (-1) = modulus n - 1
unsignedMone  Z    = Refl
unsignedMone (S _) = Refl

signedZero : (n : Nat) -> Not (n=0) -> signed {n} 0 = 0
signedZero  Z    nz = absurd $ nz Refl
signedZero (S _) _  = Refl

signedOne : (n : Nat) -> 1 `Lt` toBizNat n -> signed {n} 1 = 1
signedOne  Z        ultn = absurd ultn
signedOne (S  Z)    ultn = absurd ultn
signedOne (S (S _)) _    = Refl

signedMone : (n : Nat) -> signed {n} (-1) = -1
signedMone  Z    = Refl
signedMone (S k) =
  let dmo = bipDMO (bipPow2 k) in
  rewrite nltbLeFro (BizP $ bipPow2 k) (BizP dmo) (leDMO $ bipPow2 k) in
  rewrite sym $ succPredDouble (bipPow2 k) in
  rewrite posSubLt dmo (bipSucc dmo) (ltSuccDiagR dmo) in
  rewrite sym $ add1R dmo in
  rewrite subMaskAddDiagL dmo 1 in
  Refl

oneNotZero : (n : Nat) -> Not (n=0) -> Not (repr 1 n = repr 0 n)
oneNotZero  Z    nz = absurd $ nz Refl
oneNotZero (S _) _  = absurd . MkBizMod2Inj

unsignedReprWordsize : (n : Nat) -> unsigned (repr (toBizNat n) n) = toBizNat n
unsignedReprWordsize n = unsignedRepr (toBizNat n) n (toBizNatIsNonneg n) (wordsizeMaxUnsigned n)

-- Properties of equality

eqSym : (x, y: BizMod2 n) -> x == y = y == x
eqSym x y with ((unsigned x) == (unsigned y)) proof uxy
  | False = sym $ neqbNeqFro (unsigned y) (unsigned x) $
            neqbNeqTo (unsigned x) (unsigned y) (sym uxy) . sym
  | True  = sym $ eqbEqFro (unsigned y) (unsigned x) $
            sym $ eqbEqTo (unsigned x) (unsigned y) $
            sym uxy

eqSpec : (x, y : BizMod2 n) -> if x == y then x = y else Not (x = y)
eqSpec {n} (MkBizMod2 x rx) (MkBizMod2 y ry) =
  case decEq (MkBizMod2 x rx) (MkBizMod2 y ry) of
    Yes prf => rewrite eqbEqFro x y (MkBizMod2Inj prf) in
               prf
    No contra => let xneqy = contra . mkintEq x y n rx ry in
                 rewrite neqbNeqFro x y xneqy in
                 contra

eqTrue : (x : BizMod2 n) -> x == x = True
eqTrue x with (x==x) proof xx
  | True  = Refl
  | False = let contra = replace {P = \z => if z then x = x else Not (x = x)} (sym xx) (eqSpec x x) in
            absurd $ contra Refl

eqFalse : (x, y : BizMod2 n) -> Not (x=y) -> x == y = False
eqFalse x y neq with (x==y) proof xeqby
  | True  = let xy = replace {P = \z => if z then x = y else Not (x = y)} (sym xeqby) (eqSpec x y) in
            absurd $ neq xy
  | False = Refl

eqSigned : (x, y : BizMod2 n) -> x == y = (signed x) == (signed y)
eqSigned {n=Z} x y =
  rewrite bizMod2P0 x in
  rewrite bizMod2P0 y in
  Refl
eqSigned {n=S n} x y with ((signed x) == (signed y)) proof sxy
  | False = neqbNeqFro (unsigned x) (unsigned y) $
            neqbNeqTo (signed x) (signed y) (sym sxy) . cong {f = signed} . unsignedInj x y
  | True = rewrite sym $ reprSigned x in
           rewrite sym $ reprSigned y in
           rewrite eqbEqTo (signed x) (signed y) (sym sxy) in
           eqbEqFro ((signed y) `bizMod2` (S n)) ((signed y) `bizMod2` (S n)) Refl
