module Data.Bip.OrdSub

import Syntax.WithProof
import Data.Nat
import Data.So
import Data.Util
import Data.Bip
import Data.Bip.AddMul
import Data.Bip.Iter

%default total

%hide Data.Nat.GT
%hide Data.Nat.LT

-- sub_mask_succ_r

subMaskSuccR : (p, q : Bip) -> bimMinus p (bipSucc q) = bimMinusCarry p q
subMaskSuccR  U         U    = Refl
subMaskSuccR  U        (O _) = Refl
subMaskSuccR  U        (I _) = Refl
subMaskSuccR (O  U   )  U    = Refl
subMaskSuccR (O (O _))  U    = Refl
subMaskSuccR (O (I _))  U    = Refl
subMaskSuccR (O  _   ) (O _) = Refl
subMaskSuccR (O  a   ) (I b) = cong bimD $ subMaskSuccR a b
subMaskSuccR (I  U   )  U    = Refl
subMaskSuccR (I (O _))  U    = Refl
subMaskSuccR (I (I _))  U    = Refl
subMaskSuccR (I  _   ) (O _) = Refl
subMaskSuccR (I  a   ) (I b) = cong bimDPO $ subMaskSuccR a b

-- sub_mask_carry_spec

doublePredDpo : (p : Bim) -> bimD p = bimPred (bimDPO p)
doublePredDpo  BimO    = Refl
doublePredDpo (BimP _) = Refl
doublePredDpo  BimM    = Refl

dpoPredDouble : (p : Bim) -> bimDPO (bimPred p) = bimPred (bimD p)
dpoPredDouble  BimO        = Refl
dpoPredDouble (BimP  U   ) = Refl
dpoPredDouble (BimP (O _)) = Refl
dpoPredDouble (BimP (I _)) = Refl
dpoPredDouble  BimM        = Refl

subMaskCarrySpec : (p, q : Bip) -> bimMinusCarry p q = bimPred (bimMinus p q)
subMaskCarrySpec  U         U    = Refl
subMaskCarrySpec  U        (O _) = Refl
subMaskCarrySpec  U        (I _) = Refl
subMaskCarrySpec (O  U   )  U    = Refl
subMaskCarrySpec (O (O _))  U    = Refl
subMaskCarrySpec (O (I _))  U    = Refl
subMaskCarrySpec (O  a   ) (O b) = rewrite subMaskCarrySpec a b in
                                   dpoPredDouble (bimMinus a b)
subMaskCarrySpec (O  a   ) (I b) =
  rewrite subMaskCarrySpec a b in
  rewrite doublePredDpo (bimPred (bimMinus a b)) in
  Refl
subMaskCarrySpec (I  _   )  U    = Refl
subMaskCarrySpec (I  a   ) (O b) = doublePredDpo (bimMinus a b)
subMaskCarrySpec (I  a   ) (I b) = rewrite subMaskCarrySpec a b in
                                   dpoPredDouble (bimMinus a b)

-- TODO we use explicit proof arguments instead of Coq's GADT-like style,
-- because we can't directly split arbitrary terms in later proofs, only "bind"
-- them.
public export
data BimMinusSpec : (p, q : Bip) -> (m : Bim) -> Type where
  SubIsNul :                  p = q -> m=BimO   -> BimMinusSpec p q m
  SubIsPos : (r : Bip) -> q + r = p -> m=BimP r -> BimMinusSpec p q m
  SubIsNeg : (r : Bip) -> p + r = q -> m=BimM   -> BimMinusSpec p q m

-- sub_mask_spec

subMaskSpec : (p, q : Bip) -> BimMinusSpec p q (bimMinus p q)
subMaskSpec  U     U    = SubIsNul Refl Refl
subMaskSpec  U    (O b) = SubIsNeg (bipDMO b)
                                   (rewrite add1L (bipDMO b) in succPredDouble b)
                                    Refl
subMaskSpec  U    (I b) = SubIsNeg (O b) Refl Refl
subMaskSpec (O a)  U    = SubIsPos (bipDMO a)
                                   (rewrite add1L (bipDMO a) in succPredDouble a)
                                    Refl
subMaskSpec (O a) (O b) =
  case subMaskSpec a b of
    SubIsNul   Refl mo => rewrite mo in SubIsNul       Refl Refl
    SubIsPos r Refl mp => rewrite mp in SubIsPos (O r) Refl Refl
    SubIsNeg r Refl mm => rewrite mm in SubIsNeg (O r) Refl Refl
subMaskSpec (O a) (I b) =
  rewrite subMaskCarrySpec a b in
    case subMaskSpec a b of
      SubIsNul   Refl mo => rewrite mo in SubIsNeg U Refl Refl
      SubIsPos r Refl mp => rewrite mp in
                            SubIsPos (bipDMO r)
                                     (sym $ addXIPredDouble b r)
                                     (rewrite dpoPredDouble (BimP r) in Refl)
      SubIsNeg r Refl mm => rewrite mm in SubIsNeg (I r) Refl Refl
subMaskSpec (I a)  U    = SubIsPos (O a) Refl Refl
subMaskSpec (I a) (O b) =
  case subMaskSpec a b of
    SubIsNul   Refl mo => rewrite mo in SubIsPos  U    Refl Refl
    SubIsPos r Refl mp => rewrite mp in SubIsPos (I r) Refl Refl
    SubIsNeg r Refl mm => rewrite mm in
                          SubIsNeg (bipDMO r)
                                   (sym $ addXIPredDouble a r)
                                    Refl
subMaskSpec (I a) (I b) =
  case subMaskSpec a b of
    SubIsNul   Refl mo => rewrite mo in SubIsNul       Refl Refl
    SubIsPos r Refl mp => rewrite mp in SubIsPos (O r) Refl Refl
    SubIsNeg r Refl mm => rewrite mm in SubIsNeg (O r) Refl Refl

-- sub_mask_diag

subMaskDiag : (p : Bip) -> bimMinus p p = BimO
subMaskDiag  U    = Refl
subMaskDiag (O a) = rewrite subMaskDiag a in Refl
subMaskDiag (I a) = rewrite subMaskDiag a in Refl

-- sub_mask_nul_iff

-- TODO is split into `to` and `fro`

subMaskNulTo : (p, q : Bip) -> bimMinus p q = BimO -> p = q
subMaskNulTo p q =
  case subMaskSpec p q of
    SubIsNul   Refl _  => const Refl
    SubIsPos _ Refl mp => rewrite mp in absurd
    SubIsNeg _ Refl mm => rewrite mm in absurd

subMaskNulFro : (p, q : Bip) -> p = q -> bimMinus p q = BimO
subMaskNulFro p p Refl = subMaskDiag p

-- sub_mask_add

subMaskAdd : (p, q, r : Bip) -> bimMinus p q = BimP r -> q + r = p
subMaskAdd p q r =
  case subMaskSpec p q of
    SubIsNul   Refl mo => rewrite mo in absurd
    SubIsPos _ Refl mp => rewrite mp in cong (bipPlus q) . (\prf => sym $ BimPInj prf)
    SubIsNeg _ Refl mm => rewrite mm in absurd

-- sub_mask_add_diag_l

subMaskAddDiagL : (p, q : Bip) -> bimMinus (p+q) p = BimP q
subMaskAddDiagL p q =
  case subMaskSpec (p+q) p of
    SubIsNul   prf _  =>
      absurd $ addNoNeutral p q $
        rewrite addComm q p in
        prf
    SubIsPos r prf mp =>
        rewrite cong BimP $ sym $ addRegL p r q prf in
        mp
    SubIsNeg r prf _  =>
      absurd $ addNoNeutral p (q+r) $
        rewrite addComm (q+r) p in
        rewrite addAssoc p q r in
        prf

-- sub_mask_add_diag_r

subMaskAddDiagR : (p, q : Bip) -> bimMinus p (p+q) = BimM
subMaskAddDiagR p q =
  case subMaskSpec p (p+q) of
    SubIsNul   prf _ =>
      absurd $ addNoNeutral p q $
        rewrite addComm q p in
        sym prf
    SubIsPos r prf _ =>
      absurd $ addNoNeutral p (q+r) $
        rewrite addComm (q+r) p in
        rewrite addAssoc p q r in
        prf
    SubIsNeg _ _  mm => mm

-- sub_mask_neg_iff

-- TODO is split into `to` and `fro`

subMaskNegTo : (p, q : Bip) -> bimMinus p q = BimM -> (r ** p + r = q)
subMaskNegTo p q prf =
  case subMaskSpec p q of
    SubIsNul   Refl mo => absurd $
      the (BimO   = BimM) (rewrite sym mo in prf)
    SubIsPos r Refl mp => absurd $
      the (BimP r = BimM) (rewrite sym mp in prf)
    SubIsNeg r Refl mm => (r ** Refl)

subMaskNegFro : (p, q : Bip) -> (r ** p + r = q) -> bimMinus p q = BimM
subMaskNegFro p _ (r ** prf) = rewrite sym prf in
                               subMaskAddDiagR p r

-- eqb_eq
-- TODO is split into `to` and `fro`

eqbEqTo : (p, q : Bip) -> So (p == q) -> p = q
eqbEqTo  U     U    Oh = Refl
eqbEqTo  U    (O _) Oh impossible
eqbEqTo  U    (I _) Oh impossible
eqbEqTo (O _)  U    Oh impossible
eqbEqTo (O a) (O b) prf  = rewrite eqbEqTo a b prf in
                           Refl
eqbEqTo (O _) (I _) Oh impossible
eqbEqTo (I _)  U    Oh impossible
eqbEqTo (I _) (O _) Oh impossible
eqbEqTo (I a) (I b) prf  = rewrite eqbEqTo a b prf in
                           Refl

eqbEqFro : (p, q : Bip) -> p = q -> So (p == q)
eqbEqFro  U     U    Refl = Oh
eqbEqFro  U    (O _) Refl impossible
eqbEqFro  U    (I _) Refl impossible
eqbEqFro (O _)  U    Refl impossible
eqbEqFro (O a) (O a) Refl = eqbEqFro a a Refl
eqbEqFro (O _) (I _) Refl impossible
eqbEqFro (I _)  U    Refl impossible
eqbEqFro (I _) (O _) Refl impossible
eqbEqFro (I a) (I a) Refl = eqbEqFro a a Refl

public export
Lt : (x, y : Bip) -> Type
Lt x y = x `compare` y = LT

public export
Gt : (x, y : Bip) -> Type
Gt x y = x `compare` y = GT

public export
Le : (x, y : Bip) -> Type
Le x y = Not (x `compare` y = GT)

public export
Ge : (x, y : Bip) -> Type
Ge x y = Not (x `compare` y = LT)

-- ltb_lt
-- TODO is split into `to` and `fro`

ltbLtTo : (p, q : Bip) -> So (p < q) -> p `Lt` q
ltbLtTo p q with (p `compare` q)
  ltbLtTo p q | LT = const Refl
  ltbLtTo p q | EQ = absurd
  ltbLtTo p q | GT = absurd

ltbLtFro : (p, q : Bip) -> p `Lt` q -> So (p < q)
ltbLtFro _ _ pltq = rewrite pltq in Oh

-- leb_le
-- TODO is split into `to` and `fro`
-- TODO rename to lebNlt* for consistency or change to p <= q = True
lebLeTo : (p, q : Bip) -> Not (So (p > q)) -> p `Le` q
lebLeTo p q prf pq = prf $ rewrite pq in Oh

lebLeFro : (p, q : Bip) -> p `Le` q -> Not (So (p > q))
lebLeFro p q pleq with (p `compare` q)
  lebLeFro p q pleq | LT = uninhabited
  lebLeFro p q pleq | EQ = uninhabited
  lebLeFro p q pleq | GT = const $ pleq Refl

mutual
  compLtNotEq : (p, q : Bip) -> Not (bipCompare p q LT = EQ)
  compLtNotEq  U     U    = uninhabited
  compLtNotEq  U    (O _) = uninhabited
  compLtNotEq  U    (I _) = uninhabited
  compLtNotEq (O _)  U    = uninhabited
  compLtNotEq (O a) (O b) = compLtNotEq a b
  compLtNotEq (O a) (I b) = compLtNotEq a b
  compLtNotEq (I _)  U    = uninhabited
  compLtNotEq (I a) (O b) = compGtNotEq a b
  compLtNotEq (I a) (I b) = compLtNotEq a b

  compGtNotEq : (p, q : Bip) -> Not (bipCompare p q GT = EQ)
  compGtNotEq  U     U    = uninhabited
  compGtNotEq  U    (O _) = uninhabited
  compGtNotEq  U    (I _) = uninhabited
  compGtNotEq (O _)  U    = uninhabited
  compGtNotEq (O a) (O b) = compGtNotEq a b
  compGtNotEq (O a) (I b) = compLtNotEq a b
  compGtNotEq (I _)  U    = uninhabited
  compGtNotEq (I a) (O b) = compGtNotEq a b
  compGtNotEq (I a) (I b) = compGtNotEq a b

-- TODO Idris2 doesn't have a proper `proof` keyword
thenCompareLT : (a, b : Bip) -> thenCompare (bipCompare a b LT) o = bipCompare a b LT
thenCompareLT a b with (@@ (bipCompare a b LT))
  thenCompareLT a b | (LT**ablt) = rewrite ablt in Refl
  thenCompareLT a b | (EQ**ablt) = absurd $ compLtNotEq a b ablt
  thenCompareLT a b | (GT**ablt) = rewrite ablt in Refl

-- TODO Idris2 doesn't have a proper `proof` keyword
thenCompareGT : (a, b : Bip) -> thenCompare (bipCompare a b GT) o = bipCompare a b GT
thenCompareGT a b with (@@ (bipCompare a b GT))
  thenCompareGT a b | (LT**abgt) = rewrite abgt in Refl
  thenCompareGT a b | (EQ**abgt) = absurd $ compGtNotEq a b abgt
  thenCompareGT a b | (GT**abgt) = rewrite abgt in Refl

-- compare_cont_spec

compareContSpec : (p, q : Bip) -> (c : Ordering)
               -> bipCompare p q c = thenCompare (p `compare` q) c
compareContSpec U      U    _ = Refl
compareContSpec U     (O _) _ = Refl
compareContSpec U     (I _) _ = Refl
compareContSpec (O _)  U    _ = Refl
compareContSpec (O a) (O b) c = compareContSpec a b c
compareContSpec (O a) (I b) _ = sym $ thenCompareLT a b
compareContSpec (I _)  U    _ = Refl
compareContSpec (I a) (O b) _ = sym $ thenCompareGT a b
compareContSpec (I a) (I b) c = compareContSpec a b c

-- compare_cont_Eq

compareContEq : (p, q : Bip) -> (c : Ordering) -> bipCompare p q c = EQ -> c = EQ
compareContEq p q LT prf = absurd $ compLtNotEq p q prf
compareContEq _ _ EQ _   = Refl
compareContEq p q GT prf = absurd $ compGtNotEq p q prf

-- compare_cont_Lt_Gt
-- TODO is split into `to` and `fro`

compareContLtGtTo : (p, q : Bip) -> bipCompare p q LT = GT -> p `Gt` q
compareContLtGtTo p q prf =
  aux (p `compare` q) $
    rewrite sym $ compareContSpec p q LT in
    prf
  where
  aux : (o : Ordering) -> thenCompare o LT = GT -> o = GT
  aux LT prf = absurd prf
  aux EQ prf = absurd prf
  aux GT _   = Refl

compareContLtGtFro : (p, q : Bip) -> p `Gt` q -> bipCompare p q LT = GT
compareContLtGtFro p q pgtq = rewrite compareContSpec p q LT in
                              rewrite pgtq in
                              Refl

-- compare_cont_Lt_Lt
-- TODO is split into `to` and `fro`

compareContLtLtTo : (p, q : Bip) -> bipCompare p q LT = LT -> p `Le` q
compareContLtLtTo p q prf pgtq =
  uninhabited $ the (LT = GT) $
    rewrite sym prf in
    rewrite sym aux in
    compareContSpec p q LT
  where
  aux : thenCompare (p `compare` q) LT = GT
  aux = rewrite pgtq in Refl

compareContLtLtFro : (p, q : Bip) -> p `Le` q -> bipCompare p q LT = LT
compareContLtLtFro p q = rewrite compareContSpec p q LT in
                         aux
  where
  aux : p `Le` q -> thenCompare (p `compare` q) LT = LT
  aux prf with (p `compare` q)
    aux prf | LT = Refl
    aux prf | EQ = Refl
    aux prf | GT = absurd $ prf Refl

-- compare_cont_Gt_Lt
-- TODO is split into `to` and `fro`

compareContGtLtTo : (p, q : Bip) -> bipCompare p q GT = LT -> p `Lt` q
compareContGtLtTo p q prf =
  aux (p `compare` q) $
    rewrite sym $ compareContSpec p q GT in
    prf
  where
  aux : (o : Ordering) -> thenCompare o GT = LT -> o = LT
  aux LT _   = Refl
  aux EQ prf = absurd prf
  aux GT prf = absurd prf

compareContGtLtFro : (p, q : Bip) -> p `Lt` q -> bipCompare p q GT = LT
compareContGtLtFro p q x =
  rewrite compareContSpec p q GT in
  rewrite x in
  Refl

-- compare_cont_Gt_Gt
-- TODO is split into `to` and `fro`

compareContGtGtTo : (p, q : Bip) -> bipCompare p q GT = GT -> p `Ge` q
compareContGtGtTo p q prf pltq =
  uninhabited $ the (GT=LT) $
    rewrite sym prf in
    rewrite sym aux in
    compareContSpec p q GT
  where
  aux : thenCompare (p `compare` q) GT = LT
  aux = rewrite pltq in Refl

compareContGtGtFro : (p, q : Bip) -> p `Ge` q -> bipCompare p q GT = GT
compareContGtGtFro p q = rewrite compareContSpec p q GT in
                         aux
  where
  aux : p `Ge` q -> thenCompare (p `compare` q) GT = GT
  aux prf with (p `compare` q)
    aux prf | LT = absurd $ prf Refl
    aux prf | EQ = Refl
    aux prf | GT = Refl

-- compare_xO_xO is trivial
-- compare_xI_xI is trivial

-- compare_xI_xO

compareXIXO : (p, q : Bip) -> I p `compare` O q = thenCompare (p `compare` q) GT
compareXIXO p q = compareContSpec p q GT

-- compare_xO_xI

compareXOXI : (p, q : Bip) -> O p `compare` I q = thenCompare (p `compare` q) LT
compareXOXI p q = compareContSpec p q LT

-- mask2cmp
public export
mask2cmp : (p : Bim) -> Ordering
mask2cmp  BimO    = EQ
mask2cmp (BimP _) = GT
mask2cmp  BimM    = LT

-- compare_sub_mask

bimDCmp : (p : Bim) -> mask2cmp (bimD p) = mask2cmp p
bimDCmp  BimO    = Refl
bimDCmp (BimP _) = Refl
bimDCmp  BimM    = Refl

compareSubMask : (p, q : Bip) -> p `compare` q = mask2cmp (bimMinus p q)
compareSubMask  U     U    = Refl
compareSubMask  U    (O _) = Refl
compareSubMask  U    (I _) = Refl
compareSubMask (O _)  U    = Refl
compareSubMask (O a) (O b) = rewrite bimDCmp (bimMinus a b) in
                             compareSubMask a b
compareSubMask (O a) (I b) =
  rewrite subMaskCarrySpec a b in
  rewrite compareContSpec a b LT in
  rewrite compareSubMask a b in
  aux (bimMinus a b)
  where
  aux : (m : Bim) -> thenCompare (mask2cmp m) LT = mask2cmp (bimDPO (bimPred m))
  aux  BimO    = Refl
  aux (BimP c) = rewrite dpoPredDouble (BimP c) in Refl
  aux  BimM    = Refl
compareSubMask (I _)  U    = Refl
compareSubMask (I a) (O b) =
  rewrite compareContSpec a b GT in
  rewrite compareSubMask a b in
  aux (bimMinus a b)
  where
  aux : (m : Bim) -> thenCompare (mask2cmp m) GT = mask2cmp (bimDPO m)
  aux  BimO    = Refl
  aux (BimP _) = Refl
  aux  BimM    = Refl
compareSubMask (I a) (I b) = rewrite bimDCmp (bimMinus a b) in
                             compareSubMask a b

-- lt_iff_add
-- TODO is split into `to` and `fro`

ltIffAddTo : (p, q : Bip) -> p `Lt` q -> (r ** p + r = q)
ltIffAddTo p q = rewrite compareSubMask p q in
                 aux
  where
  -- TODO Idris2 doesn't have a proper `proof` keyword
  aux : mask2cmp (bimMinus p q) = LT -> (r : Bip ** bipPlus p r = q)
  aux with (@@ (bimMinus p q))
    aux | (BimO  **pq) = rewrite pq in absurd
    aux | (BimP _**pq) = rewrite pq in absurd
    aux | (BimM  **pq) = const $ subMaskNegTo p q pq

ltIffAddFro : (p, q : Bip) -> (r ** p + r = q) -> p `Lt` q
ltIffAddFro p q rprf =
  rewrite compareSubMask p q in
  rewrite subMaskNegFro p q rprf in
  Refl

-- gt_iff_add
-- TODO is split into `to` and `fro`

gtIffAddTo : (p, q : Bip) -> p `Gt` q -> (r ** q + r = p)
gtIffAddTo p q = rewrite compareSubMask p q in
                 aux
  where
  -- TODO Idris2 doesn't have a proper `proof` keyword
  aux : mask2cmp (bimMinus p q) = GT -> (r : Bip ** q+r = p)
  aux with (@@ (bimMinus p q))
    aux | (BimO  **pq) = rewrite pq in absurd
    aux | (BimP r**pq) = const (r ** subMaskAdd p q r pq)
    aux | (BimM  **pq) = rewrite pq in absurd

gtIffAddFro : (p, q : Bip) -> (r ** q + r = p) -> p `Gt` q
gtIffAddFro p q (r**qrp) =
  rewrite compareSubMask p q in
  rewrite sym qrp in
  rewrite subMaskAddDiagL q r in
  Refl

-- compare_cont_refl

compareContRefl : (p : Bip) -> (c : Ordering) -> bipCompare p p c = c
compareContRefl  U    c = Refl
compareContRefl (O a) c = compareContRefl a c
compareContRefl (I a) c = compareContRefl a c

-- compare_cont_antisym

compareContAntisym : (p, q : Bip) -> (c : Ordering)
                  -> compareOp (bipCompare p q c) = bipCompare q p (compareOp c)
compareContAntisym  U     U    _ = Refl
compareContAntisym  U    (O _) _ = Refl
compareContAntisym  U    (I _) _ = Refl
compareContAntisym (O a)  U    _ = Refl
compareContAntisym (O a) (O b) c = compareContAntisym a b c
compareContAntisym (O a) (I b) _ = compareContAntisym a b LT
compareContAntisym (I _)  U    _ = Refl
compareContAntisym (I a) (O b) _ = compareContAntisym a b GT
compareContAntisym (I a) (I b) c = compareContAntisym a b c

-- compare_eq_iff
-- TODO is split into `to` and `fro`

compareEqIffTo : (p, q : Bip) -> p `compare` q = EQ -> p = q
compareEqIffTo p q = rewrite compareSubMask p q in
                     aux
  where
-- TODO Idris2 doesn't have a proper `proof` keyword
  aux : mask2cmp (bimMinus p q) = EQ -> p = q
  aux with (@@ (bimMinus p q))
    aux | (BimO  **pq) = const $ subMaskNulTo p q pq
    aux | (BimP _**pq) = rewrite pq in absurd
    aux | (BimM  **pq) = rewrite pq in absurd

compareEqIffFro : (p, q : Bip) -> p = q -> p `compare` q = EQ
compareEqIffFro p q prf =
  rewrite compareSubMask p q in
  rewrite subMaskNulFro p q prf in
  Refl

-- compare_antisym

compareAntisym : (p, q : Bip) -> q `compare` p = compareOp (p `compare` q)
compareAntisym p q = sym $ compareContAntisym p q EQ

-- compare_lt_iff is trivial
-- compare_le_iff is trivial

-- gt_lt

gtLt : (p, q : Bip) -> p `Gt` q -> q `Lt` p
gtLt p q pgtq =
  rewrite compareAntisym p q in
  rewrite pgtq in
  Refl

-- lt_gt

ltGt : (p, q : Bip) -> p `Lt` q -> q `Gt` p
ltGt p q pltq =
  rewrite compareAntisym p q in
  rewrite pltq in
  Refl

-- ge_le

geLe : (p, q : Bip) -> p `Ge` q -> q `Le` p
geLe p q = rewrite compareAntisym p q in
           aux
  where
  aux : p `Ge` q -> Not (compareOp (p `compare` q) = GT)
  aux pgeq prf with (p `compare` q)
    aux pgeq prf | LT = pgeq Refl
    aux pgeq prf | EQ = uninhabited prf
    aux pgeq prf | GT = pgeq $ sym prf

-- le_ge

leGe : (p, q : Bip) -> p `Le` q -> q `Ge` p
leGe p q = rewrite compareAntisym p q in
           aux
  where
  aux : p `Le` q -> Not (compareOp (p `compare` q) = LT)
  aux pleq prf with (p `compare` q)
    aux pleq prf | LT = pleq $ sym prf
    aux pleq prf | EQ = uninhabited prf
    aux pleq prf | GT = pleq Refl

-- le_1_l

le1L : (p : Bip) -> U `Le` p
le1L  U    = uninhabited
le1L (O _) = uninhabited
le1L (I _) = uninhabited

-- nlt_1_r

nlt1R : (p : Bip) -> Not (p `Lt` U)
nlt1R  U    = uninhabited
nlt1R (O _) = uninhabited
nlt1R (I _) = uninhabited

-- compare_succ_r

compareSuccR : (p, q : Bip)
            -> thenCompare (p `compare` bipSucc q) GT = thenCompare (p `compare` q) LT
compareSuccR  U     U    = Refl
compareSuccR  U    (O _) = Refl
compareSuccR  U    (I _) = Refl
compareSuccR (O a)  U    = rewrite sym $ compareContSpec a U GT in
                           compareContGtGtFro a U $ leGe U a $ le1L a
compareSuccR (O a) (O b) = rewrite sym $ compareContSpec a b LT in
                           thenCompareLT a b
compareSuccR (O a) (I b) = rewrite compareSuccR a b in
                           rewrite sym $ compareContSpec a b LT in
                           sym $ thenCompareLT a b
compareSuccR (I a)  U    = rewrite compareContGtGtFro a U $ leGe U a $ le1L a in
                           Refl
compareSuccR (I a) (O b) = rewrite sym $ compareContSpec a b GT in
                           sym $ thenCompareGT a b
compareSuccR (I a) (I b) = rewrite sym $ compareSuccR a b in
                           rewrite sym $ compareContSpec a (bipSucc b) GT in
                           thenCompareGT a (bipSucc b)

-- compare_succ_l

compareSuccL : (p, q : Bip)
            -> thenCompare (bipSucc p `compare` q) LT = thenCompare (p `compare` q) GT
compareSuccL p q =
  rewrite sym $ compareContSpec (bipSucc p) q LT in
  rewrite sym $ compareContSpec p q GT in
  compareOpInj (bipCompare (bipSucc p) q LT) (bipCompare p q GT) $
    rewrite compareContAntisym p q GT in
    rewrite compareContAntisym (bipSucc p) q LT in
    rewrite compareContSpec q p LT in
    rewrite compareContSpec q (bipSucc p) GT in
    compareSuccR q p

-- lt_succ_r
-- TODO is split into `to` and `fro`

ltSuccRTo : (p, q : Bip) -> p `Lt` bipSucc q -> p `Le` q
ltSuccRTo p q pltsq =
  aux $ replace {p = \x => thenCompare x GT = thenCompare (p `compare` q) LT}
                pltsq (compareSuccR p q)
  where
  aux : LT = thenCompare (p `compare` q) LT -> p `Le` q
  aux prf prf1 with (p `compare` q)
    aux prf prf1 | LT = uninhabited prf1
    aux prf prf1 | EQ = uninhabited prf1
    aux prf prf1 | GT = uninhabited prf

ltSuccRFro : (p, q : Bip) -> p `Le` q -> p `Lt` bipSucc q
ltSuccRFro p q pleq = aux pleq $ compareSuccR p q
  where
  aux : p `Le` q -> thenCompare (p `compare` (bipSucc q)) GT = thenCompare (p `compare` q) LT
     -> p `compare` (bipSucc q) = LT
  aux pleq prf = ?wat0
-- with (bipCompare p q EQ)
--   aux pleq prf | LT with (bipCompare p (bipSucc q))
--      aux pleq prf | LT | LT = Refl
--      aux pleq prf | LT | EQ = absurd prf
--      aux pleq prf | LT | GT = absurd prf
--  aux pleq prf | EQ = ?wat01
--    --with (p `compare` (bipSucc q))
--    --  aux pleq prf | EQ | LT = Refl
--    --  aux pleq prf | EQ | EQ = absurd prf
--    --  aux pleq prf | EQ | GT = absurd prf
--  aux pleq prf | GT = absurd $ pleq Refl

-- lt_succ_diag_r

ltSuccDiagR : (p : Bip) -> p `Lt` bipSucc p
ltSuccDiagR p = ltIffAddFro p (bipSucc p) (U**add1R p)

-- compare_succ_succ

compareSuccSucc : (p, q : Bip) -> bipSucc p `compare` bipSucc q = p `compare` q
compareSuccSucc  U     U    = Refl
compareSuccSucc  U    (O b) = compareContLtLtFro U b $ le1L b
compareSuccSucc  U    (I b) = ltSuccRFro U b $ le1L b
compareSuccSucc (O a)  U    = compareContGtGtFro a U $ leGe U a $ le1L a
compareSuccSucc (O _) (O _) = Refl
compareSuccSucc (O a) (I b) =
  rewrite compareContSpec a (bipSucc b) GT in
  rewrite compareSuccR a b in
  sym $ compareContSpec a b LT
compareSuccSucc (I a)  U    = aux $ leGe U (bipSucc a) $ le1L (bipSucc a)
  where
  -- TODO Idris2 doesn't have a proper `proof` keyword
  aux : Not ((bipSucc a) `compare` U = LT) -> (bipSucc a) `compare` U = GT
  aux with (@@ ((bipSucc a) `compare` U))
    aux | (LT**sau) = rewrite sau in \ctra => absurd $ ctra Refl
    aux | (EQ**sau) = absurd $ succNotU a $ compareEqIffTo (bipSucc a) U sau
    aux | (GT**sau) = const sau
compareSuccSucc (I a) (O b) =
  rewrite compareContSpec (bipSucc a) b LT in
  rewrite compareContSpec a b GT in
  compareSuccL a b
compareSuccSucc (I a) (I b) = compareSuccSucc a b

-- lt_1_succ

lt1Succ : (p : Bip) -> U `Lt` bipSucc p
lt1Succ p = ltSuccRFro U p $ le1L p

-- le_nlt is just leGe / geLe

-- lt_le_incl

ltLeIncl : (p, q : Bip) -> p `Lt` q -> p `Le` q
ltLeIncl p q pltq pgtq with (p `compare` q)
  ltLeIncl p q pltq pgtq | LT = uninhabited pgtq
  ltLeIncl p q pltq pgtq | EQ = uninhabited pgtq
  ltLeIncl p q pltq pgtq | GT = uninhabited pltq

-- lt_nle
-- TODO is split into `to` and `fro`
ltNleTo : (p, q : Bip) -> p `Lt` q -> Not (q `Le` p)
ltNleTo p q pltq qlep = qlep $ ltGt p q pltq

-- TODO Idris2 doesn't have a proper `proof` keyword
ltNleFro : (p, q : Bip) -> Not (q `Le` p) -> p `Lt` q
ltNleFro p q with (@@ (p `compare` q))
  ltNleFro p q | (LT**pq) = const pq
  ltNleFro p q | (EQ**pq) =
    rewrite compareEqIffTo p q pq in
    rewrite compareContRefl q EQ in
    \ctra => absurd $ ctra uninhabited
  ltNleFro p q | (GT**pq) =
    let pleq = ltLeIncl q p $ gtLt p q pq in
    \ctra => absurd $ ctra pleq

-- lt_lt_succ

ltLtSucc : (p, q : Bip) -> p `Lt` q -> p `Lt` bipSucc q
ltLtSucc p q = ltSuccRFro p q . ltLeIncl p q

-- succ_lt_mono
-- TODO is split into `to` and `fro`

succLtMonoTo : (p, q : Bip) -> p `Lt` q -> bipSucc p `Lt` bipSucc q
succLtMonoTo p q pltq = rewrite compareSuccSucc p q in
                        pltq

succLtMonoFro : (p, q : Bip) -> bipSucc p `Lt` bipSucc q -> p `Lt` q
succLtMonoFro p q spltsq = rewrite sym $ compareSuccSucc p q in
                           spltsq

-- succ_le_mono
-- TODO is split into `to` and `fro`

succLeMonoTo : (p, q : Bip) -> p `Le` q -> bipSucc p `Le` bipSucc q
succLeMonoTo p q pleq = rewrite compareSuccSucc p q in
                        pleq

succLeMonoFro : (p, q : Bip) -> bipSucc p `Le` bipSucc q -> p `Le` q
succLeMonoFro p q splesq = rewrite sym $ compareSuccSucc p q in
                           splesq

-- lt_trans

ltTrans : (p, q, r : Bip) -> p `Lt` q -> q `Lt` r -> p `Lt` r
ltTrans p q r pltq qltr =
   let (r1 ** prf1) = ltIffAddTo p q pltq
       (r2 ** prf2) = ltIffAddTo q r qltr in
     ltIffAddFro p r (r1+r2 ** rewrite addAssoc p r1 r2 in
                               rewrite prf1 in
                               prf2)

-- TODO lt_ind, how useful is it?
-- TODO lt_strorder
-- TODO lt_compat

-- TODO Idris2 doesn't have a proper `proof` keyword
leLtOrEq : (p, q : Bip) -> p `Le` q -> Either (p `Lt` q) (p=q)
leLtOrEq p q with (@@ (p `compare` q))
  leLtOrEq p q | (LT**pq) = const $ Left pq
  leLtOrEq p q | (EQ**pq) = const $ Right $ compareEqIffTo p q pq
  leLtOrEq p q | (GT**pq) = rewrite pq in \ctra => absurd $ ctra Refl

-- lt_total
-- TODO Idris2 doesn't have a proper `proof` keyword
ltTotal : (p, q : Bip) -> Either (Either (p `Lt` q) (q `Lt` p)) (p = q)
ltTotal p q with (@@ (p `compare` q))
  ltTotal p q | (LT**pq) = Left $ Left pq
  ltTotal p q | (EQ**pq) = Right $ compareEqIffTo p q pq
  ltTotal p q | (GT**pq) = Left $ Right $ gtLt p q pq

-- le_refl

leRefl : (p : Bip) -> p `Le` p
leRefl p = rewrite compareContRefl p EQ in
           uninhabited

-- le_lt_trans
-- TODO Idris2 doesn't have a proper `proof` keyword
leLtTrans : (p, q, r : Bip) -> p `Le` q -> q `Lt` r -> p `Lt` r
leLtTrans p q r with (@@ (p `compare` q))
  leLtTrans p q r | (LT**pq) = \_, qltr => ltTrans p q r pq qltr
  leLtTrans p q r | (EQ**pq) = \_, qltr => rewrite compareEqIffTo p q pq in qltr
  leLtTrans p q r | (GT**pq) = rewrite pq in \ctra => absurd $ ctra Refl

-- le_trans
-- TODO Idris2 doesn't have a proper `proof` keyword
leTrans : (p, q, r : Bip) -> p `Le` q -> q `Le` r -> p `Le` r
leTrans p q r pleq with (@@ (q `compare` r))
  leTrans p q r pleq | (LT**qr) = \_, pgtr => uninhabited $ the (GT=LT) $
                                              rewrite sym pgtr in
                                              leLtTrans p q r pleq qr
  leTrans p q r pleq | (EQ**qr) = \_, pgtr => pleq $ rewrite compareEqIffTo q r qr in
                                                     pgtr
  leTrans p q r pleq | (GT**qr) = rewrite qr in \ctra => absurd $ ctra Refl

-- le_succ_l
-- TODO is split into `to` and `fro`

leSuccLTo : (p, q : Bip) -> bipSucc p `Le` q -> p `Lt` q
leSuccLTo p q = succLtMonoFro p q . ltSuccRFro (bipSucc p) q

leSuccLFro : (p, q : Bip) -> p `Lt` q -> bipSucc p `Le` q
leSuccLFro p q = ltSuccRTo (bipSucc p) q . succLtMonoTo p q

-- le_antisym
-- TODO Idris2 doesn't have a proper `proof` keyword
leAntisym : (p, q : Bip) -> p `Le` q -> q `Le` p -> p = q
leAntisym p q with (@@ (p `compare` q))
  leAntisym p q | (LT**pq) = \_, qlep => absurd $ qlep $ ltGt p q pq
  leAntisym p q | (EQ**pq) = const $ const $ compareEqIffTo p q pq
  leAntisym p q | (GT**pq) = rewrite pq in \ctra => absurd $ ctra Refl

-- TODO le_preorder
-- TODO le_partorder

-- lt_add_diag_r

ltAddDiagR : (p, q : Bip) -> p `Lt` (p+q)
ltAddDiagR p q = ltIffAddFro p (p+q) (q**Refl)

-- add_compare_mono_l

addCompareMonoL : (p, q, r : Bip) -> (p+q) `compare` (p+r) = q `compare` r
addCompareMonoL p q r =
  peanoRect
    (\x => (x+q) `compare` (x+r) = q `compare` r)
    base
    (\s,sqsr => rewrite addSuccL s q in
                rewrite addSuccL s r in
                rewrite compareSuccSucc (s+q) (s+r) in
                sqsr)
    p
  where
    base : (U+q) `compare` (U+r) = q `compare` r
    base =
      rewrite add1L q in
      rewrite add1L r in
      compareSuccSucc q r

-- add_compare_mono_r

addCompareMonoR : (p, q, r : Bip) -> (q+p) `compare` (r+p) = q `compare` r
addCompareMonoR p q r =
  rewrite addComm q p in
  rewrite addComm r p in
  addCompareMonoL p q r

-- add_lt_mono_l
-- TODO is split into `to` and `fro`

addLtMonoLTo : (p, q, r : Bip) -> q `Lt` r -> (p+q) `Lt` (p+r)
addLtMonoLTo p q r qltr = rewrite addCompareMonoL p q r in
                          qltr

addLtMonoLFro : (p, q, r : Bip) -> (p+q) `Lt` (p+r) -> q `Lt` r
addLtMonoLFro p q r = rewrite addCompareMonoL p q r in
                      id

-- add_lt_mono_r
-- TODO is split into `to` and `fro`

addLtMonoRTo : (p, q, r : Bip) -> q `Lt` r -> (q+p) `Lt` (r+p)
addLtMonoRTo p q r qltr = rewrite addCompareMonoR p q r in
                          qltr

addLtMonoRFro : (p, q, r : Bip) -> (q+p) `Lt` (r+p) -> q `Lt` r
addLtMonoRFro p q r = rewrite addCompareMonoR p q r in
                      id

-- add_lt_mono

addLtMono : (p, q, r, s : Bip) -> p `Lt` q -> r `Lt` s -> (p+r) `Lt` (q+s)
addLtMono p q r s pltq rlts =
  let prqr = addLtMonoRTo r p q pltq
      qrqs = addLtMonoLTo q r s rlts in
    ltTrans (p+r) (q+r) (q+s) prqr qrqs

-- add_le_mono_l
-- TODO is split into `to` and `fro`

addLeMonoLTo : (p, q, r : Bip) -> q `Le` r -> (p+q) `Le` (p+r)
addLeMonoLTo p q r qler = rewrite addCompareMonoL p q r in
                          qler

addLeMonoLFro : (p, q, r : Bip) -> (p+q) `Le` (p+r) -> q `Le` r
addLeMonoLFro p q r = rewrite addCompareMonoL p q r in
                      id

-- add_le_mono_r
-- TODO is split into `to` and `fro`

addLeMonoRTo : (p, q, r : Bip) -> q `Le` r -> (q+p) `Le` (r+p)
addLeMonoRTo p q r qltr = rewrite addCompareMonoR p q r in
                          qltr

addLeMonoRFro : (p, q, r : Bip) -> (q+p) `Le` (r+p) -> q `Le` r
addLeMonoRFro p q r = rewrite addCompareMonoR p q r in
                      id

-- add_le_mono

addLeMono : (p, q, r, s : Bip) -> p `Le` q -> r `Le` s -> (p+r) `Le` (q+s)
addLeMono p q r s pltq rlts =
  let prqr = addLeMonoRTo r p q pltq
      qrqs = addLeMonoLTo q r s rlts in
    leTrans (p+r) (q+r) (q+s) prqr qrqs

-- mul_lt_mono_l
-- TODO is split into `to` and `fro`, intermixed with mul_compare_mono_l
mulLtMonoLTo : (p, q, r : Bip) -> q `Lt` r -> (p*q) `Lt` (p*r)
mulLtMonoLTo  U    _ _ qltr = qltr
mulLtMonoLTo (O a) q r qltr = mulLtMonoLTo a q r qltr
mulLtMonoLTo (I a) q r qltr =
  let ih = mulLtMonoLTo a q r qltr in
    addLtMono q r (O $ a*q) (O $ a*r) qltr ih

-- mul_compare_mono_l
-- TODO Idris2 doesn't have a proper `proof` keyword
mulCompareMonoL : (p, q, r : Bip) -> (p*q) `compare` (p*r) = q `compare` r
mulCompareMonoL  U    _ _ = Refl
mulCompareMonoL (O a) q r = mulCompareMonoL a q r
mulCompareMonoL (I a) q r with (@@ (q `compare` r))
  mulCompareMonoL (I a) q r | (LT**qr) =
    rewrite qr in
    let aqr = mulLtMonoLTo a q r qr in
    addLtMono q r (O $ a*q) (O $ a*r) qr aqr
  mulCompareMonoL (I a) q r | (EQ**qr) =
    rewrite qr in
    rewrite compareEqIffTo q r qr in
    compareContRefl (r+(O $ a*r)) EQ
  mulCompareMonoL (I a) q r | (GT**qr) =
    rewrite qr in
    let rltq = gtLt q r qr
        arq = mulLtMonoLTo a r q rltq
        mul = addLtMono r q (O $ a*r) (O $ a*q) rltq arq
    in
    ltGt (r+(O $ a*r)) (q+(O $ a*q)) mul

-- mul_lt_mono_l
-- TODO is split into `to` and `fro`, intermixed with mul_compare_mono_l
mulLtMonoLtFro : (p, q, r : Bip) -> (p*q) `Lt` (p*r) -> q `Lt` r
mulLtMonoLtFro p q r = rewrite mulCompareMonoL p q r in
                       id

-- mul_compare_mono_r

mulCompareMonoR : (p, q, r : Bip) -> (q*p) `compare` (r*p) = q `compare` r
mulCompareMonoR p q r =
  rewrite mulComm q p in
  rewrite mulComm r p in
  mulCompareMonoL p q r

-- mul_lt_mono_r
-- TODO is split into `to` and `fro`

mulLtMonoRTo : (p, q, r : Bip) -> q `Lt` r -> (q*p) `Lt` (r*p)
mulLtMonoRTo p q r qltr = rewrite mulCompareMonoR p q r in
                          qltr

mulLtMonoRFro : (p, q, r : Bip) -> (q*p) `Lt` (r*p) -> q `Lt` r
mulLtMonoRFro p q r = rewrite mulCompareMonoR p q r in
                      id

-- mul_lt_mono

mulLtMono : (p, q, r, s: Bip) -> p `Lt` q -> r `Lt` s -> (p*r) `Lt` (q*s)
mulLtMono p q r s pltq rlts =
  let prqr = mulLtMonoRTo r p q pltq
      qrqs = mulLtMonoLTo q r s rlts in
   ltTrans (p*r) (q*r) (q*s) prqr qrqs

-- mul_le_mono_l
-- TODO is split into `to` and `fro`

mulLeMonoLTo : (p, q, r : Bip) -> q `Le` r -> (p*q) `Le` (p*r)
mulLeMonoLTo p q r qler = rewrite mulCompareMonoL p q r in
                          qler

mulLeMonoLFro : (p, q, r : Bip) -> (p*q) `Le` (p*r) -> q `Le` r
mulLeMonoLFro p q r = rewrite mulCompareMonoL p q r in
                      id

-- mul_le_mono_r
-- TODO is split into `to` and `fro`

mulLeMonoRTo : (p, q, r : Bip) -> q `Le` r -> (q*p) `Le` (r*p)
mulLeMonoRTo p q r qler = rewrite mulCompareMonoR p q r in
                          qler

mulLeMonoRFro : (p, q, r : Bip) -> (q*p) `Le` (r*p) -> q `Le` r
mulLeMonoRFro p q r = rewrite mulCompareMonoR p q r in
                      id

-- mul_le_mono

mulLeMono : (p, q, r, s: Bip) -> p `Le` q -> r `Le` s -> (p*r) `Le` (q*s)
mulLeMono p q r s pltq rlts =
  let prqr = mulLeMonoRTo r p q pltq
      qrqs = mulLeMonoLTo q r s rlts in
    leTrans (p*r) (q*r) (q*s) prqr qrqs

-- lt_add_r looks identical to lt_add_diag_r

-- lt_not_add_l

ltNotSelf : (p : Bip) -> Not (p `Lt` p)
ltNotSelf  U    = uninhabited
ltNotSelf (O a) = ltNotSelf a
ltNotSelf (I a) = ltNotSelf a

ltNotAddL : (p, q : Bip) -> Not (p+q `Lt` p)
ltNotAddL p q pqltp =
  let pltpq = ltAddDiagR p q
      pltp = ltTrans p (p+q) p pltpq pqltp in
    ltNotSelf p pltp

-- sub_1_r

sub1R : (p : Bip) -> p - U = bipPred p
sub1R  U   = Refl
sub1R (O _) = Refl
sub1R (I _) = Refl

-- pred_sub is just sym . sub1R

-- A helper to "go back" if subtraction over-evaluates

subMono : {p, q, r, s : Bip} -> p = q -> r = s -> p-r = q-s
subMono pq rs = rewrite pq in rewrite rs in Refl

-- sub_succ_r

subSuccR : (p, q : Bip) -> p - (bipSucc q) = bipPred (p - q)
subSuccR p q = rewrite subMaskSuccR p q in
  rewrite subMaskCarrySpec p q in
  aux (bimMinus p q)
  where
  aux : (m : Bim) -> bipMinusHelp (bimPred m) = bipPred (bipMinusHelp m)
  aux  BimO        = Refl
  aux (BimP  U   ) = Refl
  aux (BimP (O _)) = Refl
  aux (BimP (I _)) = Refl
  aux  BimM        = Refl

-- sub_mask_pos'

subMaskPos' : (p, q : Bip) -> q `Lt` p
                          -> (r ** (bimMinus p q = BimP r, q + r = p))
subMaskPos' p q qltp =
  let (r ** prf) = ltIffAddTo q p qltp
  in (r ** (rewrite sym prf in subMaskAddDiagL q r, prf))

-- sub_mask_pos

subMaskPos : (p, q : Bip) -> q `Lt` p -> (r ** bimMinus p q = BimP r)
subMaskPos p q qltp =
  let (r ** prf) = ltIffAddTo q p qltp
  in (r ** rewrite sym prf in subMaskAddDiagL q r)

-- sub_add

subAdd : (p, q : Bip) -> q `Lt` p -> (p-q)+q = p
subAdd p q qltp with (subMaskPos p q qltp)
  subAdd p q qltp | (r ** pmqr) = rewrite pmqr in
                                  rewrite addComm r q in
                                  subMaskAdd p q r pmqr

subInverse : (p, q, r : Bip) -> r `Lt` p -> p - r = q -> p = q + r
subInverse p q r rltp prq =
  rewrite sym $ subAdd p r rltp in
  cong (\x=>x+r) prq

-- add_sub

addSub : (p, q : Bip) -> (p+q)-q = p
addSub p q = rewrite addComm p q in
             rewrite subMaskAddDiagL q p in
             Refl

-- mul_sub_distr_l

mulSubDistrL : (p, q, r : Bip) -> r `Lt` q -> p * (q-r) = p*q - p*r
mulSubDistrL p q r rltq =
  addRegR (p * (q-r)) (p*q - p*r) (p*r) $
  rewrite subAdd (p*q) (p*r) $
            rewrite mulCompareMonoL p r q in rltq
          in
  rewrite sym $ mulAddDistrL p (q-r) r in
  rewrite subAdd q r rltq in
  Refl

-- mul_sub_distr_r

mulSubDistrR : (p, q, r : Bip) -> q `Lt` p -> (p-q)*r = p*r-q*r
mulSubDistrR p q r qltp =
  rewrite mulComm q r in
  rewrite mulComm p r in
  rewrite mulComm (p-q) r in
  mulSubDistrL r p q qltp

-- sub_lt_mono_l

gtNotSelf : (p : Bip) -> Not (p `Gt` p)
gtNotSelf  U    = uninhabited
gtNotSelf (O a) = gtNotSelf a
gtNotSelf (I a) = gtNotSelf a

subLtMonoL : (p, q, r : Bip) -> q `Lt` p -> p `Lt` r -> (r-p) `Lt` (r-q)
subLtMonoL p q r qltp pltr = addLtMonoRFro p (r-p) (r-q) $
   rewrite subAdd r p pltr in
   leLtTrans r ((r-q)+q) ((r-q)+p)
     (rewrite subAdd r q (ltTrans q p r qltp pltr) in gtNotSelf r)
     (addLtMonoLTo (r-q) q p qltp)

-- sub_compare_mono_l
-- TODO Idris2 doesn't have a proper `proof` keyword
subCompareMonoL : (p, q, r : Bip) -> q `Lt` p -> r `Lt` p
                                 -> (p-q) `compare` (p-r) = r `compare` q
subCompareMonoL p q r qltp rltp with (@@ (r `compare` q))
  subCompareMonoL p q r qltp rltp | (LT**rq) = rewrite rq in
                                               subLtMonoL q r p rq qltp
  subCompareMonoL p q r qltp rltp | (EQ**rq) = rewrite rq in
                                               rewrite compareEqIffTo r q rq in
                                               compareContRefl (p-q) EQ
  subCompareMonoL p q r qltp rltp | (GT**rq) = rewrite rq in
                                               ltGt (p-r) (p-q) $ subLtMonoL r q p (gtLt r q rq) rltp

-- sub_compare_mono_r

subCompareMonoR : (p, q, r : Bip) -> p `Lt` q -> p `Lt` r
                                 -> (q-p) `compare` (r-p) = q `compare` r
subCompareMonoR p q r pltq pltr =
  rewrite sym $ addCompareMonoR p (q-p) (r-p) in
  rewrite subAdd q p pltq in
  rewrite subAdd r p pltr in
  Refl

-- sub_lt_mono_r

subLtMonoR : (p, q, r : Bip) -> q `Lt` p -> r `Lt` q -> q-r `Lt` p-r
subLtMonoR p q r qltp rltq =
  rewrite subCompareMonoR r q p rltq (ltTrans r q p rltq qltp) in
  qltp

-- sub_decr

subDecr : (p, q : Bip) -> q `Lt` p -> (p-q) `Lt` p
subDecr p q qltp = addLtMonoRFro q (p-q) p $
  rewrite subAdd p q qltp in
  ltAddDiagR p q

-- add_sub_assoc

addSubAssoc : (p, q, r : Bip) -> r `Lt` q -> p+(q-r) = p+q-r
addSubAssoc p q r rltq = addRegR (p+(q-r)) (p+q-r) r $
  rewrite sym $ addAssoc p (q-r) r in
  rewrite subAdd q r rltq in
  rewrite subAdd (p+q) r $
            ltTrans r q (p+q) rltq $
              rewrite addComm p q in
              ltAddDiagR q p
  in Refl

-- sub_add_distr

subAddDistr : (p, q, r : Bip) -> q+r `Lt` p -> p-(q+r) = p-q-r
subAddDistr p q r qrltp =
  rewrite addComm q r in
    addRegR (p-(r+q)) (p-q-r) (r+q) $
      rewrite subAdd p (r+q) rqltp in
      rewrite addAssoc ((p-q)-r) r q in
      rewrite subAdd (p-q) r $
                addLtMonoRFro q r (p-q) $
                  rewrite subAdd p q qltp in
                  rqltp
      in sym $ subAdd p q qltp
  where
    qltp : q `Lt` p
    qltp = ltTrans q (q+r) p (ltAddDiagR q r) qrltp
    rqltp : r+q `Lt` p
    rqltp = rewrite addComm r q in qrltp

--  sub_sub_distr

subSubDistr : (p, q, r : Bip) -> r `Lt` q -> q-r `Lt` p -> p-(q-r) = p+r-q
subSubDistr p q r rltq qrltp =
  addRegR (p-(q-r)) (p+r-q) ((q-r)+r) $
    rewrite addAssoc (p-(q-r)) (q-r) r in
    rewrite subAdd p (q-r) qrltp in
    rewrite subAdd q r rltq in
    sym $ subAdd (p+r) q $
      rewrite sym $ subCompareMonoR r q (p+r) rltq $
                rewrite addComm p r in ltAddDiagR r p in
      rewrite addSub p r in
      qrltp

-- sub_xO_xO

subXOXO : (p, q : Bip) -> q `Lt` p -> (O p) - (O q) = O (p-q)
subXOXO p q qltp = rewrite snd $ subMaskPos p q qltp in
                   Refl

-- sub_xI_xI

subXIXI : (p, q : Bip) -> q `Lt` p -> (I p) - (I q) = O (p-q)
subXIXI p q qltp = rewrite snd $ subMaskPos p q qltp in
                   Refl

-- sub_xI_xO

subXIXO : (p, q : Bip) -> q `Lt` p -> (I p) - (O q) = I (p-q)
subXIXO p q qltp = rewrite snd $ subMaskPos p q qltp in
                   Refl

-- sub_xO_xI

subXOXI : (p, q : Bip) -> (O p) - (I q) = bipDMO (p-q)
subXOXI p q = rewrite subMaskCarrySpec p q in
              aux
  where
  aux : bipMinusHelp (bimDPO (bimPred (bimMinus p q))) = bipDMO (p-q)
  aux with (bimMinus p q)
    aux | BimO   = Refl
    aux | BimP a = rewrite dpoPredDouble (BimP a) in Refl
    aux | BimM   = Refl

-- sub_mask_neg_iff'
-- TODO is split into `to` and `fro`, fro case = sub_mask_neg

subMaskNegTo' : (p, q : Bip) -> bimMinus p q = BimM -> p `Lt` q
subMaskNegTo' p q = ltIffAddFro p q . subMaskNegTo p q

subMaskNeg : (p, q : Bip) -> p `Lt` q -> bimMinus p q = BimM
subMaskNeg p q = subMaskNegFro p q . ltIffAddTo p q

-- sub_le
-- TODO Idris2 doesn't have a proper `proof` keyword
subLe : (p, q : Bip) -> p `Le` q -> p-q = U
subLe p q pleq with (@@ (bimMinus p q))
  subLe p q pleq | (BimO  **pq) = rewrite pq in Refl
  subLe p q pleq | (BimP a**pq) =
    let qltp = ltGt q p $ ltIffAddFro q p (a**subMaskAdd p q a pq)
    in absurd $ pleq qltp
  subLe p q pleq | (BimM  **pq) = rewrite pq in Refl

-- sub_lt

subLt : (p, q : Bip) -> p `Lt` q -> p-q = U
subLt p q = subLe p q . ltLeIncl p q

-- sub_diag

subDiag : (p : Bip) -> p-p = U
subDiag p = rewrite subMaskDiag p in
            Refl

-- size_nat_monotone

sizeNatMonotone : (p, q : Bip) -> p `Lt` q -> bipDigitsNat p `LTE` bipDigitsNat q
sizeNatMonotone  p     U    pltq = absurd $ nlt1R p pltq
sizeNatMonotone  U    (O _) _    = LTESucc LTEZero
sizeNatMonotone  U    (I _) _    = LTESucc LTEZero
sizeNatMonotone (O a) (O b) pltq = LTESucc $ sizeNatMonotone a b pltq
sizeNatMonotone (O a) (I b) pltq = LTESucc aux
  where
-- TODO Idris2 doesn't have a proper `proof` keyword
  aux : bipDigitsNat a `LTE` bipDigitsNat b
  aux with (@@ (a `compare` b))
    aux | (LT**ab) = sizeNatMonotone a b ab
    aux | (EQ**ab) = rewrite compareEqIffTo a b ab in
                     lteRefl
    aux | (GT**ab) = absurd $ compareContLtLtTo a b pltq ab
sizeNatMonotone (I a) (O b) pltq = LTESucc $ sizeNatMonotone a b $
                                             compareContGtLtTo a b pltq
sizeNatMonotone (I a) (I b) pltq = LTESucc $ sizeNatMonotone a b pltq

-- max_l
-- TODO Idris2 doesn't have a proper `proof` keyword
maxL : (p, q : Bip) -> q `Le` p -> max p q = p
maxL p q qlep with (@@ (p `compare` q))
  maxL p q qlep | (LT**pq) = rewrite pq in absurd $ qlep $ ltGt p q pq
  maxL p q qlep | (EQ**pq) = rewrite pq in sym $ compareEqIffTo p q pq
  maxL p q qlep | (GT**pq) = rewrite pq in Refl

-- max_r

maxR : (p, q : Bip) -> p `Le` q -> max p q = q
maxR p q pleq with (p `compare` q)
  maxR p q pleq | LT = Refl
  maxR p q pleq | EQ = Refl
  maxR p q pleq | GT = absurd $ pleq Refl

-- min_l

minL : (p, q : Bip) -> p `Le` q -> min p q = p
minL p q pleq with (p `compare` q)
  minL p q pleq | LT = Refl
  minL p q pleq | EQ = Refl
  minL p q pleq | GT = absurd $ pleq Refl

-- min_r
-- TODO Idris2 doesn't have a proper `proof` keyword
minR : (p, q : Bip) -> q `Le` p -> min p q = q
minR p q qlep with (@@ (p `compare` q))
  minR p q qlep | (LT**pq) = rewrite pq in absurd $ qlep $ ltGt p q pq
  minR p q qlep | (EQ**pq) = rewrite pq in compareEqIffTo p q pq
  minR p q qlep | (GT**pq) = rewrite pq in Refl

-- max_1_l

max1L : (p : Bip) -> max U p = p
max1L  U    = Refl
max1L (O _) = Refl
max1L (I _) = Refl

-- max_1_r

max1R : (p : Bip) -> max p U = p
max1R  U    = Refl
max1R (O _) = Refl
max1R (I _) = Refl

-- min_1_l

min1L : (p : Bip) -> min U p = U
min1L  U    = Refl
min1L (O _) = Refl
min1L (I _) = Refl

-- min_1_r

min1R : (p : Bip) -> min p U = U
min1R  U    = Refl
min1R (O _) = Refl
min1R (I _) = Refl

-- distributivity with monotone functions
-- TODO Idris2 doesn't have a proper `proof` keyword
maxMonotone : (f : Bip -> Bip) ->
              ((a, b : Bip) -> (a `Le` b) -> (f a `Le` f b)) ->
              (x, y : Bip) -> max (f x) (f y) = f (max x y)
maxMonotone f fle x y with (@@ (x `compare` y))
  maxMonotone f fle x y | (LT**xy) =
      rewrite xy in
      case leLtOrEq (f x) (f y) $ fle x y $ ltLeIncl x y xy of
      Left fxlty => rewrite fxlty in Refl
      Right fxeqy => rewrite fxeqy in
                     rewrite compareContRefl (f y) EQ in
                     Refl
  maxMonotone f fle x y | (EQ**xy) =
    rewrite xy in
    rewrite compareEqIffTo x y xy in
    rewrite compareContRefl (f y) EQ in
    Refl
  maxMonotone f fle x y | (GT**xy) =
    rewrite xy in
    case leLtOrEq (f y) (f x) $ fle y x $ ltLeIncl y x $ gtLt x y xy of
      Left fyltx => rewrite ltGt (f y) (f x) fyltx in Refl
      Right fxeqy => rewrite fxeqy in
                     rewrite compareContRefl (f x) EQ in
                     Refl

-- TODO Idris2 doesn't have a proper `proof` keyword
minMonotone : (f : Bip -> Bip) ->
              ((a, b : Bip) -> (a `Le` b) -> (f a `Le` f b)) ->
              (x, y : Bip) -> min (f x) (f y) = f (min x y)
minMonotone f fle x y with (@@ (x `compare` y))
  minMonotone f fle x y | (LT**xy) =
    rewrite xy in
    case leLtOrEq (f x) (f y) $ fle x y (ltLeIncl x y xy) of
      Left fxlty => rewrite fxlty in Refl
      Right fxeqy => rewrite fxeqy in
                    rewrite compareContRefl (f y) EQ in
                    Refl
  minMonotone f fle x y | (EQ**xy) =
    rewrite xy in
    rewrite compareEqIffTo x y xy in
    rewrite compareContRefl (f y) EQ in
    Refl
  minMonotone f fle x y | (GT**xy) =
    rewrite xy in
    case leLtOrEq (f y) (f x) $ fle y x $ ltLeIncl y x $ gtLt x y xy of
      Left fyltx => rewrite ltGt (f y) (f x) fyltx in Refl
      Right fxeqy => rewrite fxeqy in
                    rewrite compareContRefl (f x) EQ in
                    Refl

-- succ_max_distr

succMaxDistr : (p, q : Bip) -> bipSucc (max p q) = max (bipSucc p) (bipSucc q)
succMaxDistr p q = sym $ maxMonotone bipSucc succLeMonoTo p q

-- succ_min_distr

succMinDistr : (p, q : Bip) -> bipSucc (min p q) = min (bipSucc p) (bipSucc q)
succMinDistr p q = sym $ minMonotone bipSucc succLeMonoTo p q

-- add_max_distr_l

addMaxDistrL : (p, q, r : Bip) -> max (r + p) (r + q) = r + max p q
addMaxDistrL p q r = maxMonotone (bipPlus r) (addLeMonoLTo r) p q

-- add_max_distr_r

addMaxDistrR : (p, q, r : Bip) -> max (p + r) (q + r) = max p q + r
addMaxDistrR p q r =
  rewrite addComm p r in
  rewrite addComm q r in
  rewrite addComm (max p q) r in
  maxMonotone (bipPlus r) (addLeMonoLTo r) p q

-- add_min_distr_l

addMinDistrL : (p, q, r : Bip) -> min (r + p) (r + q) = r + min p q
addMinDistrL p q r = minMonotone (bipPlus r) (addLeMonoLTo r) p q

-- add_min_distr_r

addMinDistrR : (p, q, r : Bip) -> min (p + r) (q + r) = min p q + r
addMinDistrR p q r =
  rewrite addComm p r in
  rewrite addComm q r in
  rewrite addComm (min p q) r in
  minMonotone (bipPlus r) (addLeMonoLTo r) p q

-- mul_max_distr_l

mulMaxDistrL : (p, q, r : Bip) -> max (r * p) (r * q) = r * max p q
mulMaxDistrL p q r = maxMonotone (bipMult r) (mulLeMonoLTo r) p q

-- mul_max_distr_r

mulMaxDistrR : (p, q, r : Bip) -> max (p * r) (q * r) = max p q * r
mulMaxDistrR p q r =
  rewrite mulComm p r in
  rewrite mulComm q r in
  rewrite mulComm (max p q) r in
  maxMonotone (bipMult r) (mulLeMonoLTo r) p q

-- mul_min_distr_l

mulMinDistrL : (p, q, r : Bip) -> min (r * p) (r * q) = r * min p q
mulMinDistrL p q r = minMonotone (bipMult r) (mulLeMonoLTo r) p q

-- mul_min_distr_r

mulMinDistrR : (p, q, r : Bip) -> min (p * r) (q * r) = min p q * r
mulMinDistrR p q r =
  rewrite mulComm p r in
  rewrite mulComm q r in
  rewrite mulComm (min p q) r in
  minMonotone (bipMult r) (mulLeMonoLTo r) p q

mutual
  ltO : (n : Bip) -> n `Lt` O n
  ltO  U    = Refl
  ltO (O a) = ltO a
  ltO (I a) = compareContGtLtFro a (I a) $ ltI a

  ltI : (n : Bip) -> n `Lt` I n
  ltI  U    = Refl
  ltI (O a) = compareContLtLtFro a (O a) $ ltLeIncl a (O a) $ ltO a
  ltI (I a) = ltI a

leDMO : (n : Bip) -> n `Le` bipDMO n
leDMO  U    = uninhabited
leDMO (O a) = leDMO a . compareContLtGtTo a (bipDMO a)
leDMO (I a) = ltLeIncl a (O a) $ ltO a
