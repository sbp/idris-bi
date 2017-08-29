module Data.Bip.Proofs

import Data.Bip

%access public export
%default total

%hide Prelude.Nat.GT
%hide Prelude.Nat.LT

-- Following PArith/BinPos.v

-- xI_succ_xO is trivial

-- succ_discr

succDiscr : (p : Bip) -> Not (p = bipSucc p)
succDiscr  U    = absurd
succDiscr (O _) = absurd
succDiscr (I _) = absurd

-- pred_double_spec is trivial

-- succ_pred_double

succPredDouble : (p : Bip) -> bipSucc (bipDMO p) = O p
succPredDouble  U    = Refl
succPredDouble (O a) = rewrite succPredDouble a in Refl
succPredDouble (I _) = Refl

-- pred_double_succ

predDoubleSucc : (p : Bip) -> bipDMO (bipSucc p) = I p
predDoubleSucc  U    = Refl
predDoubleSucc (O _) = Refl
predDoubleSucc (I a) = rewrite predDoubleSucc a in Refl

-- double_succ is trivial

-- pred_double_x0_discr

predDoubleODiscr : (p : Bip) -> Not ((bipDMO p) = (O p))
predDoubleODiscr  U    = absurd
predDoubleODiscr (O _) = absurd
predDoubleODiscr (I _) = absurd

-- succ_not_1

succNotU : (p : Bip) -> Not ((bipSucc p) = U)
succNotU  U    = absurd
succNotU (O _) = absurd
succNotU (I _) = absurd

-- pred_succ

predSucc : (p : Bip) -> bipPred (bipSucc p) = p
predSucc  U    = Refl
predSucc (O _) = Refl
predSucc (I a) = case a of
  U     => Refl
  (O _) => Refl
  (I b) => rewrite predSucc (I b) in Refl

-- succ_pred_or

succPredOr : (p : Bip) -> Either (p = U) ((bipSucc (bipPred p)) = p)
succPredOr  U    = Left Refl
succPredOr (O a) = case a of
  U     => Right Refl
  (O b) =>
    -- Either (O (O b) = U) (O (bipSucc (bipDMO b)) = O (O b))
    -- Cf. succPredDouble : (p: Bip) -> bipSucc (bipDMO p) = (O p)
    rewrite succPredDouble (O b) in
    Right Refl
  (I _) => Right Refl
succPredOr (I _) = Right Refl

-- succ_inj
||| Injectivity of successor
succInj : (p, q : Bip) -> bipSucc p = bipSucc q -> p = q
succInj  U     U    Refl = Refl
succInj  U    (O _) Refl impossible
succInj  U    (I a) prf  = absurd $ succNotU a (sym $ OInj prf)
succInj (O _)  U    prf  = absurd prf
succInj (O a) (O a) Refl = cong {f=O} Refl
succInj (O _) (I _) prf  = absurd prf
succInj (I a)  U    prf  = absurd $ succNotU a (OInj prf)
succInj (I _) (O _) prf  = absurd prf
succInj (I a) (I b) prf  = cong $ succInj a b (OInj prf)

-- pred_N_succ

predBinSucc : (p : Bip) -> bipPredBin (bipSucc p) = BinP p
predBinSucc  U    = Refl
predBinSucc (O _) = Refl
predBinSucc (I a) = cong $ predDoubleSucc a

-- add_1_r

add1R : (p : Bip) -> p + U = bipSucc p
add1R  U    = Refl
add1R (O _) = Refl
add1R (I _) = Refl

-- add_1_l

add1L : (p : Bip) -> U + p = bipSucc p
add1L  U    = Refl
add1L (O _) = Refl
add1L (I _) = Refl

-- add_carry_spec

addCarrySpec : (p, q : Bip) -> bipCarry p q = bipSucc (p + q)
addCarrySpec  U     U    = Refl
addCarrySpec  U    (O _) = Refl
addCarrySpec  U    (I _) = Refl
addCarrySpec (O _)  U    = Refl
addCarrySpec (O _) (O _) = Refl
addCarrySpec (O a) (I b) = cong $ addCarrySpec a b
addCarrySpec (I _)  U    = Refl
addCarrySpec (I a) (O b) = cong $ addCarrySpec a b
addCarrySpec (I _) (I _) = Refl

-- add_comm
||| Commutativity
addComm : (p, q : Bip) -> p + q = q + p
addComm  p     U    = rewrite add1R p in
                      rewrite add1L p in Refl
addComm  U     q    = rewrite add1R q in
                      rewrite add1L q in Refl
addComm (O a) (O b) = cong $ addComm a b
addComm (I a) (O b) = cong $ addComm a b
addComm (O a) (I b) = cong $ addComm a b
addComm (I a) (I b) = rewrite addCarrySpec a b in
                      rewrite addCarrySpec b a in
                      cong {f = O . bipSucc} $ addComm a b

-- add_succ_r

addSuccR : (p, q : Bip) -> p + bipSucc q = bipSucc (p + q)
addSuccR  U     q    = rewrite add1L (bipSucc q) in
                       rewrite add1L q in Refl
addSuccR (O a)  U    = cong $ add1R a
addSuccR (I a)  U    = cong $ add1R a
addSuccR (O _) (O _) = Refl
addSuccR (I a) (O b) = cong $ addCarrySpec a b
addSuccR (O a) (I b) = cong $ addSuccR a b
addSuccR (I a) (I b) = rewrite addCarrySpec a b in
                       cong $ addSuccR a b

-- add_succ_l

addSuccL : (p, q : Bip) -> bipSucc p + q = bipSucc (p + q)
addSuccL p q =
  rewrite addComm (bipSucc p) q in
  rewrite addComm p q in
  addSuccR q p

-- add_no_neutral
||| No neutral elements for addition
addNoNeutral : (p, q : Bip) -> Not (q + p = p)
addNoNeutral  p     U    = rewrite add1L p in succDiscr p . sym
addNoNeutral  U    (O _) = uninhabited
addNoNeutral (O a) (O b) = addNoNeutral a b . OInj
addNoNeutral (I a) (O b) = addNoNeutral a b . IInj
addNoNeutral  U    (I _) = uninhabited
addNoNeutral (O _) (I _) = uninhabited
addNoNeutral (I _) (I _) = uninhabited

--- add_carry_add

addCarryAdd : (p, q, r, s : Bip) -> bipCarry p r = bipCarry q s -> p + r = q + s
addCarryAdd p q r s =
  rewrite addCarrySpec p r in
  rewrite addCarrySpec q s in
  succInj (p+r) (q+s)

-- add_reg_r
-- TODO this can probably be simplified
addRegR : (p, q, r : Bip) -> p + r = q + r -> p = q
addRegR  p     q     U    = rewrite add1R p in
                            rewrite add1R q in
                            succInj p q

addRegR (O _)  U    (O _) = absurd
addRegR (O _)  U    (I _) = absurd
addRegR (I a)  U    (O c) = absurd . addNoNeutral c a . IInj
addRegR (I a)  U    (I c) =
  rewrite addCarrySpec a c in
  absurd . addNoNeutral c a . succInj (a+c) c . OInj

addRegR  U    (O _) (O _) = absurd
addRegR  U    (O _) (I _) = absurd
addRegR  U    (I b) (O c) = absurd . addNoNeutral c b . sym . IInj
addRegR  U    (I b) (I c) =
  rewrite addCarrySpec b c in
  absurd . addNoNeutral c b . sym . succInj c (b+c) . OInj

addRegR (O _) (I _) (O _) = absurd
addRegR (O _) (I _) (I _) = absurd
addRegR (I _) (O _) (O _) = absurd
addRegR (I _) (O _) (I _) = absurd

addRegR  U     U    _     = const Refl
addRegR (O a) (O b) (O c) = cong . addRegR a b c . OInj
addRegR (O a) (O b) (I c) = cong . addRegR a b c . IInj
addRegR (I a) (I b) (O c) = cong . addRegR a b c . IInj
addRegR (I a) (I b) (I c) =
  rewrite addCarrySpec a c in
  rewrite addCarrySpec b c in
  cong . addRegR a b c . succInj (a+c) (b+c) . OInj

-- add_reg_l

addRegL : (p, q, r : Bip) -> p + q = p + r -> q = r
addRegL p q r = rewrite addComm p q in
                rewrite addComm p r in
                addRegR q r p

-- there's no standard `<->` in Idris, only `Control.Isomorphism`
-- add_cancel_r
-- add_cancel_l

-- add_carry_reg_r

addCarryRegR : (p, q, r : Bip) -> bipCarry p r = bipCarry q r -> p = q
addCarryRegR p q r = addRegR p q r . addCarryAdd p q r r

-- add_carry_reg_l

addCarryRegL : (p, q, r : Bip) -> bipCarry p q = bipCarry p r -> q = r
addCarryRegL p q r = addRegL p q r . addCarryAdd p p q r

-- add_assoc
||| Addition is associative
addAssoc : (p, q, r : Bip) -> p + (q + r) = p + q + r
addAssoc  U     q     r    = rewrite add1L (q+r) in
                             rewrite add1L q in
                             sym $ addSuccL q r
addAssoc  p     U     r    = rewrite add1L r in
                             rewrite add1R p in
                             rewrite addSuccR p r in
                             sym $ addSuccL p r
addAssoc  p     q     U    = rewrite add1R (p+q) in
                             rewrite add1R q in
                             addSuccR p q
addAssoc (O a) (O b) (O c) = cong $ addAssoc a b c
addAssoc (O a) (O b) (I c) = cong $ addAssoc a b c
addAssoc (O a) (I b) (O c) = cong $ addAssoc a b c
addAssoc (O a) (I b) (I c) = rewrite addCarrySpec b c in
                             rewrite addCarrySpec (a+b) c in
                             rewrite addSuccR a (b+c) in
                             cong {f=O . bipSucc} $ addAssoc a b c
addAssoc (I a) (O b) (O c) = cong $ addAssoc a b c
addAssoc (I a) (O b) (I c) = rewrite addCarrySpec a (b+c) in
                             rewrite addCarrySpec (a+b) c in
                             cong {f=O . bipSucc} $ addAssoc a b c
addAssoc (I a) (I b) (O c) = rewrite addCarrySpec a (b+c) in
                             rewrite addCarrySpec a b in
                             rewrite addSuccL (a+b) c in
                             cong {f=O . bipSucc} $ addAssoc a b c
addAssoc (I a) (I b) (I c) = rewrite addCarrySpec a b in
                             rewrite addCarrySpec b c in
                             rewrite addSuccR a (b+c) in
                             rewrite addSuccL (a+b) c in
                             cong {f=I . bipSucc} $ addAssoc a b c

-- add_xO is trivial

-- add_xI_pred_double

addXIPredDouble : (p, q : Bip) -> O (p+q) = I p + bipDMO q
addXIPredDouble p q =
  rewrite aux p (bipDMO q) in
  rewrite succPredDouble q in
  Refl
  where
  aux : (p,q : Bip) -> I p + q = O p + bipSucc q
  aux p  U    = cong $ sym $ add1R p
  aux p (O _) = Refl
  aux p (I b) = rewrite addCarrySpec p b in
                cong $ sym $ addSuccR p b

-- add_xO_pred_double

addXOPredDouble : (p, q : Bip) -> bipDMO (p+q) = O p + bipDMO q
addXOPredDouble  p     U    = rewrite add1R p in
                              predDoubleSucc p
addXOPredDouble  U    (O b) = rewrite add1L (bipDMO b) in
                              cong $ sym $ succPredDouble b
addXOPredDouble (O a) (O b) = cong $ addXOPredDouble a b
addXOPredDouble (I a) (O b) = cong $ addXIPredDouble a b
addXOPredDouble  U    (I b) = cong $ predDoubleSucc b
addXOPredDouble (O _) (I _) = Refl
addXOPredDouble (I a) (I b) = rewrite addCarrySpec a b in
                              cong $ predDoubleSucc (a+b)

-- add_diag

addDiag : (p : Bip) -> p + p = O p
addDiag  U    = Refl
addDiag (O a) = cong $ addDiag a
addDiag (I a) =
  rewrite addCarrySpec a a in
  rewrite addDiag a in
  Refl

-- peano_rect

mutual
  peanoRect : (P : Bip -> Type) -> (a : P U) ->
              (f : (p : Bip) -> P p -> P (bipSucc p)) ->
              (p : Bip) -> P p
  peanoRect P a _  U    = a
  peanoRect P a f (O q) = peanoAux P a f q
  peanoRect P a f (I q) = f _ (peanoAux P a f q)

  peanoAux : (P : Bip -> Type) -> (a : P U) ->
             (f : (p : Bip) -> P p -> P (bipSucc p)) ->
             (p : Bip) -> P (O p)
  peanoAux P a f = peanoRect (P . O) (f _ a) (\_ => f _ . f _)

-- TODO rest of Peano?

-- mul_1_l is trivial

-- mul_1_r

mul1R : (p : Bip) -> p * U = p
mul1R  U    = Refl
mul1R (O a) = cong $ mul1R a
mul1R (I a) = cong $ mul1R a

-- mul_xO_r

mulXOR : (p, q : Bip) -> p * O q = O (p * q)
mulXOR  U    _ = Refl
mulXOR (O a) q = cong $ mulXOR a q
mulXOR (I a) q = cong {f=O . bipPlus q} $ mulXOR a q

-- mul_xI_r

mulXIR : (p, q : Bip) -> p * I q = p + O (p * q)
mulXIR  U    _ = Refl
mulXIR (O a) q = cong $ mulXIR a q
mulXIR (I a) q =
  rewrite addComm a (q + O (a * q)) in
  rewrite sym $ addAssoc q (O (a * q)) a in
  rewrite addComm (O (a * q)) a in
  cong {f=I . bipPlus q} $ mulXIR a q

-- mul_comm
||| Commutativity of multiplication
mulComm : (p, q : Bip) -> p * q = q * p
mulComm p  U    = mul1R p
mulComm p (O b) = rewrite mulXOR p b in
                  cong $ mulComm p b
mulComm p (I b) = rewrite mulXIR p b in
                  cong {f=bipPlus p . O} $ mulComm p b

-- mul_add_distr_l

addShuffle : (p, q, r, s : Bip) -> (p+q)+(r+s) = (p+r)+(q+s)
addShuffle p q r s =
  rewrite addAssoc (p+q) r s in
  rewrite sym $ addAssoc p q r in
  rewrite addComm q r in
  rewrite addAssoc p r q in
  rewrite sym $ addAssoc (p+r) q s in
  Refl

mulAddDistrL : (p, q, r : Bip) -> p * (q + r) = p * q + p * r
mulAddDistrL  U    _ _ = Refl
mulAddDistrL (O a) q r = cong $ mulAddDistrL a q r
mulAddDistrL (I a) q r =
  rewrite mulAddDistrL a q r in
  rewrite sym $ addShuffle q (O (a*q)) r (O (a*r)) in
  Refl

-- mul_add_distr_r

mulAddDistrR : (p, q, r : Bip) -> (p + q) * r = p * r + q * r
mulAddDistrR p q r =
  rewrite mulComm (p+q) r in
  rewrite mulComm p r in
  rewrite mulComm q r in
  mulAddDistrL r p q

-- mul_assoc
||| Associativity of multiplication
mulAssoc : (p, q, r : Bip) -> p * (q * r) = p * q * r
mulAssoc  U    _ _ = Refl
mulAssoc (O a) q r = cong $ mulAssoc a q r
mulAssoc (I a) q r = rewrite mulAddDistrR q (O (a*q)) r in
                     cong {f=bipPlus (q*r) . O} $ mulAssoc a q r

-- mul_succ_l

mulSuccL : (p, q : Bip) -> (bipSucc p) * q = q + p * q
mulSuccL  U    q = sym $ addDiag q
mulSuccL (O _) _ = Refl
mulSuccL (I a) q =
  rewrite mulSuccL a q in
  rewrite addAssoc q q (O (a*q)) in
  rewrite addDiag q in
  Refl

-- mul_succ_r

mulSuccR : (p, q : Bip) -> p * (bipSucc q) = p + p * q
mulSuccR p q =
  rewrite mulComm p (bipSucc q) in
  rewrite mulComm p q in
  mulSuccL q p

-- mul_xI_mul_xO_discr

addXONotXO : (p, q, r : Bip) -> Not (r+(O (p*r)) = O (q*r))
addXONotXO _ _  U    = uninhabited
addXONotXO p q (O c) = rewrite mulXOR p c in
                       rewrite mulXOR q c in
                       addXONotXO p q c . OInj
addXONotXO _ _ (I _) = uninhabited

-- TODO the one above seems more useful

mulXIMulXODiscr : (p, q, r : Bip) -> Not ((I p) * r = (O q) * r)
mulXIMulXODiscr p q  U    = rewrite mul1R (I p) in
                            rewrite mul1R (O q) in
                            uninhabited
mulXIMulXODiscr p q (O c) = rewrite mulXOR p c in
                            rewrite mulXOR q c in
                            addXONotXO p q c . OInj
mulXIMulXODiscr _ _ (I _) = uninhabited

-- mul_xO_discr

mulXODiscr : (p, q : Bip) -> Not (O p * q = q)
mulXODiscr _  U    = uninhabited
mulXODiscr p (O b) = rewrite mulComm p (O b) in
                     rewrite mulComm b p in
                     mulXODiscr p b . OInj
mulXODiscr _ (I _) = uninhabited

-- mul_reg_r

mulOneNeutral : (p, q : Bip) -> p*q = q -> p = U
mulOneNeutral  p     U    = rewrite mul1R p in id
mulOneNeutral  U     _    = const Refl
mulOneNeutral (O a) (O b) = absurd . mulXODiscr a (O b)
mulOneNeutral (O _) (I _) = absurd
mulOneNeutral (I a) (O b) = rewrite addComm b (a*(O b)) in
                            absurd . addNoNeutral b (a*(O b)) . OInj
mulOneNeutral (I a) (I b) = rewrite addComm b (a*(I b)) in
                            absurd . addNoNeutral b (a*(I b)) . IInj

mulRegR : (p, q, r : Bip) -> p * r = q * r -> p = q
mulRegR  p     U     r = mulOneNeutral p r
mulRegR  U     q     r = sym . mulOneNeutral q r . sym
mulRegR (O a) (O b)  r = cong . mulRegR a b r . OInj
mulRegR (I a) (I b)  r =
  cong . mulRegR a b r . OInj . addRegL r (O (a*r)) (O (b*r))
mulRegR (I a) (O b)  r = absurd . addXONotXO a b r
mulRegR (O a) (I b)  r = absurd . addXONotXO b a r . sym

-- mul_reg_l

mulRegL : (p, q, r : Bip) -> r * p = r * q -> p = q
mulRegL p q r =
  rewrite mulComm r p in
  rewrite mulComm r q in
  mulRegR p q r

-- mul_eq_1_l

mulEq1L : (p, q : Bip) -> p * q = U -> p = U
mulEq1L  U     _    Refl = Refl
mulEq1L (O _)  _    Refl impossible
mulEq1L (I _)  U    Refl impossible
mulEq1L (I _) (O _) Refl impossible
mulEq1L (I _) (I _) Refl impossible

-- mul_eq_1_r

mulEq1R : (p, q : Bip) -> p * q = U -> q = U
mulEq1R p q = rewrite mulComm p q in mulEq1L q p

-- square_xO

squareXO : (p : Bip) -> (O p) * (O p) = O (O (p*p))
squareXO p = cong $ mulXOR p p

-- square_xI

squareXI : (p : Bip) -> (I p) * (I p) = I (O (p*p + p))
squareXI p =
  rewrite mulXIR p p in
  rewrite addAssoc p p (O(p*p)) in
  rewrite addDiag p in
  cong {f=I . O} $ addComm p (p*p)

-- iter_swap_gen

iterSwapGen : {f : a -> b} -> {g : a -> a} -> {h : b -> b} ->
              ((x : a) -> f (g x) = h (f x)) ->
              (x : a) -> (p : Bip) -> (f (bipIter g x p)) = (bipIter h (f x) p)
iterSwapGen             fx x  U     = fx x
iterSwapGen {f} {g} {h} fx x (O b)  =
  rewrite sym $ iterSwapGen {f} {g} {h} fx x b in
  rewrite iterSwapGen {f} {g} {h} fx (bipIter g x b) b in
  Refl
iterSwapGen {f} {g} {h} fx x (I b) =
  rewrite sym $ iterSwapGen {f} {g} {h} fx x b in
  rewrite fx (bipIter g (bipIter g x b) b) in
  rewrite iterSwapGen {f} {g} {h} fx (bipIter g x b) b in
  Refl

-- iter_swap

iterSwap : (f : a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f (f x) p = f (bipIter f x p)
iterSwap f x p = sym $ iterSwapGen {f} {g=f} {h=f} (\_ => Refl) x p

-- iter_succ

iterSucc : (f : a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f x (bipSucc p) = f (bipIter f x p)
iterSucc _ _  U    = Refl
iterSucc _ _ (O _) = Refl
iterSucc f x (I a) =
  rewrite iterSucc f x a in
  rewrite iterSwap f (bipIter f x a) (bipSucc a) in
  rewrite iterSucc f (bipIter f x a) a in
  Refl

-- iter_add

iterAdd : (f : a -> a) -> (x: a) -> (p,q : Bip) ->
           bipIter f x (p+q) = bipIter f (bipIter f x q) p
iterAdd f x  U    q = rewrite add1L q in
                      iterSucc f x q
iterAdd f x (O a) q =
  rewrite sym $ iterAdd f x a q in
  rewrite sym $ iterAdd f x a (a+q) in
  rewrite addAssoc a a q in
  rewrite addDiag a in
  Refl
iterAdd f x (I a) q =
  rewrite sym $ iterAdd f x a q in
  rewrite sym $ iterAdd f x a (a+q) in
  rewrite sym $ iterSucc f x (a+(a+q)) in
  rewrite addAssoc a a q in
  rewrite addDiag a in
  rewrite sym $ addSuccL (O a) q in
  Refl

-- iter_invariant

iterInvariant : (f : a -> a) -> (Inv : a -> Type) -> (p : Bip) ->
                ((x : a) -> Inv x -> Inv (f x)) ->
                (x : a) -> Inv x -> Inv (bipIter f x p)
iterInvariant f Inv  U    g x ix = g x ix
iterInvariant f Inv (O b) g x ix =
  let ih = iterInvariant f Inv b g x ix in
    iterInvariant f Inv b g (bipIter f x b) ih
iterInvariant f Inv (I b) g x ix =
  let ih = iterInvariant f Inv b g x ix
      ih2 = iterInvariant f Inv b g (bipIter f x b) ih in
    g (bipIter f (bipIter f x b) b) ih2

-- pow_1_r

pow1R : (p : Bip) -> bipPow p U = p
pow1R  U    = Refl
pow1R (O a) = rewrite mul1R a in Refl
pow1R (I a) = rewrite mul1R a in Refl

-- pow_succ_r

powSuccR : (p, q : Bip) -> bipPow p (bipSucc q) = p * (bipPow p q)
powSuccR p q = iterSucc (bipMult p) U q

-- square_spec

squareSpec : (p : Bip) -> bipSquare p = p * p
squareSpec  U    = Refl
squareSpec (O a) = rewrite mulComm a (O a) in
                   cong {f=O . O} $ squareSpec a
squareSpec (I a) =
  rewrite mulXIR a a in
  rewrite addAssoc a a (O (a*a)) in
  rewrite addDiag a in
  rewrite addComm (bipSquare a) a in
  cong {f=I . O . bipPlus a} $ squareSpec a

-- sub_mask_succ_r

subMaskSuccR : (p, q : Bip) -> bimMinus p (bipSucc q) = bimMinusCarry p q
subMaskSuccR  U         U    = Refl
subMaskSuccR  U        (O _) = Refl
subMaskSuccR  U        (I _) = Refl
subMaskSuccR (O  U   )  U    = Refl
subMaskSuccR (O (O _))  U    = Refl
subMaskSuccR (O (I _))  U    = Refl
subMaskSuccR (O  _   ) (O _) = Refl
subMaskSuccR (O  a   ) (I b) = cong $ subMaskSuccR a b
subMaskSuccR (I  U   )  U    = Refl
subMaskSuccR (I (O _))  U    = Refl
subMaskSuccR (I (I _))  U    = Refl
subMaskSuccR (I  _   ) (O _) = Refl
subMaskSuccR (I  a   ) (I b) = cong $ subMaskSuccR a b

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

data BimMinusSpec : (p, q : Bip) -> (m : Bim) -> Type where
  SubIsNul :     p = q -> m=BimO   -> BimMinusSpec p q m
  SubIsPos : q + r = p -> m=BimP r -> BimMinusSpec p q m
  SubIsNeg : p + r = q -> m=BimM   -> BimMinusSpec p q m

-- sub_mask_spec

subMaskSpec : (p, q : Bip) -> BimMinusSpec p q (bimMinus p q)
subMaskSpec  U     U    = SubIsNul Refl Refl
subMaskSpec  U    (O b) = SubIsNeg {r=bipDMO b}
                           (rewrite add1L (bipDMO b) in succPredDouble b)
                            Refl
subMaskSpec  U    (I b) = SubIsNeg {r=O b} Refl Refl
subMaskSpec (O a)  U    = SubIsPos {r=bipDMO a}
                           (rewrite add1L (bipDMO a) in succPredDouble a)
                            Refl
subMaskSpec (O a) (O b) =
  case subMaskSpec a b of
    SubIsNul     Refl mo => rewrite mo in SubIsNul Refl Refl
    SubIsPos {r} Refl mp => rewrite mp in SubIsPos {r=O r} Refl Refl
    SubIsNeg {r} Refl mm => rewrite mm in SubIsNeg {r=O r} Refl Refl
subMaskSpec (O a) (I b) =
  rewrite subMaskCarrySpec a b in
    case subMaskSpec a b of
      SubIsNul     Refl mo => rewrite mo in SubIsNeg {r=U} Refl Refl
      SubIsPos {r} Refl mp => rewrite mp in
                              SubIsPos {r=bipDMO r}
                                (sym $ addXIPredDouble b r)
                                (rewrite dpoPredDouble (BimP r) in Refl)
      SubIsNeg {r} Refl mm => rewrite mm in SubIsNeg {r=I r} Refl Refl
subMaskSpec (I a)  U    = SubIsPos {r=O a} Refl Refl
subMaskSpec (I a) (O b) =
  case subMaskSpec a b of
    SubIsNul     Refl mo => rewrite mo in SubIsPos {r=U} Refl Refl
    SubIsPos {r} Refl mp => rewrite mp in SubIsPos {r=I r} Refl Refl
    SubIsNeg {r} Refl mm => rewrite mm in
                            SubIsNeg {r=bipDMO r}
                              (sym $ addXIPredDouble a r)
                              Refl
subMaskSpec (I a) (I b) =
  case subMaskSpec a b of
    SubIsNul     Refl mo => rewrite mo in SubIsNul Refl Refl
    SubIsPos {r} Refl mp => rewrite mp in SubIsPos {r=O r} Refl Refl
    SubIsNeg {r} Refl mm => rewrite mm in SubIsNeg {r=O r} Refl Refl

-- sub_mask_diag

subMaskDiag : (p : Bip) -> bimMinus p p = BimO
subMaskDiag  U    = Refl
subMaskDiag (O a) = rewrite subMaskDiag a in Refl
subMaskDiag (I a) = rewrite subMaskDiag a in Refl

-- sub_mask_nul_iff

-- TODO split into `to` and `fro`

subMaskNulTo : (p, q : Bip) -> bimMinus p q = BimO -> p = q
subMaskNulTo p q =
  case subMaskSpec p q of
    SubIsNul Refl _  => const Refl
    SubIsPos Refl mp => rewrite mp in absurd
    SubIsNeg Refl mm => rewrite mm in absurd

subMaskNulFro : (p, q : Bip) -> p = q -> bimMinus p q = BimO
subMaskNulFro p p Refl = subMaskDiag p

-- sub_mask_add

subMaskAdd : (p, q, r : Bip) -> bimMinus p q = BimP r -> q + r = p
subMaskAdd p q r =
  case subMaskSpec p q of
    SubIsNul Refl mo => rewrite mo in absurd
    SubIsPos Refl mp => rewrite mp in cong {f=bipPlus q} . sym . BimPInj
    SubIsNeg Refl mm => rewrite mm in absurd

-- sub_mask_add_diag_l

subMaskAddDiagL : (p, q : Bip) -> bimMinus (p+q) p = BimP q
subMaskAddDiagL p q =
  case subMaskSpec (p+q) p of
    SubIsNul     prf _  =>
      absurd $ addNoNeutral p q $
        rewrite addComm q p in
        prf
    SubIsPos {r} prf mp =>
        rewrite cong {f=BimP} $ sym $ addRegL p r q prf in
        mp
    SubIsNeg {r} prf _  =>
      absurd $ addNoNeutral p (q+r) $
        rewrite addComm (q+r) p in
        rewrite addAssoc p q r in
        prf

-- sub_mask_add_diag_r

subMaskAddDiagR : (p, q : Bip) -> bimMinus p (p+q) = BimM
subMaskAddDiagR p q =
  case subMaskSpec p (p+q) of
    SubIsNul     prf _ =>
      absurd $ addNoNeutral p q $
        rewrite addComm q p in
        sym prf
    SubIsPos {r} prf _ =>
      absurd $ addNoNeutral p (q+r) $
        rewrite addComm (q+r) p in
        rewrite addAssoc p q r in
        prf
    SubIsNeg {r} _  mm => mm

-- sub_mask_neg_iff

-- TODO split into `to` and `fro`

subMaskNegTo : (p, q : Bip) -> bimMinus p q = BimM -> (r ** p + r = q)
subMaskNegTo p q prf =
  case subMaskSpec p q of
    SubIsNul     Refl mo => absurd $
      the (BimO   = BimM) (rewrite sym mo in prf)
    SubIsPos {r} Refl mp => absurd $
      the (BimP r = BimM) (rewrite sym mp in prf)
    SubIsNeg {r} Refl mm => (r ** Refl)

subMaskNegFro : (p, q : Bip) -> (r ** p + r = q) -> bimMinus p q = BimM
subMaskNegFro p _ (r ** prf) = rewrite sym prf in
                               subMaskAddDiagR p r

-- eqb_eq
-- TODO split into `to` and `fro`

eqbEqTo : (p, q : Bip) -> (p == q = True) -> p=q
eqbEqTo  U     U    Refl = Refl
eqbEqTo  U    (O _) Refl impossible
eqbEqTo  U    (I _) Refl impossible
eqbEqTo (O _)  U    Refl impossible
eqbEqTo (O a) (O b) prf  = rewrite eqbEqTo a b prf in
                           Refl
eqbEqTo (O _) (I _) Refl impossible
eqbEqTo (I _)  U    Refl impossible
eqbEqTo (I _) (O _) Refl impossible
eqbEqTo (I a) (I b) prf  = rewrite eqbEqTo a b prf in
                           Refl

eqbEqFro : (p, q : Bip) -> p=q -> (p == q = True)
eqbEqFro  U     U    Refl = Refl
eqbEqFro  U    (O _) Refl impossible
eqbEqFro  U    (I _) Refl impossible
eqbEqFro (O _)  U    Refl impossible
eqbEqFro (O a) (O a) Refl = eqbEqFro a a Refl
eqbEqFro (O _) (I _) Refl impossible
eqbEqFro (I _)  U    Refl impossible
eqbEqFro (I _) (O _) Refl impossible
eqbEqFro (I a) (I a) Refl = eqbEqFro a a Refl

Lt : (x, y : Bip) -> Type
Lt x y = x `compare` y = LT

Gt : (x, y : Bip) -> Type
Gt x y = x `compare` y = GT

Le : (x, y : Bip) -> Type
Le x y = Not (x `compare` y = GT)

Ge : (x, y : Bip) -> Type
Ge x y = Not (x `compare` y = LT)

-- ltb_lt
-- TODO split into `to` and `fro`

ltbLtTo : (p, q : Bip) -> p < q = True -> p `Lt` q
ltbLtTo p q prf with (p `compare` q)
  | LT = Refl
  | EQ = absurd prf
  | GT = absurd prf

ltbLtFro : (p, q : Bip) -> p `Lt` q -> p < q = True
ltbLtFro _ _ pltq = rewrite pltq in Refl

-- TODO add to Prelude.Interfaces ?

Uninhabited (LT = EQ) where
  uninhabited Refl impossible

Uninhabited (EQ = LT) where
  uninhabited Refl impossible

Uninhabited (LT = GT) where
  uninhabited Refl impossible

Uninhabited (GT = LT) where
  uninhabited Refl impossible

Uninhabited (GT = EQ) where
  uninhabited Refl impossible

Uninhabited (EQ = GT) where
  uninhabited Refl impossible

-- leb_le
-- TODO split into `to` and `fro`

lebLeTo : (p, q : Bip) -> p > q = False -> p `Le` q
lebLeTo p q prf pq with (p `compare` q)
  | LT = absurd pq
  | EQ = absurd pq
  | GT = absurd prf

lebLeFro : (p, q : Bip) -> p `Le` q -> p > q = False
lebLeFro p q pleq with (p `compare` q)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ pleq Refl

-- switch_Eq
-- TODO use `thenCompare`?

switchEq : (c, c' : Ordering) -> Ordering
switchEq _ LT = LT
switchEq c EQ = c
switchEq _ GT = GT

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

switchEqLT : (o : Ordering) -> switchEq o (bipCompare a b LT) = bipCompare a b LT
switchEqLT {a} {b} _ with (bipCompare a b LT) proof ablt
  | LT = Refl
  | EQ = absurd $ compLtNotEq a b $ sym ablt
  | GT = Refl

switchEqGT : (o : Ordering) -> switchEq o (bipCompare a b GT) = bipCompare a b GT
switchEqGT {a} {b} _ with (bipCompare a b GT) proof ablt
  | LT = Refl
  | EQ = absurd $ compGtNotEq a b $ sym ablt
  | GT = Refl

-- compare_cont_spec

compareContSpec : (p, q : Bip) -> (c : Ordering)
               -> bipCompare p q c = switchEq c (p `compare` q)
compareContSpec U      U    _ = Refl
compareContSpec U     (O _) _ = Refl
compareContSpec U     (I _) _ = Refl
compareContSpec (O _)  U    _ = Refl
compareContSpec (O a) (O b) c = compareContSpec a b c
compareContSpec (O a) (I b) _ with (bipCompare a b LT) proof prf
  | LT = Refl
  | EQ = absurd $ compLtNotEq a b $ sym prf
  | GT = Refl
compareContSpec (I _)  U    _ = Refl
compareContSpec (I a) (O b) _ with (bipCompare a b GT) proof prf
  | LT = Refl
  | EQ = absurd $ compGtNotEq a b $ sym prf
  | GT = Refl
compareContSpec (I a) (I b) c = compareContSpec a b c

-- compare_cont_Eq

compareContEq : (p, q : Bip) -> (c : Ordering) -> bipCompare p q c = EQ -> c = EQ
compareContEq p q LT prf = absurd $ compLtNotEq p q prf
compareContEq _ _ EQ _   = Refl
compareContEq p q GT prf = absurd $ compGtNotEq p q prf

-- compare_cont_Lt_Gt
-- TODO split into `to` and `fro`

compareContLtGtTo : (p, q : Bip) -> bipCompare p q LT = GT -> p `Gt` q
compareContLtGtTo p q prf =
  aux (p `compare` q) $
    rewrite sym $ compareContSpec p q LT in
    prf
  where
  aux : (o : Ordering) -> switchEq LT o = GT -> o = GT
  aux LT prf = absurd prf
  aux EQ prf = absurd prf
  aux GT _   = Refl

compareContLtGtFro : (p, q : Bip) -> p `Gt` q -> bipCompare p q LT = GT
compareContLtGtFro p q x = rewrite compareContSpec p q LT in
                           rewrite x in
                           Refl

-- compare_cont_Lt_Lt
-- TODO split into `to` and `fro`

compareContLtLtTo : (p, q : Bip) -> bipCompare p q LT = LT -> p `Le` q
compareContLtLtTo p q prf pgtq =
  uninhabited $ the (LT = GT) $
    rewrite sym prf in
    rewrite sym aux in
    compareContSpec p q LT
  where
  aux : switchEq LT (p `compare` q) = GT
  aux = rewrite pgtq in Refl

compareContLtLtFro : (p, q : Bip) -> p `Le` q -> bipCompare p q LT = LT
compareContLtLtFro p q prf = rewrite compareContSpec p q LT in
                             aux
  where
  aux : switchEq LT (p `compare` q) = LT
  aux with (p `compare` q)
    | LT = Refl
    | EQ = Refl
    | GT = absurd $ prf Refl

-- compare_cont_Gt_Lt
-- TODO split into `to` and `fro`

compareContGtLtTo : (p, q : Bip) -> bipCompare p q GT = LT -> p `Lt` q
compareContGtLtTo p q prf =
  aux (p `compare` q) $
    rewrite sym $ compareContSpec p q GT in
    prf
  where
  aux : (o : Ordering) -> switchEq GT o = LT -> o = LT
  aux LT _   = Refl
  aux EQ prf = absurd prf
  aux GT prf = absurd prf

compareContGtLtFro : (p, q : Bip) -> p `Lt` q -> bipCompare p q GT = LT
compareContGtLtFro p q x =
  rewrite compareContSpec p q GT in
  rewrite x in
  Refl

-- compare_cont_Gt_Gt
-- TODO split into `to` and `fro`

compareContGtGtTo : (p, q : Bip) -> bipCompare p q GT = GT -> p `Ge` q
compareContGtGtTo p q prf pltq =
  uninhabited $ the (GT=LT) $
    rewrite sym prf in
    rewrite sym aux in
    compareContSpec p q GT
  where
  aux : switchEq GT (p `compare` q) = LT
  aux = rewrite pltq in Refl

compareContGtGtFro : (p, q : Bip) -> p `Ge` q -> bipCompare p q GT = GT
compareContGtGtFro p q prf = rewrite compareContSpec p q GT in
                             aux
  where
  aux : switchEq GT (p `compare` q) = GT
  aux with (p `compare` q)
    | LT = absurd $ prf Refl
    | EQ = Refl
    | GT = Refl

-- compare_xO_xO is trivial
-- compare_xI_xI is trivial

-- compare_xI_xO

compareXIXO : (p, q : Bip) -> (I p `compare` O q) = switchEq GT (p `compare` q)
compareXIXO p q = compareContSpec p q GT

-- compare_xO_xI

compareXOXI : (p, q : Bip) -> (O p `compare` I q) = switchEq LT (p `compare` q)
compareXOXI p q = compareContSpec p q LT

-- mask2cmp

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
  aux : (m : Bim) -> switchEq LT (mask2cmp m) = mask2cmp (bimDPO (bimPred m))
  aux  BimO    = Refl
  aux (BimP c) = rewrite dpoPredDouble (BimP c) in Refl
  aux  BimM    = Refl
compareSubMask (I _)  U    = Refl
compareSubMask (I a) (O b) =
  rewrite compareContSpec a b GT in
  rewrite compareSubMask a b in
  aux (bimMinus a b)
  where
  aux : (m : Bim) -> switchEq GT (mask2cmp m) = mask2cmp (bimDPO m)
  aux  BimO    = Refl
  aux (BimP _) = Refl
  aux  BimM    = Refl
compareSubMask (I a) (I b) = rewrite bimDCmp (bimMinus a b) in
                             compareSubMask a b

-- lt_iff_add
-- TODO split into `to` and `fro`

ltIffAddTo : (p, q : Bip) -> p `Lt` q -> (r ** p + r = q)
ltIffAddTo p q = rewrite compareSubMask p q in
                 aux
  where
  aux : mask2cmp (bimMinus p q) = LT -> (r : Bip ** bipPlus p r = q)
  aux prf with (bimMinus p q) proof pq
    | BimO   = absurd prf
    | BimP _ = absurd prf
    | BimM   = subMaskNegTo p q (sym pq)

ltIffAddFro : (p, q : Bip) -> (r ** p + r = q) -> p `Lt` q
ltIffAddFro p q rprf =
  rewrite compareSubMask p q in
  rewrite subMaskNegFro p q rprf in
  Refl

-- gt_iff_add
-- TODO split into `to` and `fro`

gtIffAddTo : (p, q : Bip) -> p `Gt` q -> (r ** q + r = p)
gtIffAddTo p q = rewrite compareSubMask p q in
                 aux
  where
  aux : mask2cmp (bimMinus p q) = GT -> (r : Bip ** q+r = p)
  aux prf with (bimMinus p q) proof pq
    | BimO   = absurd prf
    | BimP r = (r ** subMaskAdd p q r (sym pq))
    | BimM   = absurd prf

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

-- TODO add to Prelude.Interfaces ?
compareOp : Ordering -> Ordering
compareOp LT = GT
compareOp EQ = EQ
compareOp GT = LT

compareOpInj : (o1, o2 : Ordering) -> compareOp o1 = compareOp o2 -> o1 = o2
compareOpInj LT LT Refl = Refl
compareOpInj LT EQ Refl impossible
compareOpInj LT GT Refl impossible
compareOpInj EQ LT Refl impossible
compareOpInj EQ EQ Refl = Refl
compareOpInj EQ GT Refl impossible
compareOpInj GT LT Refl impossible
compareOpInj GT EQ Refl impossible
compareOpInj GT GT Refl = Refl

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
-- TODO split into `to` and `fro`

compareEqIffTo : (p, q : Bip) -> p `compare` q = EQ -> p = q
compareEqIffTo p q = rewrite compareSubMask p q in
                     aux
  where
  aux : mask2cmp (bimMinus p q) = EQ -> p = q
  aux prf with (bimMinus p q) proof pq
    | BimO   = subMaskNulTo p q (sym pq)
    | BimP _ = absurd prf
    | BimM   = absurd prf

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
geLe p q pgeq = rewrite compareAntisym p q in
                aux
  where
  aux : Not (compareOp (p `compare` q) = GT)
  aux prf with (p `compare` q)
    | LT = pgeq Refl
    | EQ = uninhabited prf
    | GT = pgeq $ sym prf

-- le_ge

leGe : (p, q : Bip) -> p `Le` q -> q `Ge` p
leGe p q pleq = rewrite compareAntisym p q in
                aux
  where
  aux : Not (compareOp (p `compare` q) = LT)
  aux prf with (p `compare` q)
    | LT = pleq $ sym prf
    | EQ = uninhabited prf
    | GT = pleq Refl

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
            -> switchEq GT (p `compare` bipSucc q) = switchEq LT (p `compare` q)
compareSuccR  U     U    = Refl
compareSuccR  U    (O _) = Refl
compareSuccR  U    (I _) = Refl
compareSuccR (O a)  U    = rewrite sym $ compareContSpec a U GT in
                           compareContGtGtFro a U $ leGe U a $ le1L a
compareSuccR (O a) (O b) = rewrite sym $ compareContSpec a b LT in
                           switchEqLT GT
compareSuccR (O a) (I b) = rewrite compareSuccR a b in
                           rewrite sym $ compareContSpec a b LT in
                           sym $ switchEqLT LT
compareSuccR (I a)  U    = rewrite compareContGtGtFro a U $ leGe U a $ le1L a in
                           Refl
compareSuccR (I a) (O b) = rewrite sym $ compareContSpec a b GT in
                           sym $ switchEqGT LT
compareSuccR (I a) (I b) = rewrite sym $ compareSuccR a b in
                           rewrite sym $ compareContSpec a (bipSucc b) GT in
                           switchEqGT GT

-- compare_succ_l

compareSuccL : (p, q : Bip)
            -> switchEq LT (bipSucc p `compare` q) = switchEq GT (p `compare` q)
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
-- TODO split into `to` and `fro`

ltSuccRTo : (p, q : Bip) -> p `Lt` bipSucc q -> p `Le` q
ltSuccRTo p q pltsq =
  let tt = replace {P=\x=>switchEq GT x = switchEq LT (p `compare` q)}
                   pltsq (compareSuccR p q)
  in
    aux tt
  where
  aux : LT = switchEq LT (p `compare` q) -> (p `Le` q)
  aux prf prf1 with (p `compare` q)
    | LT = uninhabited prf1
    | EQ = uninhabited prf1
    | GT = uninhabited prf

ltSuccRFro : (p, q : Bip) -> p `Le` q -> p `Lt` bipSucc q
ltSuccRFro p q pleq = aux $ compareSuccR p q
  where
  aux : switchEq GT (p `compare` (bipSucc q)) = switchEq LT (p `compare` q)
     -> p `compare` (bipSucc q) = LT
  aux prf with (p `compare` q)
    aux prf | LT with (p `compare` (bipSucc q))
      aux prf | LT | LT = Refl
      aux prf | LT | EQ = absurd prf
      aux prf | LT | GT = absurd prf
    aux prf | EQ with (p `compare` (bipSucc q))
      aux prf | EQ | LT = Refl
      aux prf | EQ | EQ = absurd prf
      aux prf | EQ | GT = absurd prf
    aux prf | GT = absurd $ pleq Refl

-- lt_succ_diag_r

ltSuccDiagR : (p : Bip) -> p `Lt` (bipSucc p)
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
  aux : Not ((bipSucc a) `compare` U = LT) -> (bipSucc a) `compare` U = GT
  aux nsalt1 with ((bipSucc a) `compare` U) proof sau
    | LT = absurd $ nsalt1 Refl
    | EQ = absurd $ succNotU a $ compareEqIffTo (bipSucc a) U $ sym sau
    | GT = Refl
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
  | LT = uninhabited pgtq
  | EQ = uninhabited pgtq
  | GT = uninhabited pltq

-- lt_nle
-- TODO split into `to` and `fro`
ltNleTo : (p, q : Bip) -> p `Lt` q -> Not (q `Le` p)
ltNleTo p q pltq qlep = qlep $ ltGt p q pltq

ltNleFro : (p, q : Bip) -> Not (q `Le` p) -> p `Lt` q
ltNleFro p q nqlep with (p `compare` q) proof pq
  | LT = Refl
  | EQ =
    let peqq = compareEqIffTo p q (sym pq)
        qq = replace {P=\x=>Not (Not (q `Gt` x))}
                     peqq nqlep
        nn = replace {P=\x=>Not (Not (x = GT))}
                     (compareContRefl q EQ) qq
    in
      absurd $ nn uninhabited
  | GT = absurd $ nqlep $ ltLeIncl q p $ gtLt p q $ sym pq

-- lt_lt_succ

ltLtSucc : (p, q : Bip) -> p `Lt` q -> p `Lt` bipSucc q
ltLtSucc p q = ltSuccRFro p q . ltLeIncl p q

-- succ_lt_mono
-- TODO split into `to` and `fro`

succLtMonoTo : (p, q : Bip) -> p `Lt` q -> bipSucc p `Lt` bipSucc q
succLtMonoTo p q pltq = rewrite compareSuccSucc p q in
                        pltq

succLtMonoFro : (p, q : Bip) -> bipSucc p `Lt` bipSucc q -> p `Lt` q
succLtMonoFro p q spltsq = rewrite sym $ compareSuccSucc p q in
                           spltsq

-- succ_le_mono
-- TODO split into `to` and `fro`

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

-- lt_total

ltTotal : (p, q : Bip) -> Either (Either (p `Lt` q) (q `Lt` p)) (p = q)
ltTotal p q with (p `compare` q) proof pq
  | LT = Left $ Left Refl
  | EQ = Right $ compareEqIffTo p q (sym pq)
  | GT = Left $ Right $ gtLt p q (sym pq)

-- le_refl

leRefl : (p : Bip) -> p `Le` p
leRefl p = rewrite compareContRefl p EQ in
           uninhabited

-- le_lt_trans

leLtTrans : (p, q, r : Bip) -> p `Le` q -> q `Lt` r -> p `Lt` r
leLtTrans p q r pleq qltr with (p `compare` q) proof pq
  | LT = ltTrans p q r (sym pq) qltr
  | EQ = rewrite compareEqIffTo p q (sym pq) in
         qltr
  | GT = absurd $ pleq Refl

-- le_trans

leTrans : (p, q, r : Bip) -> p `Le` q -> q `Le` r -> p `Le` r
leTrans p q r pleq qler pgtr with (q `compare` r) proof qr
  | LT = uninhabited $ the (GT=LT) $
           rewrite sym pgtr in
           leLtTrans p q r pleq (sym qr)
  | EQ = pleq $ rewrite compareEqIffTo q r (sym qr) in
                pgtr
  | GT = absurd $ qler Refl

-- le_succ_l
-- TODO split into `to` and `fro`

leSuccLTo : (p, q : Bip) -> bipSucc p `Le` q -> p `Lt` q
leSuccLTo p q = succLtMonoFro p q . ltSuccRFro (bipSucc p) q

leSuccLFro : (p, q : Bip) -> p `Lt` q -> bipSucc p `Le` q
leSuccLFro p q = ltSuccRTo (bipSucc p) q . succLtMonoTo p q

-- le_antisym

leAntisym : (p, q : Bip) -> p `Le` q -> q `Le` p -> p = q
leAntisym p q pleq qlep with (p `compare` q) proof pq
  | LT = absurd $ qlep $ ltGt p q (sym pq)
  | EQ = compareEqIffTo p q (sym pq)
  | GT = absurd $ pleq Refl

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
    base : ((U+q) `compare` (U+r)) = (q `compare` r)
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
-- TODO split into `to` and `fro`

addLtMonoLTo : (p, q, r : Bip) -> q `Lt` r -> (p+q) `Lt` (p+r)
addLtMonoLTo p q r qltr = rewrite addCompareMonoL p q r in
                          qltr

addLtMonoLFro : (p, q, r : Bip) -> (p+q) `Lt` (p+r) -> q `Lt` r
addLtMonoLFro p q r = rewrite addCompareMonoL p q r in
                      id

-- add_lt_mono_r
-- TODO split into `to` and `fro`

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
-- TODO split into `to` and `fro`

addLeMonoLTo : (p, q, r : Bip) -> q `Le` r -> (p+q) `Le` (p+r)
addLeMonoLTo p q r qler = rewrite addCompareMonoL p q r in
                          qler

addLeMonoLFro : (p, q, r : Bip) -> (p+q) `Le` (p+r) -> q `Le` r
addLeMonoLFro p q r = rewrite addCompareMonoL p q r in
                      id

-- add_le_mono_r
-- TODO split into `to` and `fro`

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
-- TODO split into `to` and `fro`, intermixed with mul_compare_mono_l
mulLtMonoLTo : (p, q, r : Bip) -> q `Lt` r -> (p*q) `Lt` (p*r)
mulLtMonoLTo  U    _ _ qltr = qltr
mulLtMonoLTo (O a) q r qltr = mulLtMonoLTo a q r qltr
mulLtMonoLTo (I a) q r qltr =
  let ih = mulLtMonoLTo a q r qltr in
    addLtMono q r (O $ a*q) (O $ a*r) qltr ih

-- mul_compare_mono_l

mulCompareMonoL : (p, q, r : Bip) -> (p*q) `compare` (p*r) = q `compare` r
mulCompareMonoL  U    _ _ = Refl
mulCompareMonoL (O a) q r = mulCompareMonoL a q r
mulCompareMonoL (I a) q r with (q `compare` r) proof qr
  | LT = let aqr = mulLtMonoLTo a q r (sym qr) in
           addLtMono q r (O $ a*q) (O $ a*r) (sym qr) aqr
  | EQ = rewrite compareEqIffTo q r (sym qr) in
         compareContRefl (r+(O $ a*r)) EQ
  | GT = let rltq = gtLt q r $ sym qr
             arq = mulLtMonoLTo a r q rltq
             mul = addLtMono r q (O $ a*r) (O $ a*q) rltq arq
         in
           ltGt (r+(O $ a*r)) (q+(O $ a*q)) mul

-- mul_lt_mono_l
-- TODO split into `to` and `fro`, intermixed with mul_compare_mono_l
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
-- TODO split into `to` and `fro`

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
-- TODO split into `to` and `fro`

mulLeMonoLTo : (p, q, r : Bip) -> q `Le` r -> (p*q) `Le` (p*r)
mulLeMonoLTo p q r qler = rewrite mulCompareMonoL p q r in
                          qler

mulLeMonoLFro : (p, q, r : Bip) -> (p*q) `Le` (p*r) -> q `Le` r
mulLeMonoLFro p q r = rewrite mulCompareMonoL p q r in
                      id

-- mul_le_mono_r
-- TODO split into `to` and `fro`

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

-- pow_gt_1

powGt1 : (p, q : Bip) -> U `Lt` p -> U `Lt` bipPow p q
powGt1 p q ultp =
  peanoRect
    (\x => U `Lt` bipPow p x)
    (replace (sym $ pow1R p) ultp)
    (\r,ultpr =>
       let pultppr = mulLtMonoLTo p U (bipPow p r) ultpr
           pultpsr = replace {P=\x=>(p*U) `Lt` x}
                             (sym $ powSuccR p r) pultppr
           pltpsr = replace {P=\x=>x `Lt` (bipPow p $ bipSucc r)}
                            (mul1R p) pultpsr
       in
         ltTrans U p (bipPow p (bipSucc r)) ultp pltpsr
    )
    q

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
  | (r ** pmqr) =
    rewrite pmqr in
    rewrite addComm r q in
    subMaskAdd p q r pmqr

subInverse : (p, q, r : Bip) -> r `Lt` p -> p - r = q -> p = q + r
subInverse p q r rltp prq =
  rewrite sym $ subAdd p r rltp in
  cong {f=\x=>x+r} prq

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

subCompareMonoL : (p, q, r : Bip) -> q `Lt` p -> r `Lt` p
                                 -> (p-q) `compare` (p-r) = r `compare` q
subCompareMonoL p q r qltp rltp with (r `compare` q) proof rq
  | LT = subLtMonoL q r p (sym rq) qltp
  | EQ = rewrite compareEqIffTo r q (sym rq) in compareContRefl (p-q) EQ
  | GT = ltGt (p-r) (p-q) $ subLtMonoL r q p (gtLt r q (sym rq)) rltp

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
    | BimO   = Refl
    | BimP a = rewrite dpoPredDouble (BimP a) in Refl
    | BimM   = Refl

-- sub_mask_neg_iff'
-- TODO split into `to` and `fro`, fro case = sub_mask_neg

subMaskNegTo' : (p, q : Bip) -> bimMinus p q = BimM -> p `Lt` q
subMaskNegTo' p q = ltIffAddFro p q . subMaskNegTo p q

subMaskNeg : (p, q : Bip) -> p `Lt` q -> bimMinus p q = BimM
subMaskNeg p q = subMaskNegFro p q . ltIffAddTo p q

-- sub_le

subLe : (p, q : Bip) -> p `Le` q -> p-q = U
subLe p q pleq with (bimMinus p q) proof pq
  | BimO   = Refl
  | BimP a =
    let qltp = ltGt q p $ ltIffAddFro q p (a**subMaskAdd p q a $ sym pq)
    in absurd $ pleq qltp
  | BimM   = Refl

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
  aux : bipDigitsNat a `LTE` bipDigitsNat b
  aux with (a `compare` b) proof ab
    | LT = sizeNatMonotone a b $ sym ab
    | EQ = rewrite compareEqIffTo a b $ sym ab in
           lteRefl
    | GT = absurd $ compareContLtLtTo a b pltq $ sym ab
sizeNatMonotone (I a) (O b) pltq = LTESucc $ sizeNatMonotone a b $
                                             compareContGtLtTo a b pltq
sizeNatMonotone (I a) (I b) pltq = LTESucc $ sizeNatMonotone a b pltq

--  size_gt

sizeGt : (p : Bip) -> p `Lt` bipPow 2 (bipDigits p)
sizeGt  U    = Refl
sizeGt (O a) = rewrite powSuccR 2 (bipDigits a) in
               sizeGt a
sizeGt (I a) = rewrite powSuccR 2 (bipDigits a) in
               compareContGtLtFro a (bipPow 2 (bipDigits a)) (sizeGt a)

-- size_le

sizeLe : (p : Bip) -> bipPow 2 (bipDigits p) `Le` O p
sizeLe  U    = uninhabited
sizeLe (O a) = rewrite powSuccR 2 (bipDigits a) in
               sizeLe a
sizeLe (I a) = rewrite powSuccR 2 (bipDigits a) in
               leTrans (bipPow 2 (bipDigits a)) (O a) (I a)
                 (sizeLe a) (rewrite compareContRefl a LT in
                             uninhabited)

-- max_l

maxL : (p, q : Bip) -> q `Le` p -> max p q = p
maxL p q qlep with (p `compare` q) proof pq
  | LT = absurd $ qlep $ ltGt p q $ sym pq
  | EQ = sym $ compareEqIffTo p q (sym pq)
  | GT = Refl

-- max_r

maxR : (p, q : Bip) -> p `Le` q -> max p q = q
maxR p q pleq with (p `compare` q)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ pleq Refl

-- min_l

minL : (p, q : Bip) -> p `Le` q -> min p q = p
minL p q pleq with (p `compare` q)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ pleq Refl

-- min_r

minR : (p, q : Bip) -> q `Le` p -> min p q = q
minR p q qlep with (p `compare` q) proof pq
  | LT = absurd $ qlep $ ltGt p q $ sym pq
  | EQ = compareEqIffTo p q (sym pq)
  | GT = Refl

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

leLtOrEq : (x, y : Bip) -> x `Le` y -> Either (x `Lt` y) (x=y)
leLtOrEq x y xley with (x `compare` y) proof xy
  | LT = Left Refl
  | EQ = Right $ compareEqIffTo x y (sym xy)
  | GT = absurd $ xley Refl

maxMonotone : (f : Bip -> Bip) ->
              ((a, b : Bip) -> (a `Le` b) -> (f a `Le` f b)) ->
              (x, y : Bip) -> max (f x) (f y) = f (max x y)
maxMonotone f fle x y with (x `compare` y) proof xy
  | LT =
    case leLtOrEq (f x) (f y) $ fle x y $ ltLeIncl x y $ sym xy of
      Left fxlty => rewrite fxlty in Refl
      Right fxeqy => rewrite fxeqy in
                     rewrite compareContRefl (f y) EQ in
                     Refl
  | EQ =
    rewrite compareEqIffTo x y (sym xy) in
    rewrite compareContRefl (f y) EQ in
    Refl
  | GT =
    case leLtOrEq (f y) (f x) $ fle y x $ ltLeIncl y x $ gtLt x y $ sym xy of
      Left fyltx => rewrite ltGt (f y) (f x) fyltx in Refl
      Right fxeqy => rewrite fxeqy in
                     rewrite compareContRefl (f x) EQ in
                     Refl

minMonotone : (f : Bip -> Bip) ->
              ((a, b : Bip) -> (a `Le` b) -> (f a `Le` f b)) ->
              (x, y : Bip) -> min (f x) (f y) = f (min x y)
minMonotone f fle x y with (x `compare` y) proof xy
  | LT = case leLtOrEq (f x) (f y) $ fle x y (ltLeIncl x y $ sym xy) of
           Left fxlty => rewrite fxlty in Refl
           Right fxeqy => rewrite fxeqy in
                         rewrite compareContRefl (f y) EQ in
                         Refl
  | EQ = rewrite compareEqIffTo x y $ sym xy in
         rewrite compareContRefl (f y) EQ in
         Refl
  | GT = case leLtOrEq (f y) (f x) $ fle y x $ ltLeIncl y x $ gtLt x y $ sym xy of
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

-- TODO reformulate iter_op_succ so that it describes toNatBip/bipMultNat

-- of_nat_succ

ofNatSucc : (n : Nat) -> toBipNatSucc n = toBipNat (S n)
ofNatSucc  Z    = Refl
ofNatSucc (S k) = cong $ ofNatSucc k

--- pred_of_succ_nat

predOfSuccNat : (n : Nat) -> bipPred (toBipNatSucc n) = toBipNat n
predOfSuccNat Z = Refl
predOfSuccNat (S k) = rewrite predSucc (toBipNatSucc k) in
                      ofNatSucc k

-- succ_of_nat

succOfNat : (n : Nat) -> Not (n=Z) -> bipSucc (toBipNat n) = toBipNatSucc n
succOfNat  Z    contra = absurd $ contra Refl
succOfNat (S k) _      = cong $ sym $ ofNatSucc k

-- TODO like in other specs, e.g., `BimMinusSpec` we use a workaround with eq
-- parameter

data SqrtSpec : (Bip, Bim) -> Bip -> Type where
  SqrtExact  : x=s*s   ->               pm = (s, BimO)   -> SqrtSpec pm x
  SqrtApprox : x=s*s+r -> r `Le` O s -> pm = (s, BimP r) -> SqrtSpec pm x

-- sqrtrem_step_spec

sqrtremStepSpec : Either (f=O) (f=I) -> Either (g=O) (g=I) -> SqrtSpec p x
               -> SqrtSpec (bipSqrtRemStep f g p) (g (f x))
sqrtremStepSpec (Left  fo) (Left  go) (SqrtExact {s} prf pprf) =
  rewrite fo in rewrite go in rewrite prf in rewrite pprf in
  SqrtExact {s=O s} (rewrite sym $ squareXO s in Refl) Refl
sqrtremStepSpec (Left  fo) (Right gi) (SqrtExact {s} prf pprf) =
  rewrite fo in rewrite gi in rewrite prf in rewrite pprf in
  SqrtApprox {s=O s} {r=U} (rewrite sym $ mulXOR s s in Refl) uninhabited Refl
sqrtremStepSpec (Right fi) (Left  go) (SqrtExact {s} prf pprf) =
  rewrite fi in rewrite go in rewrite prf in rewrite pprf in
  SqrtApprox {s=O s} {r=O U} (rewrite mulXOR s s in Refl) uninhabited Refl
sqrtremStepSpec (Right fi) (Right gi) (SqrtExact {s} prf pprf) =
  rewrite fi in rewrite gi in rewrite prf in rewrite pprf in
  SqrtApprox {s=O s} {r=I U} (rewrite mulXOR s s in Refl) uninhabited Refl
sqrtremStepSpec {f} {g} foi goi (SqrtApprox {s} {r} prf rle pprf) =
  rewrite prf in rewrite pprf in
  rewrite hfg (s*s) r foi goi in
  aux
  where
  hfg : (p, q : Bip) -> Either (f=O) (f=I) -> Either (g=O) (g=I)
                    -> g (f (p+q)) = O (O p) + g (f q)
  hfg _ _ (Left fo ) (Left go ) = rewrite fo in rewrite go in Refl
  hfg _ _ (Left fo ) (Right gi) = rewrite fo in rewrite gi in Refl
  hfg _ _ (Right fi) (Left go ) = rewrite fi in rewrite go in Refl
  hfg _ _ (Right fi) (Right gi) = rewrite fi in rewrite gi in Refl
  gfleii : (p, q : Bip) -> Either (f=O) (f=I) -> Either (g=O) (g=I) -> p `Le` q
                       -> g (f p) `Le` I (I q)
  gfleii p q (Left fo ) (Left go ) pleq =
    rewrite fo in rewrite go in
    pleq . compareContLtGtTo p q
  gfleii p q (Left fo ) (Right gi) pleq =
    rewrite fo in rewrite gi in
    pleq . compareContLtGtTo p q
  gfleii p q (Right fi) (Left go ) pleq =
    rewrite fi in rewrite go in
    pleq . compareContLtGtTo p q
  gfleii _ _ (Right fi) (Right gi) pleq =
    rewrite fi in rewrite gi in
    pleq
  aux : SqrtSpec
          (bipSqrtRemStepHelp s (I $ O s) (g $ f r) $
            (I $ O s) `compare` (g $ f r))
          ((O $ O $ s*s)+(g $ f r))
  aux with ((I $ O s) `compare` (g $ f r)) proof cmp
    | LT =
      let (q**qprf) = subMaskPos (g $ f r) (I $ O s) $ sym cmp
          qdef = sym $ cong {f=bipMinusHelp} qprf
      in
       rewrite qprf in
         SqrtApprox {s=I s} {r=q}
           (rewrite qdef in
            rewrite addSubAssoc (I $ s+s*(I s)) (g $ f r) (I $ O s) $ sym cmp in
            addRegR ((O $ O $ s*s)+(g $ f r)) (((I $ s+s*(I s))+(g $ f r))-(I $ O s)) (I $ O s) $
            rewrite subAdd ((I $ s+s*(I s))+(g $ f r)) (I $ O s) $
              ltTrans (I $ O s) (I $ s+s*(I s)) ((I $ s+(s*(I s)))+(g $ f r))
                (rewrite sym $ addDiag s in
                 addLtMonoLTo s s (s*(I s)) $
                 rewrite mulXIR s s in
                 ltAddDiagR s (O $ s*s))
                (ltAddDiagR (I $ s+s*(I s)) (g $ f r)) in
            rewrite sym $ addAssoc (O $ O $ s*s) (g $ f r) (I $ O s) in
            rewrite addComm (g $ f r) (I $ O s) in
            rewrite addAssoc (O $ O $ s*s) (I $ O s) (g $ f r) in
            rewrite mulXIR s s in
            rewrite addAssoc s s (O $ s*s) in
            rewrite addDiag s in
            rewrite addComm (s*s) s in
            Refl)
           (rewrite qdef in
            addLeMonoRFro (I $ O s) ((g $ f r)-(I $ O s)) (O $ I s) $
            rewrite subAdd (g $ f r) (I $ O s) $ sym cmp in
            rewrite addDiag s in
            gfleii r (O s) foi goi rle)
           Refl
    | EQ =
      rewrite sym $ compareEqIffTo (I $ O s) (g $ f r) $ sym cmp in
      rewrite subMaskDiag s in
      SqrtExact {s=I s}
        (rewrite mulXIR s s in
         rewrite addAssoc s s (O $ s*s) in
         rewrite addDiag s in
         rewrite addComm (s*s) s in
         Refl)
        Refl
    | GT =
      SqrtApprox {s=O s} {r=g $ f r}
        (rewrite mulXOR s s in Refl)
        (ltSuccRTo (g $ f r) (O $ O s) $
         gtLt (I $ O s) (g $ f r) $
         sym cmp)
        Refl

-- sqrtrem_spec

sqrtremSpec : (p : Bip) -> SqrtSpec (bipSqrtRem p) p
sqrtremSpec  U        = SqrtExact {s=U} Refl Refl
sqrtremSpec (O  U   ) = SqrtApprox {s=U} {r=U} Refl uninhabited Refl
sqrtremSpec (O (O a)) =
  sqrtremStepSpec (Left Refl ) (Left Refl ) (sqrtremSpec a)
sqrtremSpec (O (I a)) =
  sqrtremStepSpec (Right Refl) (Left Refl ) (sqrtremSpec a)
sqrtremSpec (I  U   ) = SqrtApprox {s=U} {r=O U} Refl uninhabited Refl
sqrtremSpec (I (O a)) =
  sqrtremStepSpec (Left Refl ) (Right Refl) (sqrtremSpec a)
sqrtremSpec (I (I a)) =
  sqrtremStepSpec (Right Refl) (Right Refl) (sqrtremSpec a)

-- sqrt_spec

sqrtSpec : (p : Bip) -> let s = bipSqrt p in
                        (s*s `Le` p, p `Lt` (bipSucc s)*(bipSucc s))
sqrtSpec p = case sqrtremSpec p of
  SqrtExact {s} prf srprf =>
    rewrite srprf in rewrite prf in
    ( gtNotSelf (s*s)
    , mulLtMono s (bipSucc s) s (bipSucc s) (ltSuccDiagR s) (ltSuccDiagR s)
    )
  SqrtApprox {s} {r} prf rle srprf =>
    rewrite srprf in rewrite prf in
    ( ltLeIncl (s*s) (s*s+r) $ ltAddDiagR (s*s) r
    , rewrite mulSuccR (bipSucc s) s in
      rewrite mulSuccL s s in
      rewrite addAssoc (bipSucc s) s (s*s) in
      rewrite addComm ((bipSucc s)+s) (s*s) in
      addLtMonoLTo (s*s) r ((bipSucc s)+s) $
      rewrite sym $ add1L s in
      rewrite sym $ addAssoc U s s in
      rewrite addDiag s in
      ltSuccRFro r (O s) rle
    )

bipDivides : (p, q : Bip) -> Type
bipDivides p q = (r ** q = r*p)

-- divide_add_cancel_l

divideAddCancelL : (p, q, r : Bip) -> bipDivides p r -> bipDivides p (q+r)
                                   -> bipDivides p q
divideAddCancelL p q r (s ** pr) (t ** pqr) =
   ((t-s) **
     rewrite mulSubDistrR t s p $
               mulLtMonoRFro p s t $
               rewrite sym pr in
               rewrite sym pqr in
               rewrite addComm q r in
               ltAddDiagR r q
             in
     rewrite sym pr in
     rewrite sym pqr in
     sym $ addSub q r)

-- divide_xO_xI

divideXOXI : (p, q, r : Bip) -> bipDivides p (O q) -> bipDivides p (I r)
                             -> bipDivides p q
divideXOXI  U    q _  _          _         = (q ** sym $ mul1R q)
divideXOXI (O a) _ _  _         (t ** pir) = absurd $ replace (mulXOR t a) pir
divideXOXI (I _) _ _ (s ** poq)  _         = case s of
  U   => absurd poq
  O d => (d ** OInj poq)
  I _ => absurd poq

-- divide_xO_xO

divideXOXO : (p, q : Bip) -> bipDivides (O p) (O q) -> bipDivides p q
divideXOXO p _ (r ** opoq) = (r ** OInj $ rewrite sym $ mulXOR r p in opoq)

-- divide_mul_l

divideMulL : (p, q, r : Bip) -> bipDivides p q -> bipDivides p (q*r)
divideMulL p _ r (s ** pq) = ((s*r) **
  rewrite pq in
  rewrite sym $ mulAssoc s p r in
  rewrite sym $ mulAssoc s r p in
  rewrite mulComm p r in
  Refl)

-- divide_mul_r

divideMulR : (p, q, r : Bip) -> bipDivides p r -> bipDivides p (q*r)
divideMulR p q r dpr = rewrite mulComm q r in
                       divideMulL p r q dpr

-- ggcdn_gcdn

-- The first component of GGCD is GCD

ggcdnGcdn : (n : Nat) -> (p, q : Bip) -> fst $ bipGGCDN n p q = bipGCDN n p q
ggcdnGcdn  Z     _     _    = Refl
ggcdnGcdn (S _)  U     _    = Refl
ggcdnGcdn (S _) (O _)  U    = Refl
ggcdnGcdn (S k) (O a) (O b) = cong $ ggcdnGcdn k a b
ggcdnGcdn (S k) (O a) (I b) = ggcdnGcdn k a (I b)
ggcdnGcdn (S _) (I _)  U    = Refl
ggcdnGcdn (S k) (I a) (O b) = ggcdnGcdn k (I a) b
ggcdnGcdn (S k) (I a) (I b) with (a `compare` b)
  | LT = ggcdnGcdn k (b-a) (I a)
  | EQ = Refl
  | GT = ggcdnGcdn k (a-b) (I b)

-- ggcd_gcd

ggcdGcd : (p, q : Bip) -> fst $ bipGGCD p q = bipGCD p q
ggcdGcd p q = ggcdnGcdn ((bipDigitsNat p)+(bipDigitsNat q)) p q

-- ggcdn_correct_divisors

ggcdnCorrectDivisors : (n : Nat) -> (p, q : Bip) ->
                       let gppqq = bipGGCDN n p q
                           g = fst gppqq
                           pp = fst $ snd gppqq
                           qq = snd $ snd gppqq in
                         (p=g*pp, q=g*qq)
ggcdnCorrectDivisors  Z     _     _    = (Refl, Refl)
ggcdnCorrectDivisors (S _)  U     _    = (Refl, Refl)
ggcdnCorrectDivisors (S _) (O _)  U    = (Refl, Refl)
ggcdnCorrectDivisors (S k) (O a) (O b) =
  let (aprf, bprf) = ggcdnCorrectDivisors k a b in
     (cong aprf, cong bprf)
ggcdnCorrectDivisors (S k) (O a) (I b) =
  let (aprf, ibprf) = ggcdnCorrectDivisors k a (I b)
      x = bipGGCDN k a (I b) in
    ( rewrite mulXOR (fst x) (fst $ snd x) in
      cong aprf
    , ibprf
    )
ggcdnCorrectDivisors (S _) (I _)  U    = (Refl, Refl)
ggcdnCorrectDivisors (S k) (I a) (O b) =
  let (iaprf, bprf) = ggcdnCorrectDivisors k (I a) b
      x = bipGGCDN k (I a) b
  in
    ( iaprf
    , rewrite mulXOR (fst x) (snd $ snd x) in
      cong bprf
    )
ggcdnCorrectDivisors (S k) (I a) (I b) with (a `compare` b) proof ab
  | LT = let (bmaprf, iaprf) = ggcdnCorrectDivisors k (b-a) (I a)
             x = bipGGCDN k (b-a) (I a)
             fx = fst x
             fsx = fst $ snd x
             ssx = snd $ snd x
         in
         ( iaprf
         , rewrite mulAddDistrL fx ssx (O fsx) in
           rewrite sym iaprf in
           rewrite mulXOR fx fsx in
           cong {f=I} $
           rewrite addComm a (fx*fsx) in
           subInverse b (fx*fsx) a (sym ab) $
           bmaprf
         )
  | EQ = rewrite compareEqIffTo a b $ sym ab in
         rewrite mul1R b in
         (Refl, Refl)
  | GT = let (ambprf, ibprf) = ggcdnCorrectDivisors k (a-b) (I b)
             x = bipGGCDN k (a-b) (I b)
             fx = fst x
             fsx = fst $ snd x
             ssx = snd $ snd x
         in
         ( rewrite mulAddDistrL fx ssx (O fsx) in
           rewrite sym ibprf in
           rewrite mulXOR fx fsx in
           cong {f=I} $
           rewrite addComm b (fx*fsx) in
           subInverse a (fx*fsx) b (gtLt a b $ sym ab) $
           ambprf
         , ibprf
         )

-- ggcd_correct_divisors

ggcdCorrectDivisors : (p, q : Bip) ->
                      let gppqq = bipGGCD p q
                          g = fst gppqq
                          pp = fst $ snd gppqq
                          qq = snd $ snd gppqq in
                        (p=g*pp, q=g*qq)
ggcdCorrectDivisors p q =
  ggcdnCorrectDivisors ((bipDigitsNat p) + (bipDigitsNat q)) p q

-- gcd_divide_l

gcdDivideL : (p, q : Bip) -> bipDivides (bipGCD p q) p
gcdDivideL p q =
  let (pprf, _) = ggcdCorrectDivisors p q
      x = bipGGCD p q in
  rewrite sym $ ggcdGcd p q in
  (fst $ snd x **
    rewrite mulComm (fst $ snd x) (fst x) in
    pprf)

-- gcd_divide_r

gcdDivideR : (p, q : Bip) -> bipDivides (bipGCD p q) q
gcdDivideR p q =
  let (_, qprf) = ggcdCorrectDivisors p q
      x = bipGGCD p q in
  rewrite sym $ ggcdGcd p q in
  (snd $ snd x **
    rewrite mulComm (snd $ snd x) (fst x) in
    qprf)

-- TODO contribute to Prelude.Nat?

plusLTEMonoR : (p, q, r : Nat) -> q `LTE` r -> (q+p) `LTE` (r+p)
plusLTEMonoR p  Z     r     LTEZero    = rewrite plusCommutative r p in
                                         lteAddRight p
plusLTEMonoR p (S b) (S c) (LTESucc l) = LTESucc $ plusLTEMonoR p b c l

-- gcdn_greatest

-- GCD is the greatest amongst common divisors

gcdnGreatest : (n : Nat) -> (p, q : Bip) -> (bipDigitsNat p + bipDigitsNat q) `LTE` n ->
               (r : Bip) -> bipDivides r p -> bipDivides r q -> bipDivides r (bipGCDN n p q)
gcdnGreatest  Z     U     _    pqlte  _     _          _         = absurd pqlte
gcdnGreatest  Z    (O _)  _    pqlte  _     _          _         = absurd pqlte
gcdnGreatest  Z    (I _)  _    pqlte  _     _          _         = absurd pqlte
gcdnGreatest (S _)  U     _    _      r    (s ** psr)  _         =
  (U ** sym $ mulEq1R s r $ sym psr)
gcdnGreatest (S _) (O _)  U    _      r     _         (t ** qtr) =
  (U ** sym $ mulEq1R t r $ sym qtr)
gcdnGreatest (S _) (I _)  U    _      r     _         (t ** qtr) =
  (U ** sym $ mulEq1R t r $ sym qtr)
gcdnGreatest (S k) (O a) (O b) _      U     _          _         =
  (O $ bipGCDN k a b ** rewrite mul1R (bipGCDN k a b) in
                        Refl)
gcdnGreatest (S k) (O a) (O b) pqlte (O c)  pr         qr        =
  let (r**prf) = gcdnGreatest k a b
                   (fromLteSucc $
                    lteSuccLeft $
                    rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
                    pqlte)
                   c
                   (divideXOXO c a pr)
                   (divideXOXO c b qr)
  in
    (r ** rewrite mulXOR r c in cong prf)
gcdnGreatest (S k) (O a) (O b) pqlte (I c)  pr         qr        =
  let (r**prf) = gcdnGreatest k a b
                   (fromLteSucc $
                    lteSuccLeft $
                    rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
                    pqlte)
                   (I c)
                   (divideXOXI (I c) a c pr (U**Refl))
                   (divideXOXI (I c) b c qr (U**Refl))
  in
    (O r ** cong prf)
gcdnGreatest (S k) (O a) (I b) pqlte  r     pr         qr        =
  gcdnGreatest k a (I b)
    (fromLteSucc pqlte)
     r
    (divideXOXI r a b pr qr)
     qr
gcdnGreatest (S k) (I a) (O b) pqlte  r     pr         qr        =
  gcdnGreatest k (I a) b
    (rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
     fromLteSucc pqlte)
     r
     pr
    (divideXOXI r b a qr pr)
gcdnGreatest (S k) (I a) (I b) pqlte  r    (s ** psr) (t ** qtr) with (a `compare` b) proof ab
  | LT = gcdnGreatest k (b-a) (I a)
           (lteTransitive {m=(bipDigitsNat b) + (S $ bipDigitsNat a)}
              (plusLTEMonoR (S $ bipDigitsNat a) (bipDigitsNat $ b-a) (bipDigitsNat b) $
               sizeNatMonotone (b-a) b $
               addLtMonoRFro a (b-a) b $
               rewrite subAdd b a $ sym ab in
               ltAddDiagR b a)
              (rewrite plusCommutative (bipDigitsNat b) (S $ bipDigitsNat a) in
               rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
               fromLteSucc pqlte))
            r
           (divideXOXI r (b-a) a
              (rewrite sym $ subXIXI b a $ sym ab in
               rewrite subMono qtr psr in
               rewrite sym $ mulSubDistrR t s r $
                         mulLtMonoRFro r s t $
                         rewrite sym psr in
                         rewrite sym qtr in
                         sym ab
                       in
                 (t-s ** Refl))
              (s**psr)
           )
           (s**psr)
  | EQ = (s**psr)
  | GT = gcdnGreatest k (a-b) (I b)
           (lteTransitive {m=(bipDigitsNat a) + (S $ bipDigitsNat b)}
            (plusLTEMonoR (S $ bipDigitsNat b) (bipDigitsNat $ a-b) (bipDigitsNat $ a) $
             sizeNatMonotone (a-b) a $
             addLtMonoRFro b (a-b) a $
             rewrite subAdd a b $ gtLt a b $ sym ab in
              ltAddDiagR a b)
            (fromLteSucc pqlte))
           r
           (divideXOXI r (a-b) b
              (rewrite sym $ subXIXI a b $ gtLt a b $ sym ab in
               rewrite subMono psr qtr in
               rewrite sym $ mulSubDistrR s t r $
                         mulLtMonoRFro r t s $
                         rewrite sym psr in
                         rewrite sym qtr in
                         gtLt a b $ sym ab
                       in
                 (s-t ** Refl))
              (t**qtr)
           )
           (t**qtr)

-- gcd_greatest

gcdGreatest : (p, q, r : Bip) -> bipDivides r p -> bipDivides r q
                              -> bipDivides r (bipGCD p q)
gcdGreatest p q r rp rq =
  gcdnGreatest ((bipDigitsNat p) + (bipDigitsNat q))
               p q lteRefl r rp rq

-- ggcd_greatest

-- The rests after division by GCD are relatively prime

ggcdGreatest : (p, q : Bip) ->
                let ppqq = snd $ bipGGCD p q
                    pp = fst ppqq
                    qq = snd ppqq
                in
                  (r : Bip) -> bipDivides r pp -> bipDivides r qq -> r = U
ggcdGreatest p q r (s**rpp) (t**rqq) =
  let (peq, qeq) = ggcdCorrectDivisors p q
      (rr**rprf) = gcdGreatest p q ((fst $ bipGGCD p q)*r)
                     (s ** rewrite mulComm s ((fst $ bipGGCD p q)*r) in
                           rewrite sym $ mulAssoc (fst $ bipGGCD p q) r s in
                           rewrite mulComm r s in
                           rewrite sym rpp in
                           peq)
                     (t ** rewrite mulComm t ((fst $ bipGGCD p q)*r) in
                           rewrite sym $ mulAssoc (fst $ bipGGCD p q) r t in
                           rewrite mulComm r t in
                           rewrite sym rqq in
                           qeq)
      rprf' = replace {P=\x=>x=rr*((fst $ bipGGCD p q)*r)} (sym $ ggcdGcd p q)
                      rprf
  in
    mulEq1R rr r $
    mulOneNeutral (rr*r) (fst $ bipGGCD p q) $
    rewrite sym $ mulAssoc rr r (fst $ bipGGCD p q) in
    rewrite mulComm r (fst $ bipGGCD p q) in
    sym rprf'
