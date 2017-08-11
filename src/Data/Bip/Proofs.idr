module Data.Bip.Proofs

import Data.Bip

%access public export
%default total

-- Following PArith/BinPos.v

-- xI_succ_xO

iSuccO : (p: Bip) -> I p = bipSucc (O p)
iSuccO _ = Refl

-- succ_discr

succDiscr : (p: Bip) -> Not (p = bipSucc p)
succDiscr  U    = absurd
succDiscr (O _) = absurd
succDiscr (I _) = absurd

-- pred_double_spec

predDoubleSpec : (p: Bip) -> bipDMO p = bipPred (O p)
predDoubleSpec _ = Refl

-- succ_pred_double

succPredDouble : (p: Bip) -> bipSucc (bipDMO p) = O p
succPredDouble  U    = Refl
succPredDouble (O a) = rewrite succPredDouble a in Refl
succPredDouble (I _) = Refl

-- pred_double_succ

predDoubleSucc : (p: Bip) -> bipDMO (bipSucc p) = I p
predDoubleSucc  U    = Refl
predDoubleSucc (O _) = Refl
predDoubleSucc (I a) = rewrite predDoubleSucc a in Refl

-- double_succ

doubleSucc : (p: Bip) -> (O (bipSucc p)) = (bipSucc (bipSucc (O p)))
doubleSucc _ = Refl

-- pred_double_x0_discr

predDoubleODiscr : (p: Bip) -> Not ((bipDMO p) = (O p))
predDoubleODiscr  U    = absurd
predDoubleODiscr (O _) = absurd
predDoubleODiscr (I _) = absurd

-- succ_not_1

succNotU : (p: Bip) -> Not ((bipSucc p) = U)
succNotU  U    = absurd
succNotU (O _) = absurd
succNotU (I _) = absurd

-- pred_succ

predSucc : (p: Bip) -> bipPred (bipSucc p) = p
predSucc  U    = Refl
predSucc (O _) = Refl
predSucc (I a) = case a of
  U     => Refl
  (O _) => Refl
  (I b) => rewrite predSucc (I b) in Refl

-- succ_pred_or

succPredOr : (p: Bip) -> Either (p = U) ((bipSucc (bipPred p)) = p)
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
succInj : (p,q : Bip) -> bipSucc p = bipSucc q -> p = q
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

predBinSucc : (p: Bip) -> bipPredBin (bipSucc p) = BinP p
predBinSucc  U    = Refl
predBinSucc (O _) = Refl
predBinSucc (I a) = cong $ predDoubleSucc a

-- add_1_r

add1R : (p: Bip) -> p + U = bipSucc p
add1R  U    = Refl
add1R (O _) = Refl
add1R (I _) = Refl

-- add_1_l

add1L : (p: Bip) -> U + p = bipSucc p
add1L  U    = Refl
add1L (O _) = Refl
add1L (I _) = Refl

-- add_carry_spec

addCarrySpec : (p,q : Bip) -> bipCarry p q = bipSucc (p + q)
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
addComm : (p,q : Bip) -> p + q = q + p
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

addSuccR : (p,q : Bip) -> p + bipSucc q = bipSucc (p + q)
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

addSuccL : (p,q : Bip) -> bipSucc p + q = bipSucc (p + q)
addSuccL p q =
  rewrite addComm (bipSucc p) q in
  rewrite addComm p q in
  addSuccR q p

-- add_no_neutral
||| No neutral elements for addition
addNoNeutral : (p,q : Bip) -> Not (q + p = p)
addNoNeutral  p     U    = rewrite add1L p in succDiscr p . sym
addNoNeutral  U    (O _) = uninhabited
addNoNeutral (O a) (O b) = addNoNeutral a b . OInj
addNoNeutral (I a) (O b) = addNoNeutral a b . IInj
addNoNeutral  U    (I _) = uninhabited
addNoNeutral (O _) (I _) = uninhabited
addNoNeutral (I _) (I _) = uninhabited

--- add_carry_add

addCarryAdd : (p,q,r,s : Bip) -> bipCarry p r = bipCarry q s -> p + r = q + s
addCarryAdd p q r s =
  rewrite addCarrySpec p r in
  rewrite addCarrySpec q s in
  succInj (p+r) (q+s)

-- add_reg_r
-- TODO this can probably be simplified
addRegR : (p,q,r : Bip) -> p + r = q + r -> p = q
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

addRegL : (p,q,r : Bip) -> p + q = p + r -> q = r
addRegL p q r = rewrite addComm p q in
                rewrite addComm p r in
                addRegR q r p

-- there's no standard `<->` in Idris, only `Control.Isomorphism`
-- add_cancel_r
-- add_cancel_l

-- add_carry_reg_r

addCarryRegR : (p,q,r : Bip) -> bipCarry p r = bipCarry q r -> p = q
addCarryRegR p q r = addRegR p q r . addCarryAdd p q r r

-- add_carry_reg_l

addCarryRegL : (p,q,r : Bip) -> bipCarry p q = bipCarry p r -> q = r
addCarryRegL p q r = addRegL p q r . addCarryAdd p p q r

-- add_assoc
||| Addition is associative
addAssoc : (p,q,r : Bip) -> p + (q + r) = p + q + r
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

-- add_xO

addXO : (p,q : Bip) -> O (p+q) = O p + O q
addXO _ _ = Refl

-- add_xI_pred_double

addXIPredDouble : (p,q : Bip) -> O (p+q) = I p + bipDMO q
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

addXOPredDouble : (p,q : Bip) -> bipDMO (p+q) = O p + bipDMO q
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

addDiag : (p: Bip) -> p + p = O p
addDiag  U    = Refl
addDiag (O a) = cong $ addDiag a
addDiag (I a) =
  rewrite addCarrySpec a a in
  rewrite addDiag a in
  Refl

-- peano_rect

-- TODO how useful is this? we can't do custom induction

mutual
  peanoRect : (P : Bip -> Type) -> (a : P U) ->
              (f: (p : Bip) -> P p -> P (bipSucc p)) ->
              (p: Bip) -> P p
  peanoRect P a _  U    = a
  peanoRect P a f (O q) = peanoAux P a f q
  peanoRect P a f (I q) = f _ (peanoAux P a f q)

  peanoAux : (P : Bip -> Type) -> (a : P U) ->
             (f: (p : Bip) -> P p -> P (bipSucc p)) ->
             (p: Bip) -> P (O p)
  peanoAux P a f = peanoRect (P . O) (f _ a) (\_ => f _ . f _)

-- TODO rest of Peano?

-- mul_1_l

mul1L : (p: Bip) -> U * p = p
mul1L _ = Refl

-- mul_1_r

mul1R : (p: Bip) -> p * U = p
mul1R  U    = Refl
mul1R (O a) = cong $ mul1R a
mul1R (I a) = cong $ mul1R a

-- mul_xO_r

mulXOR : (p,q : Bip) -> p * O q = O (p * q)
mulXOR  U    _ = Refl
mulXOR (O a) q = cong $ mulXOR a q
mulXOR (I a) q = cong {f=O . bipPlus q} $ mulXOR a q

-- mul_xI_r

mulXIR : (p,q : Bip) -> p * I q = p + O (p * q)
mulXIR  U    _ = Refl
mulXIR (O a) q = cong $ mulXIR a q
mulXIR (I a) q =
  rewrite addComm a (q + O (a * q)) in
  rewrite sym $ addAssoc q (O (a * q)) a in
  rewrite addComm (O (a * q)) a in
  cong {f=I . bipPlus q} $ mulXIR a q

-- mul_comm
||| Commutativity of multiplication
mulComm : (p,q : Bip) -> p * q = q * p
mulComm p  U    = mul1R p
mulComm p (O b) = rewrite mulXOR p b in
                  cong $ mulComm p b
mulComm p (I b) = rewrite mulXIR p b in
                  cong {f=bipPlus p . O} $ mulComm p b

-- mul_add_distr_l

addShuffle : (p,q,r,s : Bip) -> (p+q)+(r+s) = (p+r)+(q+s)
addShuffle p q r s =
  rewrite addAssoc (p+q) r s in
  rewrite sym $ addAssoc p q r in
  rewrite addComm q r in
  rewrite addAssoc p r q in
  rewrite sym $ addAssoc (p+r) q s in
  Refl

mulAddDistrL : (p,q,r : Bip) -> p * (q + r) = p * q + p * r
mulAddDistrL  U    _ _ = Refl
mulAddDistrL (O a) q r = cong $ mulAddDistrL a q r
mulAddDistrL (I a) q r =
  rewrite mulAddDistrL a q r in
  rewrite sym $ addShuffle q (O (a*q)) r (O (a*r)) in
  Refl


-- mul_add_distr_r

mulAddDistrR : (p,q,r : Bip) -> (p + q) * r = p * r + q * r
mulAddDistrR p q r =
  rewrite mulComm (p+q) r in
  rewrite mulComm p r in
  rewrite mulComm q r in
  mulAddDistrL r p q

-- mul_assoc
||| Associativity of multiplication
mulAssoc : (p,q,r : Bip) -> p * (q * r) = p * q * r
mulAssoc  U    _ _ = Refl
mulAssoc (O a) q r = cong $ mulAssoc a q r
mulAssoc (I a) q r = rewrite mulAddDistrR q (O (a*q)) r in
                     cong {f=bipPlus (q*r) . O} $ mulAssoc a q r

-- mul_succ_l

mulSuccL : (p,q : Bip) -> (bipSucc p) * q = q + p * q
mulSuccL  U    q = sym $ addDiag q
mulSuccL (O _) _ = Refl
mulSuccL (I a) q =
  rewrite mulSuccL a q in
  rewrite addAssoc q q (O (a*q)) in
  rewrite addDiag q in
  Refl

-- mul_succ_r

mulSuccR : (p,q : Bip) -> p * (bipSucc q) = p + p * q
mulSuccR p q =
  rewrite mulComm p (bipSucc q) in
  rewrite mulComm p q in
  mulSuccL q p

-- mul_xI_mul_xO_discr

addXONotXO : (p,q,r : Bip) -> Not (r+(O (p*r)) = O (q*r))
addXONotXO _ _  U    = uninhabited
addXONotXO p q (O c) = rewrite mulXOR p c in
                       rewrite mulXOR q c in
                       addXONotXO p q c . OInj
addXONotXO _ _ (I _) = uninhabited

-- TODO the one above seems more useful

mulXIMulXODiscr : (p,q,r : Bip) -> Not ((I p) * r = (O q) * r)
mulXIMulXODiscr p q  U    = rewrite mul1R (I p) in
                            rewrite mul1R (O q) in
                            uninhabited
mulXIMulXODiscr p q (O c) = rewrite mulXOR p c in
                            rewrite mulXOR q c in
                            addXONotXO p q c . OInj
mulXIMulXODiscr _ _ (I _) = uninhabited

-- mul_xO_discr

mulXODiscr : (p,q : Bip) -> Not (O p * q = q)
mulXODiscr _  U    = uninhabited
mulXODiscr p (O b) = rewrite mulComm p (O b) in
                     rewrite mulComm b p in
                     mulXODiscr p b . OInj
mulXODiscr _ (I _) = uninhabited

-- mul_reg_r

mulOneNeutral : (p,q : Bip) -> p*q = q -> p = U
mulOneNeutral  p     U    = rewrite mul1R p in id
mulOneNeutral  U     _    = const Refl
mulOneNeutral (O a) (O b) = absurd . mulXODiscr a (O b)
mulOneNeutral (O _) (I _) = absurd
mulOneNeutral (I a) (O b) = rewrite addComm b (a*(O b)) in
                            absurd . addNoNeutral b (a*(O b)) . OInj
mulOneNeutral (I a) (I b) = rewrite addComm b (a*(I b)) in
                            absurd . addNoNeutral b (a*(I b)) . IInj

mulRegR : (p,q,r : Bip) -> p * r = q * r -> p = q
mulRegR  p     U     r = mulOneNeutral p r
mulRegR  U     q     r = sym . mulOneNeutral q r . sym
mulRegR (O a) (O b)  r = cong . mulRegR a b r . OInj
mulRegR (I a) (I b)  r =
  cong . mulRegR a b r . OInj . addRegL r (O (a*r)) (O (b*r))
mulRegR (I a) (O b)  r = absurd . addXONotXO a b r
mulRegR (O a) (I b)  r = absurd . addXONotXO b a r . sym

-- mul_reg_l

mulRegL : (p,q,r : Bip) -> r * p = r * q -> p = q
mulRegL p q r =
  rewrite mulComm r p in
  rewrite mulComm r q in
  mulRegR p q r

-- mul_eq_1_l

mulEq1L : (p,q : Bip) -> p * q = U -> p = U
mulEq1L  U     _    Refl = Refl
mulEq1L (O _)  _    Refl impossible
mulEq1L (I _)  U    Refl impossible
mulEq1L (I _) (O _) Refl impossible
mulEq1L (I _) (I _) Refl impossible

-- mul_eq_1_r

mulEq1R : (p,q : Bip) -> p * q = U -> q = U
mulEq1R p q = rewrite mulComm p q in mulEq1L q p

-- square_xO

squareXO : (p: Bip) -> (O p) * (O p) = O (O (p*p))
squareXO p = cong $ mulXOR p p

-- square_xI

squareXI : (p: Bip) -> (I p) * (I p) = I (O (p*p + p))
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

iterSwap : (f: a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f (f x) p = f (bipIter f x p)
iterSwap f x p = sym $ iterSwapGen {f} {g=f} {h=f} (\_ => Refl) x p

-- iter_succ

iterSucc : (f: a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f x (bipSucc p) = f (bipIter f x p)
iterSucc _ _  U    = Refl
iterSucc _ _ (O _) = Refl
iterSucc f x (I a) =
  rewrite iterSucc f x a in
  rewrite iterSwap f (bipIter f x a) (bipSucc a) in
  rewrite iterSucc f (bipIter f x a) a in
  Refl

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

iterSwap : (f: a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f (f x) p = f (bipIter f x p)
iterSwap f x p = sym $ iterSwapGen {f} {g=f} {h=f} (\_ => Refl) x p

-- iter_succ

iterSucc : (f: a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f x (bipSucc p) = f (bipIter f x p)
iterSucc _ _  U    = Refl
iterSucc _ _ (O _) = Refl
iterSucc f x (I a) =
  rewrite iterSucc f x a in
  rewrite iterSwap f (bipIter f x a) (bipSucc a) in
  rewrite iterSucc f (bipIter f x a) a in
  Refl

-- iter_add

iterAdd : (f: a -> a) -> (x: a) -> (p,q : Bip) ->
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

iterInvariant : (f: a -> a) -> (Inv : a -> Type) -> (p : Bip) ->
                ((x:a) -> Inv x -> Inv (f x)) ->
                (x:a) -> Inv x -> Inv (bipIter f x p)
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

powSuccR : (p,q : Bip) -> bipPow p (bipSucc q) = p * (bipPow p q)
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

subMaskSuccR : (p,q : Bip) -> bimMinus p (bipSucc q) = bimMinusCarry p q
subMaskSuccR  U         U    = Refl
subMaskSuccR  U        (O _) = Refl
subMaskSuccR  U        (I _) = Refl
subMaskSuccR (O U)      U    = Refl
subMaskSuccR (O (O _))  U    = Refl
subMaskSuccR (O (I _))  U    = Refl
subMaskSuccR (O _)     (O _) = Refl
subMaskSuccR (O a)     (I b) = cong $ subMaskSuccR a b
subMaskSuccR (I U)      U    = Refl
subMaskSuccR (I (O _))  U    = Refl
subMaskSuccR (I (I _))  U    = Refl
subMaskSuccR (I _)     (O _) = Refl
subMaskSuccR (I a)     (I b) = cong $ subMaskSuccR a b
