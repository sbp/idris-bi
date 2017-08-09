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
succDiscr U prf = absurd prf
succDiscr (O _) prf = absurd prf
succDiscr (I _) prf = absurd prf

-- pred_double_spec

predDoubleSpec : (p: Bip) -> bipDMO p = bipPred (O p)
predDoubleSpec _ = Refl

-- succ_pred_double

succPredDouble : (p: Bip) -> bipSucc (bipDMO p) = O p
succPredDouble U = Refl
succPredDouble (O a) = rewrite succPredDouble a in Refl
succPredDouble (I _) = Refl

-- pred_double_succ

predDoubleSucc : (p: Bip) -> bipDMO (bipSucc p) = I p
predDoubleSucc U = Refl
predDoubleSucc (O _) = Refl
predDoubleSucc (I a) = rewrite predDoubleSucc a in Refl

-- double_succ

doubleSucc : (p: Bip) -> (O (bipSucc p)) = (bipSucc (bipSucc (O p)))
doubleSucc _ = Refl

-- pred_double_x0_discr

predDoubleODiscr : (p: Bip) -> Not ((bipDMO p) = (O p))
predDoubleODiscr U = absurd
predDoubleODiscr (O _) = absurd
predDoubleODiscr (I _) = absurd

-- succ_not_1

succNotU : (p: Bip) -> Not ((bipSucc p) = U)
succNotU U = absurd
succNotU (O _) = absurd
succNotU (I _) = absurd

-- pred_succ

predSucc : (p: Bip) -> bipPred (bipSucc p) = p
predSucc U = Refl
predSucc (O _) = Refl
predSucc (I a) = case a of
  U => Refl
  (O _) => Refl
  (I b) => rewrite predSucc (I b) in Refl

-- succ_pred_or

succPredOr : (p: Bip) -> Either (p = U) ((bipSucc (bipPred p)) = p)
succPredOr U = Left Refl
succPredOr (O a) = case a of
  U => Right Refl
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
succInj U U Refl = Refl
succInj U (O _) Refl impossible
succInj U (I a) prf = absurd $ succNotU a (sym $ OInj prf)
succInj (O _) U prf = absurd prf
succInj (O a) (O a) Refl = cong {f=O} Refl
succInj (O _) (I _) prf = absurd prf
succInj (I a) U prf = absurd $ succNotU a (OInj prf)
succInj (I _) (O _) prf = absurd $ sym prf
succInj (I a) (I b) prf = cong $ succInj a b (OInj prf)

-- pred_N_succ

predNSucc : (p: Bip) -> bipPredN (bipSucc p) = BinP p
predNSucc U = Refl
predNSucc (O _) = Refl
predNSucc (I a) = cong $ predDoubleSucc a

-- add_1_r

add1R : (p: Bip) -> p + U = bipSucc p
add1R U = Refl
add1R (O _) = Refl
add1R (I _) = Refl

-- add_1_l

add1L : (p: Bip) -> U + p = bipSucc p
add1L U = Refl
add1L (O _) = Refl
add1L (I _) = Refl

-- add_carry_spec

addCarrySpec : (p,q : Bip) -> bipCarry p q = bipSucc (p + q)
addCarrySpec U U = Refl
addCarrySpec U (O _) = Refl
addCarrySpec U (I _) = Refl
addCarrySpec (O _) U = Refl
addCarrySpec (O _) (O _) = Refl
addCarrySpec (O a) (I b) = cong $ addCarrySpec a b
addCarrySpec (I _) U = Refl
addCarrySpec (I a) (O b) = cong $ addCarrySpec a b
addCarrySpec (I _) (I _) = Refl

-- add_comm
||| Commutativity
addComm : (p,q : Bip) -> p + q = q + p
addComm p U = rewrite add1R p in
              rewrite add1L p in Refl
addComm U q = rewrite add1R q in
              rewrite add1L q in Refl
addComm (O a) (O b) = cong $ addComm a b
addComm (I a) (O b) = cong $ addComm a b
addComm (O a) (I b) = cong $ addComm a b
addComm (I a) (I b) = cong {f=O} $ rewrite addCarrySpec a b in
                                   rewrite addCarrySpec b a in
                                   cong $ addComm a b

-- add_succ_r

addSuccR : (p,q : Bip) -> p + bipSucc q = bipSucc (p + q)
addSuccR U q = rewrite add1L (bipSucc q) in
               rewrite add1L q in Refl
addSuccR (O a) U = cong $ add1R a
addSuccR (I a) U = cong $ add1R a
addSuccR (O _) (O _) = Refl
addSuccR (I a) (O b) = cong $ addCarrySpec a b
addSuccR (O a) (I b) = cong $ addSuccR a b
addSuccR (I a) (I b) = cong {f=I} $ rewrite addCarrySpec a b in addSuccR a b

-- add_succ_l

addSuccL : (p,q : Bip) -> bipSucc p + q = bipSucc (p + q)
addSuccL p q = rewrite addComm (bipSucc p) q in
               rewrite addComm p q in
               addSuccR q p

-- add_no_neutral
||| No neutral elements for addition
addNoNeutral : (p,q : Bip) -> Not (q + p = p)
addNoNeutral p U = rewrite add1L p in succDiscr p . sym
addNoNeutral U (O _) = uninhabited . sym
addNoNeutral (O a) (O b) = addNoNeutral a b . OInj
addNoNeutral (I a) (O b) = addNoNeutral a b . IInj
addNoNeutral U (I _) = uninhabited . sym
addNoNeutral (O _) (I _) = uninhabited
addNoNeutral (I _) (I _) = uninhabited . sym

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

addRegR (O _)  U    (O _) = absurd . sym
addRegR (O _)  U    (I _) = absurd
addRegR (I a)  U    (O c) = absurd . addNoNeutral c a . IInj
addRegR (I a)  U    (I c) = rewrite addCarrySpec a c in
                            absurd . addNoNeutral c a . succInj (a+c) c . OInj

addRegR  U    (O _) (O _) = absurd
addRegR  U    (O _) (I _) = absurd . sym
addRegR  U    (I b) (O c) = absurd . addNoNeutral c b . sym . IInj
addRegR  U    (I b) (I c) = rewrite addCarrySpec b c in
                            absurd . addNoNeutral c b . sym . succInj c (b+c) . OInj

addRegR (O _) (I _) (O _) = absurd . sym
addRegR (O _) (I _) (I _) = absurd
addRegR (I _) (O _) (O _) = absurd
addRegR (I _) (O _) (I _) = absurd . sym

addRegR  U     U    _     = const Refl
addRegR (O a) (O b) (O c) = cong . addRegR a b c . OInj
addRegR (O a) (O b) (I c) = cong . addRegR a b c . IInj
addRegR (I a) (I b) (O c) = cong . addRegR a b c . IInj
addRegR (I a) (I b) (I c) = rewrite addCarrySpec a c in
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
                             cong {f=O} $
                               rewrite addSuccR a (b+c) in
                               cong {f=bipSucc} $ addAssoc a b c
addAssoc (I a) (O b) (O c) = cong $ addAssoc a b c
addAssoc (I a) (O b) (I c) = cong {f=O} $
                               rewrite addCarrySpec a (b+c) in
                               rewrite addCarrySpec (a+b) c in
                               cong {f=bipSucc} $ addAssoc a b c
addAssoc (I a) (I b) (O c) = cong {f=O} $
                               rewrite addCarrySpec a (b+c) in
                               rewrite addCarrySpec a b in
                               rewrite addSuccL (a+b) c in
                               cong {f=bipSucc} $ addAssoc a b c
addAssoc (I a) (I b) (I c) = cong {f=I} $
                               rewrite addCarrySpec a b in
                               rewrite addCarrySpec b c in
                               rewrite addSuccR a (b+c) in
                               rewrite addSuccL (a+b) c in
                               cong {f=bipSucc} $ addAssoc a b c

-- add_xO

addXO : (p,q : Bip) -> O (p+q) = O p + O q
addXO _ _ = Refl

-- add_xI_pred_double


addXIPredDouble : (p,q : Bip) -> O (p+q) = I p + bipDMO q
addXIPredDouble p q = rewrite aux p (bipDMO q) in
                      rewrite succPredDouble q in
                      Refl
  where
  aux : (p,q : Bip) -> I p + q = O p + bipSucc q
  aux p U = cong $ sym $ add1R p
  aux p (O _) = Refl
  aux p (I b) = cong {f=O} $ rewrite addCarrySpec p b in
                             sym $ addSuccR p b

-- add_xO_pred_double

addXOPredDouble : (p,q : Bip) -> bipDMO (p+q) = O p + bipDMO q
addXOPredDouble  p     U    = rewrite add1R p in predDoubleSucc p
addXOPredDouble  U    (O b) = cong {f=I} $ rewrite add1L (bipDMO b) in
                                           sym $ succPredDouble b
addXOPredDouble (O a) (O b) = cong {f=I} $ addXOPredDouble a b
addXOPredDouble (I a) (O b) = cong {f=I} $ addXIPredDouble a b
addXOPredDouble  U    (I b) = cong {f=I} $ predDoubleSucc b
addXOPredDouble (O _) (I _) = Refl
addXOPredDouble (I a) (I b) = cong {f=I} $ rewrite addCarrySpec a b in
                                           predDoubleSucc (a+b)

-- add_diag

addDiag : (p: Bip) -> p + p = O p
addDiag U = Refl
addDiag (O a) = cong $ addDiag a
addDiag (I a) = cong {f=O} $ rewrite addCarrySpec a a in
                             rewrite addDiag a in
                             Refl

-- TODO Peano
--

-- mul_1_l

mul1L : (p: Bip) -> U * p = p
mul1L _ = Refl

-- mul_1_r

mul1R : (p: Bip) -> p * U = p
mul1R U = Refl
mul1R (O a) = cong $ mul1R a
mul1R (I a) = cong $ mul1R a

-- mul_xO_r

mulXOR : (p,q : Bip) -> p * O q = O (p * q)
mulXOR U _ = Refl
mulXOR (O a) q = cong $ mulXOR a q
mulXOR (I a) q = cong {f=\x=>O(q+x)} $ mulXOR a q

-- mul_xI_r

mulXIR : (p,q : Bip) -> p * I q = p + O (p * q)
mulXIR U _ = Refl
mulXIR (O a) q = cong $ mulXIR a q
mulXIR (I a) q = cong {f=I} $ rewrite addComm a (q + O (a * q)) in
                              rewrite sym $ addAssoc q (O (a * q)) a in
                              rewrite addComm (O (a * q)) a in
                              cong {f=bipPlus q} $ mulXIR a q

-- mul_comm
||| Commutativity of multiplication
mulComm : (p,q : Bip) -> p * q = q * p
mulComm p U = mul1R p
mulComm p (O a) = rewrite mulComm a p in mulXOR p a
mulComm p (I a) = rewrite mulComm a p in mulXIR p a
