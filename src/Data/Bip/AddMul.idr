module Data.Bip.AddMul

import Data.Bip

%default total

-- xI_succ_xO is trivial

-- succ_discr

succDiscr : (p : Bip) -> Not (p = bipSucc p)
succDiscr  U    = absurd
succDiscr (O _) = absurd
succDiscr (I _) = absurd

-- pred_double_spec is trivial

-- succ_pred_double
export
succPredDouble : (p : Bip) -> bipSucc (bipDMO p) = O p
succPredDouble  U    = Refl
succPredDouble (O a) = cong O $ succPredDouble a
succPredDouble (I _) = Refl

-- pred_double_succ

predDoubleSucc : (p : Bip) -> bipDMO (bipSucc p) = I p
predDoubleSucc  U    = Refl
predDoubleSucc (O _) = Refl
predDoubleSucc (I a) = cong I $ predDoubleSucc a

-- double_succ is trivial

-- pred_double_x0_discr

predDoubleODiscr : (p : Bip) -> Not (bipDMO p = O p)
predDoubleODiscr  U    = absurd
predDoubleODiscr (O _) = absurd
predDoubleODiscr (I _) = absurd

-- succ_not_1
export
succNotU : (p : Bip) -> Not (bipSucc p = U)
succNotU  U    = absurd
succNotU (O _) = absurd
succNotU (I _) = absurd

-- pred_succ

predSucc : (p : Bip) -> bipPred (bipSucc p) = p
predSucc  U        = Refl
predSucc (O  _)    = Refl
predSucc (I  U)    = Refl
predSucc (I (O _)) = Refl
predSucc (I (I b)) = cong I $ predSucc (I b)

-- succ_pred_or

succPredOr : (p : Bip) -> Either (p = U) (bipSucc (bipPred p) = p)
succPredOr  U        = Left Refl
succPredOr (O  U)    = Right Refl
succPredOr (O (O b)) = Right $ cong O $ succPredDouble b
succPredOr (O (I _)) = Right Refl
succPredOr (I  _)    = Right Refl

-- succ_inj
||| Injectivity of successor
succInj : (p, q : Bip) -> bipSucc p = bipSucc q -> p = q
succInj  U     U    Refl = Refl
succInj  U    (O _) Refl impossible
succInj  U    (I a) prf  = absurd $ succNotU a (sym $ OInj prf)
succInj (O _)  U    prf  = absurd prf
succInj (O a) (O a) Refl = cong O Refl
succInj (O _) (I _) prf  = absurd prf
succInj (I a)  U    prf  = absurd $ succNotU a (OInj prf)
succInj (I _) (O _) prf  = absurd prf
succInj (I a) (I b) prf  = cong I $ succInj a b (OInj prf)

-- pred_N_succ

predBinSucc : (p : Bip) -> bipPredBin (bipSucc p) = BinP p
predBinSucc  U    = Refl
predBinSucc (O _) = Refl
predBinSucc (I a) = cong BinP $ predDoubleSucc a

-- add_1_r
export
add1R : (p : Bip) -> p + U = bipSucc p
add1R  U    = Refl
add1R (O _) = Refl
add1R (I _) = Refl

-- add_1_l
export
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
addCarrySpec (O a) (I b) = cong O $ addCarrySpec a b
addCarrySpec (I _)  U    = Refl
addCarrySpec (I a) (O b) = cong O $ addCarrySpec a b
addCarrySpec (I _) (I _) = Refl

-- add_comm
||| Commutativity
export
addComm : (p, q : Bip) -> p + q = q + p
addComm  p     U    = rewrite add1R p in
                      sym $ add1L p
addComm  U     q    = rewrite add1R q in
                      add1L q
addComm (O a) (O b) = cong O $ addComm a b
addComm (I a) (O b) = cong I $ addComm a b
addComm (O a) (I b) = cong I $ addComm a b
addComm (I a) (I b) = rewrite addCarrySpec a b in
                      rewrite addCarrySpec b a in
                      cong (O . bipSucc) $ addComm a b

-- add_succ_r

addSuccR : (p, q : Bip) -> p + bipSucc q = bipSucc (p + q)
addSuccR  U     q    = rewrite add1L (bipSucc q) in
                       cong bipSucc $ sym $ add1L q
addSuccR (O a)  U    = cong O $ add1R a
addSuccR (I a)  U    = cong I $ add1R a
addSuccR (O _) (O _) = Refl
addSuccR (I a) (O b) = cong O $ addCarrySpec a b
addSuccR (O a) (I b) = cong O $ addSuccR a b
addSuccR (I a) (I b) = rewrite addCarrySpec a b in
                       cong I $ addSuccR a b

-- add_succ_l
export
addSuccL : (p, q : Bip) -> bipSucc p + q = bipSucc (p + q)
addSuccL p q =
  rewrite addComm (bipSucc p) q in
  rewrite addComm p q in
  addSuccR q p

-- add_no_neutral
||| No neutral elements for addition
export
addNoNeutral : (p, q : Bip) -> Not (q + p = p)
addNoNeutral  p     U    = rewrite add1L p in \prf => succDiscr p $ sym prf
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
export
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
addRegR  U    (I b) (O c) = absurd . addNoNeutral c b . (\prf => sym $ IInj prf)
addRegR  U    (I b) (I c) =
  rewrite addCarrySpec b c in
  absurd . addNoNeutral c b . (\prf => sym $ succInj c (b+c) $ OInj prf)

addRegR (O _) (I _) (O _) = absurd
addRegR (O _) (I _) (I _) = absurd
addRegR (I _) (O _) (O _) = absurd
addRegR (I _) (O _) (I _) = absurd

addRegR  U     U    _     = const Refl
addRegR (O a) (O b) (O c) = cong O . addRegR a b c . OInj
addRegR (O a) (O b) (I c) = cong O . addRegR a b c . IInj
addRegR (I a) (I b) (O c) = cong I . addRegR a b c . IInj
addRegR (I a) (I b) (I c) =
  rewrite addCarrySpec a c in
  rewrite addCarrySpec b c in
  cong I . addRegR a b c . succInj (a+c) (b+c) . OInj

-- add_reg_l
export
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
export
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
addAssoc (O a) (O b) (O c) = cong O $ addAssoc a b c
addAssoc (O a) (O b) (I c) = cong I $ addAssoc a b c
addAssoc (O a) (I b) (O c) = cong I $ addAssoc a b c
addAssoc (O a) (I b) (I c) = rewrite addCarrySpec b c in
                             rewrite addCarrySpec (a+b) c in
                             rewrite addSuccR a (b+c) in
                             cong (O . bipSucc) $ addAssoc a b c
addAssoc (I a) (O b) (O c) = cong I $ addAssoc a b c
addAssoc (I a) (O b) (I c) = rewrite addCarrySpec a (b+c) in
                             rewrite addCarrySpec (a+b) c in
                             cong (O . bipSucc) $ addAssoc a b c
addAssoc (I a) (I b) (O c) = rewrite addCarrySpec a (b+c) in
                             rewrite addCarrySpec a b in
                             rewrite addSuccL (a+b) c in
                             cong (O . bipSucc) $ addAssoc a b c
addAssoc (I a) (I b) (I c) = rewrite addCarrySpec a b in
                             rewrite addCarrySpec b c in
                             rewrite addSuccR a (b+c) in
                             rewrite addSuccL (a+b) c in
                             cong (I . bipSucc) $ addAssoc a b c

-- add_xO is trivial

-- add_xI_pred_double
export
addXIPredDouble : (p, q : Bip) -> O (p+q) = I p + bipDMO q
addXIPredDouble p q =
  rewrite aux p (bipDMO q) in
  rewrite succPredDouble q in
  Refl
  where
  aux : (p,q : Bip) -> I p + q = O p + bipSucc q
  aux p  U    = cong O $ sym $ add1R p
  aux p (O _) = Refl
  aux p (I b) = rewrite addCarrySpec p b in
                cong O $ sym $ addSuccR p b

-- add_xO_pred_double

addXOPredDouble : (p, q : Bip) -> bipDMO (p+q) = O p + bipDMO q
addXOPredDouble  p     U    = rewrite add1R p in
                              predDoubleSucc p
addXOPredDouble  U    (O b) = rewrite add1L (bipDMO b) in
                              cong I $ sym $ succPredDouble b
addXOPredDouble (O a) (O b) = cong I $ addXOPredDouble a b
addXOPredDouble (I a) (O b) = cong I $ addXIPredDouble a b
addXOPredDouble  U    (I b) = cong I $ predDoubleSucc b
addXOPredDouble (O _) (I _) = Refl
addXOPredDouble (I a) (I b) = rewrite addCarrySpec a b in
                              cong I $ predDoubleSucc (a+b)

-- add_diag
export
addDiag : (p : Bip) -> p + p = O p
addDiag  U    = Refl
addDiag (O a) = cong O $ addDiag a
addDiag (I a) =
  rewrite addCarrySpec a a in
  rewrite addDiag a in
  Refl

-- mul_1_l is trivial

-- mul_1_r

mul1R : (p : Bip) -> p * U = p
mul1R  U    = Refl
mul1R (O a) = cong O $ mul1R a
mul1R (I a) = cong I $ mul1R a

-- mul_xO_r

mulXOR : (p, q : Bip) -> p * O q = O (p * q)
mulXOR  U    _ = Refl
mulXOR (O a) q = cong O $ mulXOR a q
mulXOR (I a) q = cong (O . bipPlus q) $ mulXOR a q

-- mul_xI_r

mulXIR : (p, q : Bip) -> p * I q = p + O (p * q)
mulXIR  U    _ = Refl
mulXIR (O a) q = cong O $ mulXIR a q
mulXIR (I a) q =
  rewrite addComm a (q + O (a * q)) in
  rewrite sym $ addAssoc q (O (a * q)) a in
  rewrite addComm (O (a * q)) a in
  cong (I . bipPlus q) $ mulXIR a q

-- mul_comm
||| Commutativity of multiplication
export
mulComm : (p, q : Bip) -> p * q = q * p
mulComm p  U    = mul1R p
mulComm p (O b) = rewrite mulXOR p b in
                  cong O $ mulComm p b
mulComm p (I b) = rewrite mulXIR p b in
                  cong (bipPlus p . O) $ mulComm p b

-- mul_add_distr_l

addShuffle : (p, q, r, s : Bip) -> (p+q)+(r+s) = (p+r)+(q+s)
addShuffle p q r s =
  rewrite addAssoc (p+q) r s in
  rewrite sym $ addAssoc p q r in
  rewrite addComm q r in
  rewrite addAssoc p r q in
  rewrite sym $ addAssoc (p+r) q s in
  Refl

export
mulAddDistrL : (p, q, r : Bip) -> p * (q + r) = p * q + p * r
mulAddDistrL  U    _ _ = Refl
mulAddDistrL (O a) q r = cong O $ mulAddDistrL a q r
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
mulAssoc (O a) q r = cong O $ mulAssoc a q r
mulAssoc (I a) q r = rewrite mulAddDistrR q (O (a*q)) r in
                     cong (bipPlus (q*r) . O) $ mulAssoc a q r

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
mulRegR  U     q     r = \prf => sym $ mulOneNeutral q r $ sym prf
mulRegR (O a) (O b)  r = cong O . mulRegR a b r . OInj
mulRegR (I a) (I b)  r =
  cong I . mulRegR a b r . OInj . addRegL r (O (a*r)) (O (b*r))
mulRegR (I a) (O b)  r = absurd . addXONotXO a b r
mulRegR (O a) (I b)  r = absurd . addXONotXO b a r . (\prf => sym prf)

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
squareXO p = cong O $ mulXOR p p

-- square_xI

squareXI : (p : Bip) -> (I p) * (I p) = I (O (p*p + p))
squareXI p =
  rewrite mulXIR p p in
  rewrite addAssoc p p (O(p*p)) in
  rewrite addDiag p in
  cong (I . O) $ addComm p (p*p)

-- square_spec

squareSpec : (p : Bip) -> bipSquare p = p * p
squareSpec  U    = Refl
squareSpec (O a) = rewrite mulComm a (O a) in
                   cong (O . O) $ squareSpec a
squareSpec (I a) =
  rewrite mulXIR a a in
  rewrite addAssoc a a (O (a*a)) in
  rewrite addDiag a in
  rewrite addComm (bipSquare a) a in
  cong (I . O . bipPlus a) $ squareSpec a
