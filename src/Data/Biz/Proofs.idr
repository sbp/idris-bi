module Data.Biz.Proofs

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub

import Data.Biz

%default total
%access public export

-- Properties of [pos_sub]

-- [pos_sub] can be written in term of positive comparison and subtraction (cf.
-- earlier definition of addition of Z)

-- pos_sub_spec
-- TODO workaround for #4001
posSubSpecHelp : (p, q : Bip) -> (o : Ordering) -> Biz
posSubSpecHelp p q LT = BizM (q-p)
posSubSpecHelp _ _ EQ = BizO
posSubSpecHelp p q GT = BizP (p-q)

posSubSpec : (p, q : Bip) -> bipMinusBiz p q = posSubSpecHelp p q (p `compare` q)
posSubSpec  U     U    = Refl
posSubSpec  U    (O _) = Refl
posSubSpec  U    (I _) = Refl
posSubSpec (O _)  U    = Refl
posSubSpec (O a) (O b) = rewrite posSubSpec a b in
                         aux
  where
  aux : bizD (posSubSpecHelp a b (a `compare` b)) = posSubSpecHelp (O a) (O b) (a `compare` b)
  aux with (a `compare` b) proof ab
    | EQ = Refl
    | LT = rewrite snd $ subMaskPos b a $ sym ab in
           Refl
    | GT = rewrite snd $ subMaskPos a b $ gtLt a b $ sym ab in
           Refl
posSubSpec (O a) (I b) = rewrite posSubSpec a b in
                         rewrite compareContSpec a b LT in
                         ?asdaux
  where
  aux : bizDMO (posSubSpecHelp a b (a `compare` b)) = posSubSpecHelp (O a) (I b) (switchEq LT (a `compare` b))
  aux with (a `compare` b) proof ab
    | EQ = rewrite subMaskNulFro b a $ sym $ compareEqIffTo a b $ sym ab in
           Refl
    | LT = rewrite snd $ subMaskPos b a $ sym ab in
           Refl
    | GT = rewrite subMaskCarrySpec a b in
           let (x**prf) = subMaskPos a b $ gtLt a b $ sym ab in
           rewrite prf in
           rewrite dpoPredDouble (BimP x) in
           Refl
posSubSpec (I _)  U    = Refl
posSubSpec (I a) (O b) = rewrite posSubSpec a b in
                         rewrite compareContSpec a b GT in
                         aux
  where
  aux : bizDPO (posSubSpecHelp a b (a `compare` b)) = posSubSpecHelp (I a) (O b) (switchEq GT (a `compare` b))
  aux with (a `compare` b) proof ab
    | EQ = rewrite subMaskNulFro a b $ compareEqIffTo a b $ sym ab in
           Refl
    | LT = rewrite subMaskCarrySpec b a in
           let (x**prf) = subMaskPos b a $ sym ab in
           rewrite prf in
           rewrite dpoPredDouble (BimP x) in
           Refl
    | GT = rewrite snd $ subMaskPos a b $ gtLt a b $ sym ab in
           Refl
posSubSpec (I a) (I b) = rewrite posSubSpec a b in
                         ?posSubSpec_rhs_6
  where
  aux : bizD (posSubSpecHelp a b (a `compare` b)) = posSubSpecHelp (I a) (I b) (a `compare` b)
  aux with (a `compare` b) proof ab
    | EQ = Refl
    | LT = rewrite snd $ subMaskPos b a $ sym ab in
           Refl
    | GT = rewrite snd $ subMaskPos a b $ gtLt a b $ sym ab in
           Refl

-- Particular cases of the previous result

-- pos_sub_diag

posSubDiag : (p : Bip) -> bipMinusBiz p p = 0
posSubDiag p = rewrite posSubSpec p p in
               rewrite compareContRefl p EQ in
               Refl

-- pos_sub_lt

posSubLt : (p, q : Bip) -> p `Lt` q -> bipMinusBiz p q = BizM (q - p)
posSubLt p q pltq = rewrite posSubSpec p q in
                    rewrite pltq in
                    Refl

-- pos_sub_gt

posSubGt : (p, q : Bip) -> q `Lt` p -> bipMinusBiz p q = BizP (p - q)
posSubGt p q qltp = rewrite posSubSpec p q in
                    rewrite compareAntisym q p in
                    rewrite qltp in
                    Refl

-- The opposite of [pos_sub] is [pos_sub] with reversed arguments
-- pos_sub_opp
oppD : (z : Biz) -> -(bizD z) = bizD (-z)
oppD  BizO    = Refl
oppD (BizP _) = Refl
oppD (BizM _) = Refl

oppDMODPO : (z : Biz) -> -(bizDMO z) = bizDPO (-z)
oppDMODPO  BizO    = Refl
oppDMODPO (BizP _) = Refl
oppDMODPO (BizM _) = Refl

oppDPODMO : (z : Biz) -> -(bizDPO z) = bizDMO (-z)
oppDPODMO  BizO    = Refl
oppDPODMO (BizP _) = Refl
oppDPODMO (BizM _) = Refl

posSubOpp : (p, q : Bip) -> -(bipMinusBiz p q) = bipMinusBiz q p
posSubOpp  U     U    = Refl
posSubOpp  U    (O _) = Refl
posSubOpp  U    (I _) = Refl
posSubOpp (O _)  U    = Refl
posSubOpp (O a) (O b) = rewrite sym $ posSubOpp a b in
                        oppD $ bipMinusBiz a b
posSubOpp (O a) (I b) = rewrite sym $ posSubOpp a b in
                        oppDMODPO $ bipMinusBiz a b
posSubOpp (I _)  U    = Refl
posSubOpp (I a) (O b) = rewrite sym $ posSubOpp a b in
                        oppDPODMO $ bipMinusBiz a b
posSubOpp (I a) (I b) = rewrite sym $ posSubOpp a b in
                        oppD $ bipMinusBiz a b

-- Results concerning [Zpos] and [Zneg] and the operators

-- opp_Zneg is trivial
-- opp_Zpos is trivial

-- succ_Zpos

succZpos : (p : Bip) -> bizSucc (BizP p) = BizP (bipSucc p)
succZpos p = cong $ add1R p

-- add_Zpos is trivial
-- add_Zneg is trivial
-- add_Zpos_Zneg is trivial
-- add_Zneg_Zpos is trivial

-- sub_Zpos

subZpos : (n, m : Bip) -> n `Lt` m -> (BizP m) - (BizP n) = BizP (m-n)
subZpos n m = posSubGt m n

-- mul_Zpos is trivial

-- pow_Zpos

powZpos : (p, q : Bip) -> bizPow (BizP p) (BizP q) = BizP (bipPow p q)
powZpos p q = sym $ iterSwapGen {f=BizP} {g = bipMult p} {h = bizMult $ BizP p} (\_ => Refl) U q

-- inj_Zpos is just bizPInj + cong
-- inj_Zneg is just bizMInj + cong

-- pos_xI is trivial
-- pos_xO is trivial
-- neg_xI is trivial
-- neg_xO is trivial

-- Properties of addition

-- Zero is neutral for addition

-- add_0_r

add0R : (n : Biz) -> n + 0 = n
add0R  BizO    = Refl
add0R (BizP _) = Refl
add0R (BizM _) = Refl

-- Addition is commutative

-- add_comm

addComm : (n, m : Biz) -> n + m = m + n
addComm  BizO     BizO    = Refl
addComm  BizO    (BizP _) = Refl
addComm  BizO    (BizM _) = Refl
addComm (BizP _)  BizO    = Refl
addComm (BizP a) (BizP b) = cong $ addComm a b
addComm (BizP _) (BizM _) = Refl
addComm (BizM _)  BizO    = Refl
addComm (BizM _) (BizP _) = Refl
addComm (BizM a) (BizM b) = cong $ addComm a b

oppInvolutive : (n : Biz) -> -(-n) = n
oppInvolutive  BizO    = Refl
oppInvolutive (BizP _) = Refl
oppInvolutive (BizM _) = Refl

-- Opposite distributes over addition

-- opp_add_distr

oppAddDistr : (n, m : Biz) -> -(n + m) = (-n) + (-m)
oppAddDistr  BizO     _       = Refl
oppAddDistr (BizP _)  BizO    = Refl
oppAddDistr (BizP _) (BizP _) = Refl
oppAddDistr (BizP a) (BizM b) = posSubOpp a b
oppAddDistr (BizM _)  BizO    = Refl
oppAddDistr (BizM a) (BizP b) = posSubOpp b a
oppAddDistr (BizM _) (BizM _) = Refl

-- Opposite is injective

-- opp_inj

oppInj : (n, m : Biz) -> -n = -m -> n = m
oppInj  BizO     BizO    = id
oppInj  BizO    (BizP _) = absurd
oppInj  BizO    (BizM _) = absurd
oppInj (BizP _)  BizO    = absurd
oppInj (BizP _) (BizP _) = cong . bizMInj
oppInj (BizP _) (BizM _) = absurd
oppInj (BizM _)  BizO    = absurd
oppInj (BizM _) (BizP _) = absurd
oppInj (BizM _) (BizM _) = cong . bizPInj

-- Addition is associative

-- pos_sub_add

posSubAdd : (p, q, r : Bip) -> bipMinusBiz (p+q) r = (BizP p) + bipMinusBiz q r
posSubAdd p q r = rewrite posSubSpec q r in
                  aux
  where
  aux : bipMinusBiz (p+q) r = (BizP p) + (posSubSpecHelp q r (q `compare` r))
  aux with (q `compare` r) proof qr
    | EQ = rewrite compareEqIffTo q r $ sym qr in
           rewrite posSubGt (p+r) r $
              rewrite addComm p r in
              ltAddDiagR r p
             in
           cong $ addSub p r
    | LT = rewrite sym $ subAdd r q $ sym qr in
           rewrite posSubSpec (p+q) ((r-q)+q) in
           rewrite addCompareMonoR q p (r-q) in
           rewrite subAdd r q $ sym qr in     -- revert the second instance of `r`, pity you can't rewrite at specific site
           aux2
      where
        aux2 : posSubSpecHelp (p+q) r (p `compare` (r-q)) = bipMinusBiz p (r-q)
        aux2 with (p `compare` (r-q)) proof prq
          | EQ = rewrite compareEqIffTo p (r-q) $ sym prq in
                 sym $ posSubDiag (r-q)
          | LT = rewrite posSubLt p (r-q) $ sym prq in
                 rewrite addComm p q in
                 cong $ subAddDistr r q p $
                   rewrite sym $ subAdd r q $ sym qr in
                   rewrite addComm q p in
                   addLtMonoRTo q p (r-q) $ sym prq
          | GT = let rqp = gtLt p (r-q) $ sym prq in
                 rewrite posSubGt p (r-q) rqp in
                 cong $ sym $ subSubDistr p r q (sym qr) rqp
    | GT = let rq = gtLt q r $ sym qr
               rltpq = ltTrans r q (p+q) rq $
                 rewrite addComm p q in ltAddDiagR q p
             in
           rewrite posSubGt (p+q) r rltpq in
           cong $ sym $ addSubAssoc p q r rq

-- add_assoc

addPAssoc : (x : Bip) -> (y, z : Biz) -> (BizP x) + (y + z) = (BizP x) + y + z
addPAssoc _  BizO     BizO    = Refl
addPAssoc _  BizO    (BizP _) = Refl
addPAssoc _  BizO    (BizM _) = Refl
addPAssoc _ (BizP _)  BizO    = Refl
addPAssoc x (BizP a) (BizP b) = cong $ addAssoc x a b
addPAssoc x (BizP a) (BizM b) = sym $ posSubAdd x a b
addPAssoc x (BizM a)  BizO    = sym $ add0R $ bipMinusBiz x a
addPAssoc x (BizM a) (BizP b) =
  rewrite sym $ posSubAdd x b a in
  rewrite addComm (bipMinusBiz x a) (BizP b) in
  rewrite sym $ posSubAdd b x a in
  rewrite addComm x b in
  Refl
addPAssoc x (BizM a) (BizM b) =
  oppInj (bipMinusBiz x (a+b)) ((bipMinusBiz x a)+(BizM b)) $
  rewrite posSubOpp x (a+b) in
  rewrite oppAddDistr (bipMinusBiz x a) (BizM b) in
  rewrite posSubOpp x a in
  rewrite addComm (bipMinusBiz a x) (BizP b) in
  rewrite sym $ posSubAdd b a x in
  rewrite addComm a b in
  Refl

addAssoc : (n, m, p : Biz) -> n + (m + p) = n + m + p
addAssoc    BizO    _ _ = Refl
addAssoc   (BizP a) m p = addPAssoc a m p
addAssoc n@(BizM a) m p =
  oppInj (n+(m+p)) (n+m+p) $
  rewrite oppAddDistr n (m+p) in
  rewrite oppAddDistr m p in
  rewrite oppAddDistr (n+m) p in
  rewrite oppAddDistr n m in
  addPAssoc a (-m) (-p)

-- Subtraction and successor

-- sub_succ_l

subSuccL : (n, m : Biz) -> bizSucc n - m = bizSucc (n - m)
subSuccL n m = rewrite sym $ addAssoc n 1 (-m) in
               rewrite sym $ addAssoc n (-m) 1 in
               rewrite addComm 1 (-m) in
               Refl

-- Opposite is inverse for additio

-- add_opp_diag_r

addOppDiagR : (n : Biz) -> n + (-n) = 0
addOppDiagR  BizO    = Refl
addOppDiagR (BizP a) = posSubDiag a
addOppDiagR (BizM a) = posSubDiag a

-- add_opp_diag_l

addOppDiagL : (n : Biz) -> (-n) + n = 0
addOppDiagL n = rewrite addComm (-n) n in
                addOppDiagR n

-- Multiplication and constants

-- mul_1_l

mul1L : (n : Biz) -> 1 * n = n
mul1L  BizO    = Refl
mul1L (BizP _) = Refl
mul1L (BizM _) = Refl

-- mul_1_r

mul1R : (n : Biz) -> n * 1 = n
mul1R  BizO    = Refl
mul1R (BizP a) = cong $ mul1R a
mul1R (BizM a) = cong $ mul1R a

mul0R : (n : Biz) -> n * 0 = 0
mul0R  BizO    = Refl
mul0R (BizP _) = Refl
mul0R (BizM _) = Refl

-- Commutativity of multiplication

-- mul_comm

mulComm : (n, m : Biz) -> n * m = m * n
mulComm  BizO     BizO    = Refl
mulComm  BizO    (BizP _) = Refl
mulComm  BizO    (BizM _) = Refl
mulComm (BizP _)  BizO    = Refl
mulComm (BizP a) (BizP b) = cong $ mulComm a b
mulComm (BizP a) (BizM b) = cong $ mulComm a b
mulComm (BizM _)  BizO    = Refl
mulComm (BizM a) (BizP b) = cong $ mulComm a b
mulComm (BizM a) (BizM b) = cong $ mulComm a b

-- Associativity of multiplication

-- mul_assoc

mulAssoc : (n, m, p : Biz) -> n * (m * p) = n * m * p
mulAssoc  BizO     _        _       = Refl
mulAssoc  n        BizO     _       = rewrite mul0R n in
                                      Refl
mulAssoc  n        m        BizO    =
  rewrite mul0R m in
  rewrite mul0R n in
  rewrite mul0R (n*m) in
  Refl
mulAssoc (BizP a) (BizP b) (BizP c) = cong $ mulAssoc a b c
mulAssoc (BizP a) (BizP b) (BizM c) = cong $ mulAssoc a b c
mulAssoc (BizP a) (BizM b) (BizP c) = cong $ mulAssoc a b c
mulAssoc (BizP a) (BizM b) (BizM c) = cong $ mulAssoc a b c
mulAssoc (BizM a) (BizP b) (BizP c) = cong $ mulAssoc a b c
mulAssoc (BizM a) (BizP b) (BizM c) = cong $ mulAssoc a b c
mulAssoc (BizM a) (BizM b) (BizP c) = cong $ mulAssoc a b c
mulAssoc (BizM a) (BizM b) (BizM c) = cong $ mulAssoc a b c

-- Multiplication and Opposite

-- mul_opp_l

mulOppL : (n, m : Biz) -> (-n) * m = -(n * m)
mulOppL  BizO     _       = Refl
mulOppL  n        BizO    = rewrite mul0R n in
                            mul0R (-n)
mulOppL (BizP _) (BizP _) = Refl
mulOppL (BizP _) (BizM _) = Refl
mulOppL (BizM _) (BizP _) = Refl
mulOppL (BizM _) (BizM _) = Refl

-- mul_opp_r

mulOppR : (n, m : Biz) -> n * (-m) = -(n * m)
mulOppR n m = rewrite mulComm n (-m) in
              rewrite mulComm n m in
              mulOppL m n

-- mul_opp_opp

mulOppOpp : (n, m : Biz) -> (-n) * (-m) = n * m
mulOppOpp n m = rewrite mulOppL n (-m) in
                rewrite mulOppR n m in
                oppInvolutive (n*m)

-- mul_opp_comm

mulOppComm : (n, m : Biz) -> (-n) * m = n * (-m)
mulOppComm n m = rewrite mulOppR n m in
                 mulOppL n m

-- Distributivity of multiplication over addition

-- mul_add_distr_pos

mulAddDistrPosHelp : (p, q, r : Bip) -> (BizP p)*(bipMinusBiz q r) = bipMinusBiz (p*q) (p*r)
mulAddDistrPosHelp p q r =
  rewrite posSubSpec q r in
  rewrite posSubSpec (p*q) (p*r) in
  rewrite mulCompareMonoL p q r in
  aux
  where
  aux : (BizP p)*(posSubSpecHelp q r (q `compare` r)) = posSubSpecHelp (p*q) (p*r) (q `compare` r)
  aux with (q `compare` r) proof qr
    | EQ = Refl
    | LT = cong $ mulSubDistrL p r q $ sym qr
    | GT = cong $ mulSubDistrL p q r $ gtLt q r $ sym qr

mulAddDistrPos : (p : Bip) -> (n, m : Biz) -> (BizP p) * (n + m) = (BizP p) * n + (BizP p) * m
mulAddDistrPos _  BizO     _       = Refl
mulAddDistrPos p  n        BizO    = rewrite add0R n in
                                     rewrite add0R ((BizP p)*n) in
                                     Refl
mulAddDistrPos p (BizP a) (BizP b) = cong $ mulAddDistrL p a b
mulAddDistrPos p (BizP a) (BizM b) = mulAddDistrPosHelp p a b
mulAddDistrPos p (BizM a) (BizP b) = mulAddDistrPosHelp p b a
mulAddDistrPos p (BizM a) (BizM b) = cong $ mulAddDistrL p a b

-- mul_add_distr_l

mulAddDistrL : (n, m, p : Biz) -> n * (m + p) = n * m + n * p
mulAddDistrL  BizO    _ _ = Refl
mulAddDistrL (BizP a) m p = mulAddDistrPos a m p
mulAddDistrL (BizM a) m p =
  rewrite mulOppL (BizP a) (m+p) in
  rewrite mulAddDistrPos a m p in
  rewrite oppAddDistr ((BizP a)*m) ((BizP a)*p) in
  rewrite sym $ mulOppL (BizP a) m in
  rewrite sym $ mulOppL (BizP a) p in
  Refl

-- mul_add_distr_r

mulAddDistrR : (n, m, p : Biz) -> (n + m) * p = n * p + m * p
mulAddDistrR n m p =
  rewrite mulComm (n+m) p in
  rewrite mulComm n p in
  rewrite mulComm m p in
  mulAddDistrL p n m

-- Proofs of specifications

-- Specification of constants

-- one_succ is trivial
-- two_succ is trivial

-- Specification of addition

-- add_0_l is trivial

-- add_succ_l

addSuccL : (n, m : Biz) -> bizSucc n + m = bizSucc (n + m)
addSuccL n m = rewrite sym $ addAssoc n 1 m in
               rewrite sym $ addAssoc n m 1 in
               rewrite addComm 1 m in
               Refl


-- Specification of opposite

-- opp_0 is trivial

-- opp_succ

oppSucc : (n : Biz) -> -(bizSucc n) = bizPred (-n)
oppSucc n = oppAddDistr n 1

-- Specification of successor and predecessor

-- succ_pred

succPred : (n : Biz) -> bizSucc (bizPred n) = n
succPred n = rewrite sym $ addAssoc n (-1) 1 in
             add0R n

-- pred_succ

predSucc : (n : Biz) -> bizPred (bizSucc n) = n
predSucc n = rewrite sym $ addAssoc n 1 (-1) in
             add0R n

-- Specification of subtraction

-- sub_0_r

sub0R : (n : Biz) -> n - 0 = n
sub0R = add0R

-- sub_succ_r

subSuccR : (n, m : Biz) -> n - bizSucc m = bizPred (n - m)
subSuccR n m = rewrite oppAddDistr m 1 in
               addAssoc n (-m) (-1)

-- Specification of multiplication

-- mul_0_l is trivial

-- mul_succ_l

mulSuccL : (n, m : Biz) -> bizSucc n * m = n * m + m
mulSuccL n m = rewrite mulAddDistrR n 1 m in
               rewrite mul1L m in
               Refl

-- Specification of comparisons and order

-- eqb_eq

-- TODO split into `to` and `fro`

eqbEqTo : (n, m : Biz) -> n == m = True -> n = m
eqbEqTo  BizO     BizO    = const Refl
eqbEqTo  BizO    (BizP _) = absurd
eqbEqTo  BizO    (BizM _) = absurd
eqbEqTo (BizP _)  BizO    = absurd
eqbEqTo (BizP a) (BizP b) = cong . eqbEqTo a b
eqbEqTo (BizP _) (BizM _) = absurd
eqbEqTo (BizM _)  BizO    = absurd
eqbEqTo (BizM _) (BizP _) = absurd
eqbEqTo (BizM a) (BizM b) = cong . eqbEqTo a b

eqbEqFro : (n, m : Biz) -> n = m -> n == m = True
eqbEqFro  BizO     BizO    = const Refl
eqbEqFro  BizO    (BizP _) = absurd
eqbEqFro  BizO    (BizM _) = absurd
eqbEqFro (BizP _)  BizO    = absurd
eqbEqFro (BizP a) (BizP b) = eqbEqFro a b . bizPInj
eqbEqFro (BizP _) (BizM _) = absurd
eqbEqFro (BizM _)  BizO    = absurd
eqbEqFro (BizM _) (BizP _) = absurd
eqbEqFro (BizM a) (BizM b) = eqbEqFro a b . bizMInj

Lt : (x, y : Biz) -> Type
Lt x y = x `compare` y = LT

Gt : (x, y : Biz) -> Type
Gt x y = x `compare` y = GT

Le : (x, y : Biz) -> Type
Le x y = Not (x `compare` y = GT)

Ge : (x, y : Biz) -> Type
Ge x y = Not (x `compare` y = LT)

-- ltb_lt

-- TODO split into `to` and `fro`

ltbLtTo : (n, m : Biz) -> n < m = True -> n `Lt` m
ltbLtTo n m prf with (n `compare` m)
  | LT = Refl
  | EQ = absurd prf
  | GT = absurd prf

ltbLtFro : (n, m : Biz) -> n `Lt` m -> n < m = True
ltbLtFro _ _ nltm = rewrite nltm in
                    Refl

-- leb_le

-- TODO split into `to` and `fro`

lebLeTo : (n, m : Biz) -> n > m = False -> n `Le` m
lebLeTo n m prf nm with (n `compare` m)
  | LT = absurd nm
  | EQ = absurd nm
  | GT = absurd prf

lebLeFro : (n, m : Biz) -> n `Le` m -> n > m = False
lebLeFro n m nlem with (n `compare` m)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ nlem Refl

-- compare_eq_iff
-- TODO split into `to` and `fro`

compareEqIffTo : (n, m : Biz) -> n `compare` m = EQ -> n = m
compareEqIffTo  BizO     BizO    = const Refl
compareEqIffTo  BizO    (BizP _) = absurd
compareEqIffTo  BizO    (BizM _) = absurd
compareEqIffTo (BizP _)  BizO    = absurd
compareEqIffTo (BizP a) (BizP b) = cong . compareEqIffTo a b
compareEqIffTo (BizP _) (BizM _) = absurd
compareEqIffTo (BizM _)  BizO    = absurd
compareEqIffTo (BizM _) (BizP _) = absurd
compareEqIffTo (BizM a) (BizM b) = sym . cong . compareEqIffTo b a

compareEqIffFro : (n, m : Biz) -> n = m -> n `compare` m = EQ
compareEqIffFro  BizO     BizO    = const Refl
compareEqIffFro  BizO    (BizP _) = absurd
compareEqIffFro  BizO    (BizM _) = absurd
compareEqIffFro (BizP _)  BizO    = absurd
compareEqIffFro (BizP a) (BizP b) = compareEqIffFro a b . bizPInj
compareEqIffFro (BizP _) (BizM _) = absurd
compareEqIffFro (BizM _)  BizO    = absurd
compareEqIffFro (BizM _) (BizP _) = absurd
compareEqIffFro (BizM a) (BizM b) = compareEqIffFro b a . bizMInj . sym

-- compare_sub

compareSub : (n, m : Biz) -> n `compare` m = (n - m) `compare` 0
compareSub  BizO     BizO    = Refl
compareSub  BizO    (BizP _) = Refl
compareSub  BizO    (BizM _) = Refl
compareSub (BizP _)  BizO    = Refl
compareSub (BizP a) (BizP b) = rewrite posSubSpec a b in
                               aux
  where
  aux : a `compare` b = (posSubSpecHelp a b (a `compare` b)) `compare` 0
  aux with (a `compare` b)
    | LT = Refl
    | EQ = Refl
    | GT = Refl
compareSub (BizP _) (BizM _) = Refl
compareSub (BizM _)  BizO    = Refl
compareSub (BizM _) (BizP _) = Refl
compareSub (BizM a) (BizM b) = rewrite posSubSpec b a in
                               aux
  where
  aux : b `compare` a = (posSubSpecHelp b a (b `compare` a)) `compare` 0
  aux with (b `compare` a)
    | LT = Refl
    | EQ = Refl
    | GT = Refl

-- compare_antisym

compareAntisym : (n, m : Biz) -> m `compare` n = compareOp (n `compare` m)
compareAntisym  BizO     BizO    = Refl
compareAntisym  BizO    (BizP _) = Refl
compareAntisym  BizO    (BizM _) = Refl
compareAntisym (BizP _)  BizO    = Refl
compareAntisym (BizP a) (BizP b) = compareAntisym a b
compareAntisym (BizP _) (BizM _) = Refl
compareAntisym (BizM _)  BizO    = Refl
compareAntisym (BizM _) (BizP _) = Refl
compareAntisym (BizM a) (BizM b) = compareAntisym b a

-- compare_lt_iff is trivial
-- compare_le_iff is trivial