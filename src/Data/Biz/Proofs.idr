module Data.Biz.Proofs

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub
import Data.Bip.SqrtDiv

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
                         aux
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
                         aux
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
posSubDiag p =
  rewrite posSubSpec p p in
  rewrite compareContRefl p EQ in
  Refl

-- pos_sub_lt

posSubLt : (p, q : Bip) -> p `Lt` q -> bipMinusBiz p q = BizM (q - p)
posSubLt p q pltq =
  rewrite posSubSpec p q in
  rewrite pltq in
  Refl

-- pos_sub_gt

posSubGt : (p, q : Bip) -> q `Lt` p -> bipMinusBiz p q = BizP (p - q)
posSubGt p q qltp =
  rewrite posSubSpec p q in
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
subSuccL n m =
  rewrite sym $ addAssoc n 1 (-m) in
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
mulOppR n m =
  rewrite mulComm n (-m) in
  rewrite mulComm n m in
  mulOppL m n

-- mul_opp_opp

mulOppOpp : (n, m : Biz) -> (-n) * (-m) = n * m
mulOppOpp n m =
  rewrite mulOppL n (-m) in
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
mulAddDistrPos p  n        BizO    =
  rewrite add0R n in
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
addSuccL n m =
  rewrite sym $ addAssoc n 1 m in
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
mulSuccL n m =
  rewrite mulAddDistrR n 1 m in
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

-- Some more advanced properties of comparison and orders, including
-- [compare_spec] and [lt_irrefl] and [lt_eq_cases].

-- Remaining specification of [lt] and [le]

-- lt_succ_r
-- TODO split into `to` and `fro`

ltSuccRTo : (n, m : Biz) -> n `Lt` bizSucc m -> n `Le` m
ltSuccRTo n m =
  rewrite compareSub n (m+1) in
  rewrite subSuccR n m in
  rewrite compareSub n m in
  aux
  where
  aux : (n-m)-1 `Lt` 0 -> n-m `Gt` 0 -> Void
  aux nm1lt0 nmgt0 with (n-m)
    | BizO       = absurd nmgt0
    | BizP  U    = absurd nm1lt0
    | BizP (O _) = absurd nm1lt0
    | BizP (I _) = absurd nm1lt0
    | BizM  _    = absurd nmgt0

ltSuccRFro : (n, m : Biz) -> n `Le` m -> n `Lt` bizSucc m
ltSuccRFro n m =
  rewrite compareSub n (m+1) in
  rewrite subSuccR n m in
  rewrite compareSub n m in
  aux
  where
  aux : n-m `Le` 0 -> (n-m)-1 `Lt` 0
  aux nmle0 with (n-m)
    | BizO   = Refl
    | BizP _ = absurd $ nmle0 Refl
    | BizM _ = Refl

-- Specification of minimum and maximum

--max_l

maxL : (n, m : Biz) -> m `Le` n -> n `max` m = n
maxL n m mlen = rewrite compareAntisym m n in
                aux
  where
  aux : bizMinMaxHelp n m (compareOp (m `compare` n)) = n
  aux with (m `compare` n)
    | LT = Refl
    | EQ = Refl
    | GT = absurd $ mlen Refl

-- max_r

maxR : (n, m : Biz) -> n `Le` m -> n `max` m = m
maxR n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = compareEqIffTo n m $ sym nm
  | GT = absurd $ nlem Refl

-- min_l

minL : (n, m : Biz) -> n `Le` m -> n `min` m = n
minL n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = sym $ compareEqIffTo n m $ sym nm
  | GT = absurd $ nlem Refl

-- min_r

minR : (n, m : Biz) -> m `Le` n -> n `min` m = m
minR n m mlen = rewrite compareAntisym m n in
                aux
  where
  aux : bizMinMaxHelp m n (compareOp (m `compare` n)) = m
  aux with (m `compare` n)
    | LT = Refl
    | EQ = Refl
    | GT = absurd $ mlen Refl

-- Specification of absolute value

-- abs_eq

absEq : (n : Biz) -> 0 `Le` n -> abs n = n
absEq  BizO    _    = Refl
absEq (BizP _) _    = Refl
absEq (BizM _) zlen = absurd $ zlen Refl

-- abs_neq

absNeq : (n : Biz) -> n `Le` 0 -> abs n = -n
absNeq  BizO    _    = Refl
absNeq (BizP _) nle0 = absurd $ nle0 Refl
absNeq (BizM _) _    = Refl

-- Specification of sign

-- sgn_null n

sgnNull : (n : Biz) -> n = 0 -> bizSign n = 0
sgnNull  BizO    = const Refl
sgnNull (BizP _) = absurd
sgnNull (BizM _) = absurd

-- sgn_pos

sgnPos : (n : Biz) -> 0 `Lt` n -> bizSign n = 1
sgnPos  BizO    = absurd
sgnPos (BizP _) = const Refl
sgnPos (BizM _) = absurd

-- sgn_neg

sgnNeg : (n : Biz) -> n `Lt` 0 -> bizSign n = -1
sgnNeg  BizO    = absurd
sgnNeg (BizP _) = absurd
sgnNeg (BizM _) = const Refl

-- Specification of power

-- pow_0_r is trivial

-- pow_succ_r

powSuccR : (n, m : Biz) -> 0 `Le` m -> bizPow n (bizSucc m) = n * bizPow n m
powSuccR _  BizO    _    = Refl
powSuccR n (BizP a) _    = rewrite addComm a 1 in
                           iterAdd (bizMult n) 1 1 a
powSuccR _ (BizM _) zlem = absurd $ zlem Refl

-- pow_neg_r

powNegR : (n, m : Biz) -> m `Lt` 0 -> bizPow n m = 0
powNegR _  BizO    = absurd
powNegR _ (BizP _) = absurd
powNegR _ (BizM _) = const Refl

-- For folding back a [pow_pos] into a [pow]

-- pow_pos_fold is trivial

-- Specification of square

-- square_spec

squareSpec : (n : Biz) -> bizSquare n = n * n
squareSpec  BizO    = Refl
squareSpec (BizP a) = cong $ squareSpec a
squareSpec (BizM a) = cong $ squareSpec a

-- Specification of square root

-- sqrtrem_spec

sqrtremSpec : (n : Biz) -> 0 `Le` n -> let sr = bizSqrtRem n
                                           s = fst sr
                                           r = snd sr
                                         in (n = s*s + r, 0 `Le` r, r `Le` 2*s)
sqrtremSpec  BizO    _    = (Refl, uninhabited, uninhabited)
sqrtremSpec (BizP a) zlen =
  case sqrtremSpec a of
    SqrtExact  prf      prfa => rewrite prfa in
                                (cong prf, uninhabited, uninhabited)
    SqrtApprox prf prf1 prfa => rewrite prfa in
                                (cong prf, uninhabited, prf1)
sqrtremSpec (BizM a) zlen = absurd $ zlen Refl

-- sqrt_spec

sqrtSpec : (n : Biz) -> 0 `Le` n -> let s = bizSqrt n
                                      in (s*s `Le` n, n `Lt` (bizSucc s)*(bizSucc s))
sqrtSpec  BizO    zlen = (zlen, Refl)
sqrtSpec (BizP a) zlen = rewrite add1R $ bipSqrt a in
                         sqrtSpec a
sqrtSpec (BizM a) zlen = absurd $ zlen Refl

-- sqrt_neg

sqrtNeg : (n : Biz) -> n `Lt` 0 -> bizSqrt n = 0
sqrtNeg  BizO    = absurd
sqrtNeg (BizP _) = absurd
sqrtNeg (BizM _) = const Refl

-- sqrtrem_sqrt

sqrtremSqrt : (n : Biz) -> fst (bizSqrtRem n) = bizSqrt n
sqrtremSqrt  BizO    = Refl
sqrtremSqrt (BizP a) with (bipSqrtRem a)
  | (_,BimO)   = Refl
  | (_,BimP _) = Refl
  | (_,BimM)   = Refl
sqrtremSqrt (BizM _) = Refl

-- Specification of logarithm

-- log2_spec

log2Spec : (n : Biz) -> 0 `Lt` n -> (bizPow 2 (bizLog2 n) `Le` n, n `Lt` bizPow 2 (bizSucc (bizLog2 n)))
log2Spec  BizO        zltn = absurd zltn
log2Spec (BizP  U   ) _    = (uninhabited, Refl)
log2Spec (BizP (O a)) _    = rewrite powZpos 2 (bipDigits a) in
                             rewrite powZpos 2 ((bipDigits a)+1) in
                             ( sizeLe a
                             , rewrite addComm (bipDigits a) 1 in
                               rewrite iterAdd (bipMult 2) 1 1 (bipDigits a) in
                               sizeGt a
                             )
log2Spec (BizP (I a)) _    = rewrite powZpos 2 (bipDigits a) in
                             rewrite powZpos 2 ((bipDigits a)+1) in
                             ( leTrans (bipPow 2 (bipDigits a)) (O a) (I a) (sizeLe a) $
                                 rewrite compareContSpec a a LT in
                                 rewrite compareContRefl a EQ in
                                 uninhabited
                             , rewrite addComm (bipDigits a) 1 in
                               rewrite iterAdd (bipMult 2) 1 1 (bipDigits a) in
                               compareContGtLtFro a (bipPow 2 (bipDigits a)) (sizeGt a)
                             )
log2Spec (BizM _)     zltn = absurd zltn

-- log2_nonpos

log2Nonpos : (n : Biz) -> n `Le` 0 -> bizLog2 n = 0
log2Nonpos  BizO    _    = Refl
log2Nonpos (BizP _) nle0 = absurd $ nle0 Refl
log2Nonpos (BizM _) _    = Refl

-- Specification of parity functions

Even : Biz -> Type
Even a = (b ** a = 2*b)

Odd : Biz -> Type
Odd a = (b ** a = 2*b+1)

-- even_spec
-- TODO split into `to` and `fro`

evenSpecTo : (n : Biz) -> bizEven n = True -> Even n
evenSpecTo  BizO        _   = (0 ** Refl)
evenSpecTo (BizP  U   ) prf = absurd prf
evenSpecTo (BizP (O a)) _   = (BizP a ** Refl)
evenSpecTo (BizP (I _)) prf = absurd prf
evenSpecTo (BizM  U   ) prf = absurd prf
evenSpecTo (BizM (O a)) _   = (BizM a ** Refl)
evenSpecTo (BizM (I _)) prf = absurd prf

evenSpecFro : (n : Biz) -> Even n -> bizEven n = True
evenSpecFro _ (BizO   ** prf) = rewrite prf in
                                Refl
evenSpecFro _ (BizP _ ** prf) = rewrite prf in
                                Refl
evenSpecFro _ (BizM _ ** prf) = rewrite prf in
                                Refl

-- odd_spec
-- TODO split into `to` and `fro`

oddSpecTo : (n : Biz) -> bizOdd n = True -> Odd n
oddSpecTo  BizO        prf = absurd prf
oddSpecTo (BizP  U   ) _   = (0 ** Refl)
oddSpecTo (BizP (O _)) prf = absurd prf
oddSpecTo (BizP (I a)) _   = (BizP a ** Refl)
oddSpecTo (BizM  U   ) _   = (-1 ** Refl)
oddSpecTo (BizM (O _)) prf = absurd prf
oddSpecTo (BizM (I a)) _   = (BizM (bipSucc a) ** rewrite predDoubleSucc a in
                                                  Refl)

oddSpecFro : (n : Biz) -> Odd n -> bizOdd n = True
oddSpecFro _ (BizO       ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizP  _    ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizM  U    ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizM (O _) ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizM (I _) ** prf) = rewrite prf in
                                   Refl

-- Multiplication and Doubling

-- double_spec

doubleSpec : (n : Biz) -> bizD n = 2*n
doubleSpec  BizO    = Refl
doubleSpec (BizP _) = Refl
doubleSpec (BizM _) = Refl

-- succ_double_spec

succDoubleSpec : (n : Biz) -> bizDPO n = 2*n + 1
succDoubleSpec  BizO    = Refl
succDoubleSpec (BizP _) = Refl
succDoubleSpec (BizM _) = Refl

-- pred_double_spec

predDoubleSpec : (n : Biz) -> bizDMO n = 2*n - 1
predDoubleSpec  BizO    = Refl
predDoubleSpec (BizP _) = Refl
predDoubleSpec (BizM _) = Refl

-- Correctness proofs for Trunc division

-- pos_div_eucl_eq

posDivEuclEq : (a: Bip) -> (b: Biz) -> 0 `Lt` b -> let qr = bipzDivEuclid a b
                                                       q = fst qr
                                                       r = snd qr
                                                    in BizP a = q * b + r
posDivEuclEq  _       BizO    zltb = absurd zltb
posDivEuclEq  _      (BizM _) zltb = absurd zltb
posDivEuclEq  U      (BizP n) _    with (2 `compare` n) proof n2
  | LT = Refl
  | EQ = Refl
  | GT = let nle1 = ltSuccRTo n 1 $ gtLt 2 n $ sym n2 in
         cong $ leAntisym 1 n (le1L n) nle1
posDivEuclEq (O a) (BizP n) zltb with ((bizD $ snd $ bipzDivEuclid a (BizP n)) `compare` (BizP n)) proof drb
  | LT = let b = BizP n
             q = fst (bipzDivEuclid a b)
             r = snd (bipzDivEuclid a b) in
         rewrite doubleSpec q in
         rewrite sym $ mulAssoc 2 q b in
         rewrite doubleSpec r in
         rewrite sym $ mulAddDistrL 2 (q*b) r in
         cong {f=bizMult 2} $ posDivEuclEq a b zltb
  | EQ = let b = BizP n
             q = fst (bipzDivEuclid a b)
             r = snd (bipzDivEuclid a b)
             r2eqb = compareEqIffTo (bizD r) b $ sym drb in
         rewrite r2eqb in
         rewrite posSubDiag n in
         rewrite add0R ((bizDPO q)*b) in
         rewrite succDoubleSpec q in
         rewrite mulAddDistrR (2*q) 1 b in
         rewrite sym $ mulAssoc 2 q b in
         rewrite sym r2eqb in
         rewrite doubleSpec r in
         rewrite sym $ mulAddDistrL 2 ((fst (bipzDivEuclid a (2*r)))*(2*r)) r in
         rewrite sym $ doubleSpec r in     --  revert
         rewrite r2eqb in                  --
         cong {f=bizMult 2} $ posDivEuclEq a b zltb
  | GT = let b = BizP n
             q = fst (bipzDivEuclid a b)
             r = snd (bipzDivEuclid a b) in
         rewrite succDoubleSpec q in
         rewrite mulAddDistrR (2*q) 1 b in
         rewrite sym $ addAssoc ((2*q)*b) b ((bizD r)-b) in
         rewrite addAssoc b (bizD r) (-b) in
         rewrite addComm b (bizD r) in
         rewrite sym $ addAssoc (bizD r) b (-b) in
         rewrite posSubDiag n in
         rewrite add0R (bizD r) in
         rewrite sym $ mulAssoc 2 q b in
         rewrite doubleSpec r in
         rewrite sym $ mulAddDistrL 2 (q*b) r in
         cong {f=bizMult 2} $ posDivEuclEq a b zltb
posDivEuclEq (I a) (BizP n) zltb with ((bizDPO $ snd $ bipzDivEuclid a (BizP n)) `compare` (BizP n)) proof dorb
  | LT = let b = BizP n
             q = fst (bipzDivEuclid a b)
             r = snd (bipzDivEuclid a b) in
         rewrite doubleSpec q in
         rewrite sym $ mulAssoc 2 q b in
         rewrite succDoubleSpec r in
         rewrite addAssoc (2*(q*b)) (2*r) 1 in
         rewrite sym $ mulAddDistrL 2 (q*b) r in
         cong {f=\x=>2*x+1} $ posDivEuclEq a b zltb
  | EQ = let b = BizP n
             q = fst (bipzDivEuclid a b)
             r = snd (bipzDivEuclid a b)
             r21eqb = compareEqIffTo (bizDPO r) b $ sym dorb in
         rewrite r21eqb in
         rewrite posSubDiag n in
         rewrite add0R ((bizDPO q)*b) in
         rewrite succDoubleSpec q in
         rewrite mulAddDistrR (2*q) 1 b in
         rewrite sym $ mulAssoc 2 q b in
         rewrite sym r21eqb in
         rewrite succDoubleSpec r in
         rewrite addAssoc (2*((fst (bipzDivEuclid a (2*r+1)))*(2*r+1))) (2*r) 1 in
         rewrite sym $ mulAddDistrL 2 ((fst (bipzDivEuclid a (2*r+1)))*(2*r+1)) r in
         rewrite sym $ succDoubleSpec r in     --  revert
         rewrite r21eqb in                     --
         cong {f=\x=>2*x+1} $ posDivEuclEq a b zltb
  | GT = let b = BizP n
             q = fst (bipzDivEuclid a b)
             r = snd (bipzDivEuclid a b) in
         rewrite succDoubleSpec q in
         rewrite mulAddDistrR (2*q) 1 b in
         rewrite sym $ addAssoc ((2*q)*b) b ((bizDPO r)-b) in
         rewrite addAssoc b (bizDPO r) (-b) in
         rewrite addComm b (bizDPO r) in
         rewrite sym $ addAssoc (bizDPO r) b (-b) in
         rewrite posSubDiag n in
         rewrite add0R (bizDPO r) in
         rewrite sym $ mulAssoc 2 q b in
         rewrite succDoubleSpec r in
         rewrite addAssoc (2*(q*b)) (2*r) 1 in
         rewrite sym $ mulAddDistrL 2 (q*b) r in
         cong {f=\x=>2*x+1} $ posDivEuclEq a b zltb

-- div_eucl_eq

divEuclEq : (a, b : Biz) -> Not (b=0) -> let qr = bizDivEuclid a b
                                             q = fst qr
                                             r = snd qr
                                         in a = q * b + r
divEuclEq  _          BizO    bnz = absurd $ bnz Refl
divEuclEq  BizO       b       _   = Refl
divEuclEq (BizP a) b@(BizP _) _   = posDivEuclEq a b Refl
divEuclEq (BizM a)   (BizP n) _   with (snd $ bipzDivEuclid a (BizP n)) proof rprf
  | BizO   = let b = BizP n
                 q = fst (bipzDivEuclid a b) in
             rewrite add0R ((-q)*b) in
             rewrite mulOppL q b in
             oppInj (BizM a) (-(q*b)) $
             rewrite oppInvolutive (q*b) in
             rewrite posDivEuclEq a b Refl in
             rewrite sym rprf in
             add0R (q*b)
  | BizP r = let b = BizP n
                 q = fst (bipzDivEuclid a b) in
             rewrite mulOppL (q+1) b in
             rewrite mulAddDistrR q 1 b in
             rewrite oppAddDistr (q*b) b in
             rewrite sym $ addAssoc (-(q*b)) (-b) (bipMinusBiz n r) in
             rewrite addAssoc (-b) b (BizM r) in
             rewrite posSubDiag n in
             rewrite sym $ oppAddDistr (q*b) (BizP r) in
             rewrite rprf in
             cong {f=bizOpp} $ posDivEuclEq a b Refl
  -- mostly a copypaste of above with a swapped sign for r
  | BizM r = let b = BizP n
                 q = fst (bipzDivEuclid a b) in
             rewrite mulOppL (q+1) b in
             rewrite mulAddDistrR q 1 b in
             rewrite oppAddDistr (q*b) b in
             rewrite sym $ addAssoc (-(q*b)) (-b) (b+(BizP r)) in
             rewrite addAssoc (-b) b (BizP r) in
             rewrite posSubDiag n in
             rewrite sym $ oppAddDistr (q*b) (BizM r) in
             rewrite rprf in
             cong {f=bizOpp} $ posDivEuclEq a b Refl
divEuclEq (BizP a)   (BizM n) _   with (snd $ bipzDivEuclid a (BizP n)) proof rprf
  | BizO   = let b = BizP n
                 q = fst (bipzDivEuclid a b) in
             rewrite mulOppOpp q b in
             rewrite add0R (q*b) in
             rewrite posDivEuclEq a b Refl in
             rewrite sym rprf in
             add0R (q*b)
  | BizP r = let b = BizP n
                 q = fst (bipzDivEuclid a b) in
             rewrite mulOppOpp (q+1) b in
             rewrite mulAddDistrR q 1 b in
             rewrite sym $ addAssoc (q*b) b (bipMinusBiz r n) in
             rewrite addComm b (bipMinusBiz r n) in
             rewrite sym $ addAssoc (BizP r) (-b) b in
             rewrite posSubDiag n in
             rewrite rprf in
             posDivEuclEq a b Refl
  -- mostly a copypaste of above with a swapped sign for r
  | BizM r = let b = BizP n
                 q = fst (bipzDivEuclid a b) in
             rewrite mulOppOpp (q+1) b in
             rewrite mulAddDistrR q 1 b in
             rewrite sym $ addAssoc (q*b) b ((BizM r)-b) in
             rewrite posSubLt n (r+n) $ rewrite addComm r n in
                                        ltAddDiagR n r
                     in
             rewrite addSub r n in
             rewrite rprf in
             posDivEuclEq a b Refl
divEuclEq (BizM a)   (BizM n) _   =
    let b = BizP n
        q = fst (bipzDivEuclid a b)
        r = snd (bipzDivEuclid a b) in
    rewrite mulOppR q b in
    rewrite sym $ oppAddDistr (q*b) r in
    cong {f=bizOpp} $ posDivEuclEq a b Refl