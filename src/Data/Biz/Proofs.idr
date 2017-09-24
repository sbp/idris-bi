module Data.Biz.Proofs

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub
import Data.Bip.SqrtDiv

import Data.Bin.Proofs

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
powZpos p q = sym $ iterSwapGen BizP (bipMult p) (bizMult $ BizP p) (\_ => Refl) U q

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

-- Opposite is inverse for addition

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

ltLeIncl : (n, m : Biz) -> n `Lt` m -> n `Le` m
ltLeIncl n m nltm ngtm with (n `compare` m)
  | LT = uninhabited ngtm
  | EQ = uninhabited ngtm
  | GT = uninhabited nltm

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

-- Comparison and opposite
-- compare_opp
compareOpp : (n, m : Biz) -> n `compare` m = (-m) `compare` (-n)
compareOpp n m =
  rewrite compareSub n m in
  rewrite compareSub (-m) (-n) in
  rewrite oppInvolutive n in
  rewrite addComm n (-m) in
  Refl

-- gt_lt

gtLt : (p, q : Biz) -> p `Gt` q -> q `Lt` p
gtLt p q pgtq =
  rewrite compareAntisym p q in
  rewrite pgtq in
  Refl

-- lt_gt

ltGt : (p, q : Biz) -> p `Lt` q -> q `Gt` p
ltGt p q pltq =
  rewrite compareAntisym p q in
  rewrite pltq in
  Refl

-- ge_le

geLe : (n, m : Biz) -> n `Ge` m -> m `Le` n
geLe n m ngem = rewrite compareAntisym n m in
                aux
  where
  aux : Not (compareOp (n `compare` m) = GT)
  aux prf with (n `compare` m)
    | LT = ngem Refl
    | EQ = uninhabited prf
    | GT = ngem $ sym prf

-- le_ge

leGe : (n, m : Biz) -> n `Le` m -> m `Ge` n
leGe n m nlem = rewrite compareAntisym n m in
                aux
  where
  aux : Not (compareOp (n `compare` m) = LT)
  aux prf with (n `compare` m)
    | LT = nlem $ sym prf
    | EQ = uninhabited prf
    | GT = nlem Refl

-- compare_lt_iff is trivial
-- compare_le_iff is trivial

-- Some more advanced properties of comparison and orders, including
-- [compare_spec] and [lt_irrefl] and [lt_eq_cases].

mulCompareMonoL : (p, q, r : Biz) -> 0 `Lt` p -> (p*q) `compare` (p*r) = q `compare` r
mulCompareMonoL  BizO     _        _       zltp = absurd zltp
mulCompareMonoL (BizM _)  _        _       zltp = absurd zltp
mulCompareMonoL (BizP _)  BizO     BizO    _    = Refl
mulCompareMonoL (BizP _)  BizO    (BizP _) _    = Refl
mulCompareMonoL (BizP _)  BizO    (BizM _) _    = Refl
mulCompareMonoL (BizP _) (BizP _)  BizO    _    = Refl
mulCompareMonoL (BizP a) (BizP b) (BizP c) _    = mulCompareMonoL a b c
mulCompareMonoL (BizP _) (BizP _) (BizM _) _    = Refl
mulCompareMonoL (BizP _) (BizM _)  BizO    _    = Refl
mulCompareMonoL (BizP _) (BizM _) (BizP _) _    = Refl
mulCompareMonoL (BizP a) (BizM b) (BizM c) _    = mulCompareMonoL a c b

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

absNonneg : (a : Biz) -> 0 `Le` bizAbs a
absNonneg  BizO    = uninhabited
absNonneg (BizP _) = uninhabited
absNonneg (BizM _) = uninhabited

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

-- Addition and Doubling

bizDLinear : (n, m : Biz) -> (bizD n)+(bizD m) = bizD (n+m)
bizDLinear  BizO     _       = Refl
bizDLinear  n        BizO    = rewrite add0R n in
                          add0R $ bizD n
bizDLinear (BizP _) (BizP _) = Refl
bizDLinear (BizP _) (BizM _) = Refl
bizDLinear (BizM _) (BizP _) = Refl
bizDLinear (BizM _) (BizM _) = Refl

bizDPOLinearD : (n, m : Biz) -> (bizDPO n)+(bizD m) = bizDPO (n+m)
bizDPOLinearD n m = rewrite addComm (bizDPO n) (bizD m) in
               rewrite succDoubleSpec n in
               rewrite sym $ doubleSpec n in
               rewrite addAssoc (bizD m) (bizD n) 1 in
               rewrite bizDLinear m n in
               rewrite addComm m n in
               rewrite doubleSpec (n+m) in
               sym $ succDoubleSpec (n+m)



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

-- div_mod
-- TODO doesn't seem useful, keep as a sanity check?
divMod : (a, b : Biz) -> Not (b=0) -> a = (bizDiv a b)*b + (bizMod a b)
divMod = divEuclEq

-- pos_div_eucl_bound

posDivEuclBound : (a : Bip) -> (b : Biz) -> 0 `Lt` b -> let r = snd $ bipzDivEuclid a b in (0 `Le` r, r `Lt` b)
posDivEuclBound  _     BizO    zltb = absurd zltb
posDivEuclBound  _    (BizM _) zltb = absurd zltb
posDivEuclBound  U    (BizP b) zltb with (2 `compare` b) proof b2
  | LT = (uninhabited, leSuccLTo 1 b $ ltLeIncl 2 b $ sym b2)
  | EQ = (uninhabited, rewrite sym $ compareEqIffTo 2 b $ sym b2 in
                       Refl)
  | GT = (uninhabited, Refl)
posDivEuclBound (O a) (BizP n) zltb with ((bizD $ snd $ bipzDivEuclid a (BizP n)) `compare` (BizP n)) proof drb
  | LT = let b = BizP n
             r = snd $ bipzDivEuclid a b in
         ( aux r (fst $ posDivEuclBound a b zltb)
         , sym drb
         )
    where
      aux : (n : Biz) -> 0 `Le` n -> 0 `Le` bizD n
      aux n zlen = rewrite doubleSpec n in
                   rewrite mulCompareMonoL 2 0 n Refl in
                   zlen
  | EQ = let b = BizP n
             r = snd $ bipzDivEuclid a b in
         rewrite compareEqIffTo (bizD r) b $ sym drb in
         rewrite posSubDiag n in
         (uninhabited, Refl)
  | GT = let b = BizP n
             r = snd $ bipzDivEuclid a b in
         ( geLe ((bizD r)-b) 0 $
           rewrite sym $ compareSub (bizD r) b in
           rewrite sym drb in
           uninhabited
         , rewrite compareSub ((bizD r)-b) b in
           rewrite sym $ addAssoc (bizD r) (-b) (-b) in
           rewrite addDiag n in
           rewrite bizDLinear r (-b) in
           aux (r-b) $
           rewrite sym $ compareSub r b in
           snd $ posDivEuclBound a b zltb
         )
    where
      aux : (n : Biz) -> n `Lt` 0 -> bizD n `Lt` 0
      aux n nltz = rewrite doubleSpec n in
                   rewrite mulCompareMonoL 2 n 0 Refl in
                   nltz
posDivEuclBound (I a) (BizP n) zltb with ((bizDPO $ snd $ bipzDivEuclid a (BizP n)) `compare` (BizP n)) proof dorb
  | LT = let b = BizP n
             r = snd $ bipzDivEuclid a b in
         ( aux r (fst $ posDivEuclBound a b zltb)
         , sym dorb
         )
    where
      aux : (n : Biz) -> 0 `Le` n -> 0 `Le` bizDPO n
      aux n zlen = ltLeIncl 0 (bizDPO n) $
                   rewrite succDoubleSpec n in
                   ltSuccRFro 0 (2*n) $
                   rewrite mulCompareMonoL 2 0 n Refl in
                   zlen
  | EQ = let b = BizP n
             r = snd $ bipzDivEuclid a b in
         rewrite compareEqIffTo (bizDPO r) b $ sym dorb in
         rewrite posSubDiag n in
         (uninhabited, Refl)
  | GT = let b = BizP n
             r = snd $ bipzDivEuclid a b in
         ( geLe ((bizDPO r)-b) 0 $
           rewrite sym $ compareSub (bizDPO r) b in
           rewrite sym dorb in
           uninhabited
         , rewrite compareSub ((bizDPO r)-b) b in
           rewrite sym $ addAssoc (bizDPO r) (-b) (-b) in
           rewrite addDiag n in
           rewrite bizDPOLinearD r (-b) in
           aux (r-b) $
           rewrite sym $ compareSub r b in
           snd $ posDivEuclBound a b zltb
         )
    where
      aux : (n : Biz) -> n `Lt` 0 -> bizDPO n `Lt` 0
      aux  BizO    nlt0    = absurd nlt0
      aux (BizP _) nlt0    = absurd nlt0
      aux (BizM _) _       = Refl

-- mod_pos_bound

modPosBound : (a, b : Biz) -> 0 `Lt` b -> let m = bizMod a b in (0 `Le` m, m `Lt` b)
modPosBound  _          BizO    zltb = absurd zltb
modPosBound  _         (BizM _) zltb = absurd zltb
modPosBound  BizO      (BizP _) _    = (uninhabited, Refl)
modPosBound (BizP a) b@(BizP _) _    = posDivEuclBound a b Refl
modPosBound (BizM a)   (BizP b) _    with (snd $ bipzDivEuclid a (BizP b)) proof rprf
  | BizO   = (uninhabited, Refl)
  | BizP r =
      let rltb' = snd $ posDivEuclBound a (BizP b) Refl
          rltb = replace {P=\x=>x `Lt` (BizP b)} (sym rprf) rltb' in
      rewrite posSubGt b r rltb in
      (uninhabited, subDecr b r rltb)
  | BizM _ =
      let zler' = fst $ posDivEuclBound a (BizP b) Refl
          zler = replace {P=\x=>0 `Le` x} (sym rprf) zler' in
-- TODO bug? we arrive at `zler:(GT=GT)->Void` but the following results in
-- `zler does not have a function type ((\x => ([__])) (BizM _))`
          --absurd $ zler Refl
          really_believe_me zler


-- mod_neg_bound

modNegBound : (a, b : Biz) -> b `Lt` 0 -> let m = bizMod a b in (b `Lt` m, m `Le` 0)
modNegBound  _        BizO    blt0 = absurd blt0
modNegBound  _       (BizP _) blt0 = absurd blt0
modNegBound  BizO    (BizM _) _    = (Refl, uninhabited)
modNegBound (BizP a) (BizM b) _    with (snd $ bipzDivEuclid a (BizP b)) proof rprf
  | BizO   = (Refl, uninhabited)
  | BizP r =
    let rltb' = snd $ posDivEuclBound a (BizP b) Refl
        rltb = replace {P=\x=>x `Lt` (BizP b)} (sym rprf) rltb' in
    rewrite posSubLt r b rltb in
    ( subDecr b r rltb
    , uninhabited
    )
  | BizM _ =
      let zler' = fst $ posDivEuclBound a (BizP b) Refl
          zler = replace {P=\x=>0 `Le` x} (sym rprf) zler' in
-- TODO bug? see above
      --absurd $ zler Refl
      really_believe_me zler
modNegBound (BizM a) (BizM b) _    =
  let (zltr, rltb) = posDivEuclBound a (BizP b) Refl in
  ( rewrite sym $ compareOpp (snd $ bipzDivEuclid a (BizP b)) (BizP b) in
    rltb
  , rewrite sym $ compareOpp 0 (snd $ bipzDivEuclid a (BizP b)) in
    zltr
  )

-- Correctness proofs for Floor division

-- TODO move to Nat.idr

toBizBinInjAdd : (n, m : Bin) -> toBizBin (n+m) = toBizBin n + toBizBin m
toBizBinInjAdd  BinO     m       = rewrite addZeroL m in Refl
toBizBinInjAdd (BinP _)  BinO    = Refl
toBizBinInjAdd (BinP _) (BinP _) = Refl


toBizBinInjMul : (n, m : Bin) -> toBizBin (n*m) = toBizBin n * toBizBin m
toBizBinInjMul  BinO     m       = rewrite mulZeroL m in Refl
toBizBinInjMul (BinP _)  BinO    = Refl
toBizBinInjMul (BinP _) (BinP _) = Refl

-- quotrem_eq

quotremEq : (a, b : Biz) -> let qr = bizQuotRem a b in
                            a = fst qr * b + snd qr
quotremEq  BizO     _       = Refl
quotremEq (BizP _)  BizO    = Refl
quotremEq (BizM _)  BizO    = Refl
quotremEq (BizP a) (BizP b) =
  let qr = bipDivEuclid a (BinP b)
      q = fst qr
      r = snd qr in
  rewrite sym $ toBizBinInjMul q (BinP b) in
  rewrite sym $ toBizBinInjAdd (q*(BinP b)) r in
  cong {f=toBizBin} $ posDivEuclSpec a (BinP b)
quotremEq (BizP a) (BizM b) =
  let qr = bipDivEuclid a (BinP b)
      q = fst qr
      r = snd qr in
  rewrite mulOppOpp (toBizBin q) (BizP b) in
  rewrite sym $ toBizBinInjMul q (BinP b) in
  rewrite sym $ toBizBinInjAdd (q*(BinP b)) r in
  cong {f=toBizBin} $ posDivEuclSpec a (BinP b)
quotremEq (BizM a) (BizP b) =
  let qr = bipDivEuclid a (BinP b)
      q = fst qr
      r = snd qr in
  rewrite mulOppL (toBizBin q) (BizP b) in
  rewrite sym $ oppAddDistr ((toBizBin q)*(BizP b)) (toBizBin r) in
  rewrite sym $ toBizBinInjMul q (BinP b) in
  rewrite sym $ toBizBinInjAdd (q*(BinP b)) r in
  cong {f=bizOpp . toBizBin} $ posDivEuclSpec a (BinP b)
quotremEq (BizM a) (BizM b) =
  let qr = bipDivEuclid a (BinP b)
      q = fst qr
      r = snd qr in
  rewrite mulOppR (toBizBin q) (BizP b) in
  rewrite sym $ oppAddDistr ((toBizBin q)*(BizP b)) (toBizBin r) in
  rewrite sym $ toBizBinInjMul q (BinP b) in
  rewrite sym $ toBizBinInjAdd (q*(BinP b)) r in
  cong {f=bizOpp . toBizBin} $ posDivEuclSpec a (BinP b)

-- quot_rem'
-- TODO doesn't seem useful, keep as a sanity check?
quotRem0 : (a, b : Biz) -> a = (bizQuot a b)*b + bizRem a b
quotRem0 = quotremEq

-- quot_rem is just quot_rem' with added constraint

-- rem_bound_pos

remBoundPos : (a, b : Biz) -> 0 `Le` a -> 0 `Lt` b -> let r = bizRem a b in (0 `Le` r, r `Lt` b)
remBoundPos  _        BizO    _    zltb = absurd zltb
remBoundPos  _       (BizM _) _    zltb = absurd zltb
remBoundPos (BizM _)  _       zlea _    = absurd $ zlea Refl
remBoundPos  BizO    (BizP _) _    _    = (uninhabited, Refl)
remBoundPos (BizP a) (BizP b) zlea zltb with (snd $ bipDivEuclid a (BinP b)) proof rprf
  | BinO   = (uninhabited, Refl)
  | BinP _ = (uninhabited, let rltb = posDivEuclRemainder a (BinP b) uninhabited in
                           replace {P =\x => x `Lt` BinP b} (sym rprf) rltb)

-- rem_opp_l'

remOppL : (a, b : Biz) -> bizRem (-a) b = -(bizRem a b)
remOppL  BizO     _       = Refl
remOppL (BizP _)  BizO    = Refl
remOppL (BizM _)  BizO    = Refl
remOppL (BizP _) (BizP _) = Refl
remOppL (BizP _) (BizM _) = Refl
remOppL (BizM a) (BizP b) = sym $ oppInvolutive $ toBizBin $ snd $ bipDivEuclid a (BinP b)
remOppL (BizM a) (BizM b) = sym $ oppInvolutive $ toBizBin $ snd $ bipDivEuclid a (BinP b)

-- rem_opp_r'

remOppR : (a, b : Biz) -> bizRem a (-b) = bizRem a b
remOppR  BizO     _       = Refl
remOppR (BizP _)  BizO    = Refl
remOppR (BizM _)  BizO    = Refl
remOppR (BizP _) (BizP _) = Refl
remOppR (BizP _) (BizM _) = Refl
remOppR (BizM _) (BizP _) = Refl
remOppR (BizM _) (BizM _) = Refl

-- rem_opp_l is just rem_opp_l' with added constraint

-- rem_opp_r is just rem_opp_r' with added constraint

-- Basic properties of divisibility

bizDivides : (x, y : Biz) -> Type
bizDivides x y = (z ** y = z*x)

-- divide_Zpos
-- TODO split into `to` and `fro`

divideZposTo : (p, q : Bip) -> bizDivides (BizP p) (BizP q) -> bipDivides p q
divideZposTo _ _ (BizO   ** prf) = absurd prf
divideZposTo _ _ (BizM _ ** prf) = absurd prf
divideZposTo _ _ (BizP z ** prf) = (z ** bizPInj prf)

divideZposFro : (p, q : Bip) -> bipDivides p q -> bizDivides (BizP p) (BizP q)
divideZposFro _ _ (r ** prf) = (BizP r ** cong prf)

-- divide_Zpos_Zneg_r
-- TODO split into `to` and `fro`

divideZposZnegRTo : (n : Biz) -> (p : Bip) -> bizDivides n (BizP p) -> bizDivides n (BizM p)
divideZposZnegRTo n _ (z ** prf) = (-z ** rewrite mulOppL z n in
                                          cong {f=bizOpp} prf)

divideZposZnegRFro : (n : Biz) -> (p : Bip) -> bizDivides n (BizM p) -> bizDivides n (BizP p)
divideZposZnegRFro n _ (z ** prf) = (-z ** rewrite mulOppL z n in
                                           cong {f=bizOpp} prf)

-- divide_Zpos_Zneg_l
-- TODO split into `to` and `fro`

divideZposZnegLTo : (n : Biz) -> (p : Bip) -> bizDivides (BizP p) n -> bizDivides (BizM p) n
divideZposZnegLTo _ p (z ** prf) = (-z ** rewrite mulOppOpp z (BizP p) in
                                          prf)

divideZposZnegLFro : (n : Biz) -> (p : Bip) -> bizDivides (BizM p) n -> bizDivides (BizP p) n
divideZposZnegLFro _ p (z ** prf) = (-z ** rewrite mulOppOpp z (BizM p) in
                                           prf)

-- Correctness proofs for gcd

ggcdGcd : (a, b : Biz) -> fst (bizGGCD a b) = bizGCD a b
ggcdGcd  BizO     _       = Refl
ggcdGcd (BizP _)  BizO    = Refl
ggcdGcd (BizM _)  BizO    = Refl
ggcdGcd (BizP a) (BizP b) = cong $ ggcdGcd a b
ggcdGcd (BizP a) (BizM b) = cong $ ggcdGcd a b
ggcdGcd (BizM a) (BizP b) = cong $ ggcdGcd a b
ggcdGcd (BizM a) (BizM b) = cong $ ggcdGcd a b

-- ggcd_correct_divisors

ggcdCorrectDivisors : (a, b : Biz) -> let gaabb = bizGGCD a b
                                          g = fst gaabb
                                          aa = fst $ snd gaabb
                                          bb = snd $ snd gaabb in
                                      (a = g*aa, b = g*bb)
ggcdCorrectDivisors  BizO     BizO    = (Refl, Refl)
ggcdCorrectDivisors  BizO    (BizP b) = (Refl, cong $ sym $ mul1R b)
ggcdCorrectDivisors  BizO    (BizM b) = (Refl, cong $ sym $ mul1R b)
ggcdCorrectDivisors (BizP a)  BizO    = (cong $ sym $ mul1R a, Refl)
ggcdCorrectDivisors (BizP a) (BizP b) = let (aa, bb) = ggcdCorrectDivisors a b in
                                        (cong aa, cong bb)
ggcdCorrectDivisors (BizP a) (BizM b) = let (aa, bb) = ggcdCorrectDivisors a b in
                                        (cong aa, cong bb)
ggcdCorrectDivisors (BizM a)  BizO    = (cong $ sym $ mul1R a, Refl)
ggcdCorrectDivisors (BizM a) (BizP b) = let (aa, bb) = ggcdCorrectDivisors a b in
                                        (cong aa, cong bb)
ggcdCorrectDivisors (BizM a) (BizM b) = let (aa, bb) = ggcdCorrectDivisors a b in
                                        (cong aa, cong bb)

-- gcd_divide_l

gcdDivideL : (a, b : Biz) -> bizDivides (bizGCD a b) a
gcdDivideL a b =
  rewrite sym $ ggcdGcd a b in
  (fst $ snd $ bizGGCD a b **
     rewrite mulComm (fst $ snd $ bizGGCD a b) (fst $ bizGGCD a b) in
     fst $ ggcdCorrectDivisors a b
  )

-- gcd_divide_r

gcdDivideR : (a, b : Biz) -> bizDivides (bizGCD a b) b
gcdDivideR a b =
  rewrite sym $ ggcdGcd a b in
  (snd $ snd $ bizGGCD a b **
     rewrite mulComm (snd $ snd $ bizGGCD a b) (fst $ bizGGCD a b) in
     snd $ ggcdCorrectDivisors a b
  )

-- gcd_greatest

gcdGreatestPos : (p, q : Bip) -> (r : Biz) -> bizDivides r (BizP p) -> bizDivides r (BizP q) -> bizDivides r (BizP $ bipGCD p q)
gcdGreatestPos _ _  BizO    (z ** prf) _  = absurd $ replace (mul0R z) prf
gcdGreatestPos p q (BizP a)  rp        rq = divideZposFro a (bipGCD p q) $
                                            gcdGreatest p q a (divideZposTo a p rp) (divideZposTo a q rq)
gcdGreatestPos p q (BizM a)  rp        rq =
  divideZposZnegLTo (BizP $ bipGCD p q) a $
  divideZposFro a (bipGCD p q) $
  gcdGreatest p q a
    (divideZposTo a p $ divideZposZnegLFro (BizP p) a rp)
    (divideZposTo a q $ divideZposZnegLFro (BizP q) a rq)

gcdGreatest : (a, b, c : Biz) -> bizDivides c a -> bizDivides c b -> bizDivides c (bizGCD a b)
gcdGreatest  BizO     BizO    _ _  _  = (0 ** Refl)
gcdGreatest  BizO    (BizP _) _ _  cb = cb
gcdGreatest  BizO    (BizM b) c _  cb = divideZposZnegRFro c b cb
gcdGreatest (BizP _)  BizO    _ ca _  = ca
gcdGreatest (BizP a) (BizP b) c ca cb = gcdGreatestPos a b c ca cb
gcdGreatest (BizP a) (BizM b) c ca cb = gcdGreatestPos a b c ca (divideZposZnegRFro c b cb)
gcdGreatest (BizM a)  BizO    c ca _  = divideZposZnegRFro c a ca
gcdGreatest (BizM a) (BizP b) c ca cb = gcdGreatestPos a b c (divideZposZnegRFro c a ca) cb
gcdGreatest (BizM a) (BizM b) c ca cb = gcdGreatestPos a b c (divideZposZnegRFro c a ca) (divideZposZnegRFro c b cb)

-- gcd_nonneg

gcdNonneg : (a, b : Biz) -> 0 `Le` bizGCD a b
gcdNonneg  BizO     b       = absNonneg b
gcdNonneg (BizP _)  BizO    = uninhabited
gcdNonneg (BizM _)  BizO    = uninhabited
gcdNonneg (BizP a) (BizP b) = uninhabited
gcdNonneg (BizP a) (BizM b) = uninhabited
gcdNonneg (BizM a) (BizP b) = uninhabited
gcdNonneg (BizM a) (BizM b) = uninhabited

-- ggcd and opp : an auxiliary result used in QArith

-- ggcd_opp

ggcdOpp : (a, b : Biz) -> let gaabb = bizGGCD a b
                              g = fst gaabb
                              aa = fst $ snd gaabb
                              bb = snd $ snd gaabb in
                          bizGGCD (-a) b = (g,(-aa,bb))
ggcdOpp  BizO     _       = Refl
ggcdOpp (BizP _)  BizO    = Refl
ggcdOpp (BizM _)  BizO    = Refl
ggcdOpp (BizP _) (BizP _) = Refl
ggcdOpp (BizP _) (BizM _) = Refl
ggcdOpp (BizM _) (BizP _) = Refl
ggcdOpp (BizM _) (BizM _) = Refl

-- Conversions between [Z.testbit] and [N.testbit]

-- testbit_of_N

testbitOfN : (a, n : Bin) -> bizTestBit (toBizBin a) (toBizBin n) = binTestBit a n
testbitOfN  BinO         BinO    = Refl
testbitOfN  BinO        (BinP _) = Refl
testbitOfN (BinP  U   )  BinO    = Refl
testbitOfN (BinP (O _))  BinO    = Refl
testbitOfN (BinP (I _))  BinO    = Refl
testbitOfN (BinP  _   ) (BinP _) = Refl

-- testbit_of_N'

testbitOfN1 : (a : Bin) -> (n : Biz) -> 0 `Le` n -> bizTestBit (toBizBin a) n = binTestBit a (toBinBiz n)
testbitOfN1 a  BizO    _    = testbitOfN a BinO
testbitOfN1 a (BizP b) _    = testbitOfN a (BinP b)
testbitOfN1 _ (BizM _) zlen = absurd $ zlen Refl

-- testbit_Zpos

testbitZpos : (a : Bip) -> (n : Biz) -> 0 `Le` n -> bizTestBit (BizP a) n = binTestBit (BinP a) (toBinBiz n)
testbitZpos a = testbitOfN1 (BinP a)

-- testbit_Zneg

testbitZneg : (a : Bip) -> (n : Biz) -> 0 `Le` n -> bizTestBit (BizM a) n = not (binTestBit (bipPredBin a) (toBinBiz n))
testbitZneg  U     BizO    _    = Refl
testbitZneg (O a)  BizO    _    = rewrite zeroBitDMO a in
                                  Refl
testbitZneg (I _)  BizO    _    = Refl
testbitZneg  _    (BizP _) _    = Refl
testbitZneg  _    (BizM _) zlen = absurd $ zlen Refl

-- Proofs of specifications for bitwise operations

-- div2_spec is trivial

-- testbit_0_l

testbit0L : (n : Biz) -> bizTestBit 0 n = False
testbit0L  BizO    = Refl
testbit0L (BizP _) = Refl
testbit0L (BizM _) = Refl

-- testbit_neg_r

testbitNegR : (a, n : Biz) -> n `Lt` 0 -> bizTestBit a n = False
testbitNegR  _        BizO    nlt0 = absurd nlt0
testbitNegR  _       (BizP _) nlt0 = absurd nlt0
testbitNegR  BizO    (BizM _) _    = Refl
testbitNegR (BizP _) (BizM _) _    = Refl
testbitNegR (BizM _) (BizM _) _    = Refl

-- testbit_odd_0

testbitOdd0 : (a : Biz) -> bizTestBit (bizDPO a) 0 = True
testbitOdd0  BizO        = Refl
testbitOdd0 (BizP  _   ) = Refl
testbitOdd0 (BizM  U   ) = Refl
testbitOdd0 (BizM (O _)) = Refl
testbitOdd0 (BizM (I _)) = Refl

-- testbit_even_0

testbitEven0 : (a : Biz) -> bizTestBit (bizD a) 0 = False
testbitEven0  BizO    = Refl
testbitEven0 (BizP _) = Refl
testbitEven0 (BizM _) = Refl

-- testbit_odd_succ

testbitOddSucc : (a, n : Biz) -> 0 `Le` n -> bizTestBit (bizDPO a) (bizSucc n) = bizTestBit a n
testbitOddSucc  BizO         BizO    _    = Refl
testbitOddSucc (BizP  U   )  BizO    _    = Refl
testbitOddSucc (BizP (O _))  BizO    _    = Refl
testbitOddSucc (BizP (I _))  BizO    _    = Refl
testbitOddSucc (BizM  U   )  BizO    _    = Refl
testbitOddSucc (BizM (O a))  BizO    _    = rewrite zeroBitDMO a in
                                            Refl
testbitOddSucc (BizM (I _))  BizO    _    = Refl
testbitOddSucc  BizO        (BizP _) _    = Refl
testbitOddSucc (BizP  U   ) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizP (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizP (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizM  U   ) (BizP _) _    = Refl
testbitOddSucc (BizM (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizM (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc  _           (BizM _) zlen = absurd $ zlen Refl

-- testbit_even_succ

testbitEvenSucc : (a, n : Biz) -> 0 `Le` n -> bizTestBit (bizD a) (bizSucc n) = bizTestBit a n
testbitEvenSucc  BizO         BizO    _    = Refl
testbitEvenSucc (BizP  U   )  BizO    _    = Refl
testbitEvenSucc (BizP (O _))  BizO    _    = Refl
testbitEvenSucc (BizP (I _))  BizO    _    = Refl
testbitEvenSucc (BizM  U   )  BizO    _    = Refl
testbitEvenSucc (BizM (O a))  BizO    _    = rewrite zeroBitDMO a in
                                             Refl
testbitEvenSucc (BizM (I _))  BizO    _    = Refl
testbitEvenSucc  BizO        (BizP _) _    = Refl
testbitEvenSucc (BizP  U   ) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizP (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizP (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizM  U   ) (BizP _) _    = Refl
testbitEvenSucc (BizM (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizM (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc  _           (BizM _) zlen = absurd $ zlen Refl

-- Correctness proofs about [Z.shiftr] and [Z.shiftl]

div2BizBin : (x : Bin) -> toBizBin (binDivTwo x) = bizDivTwo (toBizBin x)
div2BizBin  BinO        = Refl
div2BizBin (BinP  U   ) = Refl
div2BizBin (BinP (O _)) = Refl
div2BizBin (BinP (I _)) = Refl

div2BipBin : (x : Bip) -> bipPredBin (bipDivTwoCeil x) = binDivTwo (bipPredBin x)
div2BipBin  U    = Refl
div2BipBin (O a) = rewrite dmoPredDPO a in
                   sym $ divTwoSuccDouble (bipPredBin a)
div2BipBin (I a) = predBinSucc a

-- shiftr_spec_aux

shiftrSpecAux : (a, n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizTestBit (bizShiftR a n) m = bizTestBit a (m+n)
shiftrSpecAux  _       (BizM _)  _       zlen _    = absurd $ zlen Refl
shiftrSpecAux  _        _       (BizM _) _    zlem = absurd $ zlem Refl
shiftrSpecAux  _        BizO     BizO    _    _    = Refl
shiftrSpecAux  _        BizO    (BizP _) _    _    = Refl
shiftrSpecAux  BizO    (BizP b)  m       _    _    =
  let zeroIterDiv2 = iterInvariant bizDivTwo (\x=>x=0) b (\_,prf => rewrite prf in Refl) 0 Refl in
  rewrite zeroIterDiv2 in
  rewrite testbit0L (m+(BizP b)) in
  testbit0L m
shiftrSpecAux (BizP a) (BizP b)  BizO    _    _    =
  rewrite sym $ iterSwapGen toBizBin binDivTwo bizDivTwo div2BizBin (BinP a) b in
  rewrite testbitOfN1 (bipIter binDivTwo (BinP a) b) 0 uninhabited in
  shiftrSpec (BinP a) (BinP b) 0
shiftrSpecAux (BizP a) (BizP b) (BizP c) _    _    =
  rewrite sym $ iterSwapGen toBizBin binDivTwo bizDivTwo div2BizBin (BinP a) b in
  rewrite testbitOfN1 (bipIter binDivTwo (BinP a) b) (BizP c) uninhabited in
  shiftrSpec (BinP a) (BinP b) (BinP c)
shiftrSpecAux (BizM a) (BizP b)  BizO    _    _    =
  rewrite sym $ iterSwapGen BizM bipDivTwoCeil bizDivTwo (\_ => Refl) a b in
  rewrite testbitZneg (bipIter bipDivTwoCeil a b) 0 uninhabited in
  rewrite iterSwapGen bipPredBin bipDivTwoCeil binDivTwo div2BipBin a b in
  cong $ shiftrSpec (bipPredBin a) (BinP b) 0
shiftrSpecAux (BizM a) (BizP b) (BizP c) _    _    =
  rewrite sym $ iterSwapGen BizM bipDivTwoCeil bizDivTwo (\_ => Refl) a b in
  rewrite iterSwapGen bipPredBin bipDivTwoCeil binDivTwo div2BipBin a b in
  cong $ shiftrSpec (bipPredBin a) (BinP b) (BinP c)

-- shiftl_spec_low

shiftlSpecLow : (a, n, m : Biz) -> m `Lt` n -> bizTestBit (bizShiftL a n) m = False
shiftlSpecLow  _        BizO     BizO    mltn = absurd mltn
shiftlSpecLow  _        BizO    (BizP _) mltn = absurd mltn
shiftlSpecLow  a        n       (BizM c) _    = testbitNegR (bizShiftL a n) (BizM c) Refl
shiftlSpecLow  a       (BizP b)  BizO    _    =
  case succPredOr b of
    Left  lprf =>
      rewrite lprf in
      rewrite sym $ doubleSpec a in
      testbitEven0 a
    Right rprf =>
      rewrite sym rprf in
      rewrite iterSucc (bizMult 2) a (bipPred b) in
      rewrite sym $ doubleSpec (bipIter (bizMult 2) a (bipPred b)) in
      testbitEven0 (bipIter (bizMult 2) a (bipPred b))
shiftlSpecLow  BizO    (BizP b) (BizP c) _    =
  let zeroIterMul2 = iterInvariant (bizMult 2) (\x=>x=0) b (\_,prf => rewrite prf in Refl) 0 Refl in
  rewrite zeroIterMul2 in
  Refl
shiftlSpecLow (BizP a) (BizP b) (BizP c) mltn =
  rewrite sym $ iterSwapGen BizP O (bizMult 2) (\_ => Refl) a b in
  shiftlSpecLow (BinP a) (BinP b) (BinP c) mltn
shiftlSpecLow (BizM a) (BizP b) (BizP c) mltn =
  rewrite sym $ iterSwapGen BizM O (bizMult 2) (\_ => Refl) a b in
  cong {f=not} $ posPredShiftlLow a (BinP b) (BinP c) mltn
shiftlSpecLow  _       (BizM _)  BizO    mltn = absurd mltn
shiftlSpecLow  _       (BizM _) (BizP _) mltn = absurd mltn

-- shiftl_spec_high

minusBiz : (p, q : Bip) -> bimToBin $ bimMinus p q = toBinBiz $ bipMinusBiz p q
minusBiz p q = case ltTotal p q of
  Left $ Left pq  =>
    rewrite subMaskNeg p q pq in
    rewrite posSubLt p q pq in
    Refl
  Right eq        =>
    rewrite eq in
    rewrite subMaskDiag q in
    rewrite posSubDiag q in
    Refl
  Left $ Right qp =>
    let (_**prf) = subMaskPos p q qp in
    rewrite prf in
    rewrite posSubGt p q qp in
    cong {f = BinP . bipMinusHelp} $ sym prf

shiftlSpecHigh : (a, n, m : Biz) -> 0 `Le` m -> n `Le` m -> bizTestBit (bizShiftL a n) m = bizTestBit a (m-n)
shiftlSpecHigh  _        BizO     m       _    _    = rewrite add0R m in
                                                      Refl
shiftlSpecHigh  a       (BizM b)  m       zlem _    = shiftrSpecAux a (BizP b) m uninhabited zlem
shiftlSpecHigh  _       (BizP _)  BizO    _    nlem = absurd $ nlem Refl
shiftlSpecHigh  BizO    (BizP b) (BizP c) _    _    =
  let zeroIterMul2 = iterInvariant (bizMult 2) (\x=>x=0) b (\_,prf => rewrite prf in Refl) 0 Refl in
  rewrite zeroIterMul2 in
  sym $ testbit0L (bipMinusBiz c b)
shiftlSpecHigh (BizP a) (BizP b) (BizP c) _    nlem =
  rewrite sym $ iterSwapGen BizP O (bizMult 2) (\_ => Refl) a b in
  rewrite shiftlSpecHigh (BinP a) (BinP b) (BinP c) nlem in
  rewrite testbitZpos a (bipMinusBiz c b) $
            geLe (bipMinusBiz c b) 0 $
            rewrite sym $ compareSub (BizP c) (BizP b) in
            leGe b c nlem
    in
  cong $ minusBiz c b
shiftlSpecHigh (BizM a) (BizP b) (BizP c) _    nlem =
  rewrite sym $ iterSwapGen BizM O (bizMult 2) (\_ => Refl) a b in
  rewrite posPredShiftlHigh a (BinP b) (BinP c) nlem in
  rewrite testbitZneg a (bipMinusBiz c b) $
            geLe (bipMinusBiz c b) 0 $
            rewrite sym $ compareSub (BizP c) (BizP b) in
            leGe b c nlem
    in
  rewrite shiftlSpecHigh (bipPredBin a) (BinP b) (BinP c) nlem in
  cong {f = not . binTestBit (bipPredBin a)} $ minusBiz c b
shiftlSpecHigh  _        _       (BizM _) zlem _    = absurd $ zlem Refl

-- shiftr_spec

shiftrSpec : (a, n, m : Biz) -> 0 `Le` m -> bizTestBit (bizShiftR a n) m = bizTestBit a (m+n)
shiftrSpec a    BizO    m zlem = shiftrSpecAux a 0 m uninhabited zlem
shiftrSpec a n@(BizP _) m zlem = shiftrSpecAux a n m uninhabited zlem
shiftrSpec a   (BizM b) m zlem with ((BizP b) `compare` m) proof nm
  | LT = shiftlSpecHigh a (BizP b) m zlem $ ltLeIncl (BizP b) m $ sym nm
  | EQ = shiftlSpecHigh a (BizP b) m zlem $ rewrite sym nm in
                                            uninhabited
  | GT = rewrite shiftlSpecLow a (BizP b) m $ gtLt (BizP b) m $ sym nm in
         sym $ testbitNegR a (m-(BizP b)) $
           rewrite sym $ compareSub m (BizP b) in
           gtLt (BizP b) m $ sym nm

-- Correctness proofs for bitwise operations

------------ TODO add to Prelude.Bool ----------

notAnd : (x, y : Bool) -> not (x && y) = (not x) || (not y)
notAnd True  True  = Refl
notAnd True  False = Refl
notAnd False True  = Refl
notAnd False False = Refl

notNot : (x : Bool) -> not (not x) = x
notNot True  = Refl
notNot False = Refl

orComm : (x, y : Bool) -> x || y = y || x
orComm True  True  = Refl
orComm True  False = Refl
orComm False True  = Refl
orComm False False = Refl

andComm : (x, y : Bool) -> x && y = y && x
andComm True  True  = Refl
andComm True  False = Refl
andComm False True  = Refl
andComm False False = Refl

notOr : (x, y : Bool) -> not (x || y) = (not x) && (not y)
notOr True  True  = Refl
notOr True  False = Refl
notOr False True  = Refl
notOr False False = Refl

notXorR : (x, y : Bool) -> not (x `xor` y) = x `xor` (not y)
notXorR True  True  = Refl
notXorR True  False = Refl
notXorR False True  = Refl
notXorR False False = Refl

notXorL : (x, y : Bool) -> not (x `xor` y) = (not x) `xor` y
notXorL True  True  = Refl
notXorL True  False = Refl
notXorL False True  = Refl
notXorL False False = Refl

notXor2 : (x, y : Bool) -> x `xor` y = (not x) `xor` (not y)
notXor2 True  True  = Refl
notXor2 True  False = Refl
notXor2 False True  = Refl
notXor2 False False = Refl

------------------------------------------------

-- lor_spec

or0R : (n : Biz) -> bizOr n BizO = n
or0R  BizO    = Refl
or0R (BizP _) = Refl
or0R (BizM _) = Refl

lorSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizOr a b) n = bizTestBit a n || bizTestBit b n
lorSpecNonneg  BizO     _       n _    = rewrite testbit0L n in
                                         Refl
lorSpecNonneg  a        BizO    n _    =
  rewrite or0R a in
  rewrite testbit0L n in
  sym $ orFalse (bizTestBit a n)
lorSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitZpos (bipOr a b) n zlen in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  posLorSpec a b (toBinBiz n)
lorSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binDiff (bipPredBin b) (BinP a))) n zlen in
  rewrite posPredSucc (binDiff (bipPredBin b) (BinP a)) in
  rewrite ldiffSpec (bipPredBin b) (BinP a) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  rewrite notAnd (binTestBit (bipPredBin b) (toBinBiz n)) (not (bipTestBit a (toBinBiz n))) in
  rewrite notNot (bipTestBit a (toBinBiz n)) in
  orComm (not (binTestBit (bipPredBin b) (toBinBiz n))) (bipTestBit a (toBinBiz n))
lorSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitZneg (binSuccBip (binDiff (bipPredBin a) (BinP b))) n zlen in
  rewrite posPredSucc (binDiff (bipPredBin a) (BinP b)) in
  rewrite ldiffSpec (bipPredBin a) (BinP b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  rewrite notAnd (binTestBit (bipPredBin a) (toBinBiz n)) (not (bipTestBit b (toBinBiz n))) in
  rewrite notNot (bipTestBit b (toBinBiz n)) in
  Refl
lorSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binAnd (bipPredBin a) (bipPredBin b))) n zlen in
  rewrite posPredSucc (binAnd (bipPredBin a) (bipPredBin b)) in
  rewrite landSpec (bipPredBin a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  notAnd (binTestBit (bipPredBin a) (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))

lorSpec : (a, b, n : Biz) -> bizTestBit (bizOr a b) n = bizTestBit a n || bizTestBit b n
lorSpec a b    BizO    = lorSpecNonneg a b 0 uninhabited
lorSpec a b n@(BizP _) = lorSpecNonneg a b n uninhabited
lorSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  rewrite testbitNegR b n Refl in
  testbitNegR (bizOr a b) n Refl

-- land_spec

and0R : (n : Biz) -> bizAnd n BizO = BizO
and0R  BizO    = Refl
and0R (BizP _) = Refl
and0R (BizM _) = Refl

landSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizAnd a b) n = bizTestBit a n && bizTestBit b n
landSpecNonneg  BizO     _       n _    = rewrite testbit0L n in
                                          Refl
landSpecNonneg  a        BizO    n _    =
  rewrite and0R a in
  rewrite testbit0L n in
  sym $ andFalse (bizTestBit a n)
landSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitOfN1 (bipAnd a b) n zlen in
  rewrite landSpec (BinP a) (BinP b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  Refl
landSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitOfN1 (binDiff (BinP a) (bipPredBin b)) n zlen in
  rewrite ldiffSpec (BinP a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  Refl
landSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitOfN1 (binDiff (BinP b) (bipPredBin a)) n zlen in
  rewrite ldiffSpec (BinP b) (bipPredBin a) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  andComm (bipTestBit b (toBinBiz n)) (not (binTestBit (bipPredBin a) (toBinBiz n)))
landSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binOr (bipPredBin a) (bipPredBin b))) n zlen in
  rewrite posPredSucc (binOr (bipPredBin a) (bipPredBin b)) in
  rewrite lorSpec (bipPredBin a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  notOr (binTestBit (bipPredBin a) (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))

landSpec : (a, b, n : Biz) -> bizTestBit (bizAnd a b) n = bizTestBit a n && bizTestBit b n
landSpec a b    BizO    = landSpecNonneg a b 0 uninhabited
landSpec a b n@(BizP _) = landSpecNonneg a b n uninhabited
landSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  testbitNegR (bizAnd a b) n Refl

-- ldiff_spec

diff0R : (n : Biz) -> bizDiff n BizO = n
diff0R  BizO    = Refl
diff0R (BizP _) = Refl
diff0R (BizM _) = Refl

ldiffSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizDiff a b) n = bizTestBit a n && not (bizTestBit b n)
ldiffSpecNonneg  BizO     _       n _    = rewrite testbit0L n in
                                           Refl

ldiffSpecNonneg  a        BizO    n _    =
  rewrite diff0R a in
  rewrite testbit0L n in
  sym $ andTrue (bizTestBit a n)
ldiffSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitOfN1 (bipDiff a b) n zlen in
  rewrite ldiffSpec (BinP a) (BinP b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  Refl
ldiffSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitOfN1 (binAnd (BinP a) (bipPredBin b)) n zlen in
  rewrite landSpec (BinP a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  rewrite notNot (binTestBit (bipPredBin b) (toBinBiz n)) in
  Refl
ldiffSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitZneg (binSuccBip (binOr (bipPredBin a) (BinP b))) n zlen in
  rewrite posPredSucc (binOr (bipPredBin a) (BinP b)) in
  rewrite lorSpec (bipPredBin a) (BinP b)  (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  notOr (binTestBit (bipPredBin a) (toBinBiz n)) (bipTestBit b (toBinBiz n))
ldiffSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitOfN1 (binDiff (bipPredBin b) (bipPredBin a)) n zlen in
  rewrite ldiffSpec (bipPredBin b) (bipPredBin a) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  rewrite notNot (binTestBit (bipPredBin b) (toBinBiz n)) in
  andComm (binTestBit (bipPredBin b) (toBinBiz n)) (not (binTestBit (bipPredBin a) (toBinBiz n)))

ldiffSpec : (a, b, n : Biz) -> bizTestBit (bizDiff a b) n = bizTestBit a n && not (bizTestBit b n)
ldiffSpec a b    BizO    = ldiffSpecNonneg a b 0 uninhabited
ldiffSpec a b n@(BizP _) = ldiffSpecNonneg a b n uninhabited
ldiffSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  testbitNegR (bizDiff a b) n Refl

--lxor_spec

xor0R : (n : Biz) -> bizXor n BizO = n
xor0R  BizO    = Refl
xor0R (BizP _) = Refl
xor0R (BizM _) = Refl

lxorSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizXor a b) n = (bizTestBit a n) `xor` (bizTestBit b n)
lxorSpecNonneg  BizO     b       n _    = rewrite testbit0L n in
                                          sym $ xorFalse (bizTestBit b n)
lxorSpecNonneg  a        BizO    n _    =
  rewrite testbit0L n in
  rewrite xor0R a in
  rewrite xorComm (bizTestBit a n) False in
  sym $ xorFalse (bizTestBit a n)
lxorSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitOfN1 (bipXor a b) n zlen in
  rewrite lxorSpec (BinP a) (BinP b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  Refl
lxorSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binXor (BinP a) (bipPredBin b))) n zlen in
  rewrite posPredSucc (binXor (BinP a) (bipPredBin b)) in
  rewrite lxorSpec (BinP a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  notXorR (bipTestBit a (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))
lxorSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitZneg (binSuccBip (binXor (bipPredBin a) (BinP b))) n zlen in
  rewrite posPredSucc (binXor (bipPredBin a) (BinP b)) in
  rewrite lxorSpec (bipPredBin a) (BinP b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  notXorL (binTestBit (bipPredBin a) (toBinBiz n)) (bipTestBit b (toBinBiz n))
lxorSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitOfN1 (binXor (bipPredBin a) (bipPredBin b)) n zlen in
  rewrite lxorSpec (bipPredBin a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  notXor2 (binTestBit (bipPredBin a) (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))

lxorSpec : (a, b, n : Biz) -> bizTestBit (bizXor a b) n = (bizTestBit a n) `xor` (bizTestBit b n)
lxorSpec a b    BizO    = lxorSpecNonneg a b 0 uninhabited
lxorSpec a b n@(BizP _) = lxorSpecNonneg a b n uninhabited
lxorSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  rewrite testbitNegR b n Refl in
  testbitNegR (bizXor a b) n Refl

-- peano_ind
-- TODO rename all versions to peanoInd ?
peanoRect : (P : Biz -> Type) -> (f0 : P BizO)
-> (fs : (x : Biz) -> P x -> P (bizSucc x))
-> (fp : (x : Biz) -> P x -> P (bizPred x))
-> (z : Biz) -> P z
peanoRect _ f0 _  _   BizO    = f0
peanoRect P f0 fs _  (BizP a) = peanoRect (P . BizP) (fs BizO f0) (\p => rewrite sym $ add1R p in
                                                                fs $ BizP p) a
peanoRect P f0 _  fp (BizM a) = peanoRect (P . BizM) (fp BizO f0) (\p => rewrite sym $ add1R p in
                                                                fp $ BizM p) a
-- TODO bi_induction

-- TODO boolean comparisons ?

-- add_reg_l

-- TODO import Control.Pipeline from contrib
infixl 9 |>
(|>) : a -> (a -> b) -> b
a |> f = f a

addRegR : (n, m, p : Biz) -> m + n = p + n -> m = p
addRegR n m p prf =
     cong {f=\x=>x-n} prf
  |> replace {P=\x=>x=p+n-n}   (sym $ addAssoc m n (-n))
  |> replace {P=\x=>m+x=p+n-n} (addOppDiagR n)
  |> replace {P=\x=>x=p+n-n}   (add0R m)
  |> replace {P=\x=>m=x}       (sym $ addAssoc p n (-n))
  |> replace {P=\x=>m=p+x}     (addOppDiagR n)
  |> replace {P=\x=>m=x}       (add0R p)

addRegL : (n, m, p : Biz) -> n + m = n + p -> m = p
addRegL n m p =
  rewrite addComm n m in
  rewrite addComm n p in
  addRegR n m p

-- mul_reg_l

mulRegL : (n, m, p : Biz) -> Not (p = 0) -> p * n = p * m -> n = m
mulRegL n m p pnz prf with (p `compare` 0) proof pz
  | LT =    compareEqIffFro (p*n) (p*m) prf
         |> replace {P=\x=>x=EQ}                      (compareOpp (p*n) (p*m))
         |> replace {P=\x=>(-(p*m)) `compare` x = EQ} (sym $ mulOppL p n)
         |> replace {P=\x=>x `compare` ((-p)*n) = EQ} (sym $ mulOppL p m)
         |> replace {P=\x=>x=EQ}                      (mulCompareMonoL (-p) m n $
                                                         rewrite compareOpp 0 (-p) in
                                                         rewrite oppInvolutive p in
                                                         sym pz)
         |> compareEqIffTo m n
         |> sym
  | EQ = absurd $ pnz $ compareEqIffTo p 0 $ sym pz
  | GT =    compareEqIffFro (p*n) (p*m) prf
         |> replace {P=\x=>x=EQ} (mulCompareMonoL p n m $ gtLt p 0 $ sym pz)
         |> compareEqIffTo n m

-- mul_reg_r

mulRegR : (n, m, p : Biz) -> Not (p = 0) -> n * p = m * p -> n = m
mulRegR n m p =
  rewrite mulComm n p in
  rewrite mulComm m p in
  mulRegL n m p

-- opp_eq_mul_m1

oppEqMulM1 : (n : Biz) -> -n = n * (-1)
oppEqMulM1  BizO    = Refl
oppEqMulM1 (BizP a) = cong $ sym $ mul1R a
oppEqMulM1 (BizM a) = cong $ sym $ mul1R a

-- add_diag

addDiag : (n : Biz) -> n + n = 2 * n
addDiag n =
  rewrite mulAddDistrR 1 1 n in
  rewrite mul1L n in
  Refl

-- Comparison and addition
-- add_compare_mono_l
addCompareMonoL : (n, m, p : Biz) -> (n + m) `compare` (n + p) = m `compare` p
addCompareMonoL n m p =
  rewrite compareSub (n+m) (n+p) in
  rewrite oppAddDistr n p in
  rewrite addAssoc (n+m) (-n) (-p) in
  rewrite addComm (n+m) (-n) in
  rewrite addAssoc (-n) n m in
  rewrite addOppDiagL n in
  sym $ compareSub m p