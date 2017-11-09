module Data.Biz.AddSubMul

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub

import Data.Biz

%access public export
%default total

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

-- add_reg_l

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

notDDPO : (x, y : Biz) -> Not (bizD x = bizDPO y)
notDDPO  BizO     BizO    = uninhabited
notDDPO  BizO    (BizP _) = uninhabited
notDDPO  BizO    (BizM _) = uninhabited
notDDPO (BizP _)  BizO    = uninhabited . bizPInj
notDDPO (BizP _) (BizP _) = uninhabited . bizPInj
notDDPO (BizP _) (BizM _) = uninhabited
notDDPO (BizM _)  BizO    = uninhabited
notDDPO (BizM _) (BizP _) = uninhabited
notDDPO (BizM _) (BizM b) =
  case succPredOr b of
    Left bu => rewrite bu in
               uninhabited . bizMInj
    Right bs => rewrite sym bs in
                rewrite predDoubleSucc (bipPred b) in
                uninhabited . bizMInj

addTransferLZ : (x, y, z : Biz) -> x = y+z -> z = x-y
addTransferLZ x y z prf =
  rewrite prf in
  rewrite addComm y z in
  rewrite sym $ addAssoc z y (-y) in
  rewrite addOppDiagR y in
  sym $ add0R z

succPredZ : (x : Biz) -> x = bizSucc (bizPred x)
succPredZ x = rewrite sym $ addAssoc x (-1) 1 in
              sym $ add0R x