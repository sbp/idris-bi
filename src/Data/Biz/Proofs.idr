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
oppD : (z : Biz) -> bizOpp (bizD z) = bizD (bizOpp z)
oppD  BizO    = Refl
oppD (BizP _) = Refl
oppD (BizM _) = Refl

oppDMODPO : (z : Biz) -> bizOpp (bizDMO z) = bizDPO (bizOpp z)
oppDMODPO  BizO    = Refl
oppDMODPO (BizP _) = Refl
oppDMODPO (BizM _) = Refl

oppDPODMO : (z : Biz) -> bizOpp (bizDPO z) = bizDMO (bizOpp z)
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