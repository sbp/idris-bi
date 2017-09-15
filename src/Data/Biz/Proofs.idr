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
