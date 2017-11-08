module Data.Biz.DivMod

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.Div

import Data.Bin.AddSubMul
import Data.Bin.Ord
import Data.Bin.DivMod

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.Bitwise

%access public export
%default total

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

divModUniquePosAux : (b, q1, q2, r1, r2 : Biz) -> b*q1+r1 = b*q2+r2
   -> 0 `Le` r1 -> r1 `Lt` b
   -> 0 `Le` r2
   -> q1 `Ge` q2
divModUniquePosAux b q1 q2 r1 r2 prf zler1 r1ltab zler2 q1ltq2 =
  let (q3**(zltq3,q2eq)) = minusPos q1 q2 q1ltq2
      r1prf = prf
           |> replace {P = \x => b*q1+r1 = b*x+r2 } q2eq
           |> replace {P = \x => b*q1+r1 = x+r2 }   (mulAddDistrL b q1 q3)
           |> replace (sym $ addAssoc (b*q1) (b*q3) r2)
           |> addRegL (b*q1) r1 ((b*q3)+r2)
      geprf = linearGe b q3 r2 (leLtTrans 0 r1 b zler1 r1ltab) zltq3 zler2
      r1geb = replace {P = \x => x `Ge` b} (sym r1prf) geprf
  in
    absurd $ r1geb r1ltab
  where
  minusPos : (n, m : Biz) -> n `Lt` m -> (p ** (0 `Lt` p, m = n + p))
  minusPos n m nltm = ((m-n)**( rewrite compareAntisym (m-n) 0 in
                            rewrite sym $ compareSub m n in
                            rewrite compareAntisym n m in
                            cong {f=compareOp . compareOp} nltm
                          , rewrite addComm m (-n) in
                            rewrite addAssoc n (-n) m in
                            rewrite addOppDiagR n in
                            Refl
                          ))
  linearGe : (n, m, p : Biz) -> 0 `Lt` n -> 0 `Lt` m -> 0 `Le` p -> n*m+p `Ge` n
  linearGe  BizO     _        _       zltn _    _    = absurd zltn
  linearGe (BizM _)  _        _       zltn _    _    = absurd zltn
  linearGe  _        BizO     _       _    zltm _    = absurd zltm
  linearGe (BizP a) (BizP b)  BizO    _    _    _    =
    rewrite sym $ mul1R a in
    rewrite sym $ mulAssoc a 1 b in
    rewrite mulCompareMonoL a b 1 in
    nlt1R b
  linearGe (BizP a) (BizP b) (BizP c) _    _    _    =
    leGe a ((a*b)+c) $
    leTrans a (a*b) ((a*b)+c)
      (rewrite sym $ mul1R a in
       rewrite sym $ mulAssoc a 1 b in
       rewrite mulCompareMonoL a 1 b in
       le1L b)
      (geLe ((a*b)+c) (a*b) $
       ltNotAddL (a*b) c)
  linearGe  _       (BizM _)  _       _    zltm _    = absurd zltm
  linearGe  _        _       (BizM _) _    _    zlep = absurd $ zlep Refl

-- TODO q1/2 and b are flipped?
-- TODO a *Neg version of this where `b<r1<=0` and `b<r2<=0` ?

divModUniquePos : (b, q1, q2, r1, r2 : Biz)
           -> 0 `Le` r1 -> r1 `Lt` bizAbs b
           -> 0 `Le` r2 -> r2 `Lt` bizAbs b
           -> b*q1+r1 = b*q2+r2
           -> (q1 = q2, r1 = r2)
divModUniquePos  BizO    _  _  r1 _  zler1 r1ltab _     _      _   = absurd $ zler1 $ ltGt r1 0 r1ltab
divModUniquePos (BizP a) q1 q2 r1 r2 zler1 r1ltab zler2 r2ltab prf with (q1 `compare` q2) proof q1q2
  | LT = let q1geq2 = divModUniquePosAux (BizP a) q1 q2 r1 r2 prf zler1 r1ltab zler2 in
         absurd $ q1geq2 $ sym q1q2
  | EQ = let qeq = compareEqIffTo q1 q2 $ sym q1q2
             req = prf
                |> replace {P=\x=> (BizP a)*x+r1 = (BizP a)*q2+r2} qeq
                |> addRegL ((BizP a)*q2) r1 r2
         in
         (qeq, req)
  | GT = let q2geq1 = divModUniquePosAux (BizP a) q2 q1 r2 r1 (sym prf) zler2 r2ltab zler1 in
         absurd $ q2geq1 $ gtLt q1 q2 $ sym q1q2
divModUniquePos (BizM a) q1 q2 r1 r2 zler1 r1ltab zler2 r2ltab prf with (q1 `compare` q2) proof q1q2
  | LT = let q2geq1op = divModUniquePosAux (BizP a) (-q2) (-q1) r2 r1
                          (rewrite sym $ mulOppComm (BizP a) q1 in
                           rewrite sym $ mulOppComm (BizP a) q2 in
                           sym prf) zler2 r2ltab zler1
             q2q1op = replace {P=\x=>x=LT} (compareOpp q1 q2) (sym q1q2)
          in
          absurd $ q2geq1op q2q1op
  | EQ = let qeq = compareEqIffTo q1 q2 $ sym q1q2
             req = prf
                |> replace {P=\x=> (BizM a)*x+r1 = (BizM a)*q2+r2} qeq
                |> addRegL ((BizM a)*q2) r1 r2
         in
          (qeq, req)
  | GT = let q1geq2op = divModUniquePosAux (BizP a) (-q1) (-q2) r1 r2
                          (rewrite sym $ mulOppComm (BizP a) q1 in
                           rewrite sym $ mulOppComm (BizP a) q2 in
                           prf) zler1 r1ltab zler2
             q1q2op = replace {P=\x=>x=LT} (compareOpp q2 q1) (gtLt q1 q2 $ sym q1q2)
          in
          absurd $ q1geq2op q1q2op

-- TODO a *Neg version, see above

divModPos : (a, b, q, r : Biz) -> 0 `Le` r -> r `Lt` b -> a = q*b + r -> (q = a `bizDiv` b, r = a `bizMod` b)
divModPos _  BizO    _ r zler rltb _   = absurd $ zler $ ltGt r 0 rltb
divModPos a (BizP b) q r zler rltb prf =
    let (zlem, mltb) = modPosBound a (BizP b) Refl in
    divModUniquePos (BizP b) q (a `bizDiv` (BizP b)) r (a `bizMod` (BizP b)) zler rltb zlem mltb $
      rewrite mulComm (BizP b) (a `bizDiv` (BizP b)) in
      rewrite sym $ divEuclEq a (BizP b) uninhabited in
      rewrite mulComm (BizP b) q in
      sym prf
divModPos _ (BizM b) _ r zler rltb _   = absurd $ zler $ ltGt r 0 $ ltTrans r (BizM b) 0 rltb Refl