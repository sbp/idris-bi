module Data.Bin.DivMod

--import Data.Bip.Iter
import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.Div

import Data.Bin
import Data.Bin.AddSubMul
import Data.Bin.Ord

%access public export
%default total

-- Specification of the euclidean division

-- pos_div_eucl_spec

posDivEuclSpec : (a : Bip) -> (b : Bin) -> let qr = bipDivEuclid a b
                                               q = fst qr
                                               r = snd qr
                                           in
                                           BinP a = q * b + r
posDivEuclSpec  U     BinO        = Refl
posDivEuclSpec  U    (BinP  U   ) = Refl
posDivEuclSpec  U    (BinP (O _)) = Refl
posDivEuclSpec  U    (BinP (I _)) = Refl
posDivEuclSpec (O a)  b           =
  -- BUG? can't directly rewrite with cong ..
  let ih = cong {f=binD} $ posDivEuclSpec a b
      qr = bipDivEuclid a b
      q = fst qr
      r = snd qr
    in
  rewrite ih in
  rewrite doubleAdd (q*b) r in
  rewrite doubleMul q b in
  aux q r
  where
  aux : (q, r : Bin) -> let res = bipDivEuclidHelp q (binD r) b (b `compare` binD r)
                       in ((binD q)*b)+(binD r) = ((fst res)*b)+(snd res)
  aux q r with (b `compare` binD r) proof cmp
    | LT = rewrite succDoubleMul q b in
           rewrite sym $ addAssoc ((binD q)*b) b ((binD r)-b) in
           rewrite addComm b ((binD r)-b) in
           rewrite subAdd b (binD r) $ ltLeIncl b (binD r) $ sym cmp in
           Refl
    | EQ = rewrite sym $ compareEqIffTo b (binD r) $ sym cmp in
           rewrite subDiag b in
           rewrite addZeroR ((binDPO q)*b) in
           sym $ succDoubleMul q b
    | GT = Refl
posDivEuclSpec (I a)  b           =
  let ih = cong {f=binDPO} $ posDivEuclSpec a b
      qr = bipDivEuclid a b
      q = fst qr
      r = snd qr
   in
  rewrite ih in
  rewrite succDoubleAdd (q*b) r in
  rewrite doubleMul q b in
  aux q r
  where
  aux : (q, r : Bin) -> let res = bipDivEuclidHelp q (binDPO r) b (b `compare` binDPO r)
                       in ((binD q)*b)+(binDPO r) = ((fst res)*b)+(snd res)
  aux q r with (b `compare` binDPO r) proof cmp
    | LT = rewrite succDoubleMul q b in
           rewrite sym $ addAssoc ((binD q)*b) b ((binDPO r)-b) in
           rewrite addComm b ((binDPO r)-b) in
           rewrite subAdd b (binDPO r) $ ltLeIncl b (binDPO r) $ sym cmp in
           Refl
    | EQ = rewrite sym $ compareEqIffTo b (binDPO r) $ sym cmp in
           rewrite subDiag b in
           rewrite addZeroR ((binDPO q)*b) in
           sym $ succDoubleMul q b
    | GT = Refl

-- div_eucl_spec
-- why is q*b flipped here?
divEuclSpec : (a, b : Bin) -> let qr = binDivEuclid a b
                                  q = fst qr
                                  r = snd qr
                              in a = b * q + r
divEuclSpec  BinO     BinO    = Refl
divEuclSpec  BinO    (BinP _) = Refl
divEuclSpec (BinP _)  BinO    = Refl
divEuclSpec (BinP a) (BinP b) =
  rewrite mulComm (BinP b) (fst (bipDivEuclid a (BinP b))) in
  posDivEuclSpec a (BinP b)

-- div_mod'
-- this looks redundant
divMod' : (a, b : Bin) -> a = b * (a `div` b) + (a `mod` b)
divMod' = divEuclSpec

-- div_mod looks even more redundant

-- pos_div_eucl_remainder

posDivEuclRemainder : (a : Bip) -> (b : Bin) -> Not (b=0) -> (snd $ bipDivEuclid a b) `Lt` b
posDivEuclRemainder  _     BinO        bz = absurd $ bz Refl
posDivEuclRemainder  U    (BinP  U   ) _  = Refl
posDivEuclRemainder  U    (BinP (O _)) _  = Refl
posDivEuclRemainder  U    (BinP (I _)) _  = Refl
posDivEuclRemainder (O a) (BinP  y   ) bz with ((BinP y) `compare` (binD $ snd $ bipDivEuclid a (BinP y))) proof cmp
  | LT = let b = BinP y
             r = snd $ bipDivEuclid a b
         in
         addLtCancelL ((binD r)-b) b b $
         rewrite addComm b ((binD r)-b) in
         rewrite subAdd b (binD r) $ ltLeIncl b (binD r) $ sym cmp in
         rewrite addDiag y in
         let ih = posDivEuclRemainder a b bz in
         dpoLt (snd $ bipDivEuclid a b) (BinP (O y)) $
         succDoubleLt r b ih
  | EQ = rewrite sym $ compareEqIffTo (BinP y) (binD $ snd $ bipDivEuclid a (BinP y)) $ sym cmp in
         rewrite subDiag (BinP y) in
         Refl
  | GT = gtLt (BinP y) (binD $ snd $ bipDivEuclid a (BinP y)) $ sym cmp
posDivEuclRemainder (I a) (BinP  y   ) bz with ((BinP y) `compare` (binDPO $ snd $ bipDivEuclid a (BinP y))) proof cmp
  | LT = let b = BinP y
             r = snd $ bipDivEuclid a b
         in
         addLtCancelL ((binDPO r)-b) b b $
         rewrite addComm b ((binDPO r)-b) in
         rewrite subAdd b (binDPO r) $ ltLeIncl b (binDPO r) $ sym cmp in
         rewrite addDiag y in
         let ih = posDivEuclRemainder a b bz in
         succDoubleLt r b ih
  | EQ = rewrite sym $ compareEqIffTo (BinP y) (binDPO $ snd $ bipDivEuclid a (BinP y)) $ sym cmp in
         rewrite subDiag (BinP y) in
         Refl
  | GT = gtLt (BinP y) (binDPO $ snd $ bipDivEuclid a (BinP y)) $ sym cmp

-- mod_lt

modLt : (a, b : Bin) -> Not (b=0) -> (a `mod` b) `Lt` b
modLt  _        BinO    bz = absurd $ bz Refl
modLt  BinO    (BinP _) _  = Refl
modLt (BinP a) (BinP b) bz = posDivEuclRemainder a (BinP b) bz

-- mod_bound_pos is just mod_lt + le_0_l

bipDivEuclid1R : (a : Bip) -> a `bipDivEuclid` 1 = (BinP a, BinO)
bipDivEuclid1R  U    = Refl
bipDivEuclid1R (O a) = rewrite bipDivEuclid1R a in
                       Refl
bipDivEuclid1R (I a) = rewrite bipDivEuclid1R a in
                       Refl

-- Specification of gcd

-- ggcd_gcd
-- The first component of binGGCD is binGCD
ggcdGcd : (a, b : Bin) -> fst (binGGCD a b) = binGCD a b
ggcdGcd  BinO     BinO    = Refl
ggcdGcd  BinO    (BinP _) = Refl
ggcdGcd (BinP _)  BinO    = Refl
ggcdGcd (BinP a) (BinP b) = cong $ ggcdGcd a b

-- ggcd_correct_divisors
-- The other components of binGGCD are indeed the correct factors
ggcdCorrectDivisors : (a, b : Bin) -> let gaabb = binGGCD a b
                                          g = fst gaabb
                                          aa = fst $ snd gaabb
                                          bb = snd $ snd gaabb in
                                        (a=g*aa, b=g*bb)
ggcdCorrectDivisors  BinO     BinO    = (Refl, Refl)
ggcdCorrectDivisors  BinO    (BinP b) = (Refl, rewrite mul1R b in
                                               Refl)
ggcdCorrectDivisors (BinP a)  BinO    = (rewrite mul1R a in
                                         Refl, Refl)
ggcdCorrectDivisors (BinP a) (BinP b) = let (prf1, prf2) = ggcdCorrectDivisors a b in
                                        (cong prf1, cong prf2)

binDivides : (a, b : Bin) -> Type
binDivides a b = (c ** b = c*a)

-- gcd_divide_l

gcdDivideL : (a, b : Bin) -> binDivides (binGCD a b) a
gcdDivideL a b =
  let (aprf, _) = ggcdCorrectDivisors a b
      x = binGGCD a b in
  rewrite sym $ ggcdGcd a b in
  (fst $ snd x **
    rewrite mulComm (fst $ snd x) (fst x) in
    aprf)

-- gcd_divide_r

gcdDivideR : (a, b : Bin) -> binDivides (binGCD a b) b
gcdDivideR a b =
  let (_, bprf) = ggcdCorrectDivisors a b
      x = binGGCD a b in
  rewrite sym $ ggcdGcd a b in
  (snd $ snd x **
    rewrite mulComm (snd $ snd x) (fst x) in
    bprf)

-- gcd_greatest

gcdGreatest : (a, b, c : Bin) -> binDivides c a -> binDivides c b
                              -> binDivides c (binGCD a b)
gcdGreatest  BinO     BinO     c       _        _        = (0 ** rewrite mulZeroL c in Refl)
gcdGreatest  BinO    (BinP _)  _       _        cb       = cb
gcdGreatest (BinP _)  BinO     _       ca       _        = ca
gcdGreatest (BinP _) (BinP _)  BinO    (d**pca) _        = absurd $ replace (mulZeroR d) pca
gcdGreatest (BinP a) (BinP b) (BinP c) (d**pca) (e**pcb) = aux d e pca pcb
  where
  aux : (d, e : Bin) -> BinP a = binMult d (BinP c) -> BinP b = binMult e (BinP c)
                     -> (z ** BinP (bipGCD a b) = z*(BinP c))
  aux  BinO     _       pca _   = absurd pca
  aux  _        BinO    _   pcb = absurd pcb
  aux (BinP x) (BinP y) pca pcb =
    let (r**prf) = gcdGreatest a b c (x**binPInj pca) (y**binPInj pcb)
    in
    (BinP r ** cong prf)

-- gcd_nonneg is just le_0_l
