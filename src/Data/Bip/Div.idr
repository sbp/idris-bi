module Data.Bip.Div

import Data.Util

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.OrdSub

%access export
%default total

public export
bipDivides : (p, q : Bip) -> Type
bipDivides p q = (r ** q = r*p)

-- divide_add_cancel_l

divideAddCancelL : (p, q, r : Bip) -> bipDivides p r -> bipDivides p (q+r)
                                   -> bipDivides p q
divideAddCancelL p q r (s ** pr) (t ** pqr) =
   ((t-s) **
     rewrite mulSubDistrR t s p $
               mulLtMonoRFro p s t $
               rewrite sym pr in
               rewrite sym pqr in
               rewrite addComm q r in
               ltAddDiagR r q
             in
     rewrite sym pr in
     rewrite sym pqr in
     sym $ addSub q r)

-- divide_xO_xI

divideXOXI : (p, q, r : Bip) -> bipDivides p (O q) -> bipDivides p (I r)
                             -> bipDivides p q
divideXOXI  U    q _  _          _         = (q ** sym $ mul1R q)
divideXOXI (O a) _ _  _         (t ** pir) = absurd $ replace (mulXOR t a) pir
divideXOXI (I _) _ _ (s ** poq)  _         = case s of
  U   => absurd poq
  O d => (d ** OInj poq)
  I _ => absurd poq

-- divide_xO_xO

divideXOXO : (p, q : Bip) -> bipDivides (O p) (O q) -> bipDivides p q
divideXOXO p _ (r ** opoq) = (r ** OInj $ rewrite sym $ mulXOR r p in opoq)

-- divide_mul_l

divideMulL : (p, q, r : Bip) -> bipDivides p q -> bipDivides p (q*r)
divideMulL p _ r (s ** pq) = ((s*r) **
  rewrite pq in
  rewrite sym $ mulAssoc s p r in
  rewrite sym $ mulAssoc s r p in
  rewrite mulComm p r in
  Refl)

-- divide_mul_r

divideMulR : (p, q, r : Bip) -> bipDivides p r -> bipDivides p (q*r)
divideMulR p q r dpr = rewrite mulComm q r in
                       divideMulL p r q dpr

-- ggcdn_gcdn

-- The first component of GGCD is GCD

ggcdnGcdn : (n : Nat) -> (p, q : Bip) -> fst $ bipGGCDN n p q = bipGCDN n p q
ggcdnGcdn  Z     _     _    = Refl
ggcdnGcdn (S _)  U     _    = Refl
ggcdnGcdn (S _) (O _)  U    = Refl
ggcdnGcdn (S k) (O a) (O b) = cong $ ggcdnGcdn k a b
ggcdnGcdn (S k) (O a) (I b) = ggcdnGcdn k a (I b)
ggcdnGcdn (S _) (I _)  U    = Refl
ggcdnGcdn (S k) (I a) (O b) = ggcdnGcdn k (I a) b
ggcdnGcdn (S k) (I a) (I b) with (a `compare` b)
  | LT = ggcdnGcdn k (b-a) (I a)
  | EQ = Refl
  | GT = ggcdnGcdn k (a-b) (I b)

-- ggcd_gcd

ggcdGcd : (p, q : Bip) -> fst $ bipGGCD p q = bipGCD p q
ggcdGcd p q = ggcdnGcdn ((bipDigitsNat p)+(bipDigitsNat q)) p q

-- ggcdn_correct_divisors

ggcdnCorrectDivisors : (n : Nat) -> (p, q : Bip) ->
                       let gppqq = bipGGCDN n p q
                           g = fst gppqq
                           pp = fst $ snd gppqq
                           qq = snd $ snd gppqq in
                         (p=g*pp, q=g*qq)
ggcdnCorrectDivisors  Z     _     _    = (Refl, Refl)
ggcdnCorrectDivisors (S _)  U     _    = (Refl, Refl)
ggcdnCorrectDivisors (S _) (O _)  U    = (Refl, Refl)
ggcdnCorrectDivisors (S k) (O a) (O b) =
  let (aprf, bprf) = ggcdnCorrectDivisors k a b in
     (cong aprf, cong bprf)
ggcdnCorrectDivisors (S k) (O a) (I b) =
  let (aprf, ibprf) = ggcdnCorrectDivisors k a (I b)
      x = bipGGCDN k a (I b) in
    ( rewrite mulXOR (fst x) (fst $ snd x) in
      cong aprf
    , ibprf
    )
ggcdnCorrectDivisors (S _) (I _)  U    = (Refl, Refl)
ggcdnCorrectDivisors (S k) (I a) (O b) =
  let (iaprf, bprf) = ggcdnCorrectDivisors k (I a) b
      x = bipGGCDN k (I a) b
  in
    ( iaprf
    , rewrite mulXOR (fst x) (snd $ snd x) in
      cong bprf
    )
ggcdnCorrectDivisors (S k) (I a) (I b) with (a `compare` b) proof ab
  | LT = let (bmaprf, iaprf) = ggcdnCorrectDivisors k (b-a) (I a)
             x = bipGGCDN k (b-a) (I a)
             fx = fst x
             fsx = fst $ snd x
             ssx = snd $ snd x
         in
         ( iaprf
         , rewrite mulAddDistrL fx ssx (O fsx) in
           rewrite sym iaprf in
           rewrite mulXOR fx fsx in
           cong {f=I} $
           rewrite addComm a (fx*fsx) in
           subInverse b (fx*fsx) a (sym ab) $
           bmaprf
         )
  | EQ = rewrite compareEqIffTo a b $ sym ab in
         rewrite mul1R b in
         (Refl, Refl)
  | GT = let (ambprf, ibprf) = ggcdnCorrectDivisors k (a-b) (I b)
             x = bipGGCDN k (a-b) (I b)
             fx = fst x
             fsx = fst $ snd x
             ssx = snd $ snd x
         in
         ( rewrite mulAddDistrL fx ssx (O fsx) in
           rewrite sym ibprf in
           rewrite mulXOR fx fsx in
           cong {f=I} $
           rewrite addComm b (fx*fsx) in
           subInverse a (fx*fsx) b (gtLt a b $ sym ab) $
           ambprf
         , ibprf
         )

-- ggcd_correct_divisors

ggcdCorrectDivisors : (p, q : Bip) ->
                      let gppqq = bipGGCD p q
                          g = fst gppqq
                          pp = fst $ snd gppqq
                          qq = snd $ snd gppqq in
                        (p=g*pp, q=g*qq)
ggcdCorrectDivisors p q =
  ggcdnCorrectDivisors ((bipDigitsNat p) + (bipDigitsNat q)) p q

-- gcd_divide_l

gcdDivideL : (p, q : Bip) -> bipDivides (bipGCD p q) p
gcdDivideL p q =
  let (pprf, _) = ggcdCorrectDivisors p q
      x = bipGGCD p q in
  rewrite sym $ ggcdGcd p q in
  (fst $ snd x **
    rewrite mulComm (fst $ snd x) (fst x) in
    pprf)

-- gcd_divide_r

gcdDivideR : (p, q : Bip) -> bipDivides (bipGCD p q) q
gcdDivideR p q =
  let (_, qprf) = ggcdCorrectDivisors p q
      x = bipGGCD p q in
  rewrite sym $ ggcdGcd p q in
  (snd $ snd x **
    rewrite mulComm (snd $ snd x) (fst x) in
    qprf)

-- gcdn_greatest

-- GCD is the greatest amongst common divisors

gcdnGreatest : (n : Nat) -> (p, q : Bip) -> (bipDigitsNat p + bipDigitsNat q) `LTE` n ->
               (r : Bip) -> bipDivides r p -> bipDivides r q -> bipDivides r (bipGCDN n p q)
gcdnGreatest  Z     U     _    pqlte  _     _          _         = absurd pqlte
gcdnGreatest  Z    (O _)  _    pqlte  _     _          _         = absurd pqlte
gcdnGreatest  Z    (I _)  _    pqlte  _     _          _         = absurd pqlte
gcdnGreatest (S _)  U     _    _      r    (s ** psr)  _         =
  (U ** sym $ mulEq1R s r $ sym psr)
gcdnGreatest (S _) (O _)  U    _      r     _         (t ** qtr) =
  (U ** sym $ mulEq1R t r $ sym qtr)
gcdnGreatest (S _) (I _)  U    _      r     _         (t ** qtr) =
  (U ** sym $ mulEq1R t r $ sym qtr)
gcdnGreatest (S k) (O a) (O b) _      U     _          _         =
  (O $ bipGCDN k a b ** rewrite mul1R (bipGCDN k a b) in
                        Refl)
gcdnGreatest (S k) (O a) (O b) pqlte (O c)  pr         qr        =
  let (r**prf) = gcdnGreatest k a b
                   (fromLteSucc $
                    lteSuccLeft $
                    rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
                    pqlte)
                   c
                   (divideXOXO c a pr)
                   (divideXOXO c b qr)
  in
    (r ** rewrite mulXOR r c in cong prf)
gcdnGreatest (S k) (O a) (O b) pqlte (I c)  pr         qr        =
  let (r**prf) = gcdnGreatest k a b
                   (fromLteSucc $
                    lteSuccLeft $
                    rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
                    pqlte)
                   (I c)
                   (divideXOXI (I c) a c pr (U**Refl))
                   (divideXOXI (I c) b c qr (U**Refl))
  in
    (O r ** cong prf)
gcdnGreatest (S k) (O a) (I b) pqlte  r     pr         qr        =
  gcdnGreatest k a (I b)
    (fromLteSucc pqlte)
     r
    (divideXOXI r a b pr qr)
     qr
gcdnGreatest (S k) (I a) (O b) pqlte  r     pr         qr        =
  gcdnGreatest k (I a) b
    (rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
     fromLteSucc pqlte)
     r
     pr
    (divideXOXI r b a qr pr)
gcdnGreatest (S k) (I a) (I b) pqlte  r    (s ** psr) (t ** qtr) with (a `compare` b) proof ab
  | LT = gcdnGreatest k (b-a) (I a)
           (lteTransitive {m=(bipDigitsNat b) + (S $ bipDigitsNat a)}
              (plusLTEMonoR (S $ bipDigitsNat a) (bipDigitsNat $ b-a) (bipDigitsNat b) $
               sizeNatMonotone (b-a) b $
               addLtMonoRFro a (b-a) b $
               rewrite subAdd b a $ sym ab in
               ltAddDiagR b a)
              (rewrite plusCommutative (bipDigitsNat b) (S $ bipDigitsNat a) in
               rewrite plusSuccRightSucc (bipDigitsNat a) (bipDigitsNat b) in
               fromLteSucc pqlte))
            r
           (divideXOXI r (b-a) a
              (rewrite sym $ subXIXI b a $ sym ab in
               rewrite subMono qtr psr in
               rewrite sym $ mulSubDistrR t s r $
                         mulLtMonoRFro r s t $
                         rewrite sym psr in
                         rewrite sym qtr in
                         sym ab
                       in
                 (t-s ** Refl))
              (s**psr)
           )
           (s**psr)
  | EQ = (s**psr)
  | GT = gcdnGreatest k (a-b) (I b)
           (lteTransitive {m=(bipDigitsNat a) + (S $ bipDigitsNat b)}
            (plusLTEMonoR (S $ bipDigitsNat b) (bipDigitsNat $ a-b) (bipDigitsNat $ a) $
             sizeNatMonotone (a-b) a $
             addLtMonoRFro b (a-b) a $
             rewrite subAdd a b $ gtLt a b $ sym ab in
              ltAddDiagR a b)
            (fromLteSucc pqlte))
           r
           (divideXOXI r (a-b) b
              (rewrite sym $ subXIXI a b $ gtLt a b $ sym ab in
               rewrite subMono psr qtr in
               rewrite sym $ mulSubDistrR s t r $
                         mulLtMonoRFro r t s $
                         rewrite sym psr in
                         rewrite sym qtr in
                         gtLt a b $ sym ab
                       in
                 (s-t ** Refl))
              (t**qtr)
           )
           (t**qtr)

-- gcd_greatest

gcdGreatest : (p, q, r : Bip) -> bipDivides r p -> bipDivides r q
                              -> bipDivides r (bipGCD p q)
gcdGreatest p q r rp rq =
  gcdnGreatest ((bipDigitsNat p) + (bipDigitsNat q))
               p q lteRefl r rp rq

-- ggcd_greatest

-- The rests after division by GCD are relatively prime

ggcdGreatest : (p, q : Bip) ->
                let ppqq = snd $ bipGGCD p q
                    pp = fst ppqq
                    qq = snd ppqq
                in
                  (r : Bip) -> bipDivides r pp -> bipDivides r qq -> r = U
ggcdGreatest p q r (s**rpp) (t**rqq) =
  let (peq, qeq) = ggcdCorrectDivisors p q
      (rr**rprf) = gcdGreatest p q ((fst $ bipGGCD p q)*r)
                     (s ** rewrite mulComm s ((fst $ bipGGCD p q)*r) in
                           rewrite sym $ mulAssoc (fst $ bipGGCD p q) r s in
                           rewrite mulComm r s in
                           rewrite sym rpp in
                           peq)
                     (t ** rewrite mulComm t ((fst $ bipGGCD p q)*r) in
                           rewrite sym $ mulAssoc (fst $ bipGGCD p q) r t in
                           rewrite mulComm r t in
                           rewrite sym rqq in
                           qeq)
      rprf' = replace {P=\x=>x=rr*((fst $ bipGGCD p q)*r)} (sym $ ggcdGcd p q)
                      rprf
  in
    mulEq1R rr r $
    mulOneNeutral (rr*r) (fst $ bipGGCD p q) $
    rewrite sym $ mulAssoc rr r (fst $ bipGGCD p q) in
    rewrite mulComm r (fst $ bipGGCD p q) in
    sym rprf'