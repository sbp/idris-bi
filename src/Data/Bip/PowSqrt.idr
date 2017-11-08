module Data.Bip.PowSqrt

import Data.Util

import Data.Bip
import Data.Bip.Iter
import Data.Bip.AddMul
import Data.Bip.OrdSub

%access public export
%default total

-- pow_1_r

pow1R : (p : Bip) -> bipPow p U = p
pow1R  U    = Refl
pow1R (O a) = rewrite mul1R a in Refl
pow1R (I a) = rewrite mul1R a in Refl

-- pow_succ_r

powSuccR : (p, q : Bip) -> bipPow p (bipSucc q) = p * (bipPow p q)
powSuccR p q = iterSucc (bipMult p) U q

-- pow_gt_1

powGt1 : (p, q : Bip) -> U `Lt` p -> U `Lt` bipPow p q
powGt1 p q ultp =
  peanoRect
    (\x => U `Lt` bipPow p x)
    (replace (sym $ pow1R p) ultp)
    (\r,ultpr =>
       let pultppr = mulLtMonoLTo p U (bipPow p r) ultpr
           pultpsr = replace {P=\x=>(p*U) `Lt` x}
                             (sym $ powSuccR p r) pultppr
           pltpsr = replace {P=\x=>x `Lt` (bipPow p $ bipSucc r)}
                            (mul1R p) pultpsr
       in
         ltTrans U p (bipPow p (bipSucc r)) ultp pltpsr
    )
    q

--  size_gt

sizeGt : (p : Bip) -> p `Lt` bipPow 2 (bipDigits p)
sizeGt  U    = Refl
sizeGt (O a) = rewrite powSuccR 2 (bipDigits a) in
               sizeGt a
sizeGt (I a) = rewrite powSuccR 2 (bipDigits a) in
               compareContGtLtFro a (bipPow 2 (bipDigits a)) (sizeGt a)

-- size_le

sizeLe : (p : Bip) -> bipPow 2 (bipDigits p) `Le` O p
sizeLe  U    = uninhabited
sizeLe (O a) = rewrite powSuccR 2 (bipDigits a) in
               sizeLe a
sizeLe (I a) = rewrite powSuccR 2 (bipDigits a) in
               leTrans (bipPow 2 (bipDigits a)) (O a) (I a)
                 (sizeLe a) (rewrite compareContRefl a LT in
                             uninhabited)

-- TODO like in other specs, e.g., `BimMinusSpec` we use a workaround with eq
-- parameter

data SqrtSpec : (Bip, Bim) -> Bip -> Type where
  SqrtExact  : x=s*s   ->               pm = (s, BimO)   -> SqrtSpec pm x
  SqrtApprox : x=s*s+r -> r `Le` O s -> pm = (s, BimP r) -> SqrtSpec pm x

-- sqrtrem_step_spec

sqrtremStepSpec : Either (f=O) (f=I) -> Either (g=O) (g=I) -> SqrtSpec p x
               -> SqrtSpec (bipSqrtRemStep f g p) (g (f x))
sqrtremStepSpec (Left  fo) (Left  go) (SqrtExact {s} prf pprf) =
  rewrite fo in rewrite go in rewrite prf in rewrite pprf in
  SqrtExact {s=O s} (rewrite sym $ squareXO s in Refl) Refl
sqrtremStepSpec (Left  fo) (Right gi) (SqrtExact {s} prf pprf) =
  rewrite fo in rewrite gi in rewrite prf in rewrite pprf in
  SqrtApprox {s=O s} {r=U} (rewrite sym $ mulXOR s s in Refl) uninhabited Refl
sqrtremStepSpec (Right fi) (Left  go) (SqrtExact {s} prf pprf) =
  rewrite fi in rewrite go in rewrite prf in rewrite pprf in
  SqrtApprox {s=O s} {r=O U} (rewrite mulXOR s s in Refl) uninhabited Refl
sqrtremStepSpec (Right fi) (Right gi) (SqrtExact {s} prf pprf) =
  rewrite fi in rewrite gi in rewrite prf in rewrite pprf in
  SqrtApprox {s=O s} {r=I U} (rewrite mulXOR s s in Refl) uninhabited Refl
sqrtremStepSpec {f} {g} foi goi (SqrtApprox {s} {r} prf rle pprf) =
  rewrite prf in rewrite pprf in
  rewrite hfg (s*s) r foi goi in
  aux
  where
  hfg : (p, q : Bip) -> Either (f=O) (f=I) -> Either (g=O) (g=I)
                    -> g (f (p+q)) = O (O p) + g (f q)
  hfg _ _ (Left fo ) (Left go ) = rewrite fo in rewrite go in Refl
  hfg _ _ (Left fo ) (Right gi) = rewrite fo in rewrite gi in Refl
  hfg _ _ (Right fi) (Left go ) = rewrite fi in rewrite go in Refl
  hfg _ _ (Right fi) (Right gi) = rewrite fi in rewrite gi in Refl
  gfleii : (p, q : Bip) -> Either (f=O) (f=I) -> Either (g=O) (g=I) -> p `Le` q
                       -> g (f p) `Le` I (I q)
  gfleii p q (Left fo ) (Left go ) pleq =
    rewrite fo in rewrite go in
    pleq . compareContLtGtTo p q
  gfleii p q (Left fo ) (Right gi) pleq =
    rewrite fo in rewrite gi in
    pleq . compareContLtGtTo p q
  gfleii p q (Right fi) (Left go ) pleq =
    rewrite fi in rewrite go in
    pleq . compareContLtGtTo p q
  gfleii _ _ (Right fi) (Right gi) pleq =
    rewrite fi in rewrite gi in
    pleq
  aux : SqrtSpec
          (bipSqrtRemStepHelp s (I $ O s) (g $ f r) $
            (I $ O s) `compare` (g $ f r))
          ((O $ O $ s*s)+(g $ f r))
  aux with ((I $ O s) `compare` (g $ f r)) proof cmp
    | LT =
      let (q**qprf) = subMaskPos (g $ f r) (I $ O s) $ sym cmp
          qdef = sym $ cong {f=bipMinusHelp} qprf
      in
       rewrite qprf in
         SqrtApprox {s=I s} {r=q}
           (rewrite qdef in
            rewrite addSubAssoc (I $ s+s*(I s)) (g $ f r) (I $ O s) $ sym cmp in
            addRegR ((O $ O $ s*s)+(g $ f r)) (((I $ s+s*(I s))+(g $ f r))-(I $ O s)) (I $ O s) $
            rewrite subAdd ((I $ s+s*(I s))+(g $ f r)) (I $ O s) $
              ltTrans (I $ O s) (I $ s+s*(I s)) ((I $ s+(s*(I s)))+(g $ f r))
                (rewrite sym $ addDiag s in
                 addLtMonoLTo s s (s*(I s)) $
                 rewrite mulXIR s s in
                 ltAddDiagR s (O $ s*s))
                (ltAddDiagR (I $ s+s*(I s)) (g $ f r)) in
            rewrite sym $ addAssoc (O $ O $ s*s) (g $ f r) (I $ O s) in
            rewrite addComm (g $ f r) (I $ O s) in
            rewrite addAssoc (O $ O $ s*s) (I $ O s) (g $ f r) in
            rewrite mulXIR s s in
            rewrite addAssoc s s (O $ s*s) in
            rewrite addDiag s in
            rewrite addComm (s*s) s in
            Refl)
           (rewrite qdef in
            addLeMonoRFro (I $ O s) ((g $ f r)-(I $ O s)) (O $ I s) $
            rewrite subAdd (g $ f r) (I $ O s) $ sym cmp in
            rewrite addDiag s in
            gfleii r (O s) foi goi rle)
           Refl
    | EQ =
      rewrite sym $ compareEqIffTo (I $ O s) (g $ f r) $ sym cmp in
      rewrite subMaskDiag s in
      SqrtExact {s=I s}
        (rewrite mulXIR s s in
         rewrite addAssoc s s (O $ s*s) in
         rewrite addDiag s in
         rewrite addComm (s*s) s in
         Refl)
        Refl
    | GT =
      SqrtApprox {s=O s} {r=g $ f r}
        (rewrite mulXOR s s in Refl)
        (ltSuccRTo (g $ f r) (O $ O s) $
         gtLt (I $ O s) (g $ f r) $
         sym cmp)
        Refl

-- sqrtrem_spec

sqrtremSpec : (p : Bip) -> SqrtSpec (bipSqrtRem p) p
sqrtremSpec  U        = SqrtExact {s=U} Refl Refl
sqrtremSpec (O  U   ) = SqrtApprox {s=U} {r=U} Refl uninhabited Refl
sqrtremSpec (O (O a)) =
  sqrtremStepSpec (Left Refl ) (Left Refl ) (sqrtremSpec a)
sqrtremSpec (O (I a)) =
  sqrtremStepSpec (Right Refl) (Left Refl ) (sqrtremSpec a)
sqrtremSpec (I  U   ) = SqrtApprox {s=U} {r=O U} Refl uninhabited Refl
sqrtremSpec (I (O a)) =
  sqrtremStepSpec (Left Refl ) (Right Refl) (sqrtremSpec a)
sqrtremSpec (I (I a)) =
  sqrtremStepSpec (Right Refl) (Right Refl) (sqrtremSpec a)

-- sqrt_spec

sqrtSpec : (p : Bip) -> let s = bipSqrt p in
                        (s*s `Le` p, p `Lt` (bipSucc s)*(bipSucc s))
sqrtSpec p = case sqrtremSpec p of
  SqrtExact {s} prf srprf =>
    rewrite srprf in rewrite prf in
    ( gtNotSelf (s*s)
    , mulLtMono s (bipSucc s) s (bipSucc s) (ltSuccDiagR s) (ltSuccDiagR s)
    )
  SqrtApprox {s} {r} prf rle srprf =>
    rewrite srprf in rewrite prf in
    ( ltLeIncl (s*s) (s*s+r) $ ltAddDiagR (s*s) r
    , rewrite mulSuccR (bipSucc s) s in
      rewrite mulSuccL s s in
      rewrite addAssoc (bipSucc s) s (s*s) in
      rewrite addComm ((bipSucc s)+s) (s*s) in
      addLtMonoLTo (s*s) r ((bipSucc s)+s) $
      rewrite sym $ add1L s in
      rewrite sym $ addAssoc U s s in
      rewrite addDiag s in
      ltSuccRFro r (O s) rle
    )