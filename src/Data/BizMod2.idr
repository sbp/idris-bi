module Data.BizMod2

import public Data.Bip
import public Data.Bip.AddMul
import public Data.Bip.OrdSub
import public Data.Biz
import public Data.Biz.Proofs

%default total
%access public export

twoPowerNat : Nat -> Bip
twoPowerNat  Z    = U
twoPowerNat (S k) = O (twoPowerNat k)

modulus : Nat -> Biz
modulus = BizP . twoPowerNat

data BizMod2 : (n : Nat) -> Type where
  MkBizMod2 : (intVal : Biz) -> (lowrange : -1 `Lt` intVal) -> (hirange : intVal `Lt` modulus n) -> BizMod2 n

MkBizMod2Inj : MkBizMod2 x lox hix = MkBizMod2 y loy hiy -> x = y
MkBizMod2Inj Refl = Refl

-- Fast normalization modulo [2^wordsize]

pModTwoP : (p : Bip) -> (n : Nat) -> Biz
pModTwoP  _     Z    = 0
pModTwoP  U    (S _) = 1
pModTwoP (O a) (S k) = bizD (pModTwoP a k)
pModTwoP (I a) (S k) = bizDPO (pModTwoP a k)

zModModulus : (x : Biz) -> (wordSize : Nat) -> Biz
zModModulus  BizO    _        = 0
zModModulus (BizP a) wordSize = pModTwoP a wordSize
zModModulus (BizM a) wordSize = let r = pModTwoP a wordSize in 
                                if r==0 then 0
                                        else (modulus wordSize) - r

-- TODO add to Prelude? 

opSwitch : (o, o1 : Ordering) -> compareOp (switchEq o o1) = switchEq (compareOp o) (compareOp o1)
opSwitch _ LT = Refl
opSwitch _ EQ = Refl
opSwitch _ GT = Refl                                        

-- TODO add to Biz.Proofs                                         

bizDPODCompare : (n, m : Biz) -> bizDPO n `compare` bizD m = switchEq GT (n `compare` m)
bizDPODCompare  BizO     BizO    = Refl
bizDPODCompare  BizO    (BizP _) = Refl
bizDPODCompare  BizO    (BizM _) = Refl
bizDPODCompare (BizP _)  BizO    = Refl
bizDPODCompare (BizP a) (BizP b) = compareContSpec a b GT
bizDPODCompare (BizP _) (BizM _) = Refl
bizDPODCompare (BizM _)  BizO    = Refl
bizDPODCompare (BizM _) (BizP _) = Refl
bizDPODCompare (BizM a) (BizM b) = 
  case succPredOr a of 
    Left lprf => 
      rewrite lprf in 
      rewrite sym $ compareContSpec b U GT in 
      sym $ compareContGtGtFro b U $ nlt1R b
    Right rprf => 
      rewrite sym rprf in 
      rewrite predDoubleSucc (bipPred a) in 
      rewrite compareSuccR b (bipPred a) in 
      compareContSpec b (bipPred a) LT

bizDDPOCompare : (n, m : Biz) -> bizD n `compare` bizDPO m = switchEq LT (n `compare` m)
bizDDPOCompare n m =
  rewrite compareAntisym (bizDPO m) (bizD n) in
  rewrite bizDPODCompare m n in
  rewrite compareAntisym m n in
  opSwitch GT (m `compare` n)

bizDCompare : (n, m : Biz) -> bizD n `compare` bizD m = n `compare` m
bizDCompare n m = 
  rewrite doubleSpec n in 
  rewrite doubleSpec m in 
  mulCompareMonoL 2 n m Refl

--  

pModTwoPRange : (n : Nat) -> (p : Bip) -> (0 `Le` pModTwoP p n, pModTwoP p n `Lt` modulus n)
pModTwoPRange  Z     _    = (uninhabited, Refl)
pModTwoPRange (S _)  U    = (uninhabited, Refl)
pModTwoPRange (S k) (O a) = 
  let (lo, hi) = pModTwoPRange k a in 
  ( rewrite bizDCompare 0 (pModTwoP a k) in 
    lo
  , rewrite bizDCompare (pModTwoP a k) (modulus k) in 
    hi
  )
pModTwoPRange (S k) (I a) = 
  let (lo, hi) = pModTwoPRange k a in 
  ( rewrite bizDDPOCompare 0 (pModTwoP a k) in
    case leLtOrEq 0 (pModTwoP a k) lo of
      Left lprf => rewrite lprf in 
                   uninhabited
      Right rprf => rewrite sym rprf in 
                    uninhabited
  , rewrite bizDPODCompare (pModTwoP a k) (modulus k) in 
    rewrite hi in 
    Refl
  )

pModTwoPEq : (n : Nat) -> (p : Bip) -> pModTwoP p n = BizP p `bizMod` modulus n
pModTwoPEq n p = let (y**prf) = aux n p 
                     (zlemt, mtltmod) = pModTwoPRange n p
                 in
                 snd $ divModPos (BizP p) (modulus n) y (pModTwoP p n) zlemt mtltmod prf
  where 
  aux : (n : Nat) -> (p : Bip) -> (y ** BizP p = y * modulus n + pModTwoP p n)
  aux  Z     p    = (BizP p ** cong $ sym $ mul1R p)
  aux (S _)  U    = (0 ** Refl)
  aux (S k) (O a) = let (y**prf) = aux k a in 
                    (y ** rewrite doubleSpec (pModTwoP a k) in 
                          rewrite mulAssoc y 2 (modulus k) in 
                          rewrite mulComm y 2 in
                          rewrite sym $ mulAssoc 2 y (modulus k) in
                          rewrite sym $ mulAddDistrL 2 (y*(modulus k)) (pModTwoP a k) in
                          cong {f = bizMult 2} prf)
  aux (S k) (I a) = let (y**prf) = aux k a in 
                    (y ** rewrite succDoubleSpec (pModTwoP a k) in 
                          rewrite mulAssoc y 2 (modulus k) in 
                          rewrite mulComm y 2 in
                          rewrite sym $ mulAssoc 2 y (modulus k) in
                          rewrite addAssoc (2*(y*(modulus k))) (2*(pModTwoP a k)) 1 in
                          rewrite sym $ mulAddDistrL 2 (y*(modulus k)) (pModTwoP a k) in
                          cong {f = \x => 2*x+1} prf)

zModModulusRange : (x : Biz) -> (n : Nat) -> (0 `Le` zModModulus x n, zModModulus x n `Lt` modulus n)
zModModulusRange  BizO    _ = (uninhabited, Refl)
zModModulusRange (BizP a) n = pModTwoPRange n a
zModModulusRange (BizM a) n with ((pModTwoP a n) == 0) proof zprf
  | False = 
    let (lo, hi) = pModTwoPRange n a in
    ( rewrite compareAntisym ((modulus n)-(pModTwoP a n)) 0 in
      rewrite sym $ compareSub (modulus n) (pModTwoP a n) in 
      rewrite compareAntisym (pModTwoP a n) (modulus n) in 
      rewrite hi in 
      uninhabited
    , case leLtOrEq 0 (pModTwoP a n) lo of 
        Left lprf => 
          rewrite addCompareMonoL (modulus n) (-(pModTwoP a n)) 0 in
          rewrite sym $ compareOpp 0 (pModTwoP a n) in 
          lprf
        Right rprf => 
          let pmodeq0 = eqbEqFro (pModTwoP a n) 0 $ sym rprf in 
          absurd $ replace pmodeq0 zprf 
    )
  | True = (uninhabited, Refl)

zModModulusRange' : (x : Biz) -> (n : Nat) -> (-1 `Lt` zModModulus x n, zModModulus x n `Lt` modulus n)
zModModulusRange' x n = 
  let lohi = zModModulusRange x n 
      lo = fst lohi
      hi = snd lohi
  in 
  ( rewrite sym $ addCompareMonoR (-1) (zModModulus x n) 1 in 
    ltSuccRFro 0 (zModModulus x n) lo
  , hi)

-- TODO add to Biz.Proofs, look where it can be inserted

compareSubR : (n, m : Biz) -> n `compare` m = 0 `compare` (m-n)
compareSubR n m = 
  rewrite compareAntisym (m-n) 0 in
  rewrite sym $ compareSub m n in
  compareAntisym m n

zModModulusEq : (x : Biz) -> (n : Nat) -> zModModulus x n = x `bizMod` (modulus n)
zModModulusEq  BizO    _ = Refl
zModModulusEq (BizP a) n = pModTwoPEq n a
zModModulusEq (BizM a) n with (pModTwoP a n) proof pz
  zModModulusEq (BizM a) n | BizO = 
    let
      deq = divEuclEq (BizM a) (modulus n) uninhabited  
      pmodz = sym $ trans pz (pModTwoPEq n a)
      divmod = divModPos (BizM a) (modulus n) ((BizM a) `bizDiv` (modulus n)) 0 uninhabited Refl $ 
               replace {P=\x => BizM a = (((BizM a) `bizDiv` (modulus n)) * (modulus n)) + (snd (bizDivEuclidHelp1 (fst (bipzDivEuclid a (modulus n))) x (modulus n)))} pmodz deq
    in
    snd divmod
  zModModulusEq (BizM a) n | BizP b = 
    let 
      deq = divEuclEq (BizM a) (modulus n) uninhabited  
      bmodz = sym $ trans pz (pModTwoPEq n a)
      divmod = divModPos (BizM a) (modulus n) ((BizM a) `bizDiv` (modulus n)) (bipMinusBiz (twoPowerNat n) b) 
             (rewrite sym $ compareSubR (BizP b) (modulus n) in 
              ltLeIncl b (twoPowerNat n) $ 
              replace {P = \x => x `Lt` modulus n} (sym pz) (snd $ pModTwoPRange n a)
             ) 
             (rewrite compareSubR ((modulus n)-(BizP b)) (modulus n) in 
              rewrite oppAddDistr (modulus n) (BizM b) in 
              rewrite addAssoc (modulus n) (-(modulus n)) (BizP b) in 
              rewrite posSubDiag (twoPowerNat n) in 
              Refl
             ) $
             replace {P=\x => BizM a = (((BizM a) `bizDiv` (modulus n)) * (modulus n)) + (snd (bizDivEuclidHelp1 (fst (bipzDivEuclid a (modulus n))) x (modulus n)))} bmodz deq
    in 
    snd divmod
  zModModulusEq (BizM a) n | BizM b = 
    let 
      zlep = fst $ pModTwoPRange n a 
      zleneg = replace {P = \x => 0 `Le` x} (sym pz) zlep
    in
    -- TODO bug: we arrive at `zleneg:(GT=GT)->Void` but the following results in
    -- `zleneg does not have a function type ((\x => ([__])) (BizM b))`          
    --absurd $ zleneg Refl                                             
    really_believe_me zleneg           
    
-- The [unsigned] and [signed] functions return a Biz corresponding to the given
-- machine integer, interpreted as unsigned or signed respectively.
                          
unsigned : BizMod2 n -> Biz
unsigned (MkBizMod2 intVal _ _) = intVal

signed : BizMod2 n -> Biz
signed {n} bm = 
  let x = unsigned bm
      m = modulus n
  in 
  if x < bizDivTwo m
    then x
    else x-m      

-- Conversely, [repr] takes a Biz and returns the corresponding machine integer.
-- The argument is treated modulo [modulus n].             
                                                                             
repr : (x : Biz) -> (n : Nat) -> BizMod2 n
repr x n = 
  let lohi = zModModulusRange' x n 
      lo = fst lohi
      hi = snd lohi
  in
  MkBizMod2 (zModModulus x n) lo hi

mkintEq : (x, y : Biz) -> (n : Nat) 
       -> (lox : -1 `Lt` x) -> (hix : x `Lt` modulus n) 
       -> (loy : -1 `Lt` y) -> (hiy : y `Lt` modulus n) 
       -> x = y 
       -> MkBizMod2 x lox hix = MkBizMod2 y loy hiy
mkintEq y y n lox hix loy hiy Refl = 
  rewrite aux (-1) y lox loy in 
  rewrite aux y (modulus n) hix hiy in 
  Refl
  where
  -- this seems like a variation on UIP/axiom K
  aux : (x, y : Biz) -> (p1, p2 : x `Lt` y) -> p1 = p2
  aux x y p1 p2 with (x `compare` y)
    aux _ _ Refl Refl | LT = Refl
    aux _ _ p1   _    | EQ = absurd p1
    aux _ _ p1   _    | GT = absurd p1
  
DecEq (BizMod2 n) where
  decEq (MkBizMod2 x lox hix) (MkBizMod2 y loy hiy) = case decEq x y of 
    Yes prf => Yes (mkintEq x y n lox hix loy hiy prf)
    No contra => No (contra . MkBizMod2Inj)
  
-- Arithmetic and logical operations over machine integers

Eq (BizMod2 n) where
  x == y = (unsigned x) == (unsigned y)

Ord (BizMod2 n) where
  compare x y = (unsigned x) `compare` (unsigned y)

Num (BizMod2 n) where
  x + y         = repr (unsigned x + unsigned y) n
  x * y         = repr (unsigned x * unsigned y) n
  fromInteger i = repr (fromInteger i) n

Neg (BizMod2 n) where
  negate x = repr (-(unsigned x)) n
  abs x    = repr (abs (signed x)) n  -- TODO is this correct?
  x - y    = repr (unsigned x - unsigned y) n

-- TODO which of the following to use for `Integral`?
divs : (x, y : BizMod2 n) -> BizMod2 n 
divs {n} x y = repr ((signed x) `bizQuot` (signed y)) n

mods : (x, y : BizMod2 n) -> BizMod2 n 
mods {n} x y = repr ((signed x) `bizRem` (signed y)) n

divu : (x, y : BizMod2 n) -> BizMod2 n 
divu {n} x y = repr ((unsigned x) `bizDiv` (unsigned y)) n

modu : (x, y : BizMod2 n) -> BizMod2 n 
modu {n} x y = repr ((unsigned x) `bizMod` (unsigned y)) n  
    