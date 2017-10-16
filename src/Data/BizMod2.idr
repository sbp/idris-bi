module Data.BizMod2

import public Data.Bip
import public Data.Bip.AddMul
import public Data.Bip.IterPow
import public Data.Bip.OrdSub

import public Data.Biz
import public Data.Biz.Proofs
import public Data.Biz.Nat

%default total
%access public export

-- TODO add to Bip/Biz?

twoPowerNat : Nat -> Bip
twoPowerNat  Z    = U
twoPowerNat (S k) = O (twoPowerNat k)

twoP : (x : Biz) -> Biz
twoP  BizO = 1
twoP (BizP y) = BizP $ bipIter O 1 y
twoP (BizM _) = 0

-- TODO add %static on `n` everywhere to minimize recalculation

modulus : (n : Nat) -> Biz
modulus = BizP . twoPowerNat

halfModulus : (n : Nat) -> Biz
halfModulus = bizDivTwo . modulus

maxUnsigned : (n : Nat) -> Biz
maxUnsigned = bizPred . modulus

maxSigned : (n : Nat) -> Biz
maxSigned = bizPred . halfModulus

minSigned : (n : Nat) -> Biz
minSigned = bizOpp . halfModulus

modulusPower : (n : Nat) -> modulus n = twoP (toBizNat n)
modulusPower  Z        = Refl
modulusPower (S  Z)    = Refl
modulusPower (S (S k)) =
  -- TODO bug? somehow you can't rewrite with this directly
  let ih2 = cong {f = bizMult 2} $ modulusPower (S k) in
  rewrite ih2 in
  cong $ sym $ iterSucc O U (toBipNatSucc k)

-- modulus_pos is trivial

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

zModModulus : (x : Biz) -> (n : Nat) -> Biz
zModModulus  BizO    _ = 0
zModModulus (BizP a) n = pModTwoP a n
zModModulus (BizM a) n = let r = pModTwoP a n in
                         if r==0 then 0
                                 else (modulus n) - r

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
  compare x y = (signed x) `compare` (signed y)

ltu : (x, y : BizMod2 n) -> Bool
ltu x y = (unsigned x) < (unsigned y)

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

-- Bitwise boolean operations

and : (x, y : BizMod2 n) -> BizMod2 n
and {n} x y = repr ((unsigned x) `bizAnd` (unsigned y)) n

or : (x, y : BizMod2 n) -> BizMod2 n
or {n} x y = repr ((unsigned x) `bizOr` (unsigned y)) n

xor : (x, y : BizMod2 n) -> BizMod2 n
xor {n} x y = repr ((unsigned x) `bizXor` (unsigned y)) n

not : (x : BizMod2 n) -> BizMod2 n
not x = x `xor` (-1)

-- Shifts and rotates

shl : (x, y : BizMod2 n) -> BizMod2 n
shl {n} x y = repr ((unsigned x) `bizShiftL` (unsigned y)) n

shru : (x, y : BizMod2 n) -> BizMod2 n
shru {n} x y = repr ((unsigned x) `bizShiftR` (unsigned y)) n

shr : (x, y : BizMod2 n) -> BizMod2 n
shr {n} x y = repr ((signed x) `bizShiftR` (unsigned y)) n

rol : (x, y : BizMod2 n) -> BizMod2 n
rol {n} x y =
  let
    zws = toBizNat n
    m = (unsigned y) `bizMod` zws
    x' = unsigned x
  in
  repr ((x' `bizShiftL` m) `bizOr` (x' `bizShiftR` (zws - m))) n

ror : (x, y : BizMod2 n) -> BizMod2 n
ror {n} x y =
  let
    zws = toBizNat n
    m = (unsigned y) `bizMod` zws
    x' = unsigned x
  in
  repr ((x' `bizShiftR` m) `bizOr` (x' `bizShiftL` (zws - m))) n

rolm : (x, a, m : BizMod2 n) -> BizMod2 n
rolm x a m = (x `rol` a) `and` m

-- Viewed as signed divisions by powers of two, [shrx] rounds towards zero,
-- while [shr] rounds towards minus infinity.

shrx : (x, y : BizMod2 n) -> BizMod2 n
shrx {n} x y = x `divs` (1 `shl` y)

-- High half of full multiply.

mulhu : (x, y : BizMod2 n) -> BizMod2 n
mulhu {n} x y = repr ((unsigned x * unsigned y) `bizDiv` modulus n) n

mulhs : (x, y : BizMod2 n) -> BizMod2 n
mulhs {n} x y = repr ((signed x * signed y) `bizDiv` modulus n) n

-- Condition flags

negative : (x : BizMod2 n) -> BizMod2 n
negative x = if x < 0 then 1 else 0

addCarry : (x, y, cin : BizMod2 n) -> BizMod2 n
addCarry x y cin = if (unsigned x + unsigned y + unsigned cin) < modulus n then 0 else 1

addOverflow : (x, y, cin : BizMod2 n) -> BizMod2 n
addOverflow {n} x y cin =
  let s = signed x + signed y + signed cin in
  if minSigned n <= s && s <= maxSigned n then 0 else 1

subBorrow : (x, y, bin : BizMod2 n) -> BizMod2 n
subBorrow x y bin = if (unsigned x - unsigned y - unsigned bin) < 0 then 1 else 0

subOverflow : (x, y, bin : BizMod2 n) -> BizMod2 n
subOverflow x y bin =
  let s = signed x - signed y - signed bin in
  if minSigned n <= s && s <= maxSigned n then 0 else 1

-- [shr_carry x y] is 1 if [x] is negative and at least one 1 bit is shifted
-- away.

shrCarry : (x, y : BizMod2 n) -> BizMod2 n
shrCarry x y = if x < 0 && (x `and` ((1 `shl` y)-1)) /= 0 then 1 else 0

-- Zero and sign extensions

zShiftin : (b : Bool) -> (x : Biz) -> Biz
zShiftin b x = if b then bizDPO x else bizD x

zZeroExt : (n, x : Biz) -> Biz
zZeroExt n = bizIter (\rec, x => zShiftin (bizOdd x) (rec (bizDivTwo x))) n (\_ => 0)

zSignExt : (n, x : Biz) -> Biz
zSignExt n = bizIter (\rec, x => zShiftin (bizOdd x) (rec (bizDivTwo x))) (bizPred n) (\x => if bizOdd x then -1 else 0)

-- TODO should these change the word size?

zeroExt : (m : Biz) -> (x : BizMod2 n) -> BizMod2 n
zeroExt {n} m x = repr (zZeroExt m (unsigned x)) n

signExt : (m : Biz) -> (x : BizMod2 n) -> BizMod2 n
signExt {n} m x = repr (zSignExt m (unsigned x)) n

-- Decomposition of a number as a sum of powers of two.

zOneBits : (n : Nat) -> (x, i : Biz) -> List Biz
zOneBits  Z    _ _ = []
zOneBits (S k) x i = if bizOdd x
                       then i :: zOneBits k (bizDivTwo x) (bizSucc i)
                       else zOneBits k (bizDivTwo x) (bizSucc i)

oneBits : (x : BizMod2 n) -> List (BizMod2 n)
oneBits {n} x = (\x => repr x n) <$> (zOneBits n (unsigned x) 0)

-- Recognition of powers of two.

isPower2 : (x : BizMod2 n) -> Maybe (BizMod2 n)
isPower2 {n} x = case zOneBits n (unsigned x) 0 of
  [i] => Just (repr i n)
  _   => Nothing

-- Comparisons.

data Comparison =
      Ceq -- same
    | Cne -- different
    | Clt -- less than
    | Cle -- less than or equal
    | Cgt -- greater than
    | Cge -- greater than or equal

negateComparison : Comparison -> Comparison
negateComparison Ceq = Cne
negateComparison Cne = Ceq
negateComparison Clt = Cge
negateComparison Cle = Cgt
negateComparison Cgt = Cle
negateComparison Cge = Clt

swapСomparison : Comparison -> Comparison
swapСomparison Ceq = Ceq
swapСomparison Cne = Cne
swapСomparison Clt = Cgt
swapСomparison Cle = Cge
swapСomparison Cgt = Clt
swapСomparison Cge = Cle

cmp : (c : Comparison) -> (x, y : BizMod2 n) -> Bool
cmp Ceq = (==)
cmp Cne = (/=)
cmp Clt = (<)
cmp Cle = (<=)
cmp Cgt = (>)
cmp Cge = (>=)

cmpu : (c : Comparison) -> (x, y : BizMod2 n) -> Bool
cmpu Ceq = (==)
cmpu Cne = (/=)
cmpu Clt = ltu
cmpu Cle = \x,y => not (x `ltu` y)
cmpu Cgt = \x,y => y `ltu` x
cmpu Cge = \x,y => not (y `ltu` x)

isFalse : (x : BizMod2 n) -> Type
isFalse x = x=0

isTrue : (x : BizMod2 n) -> Type
isTrue x = Not (x=0)

notbool : (x : BizMod2 n) -> BizMod2 n
notbool x = if x == 0 then 1 else 0

-- x86-style extended division and modulus

divmodu2 : (nhi, nlo, d : BizMod2 n) -> Maybe (BizMod2 n, BizMod2 n)
divmodu2 {n} nhi nlo d =
  if d==0 then Nothing
    else let
        (q, r) = bizDivEuclid ((unsigned nhi) * (modulus n) + (unsigned nlo)) (unsigned d)
      in
        if q <= maxUnsigned n then Just (repr q n, repr r n) else Nothing

divmods2 : (nhi, nlo, d : BizMod2 n) -> Maybe (BizMod2 n, BizMod2 n)
divmods2 {n} nhi nlo d =
  if d==0 then Nothing
    else let
        (q, r) = bizQuotRem ((signed nhi) * (modulus n) + (unsigned nlo)) (signed d)
      in
        if minSigned n <= q && q <= maxSigned n then Just (repr q n, repr r n) else Nothing

-- Properties of integers and integer arithmetic

-- Properties of [modulus], [max_unsigned], etc.

halfModulusPower : (n : Nat) -> halfModulus n = twoP (toBizNat n - 1)
halfModulusPower n =
  rewrite modulusPower n in
  aux
  where
  aux : bizDivTwo (twoP (toBizNat n)) = twoP (toBizNat n - 1)
  aux with (toBizNat n) proof bn
    | BizO   = Refl
    | BizP a = case succPredOr a of
                 Left  lprf => rewrite lprf in
                               Refl
                 Right rprf => rewrite sym rprf in
                               rewrite iterSucc O U (bipPred a) in
                               rewrite sym $ add1R (bipPred a) in
                               rewrite posSubAdd (bipPred a) 1 1 in
                               Refl
    | BizM _ = let zneg = replace {P = \x => 0 `Le` x} (sym bn) (toBizNatIsNonneg n)
               in
               -- TODO bug: `zneg does not have a function type ((\x => ([__])) (BizM _))`
               -- absurd $ zneg Refl
               really_believe_me zneg

halfModulusModulus : (n : Nat) -> Not (n=0) -> modulus n = 2 * halfModulus n
halfModulusModulus n nz =
  rewrite halfModulusPower n in
  rewrite modulusPower n in
  aux
  where
  aux : twoP (toBizNat n) = 2 * (twoP (toBizNat n - 1))
  aux with (toBizNat n) proof bn
    | BizO   = absurd $ nz $ toBizNatInj n 0 $ sym bn
    | BizP a = case succPredOr a of
                 Left  lprf => rewrite lprf in
                               Refl
                 Right rprf => rewrite sym rprf in
                               rewrite iterSucc O U (bipPred a) in
                               rewrite sym $ add1R (bipPred a) in
                               rewrite posSubAdd (bipPred a) 1 1 in
                               Refl
    | BizM _ = let zneg = replace {P = \x => 0 `Le` x} (sym bn) (toBizNatIsNonneg n)
               in
               -- TODO bug: `zneg does not have a function type ((\x => ([__])) (BizM _))`
               -- absurd $ zneg Refl
               really_believe_me zneg

{- Relative positions, from greatest to smallest:

      max_unsigned
      max_signed
      2*wordsize-1
      wordsize
      0
      min_signed
-}

halfModulusPos : (n : Nat) -> Not (n=0) -> 0 `Lt` halfModulus n
halfModulusPos  Z    nz = absurd $ nz Refl
halfModulusPos (S _) _  = Refl

minSignedNeg : (n : Nat) -> Not (n=0) -> minSigned n `Lt` 0
minSignedNeg  Z    nz = absurd $ nz Refl
minSignedNeg (S _) _  = Refl

maxSignedPos : (n : Nat) -> Not (n=0) -> 0 `Le` maxSigned n
maxSignedPos  Z        nz = absurd $ nz Refl
maxSignedPos (S  Z)    _  = uninhabited
maxSignedPos (S (S _)) _  = uninhabited

-- TODO add to Bip.OrdSub ?
mutual
  ltO : (n : Bip) -> n `Lt` O n
  ltO  U    = Refl
  ltO (O a) = ltO a
  ltO (I a) = compareContGtLtFro a (I a) $ ltI a

  ltI : (n : Bip) -> n `Lt` I n
  ltI  U    = Refl
  ltI (O a) = compareContLtLtFro a (O a) $ ltLeIncl a (O a) $ ltO a
  ltI (I a) = ltI a

leDMO : (n : Bip) -> n `Le` bipDMO n
leDMO  U    = uninhabited
leDMO (O a) = leDMO a . compareContLtGtTo a (bipDMO a)
leDMO (I a) = ltLeIncl a (O a) $ ltO a

twoWordsizeMaxUnsigned : (n : Nat) -> bizDMO (toBizNat n) `Le` maxUnsigned n
twoWordsizeMaxUnsigned  Z = uninhabited
twoWordsizeMaxUnsigned (S Z) = uninhabited
twoWordsizeMaxUnsigned (S (S k)) =
  let ih = twoWordsizeMaxUnsigned (S k)
      bs = toBipNatSucc k
  in
  rewrite predDoubleSucc bs in
  leTrans bs (bipDMO bs) (bipDMO (twoPowerNat k)) (leDMO bs) ih

wordsizeMaxUnsigned : (n : Nat) -> toBizNat n `Le` maxUnsigned n
wordsizeMaxUnsigned  Z     = uninhabited
wordsizeMaxUnsigned (S k) =
  leTrans (toBizNat (S k)) (bizDMO (toBizNat (S k))) (maxUnsigned (S k))
    (leDMO (toBipNatSucc k))
    (twoWordsizeMaxUnsigned (S k))

-- TODO add to Biz.Proofs and rewrite leLtTrans similarly

ltLeTrans : (p, q, r : Biz) -> p `Lt` q -> q `Le` r -> p `Lt` r
ltLeTrans p q r pltq qler =
  case leLtOrEq q r qler of
    Left qltr => ltTrans p q r pltq qltr
    Right qeqr => rewrite sym qeqr in pltq

maxSignedUnsigned : (n : Nat) -> maxSigned n `Lt` maxUnsigned n
maxSignedUnsigned  Z    = Refl
maxSignedUnsigned (S k) =
  let pk = twoPowerNat k in
  ltLeTrans (bipMinusBiz pk U) (BizP pk) (BizP (bipDMO pk))
    -- a proof of bizPred (BizP pk) `Lt` (BizP pk)
    (rewrite compareSub (BizP pk - 1) (BizP pk) in
     rewrite sym $ addAssoc (BizP pk) (-1) (BizM pk) in
     rewrite addComm 1 pk in
     rewrite addAssoc (BizP pk) (BizM pk) (-1) in
     rewrite posSubDiag pk in
     Refl)
    (leDMO pk)

-- this is trivial
unsignedReprEq : (x : Biz) -> (n : Nat) -> unsigned (repr x n) = x `bizMod` modulus n
unsignedReprEq = zModModulusEq

signedReprEq : (x : Biz) -> (n : Nat) -> let m = modulus n
                                             xm = x `bizMod` m
                                        in signed (repr x n) = if xm < halfModulus n then xm else xm - m
signedReprEq x n = rewrite zModModulusEq x n in
                   Refl

-- TODO move to BizMod ?

-- Modulo arithmetic

-- We define and state properties of equality and arithmetic modulo a positive
-- integer.

eqmod : (x, y, m : Biz) -> Type
eqmod x y m = (k ** x = k * m + y)

eqmodRefl : (x, m : Biz) -> eqmod x x m
eqmodRefl _ _ = (0 ** Refl)

eqmodRefl2 : (x, y, m : Biz) -> x = y -> eqmod x y m
eqmodRefl2 y y m Refl = eqmodRefl y m

eqmodSym : (x, y, m : Biz) -> eqmod x y m -> eqmod y x m
eqmodSym _ y m (k ** prf) =
  ((-k) ** rewrite prf in
           rewrite addAssoc ((-k)*m) (k*m) y in
           rewrite sym $ mulAddDistrR (-k) k m in
           rewrite addOppDiagL k in
           Refl)

eqmodTrans : (x, y, z, m : Biz) -> eqmod x y m -> eqmod y z m -> eqmod x z m
eqmodTrans _ _ z m (k1 ** prf1) (k2 ** prf2) =
  (k1+k2 ** rewrite prf1 in
            rewrite prf2 in
            rewrite addAssoc (k1*m) (k2*m) z in
            rewrite sym $ mulAddDistrR k1 k2 m in
            Refl)

-- TODO add to Biz.Proofs

divModSmall : (x, y : Biz) -> 0 `Le` x -> x `Lt` y -> (x `bizDiv` y = 0, x `bizMod` y = x)
divModSmall x y zlex xlty = let (dprf, mprf) = divModPos x y 0 x zlex xlty Refl in
                            (sym dprf, sym mprf)

modPlus : (a, b, c : Biz) -> 0 `Lt` c -> (a + b * c) `bizMod` c = a `bizMod` c
modPlus a b c zltc =
  let (lom, him) = modPosBound a c zltc in
  sym $ snd $ divModPos (a + b * c) c (b + (a `bizDiv` c)) (a `bizMod` c) lom him $
  rewrite mulAddDistrR b (a `bizDiv` c) c in
  rewrite sym $ addAssoc (b*c) ((a `bizDiv` c)*c) (a `bizMod` c) in
  rewrite addComm a (b*c) in
  cong {f = bizPlus (b*c)} $ divEuclEq a c $
  -- proof of 0 `Lt` x -> Not (x=0)
  \cz => absurd $ replace cz zltc

eqmodSmallEq : (x, y, m : Biz) -> eqmod x y m -> 0 `Le` x -> x `Lt` m -> 0 `Le` y -> y `Lt` m -> x = y
eqmodSmallEq x y m (k ** prf) zlex xltm zley yltm =
  let dprf = fst $ divModPos x m k y zley yltm prf
      zdiv = fst $ divModSmall x m zlex xltm
      kz = trans dprf zdiv
  in
  replace kz prf

eqmodModEq : (x, y, m : Biz) -> 0 `Lt` m -> eqmod x y m -> x `bizMod` m = y `bizMod` m
eqmodModEq x y m zltm (k**prf) =
  rewrite prf in
  rewrite addComm (k*m) y in
  modPlus y k m zltm

eqmodMod : (x, m : Biz) -> Not (m=0) -> eqmod x (x `bizMod` m) m
eqmodMod x m mnz = (x `bizDiv` m ** divEuclEq x m mnz)

eqmodAdd : (a, b, c, d, m : Biz) -> eqmod a b m -> eqmod c d m -> eqmod (a + c) (b + d) m
eqmodAdd _ b _ d m (k1**prf1) (k2**prf2) =
  (k1+k2 ** rewrite prf1 in
            rewrite prf2 in
            rewrite addAssoc (k1*m+b) (k2*m) d in
            rewrite sym $ addAssoc (k1*m) b (k2*m) in
            rewrite addComm b (k2*m) in
            rewrite addAssoc (k1*m) (k2*m) b in
            rewrite sym $ mulAddDistrR k1 k2 m in
            rewrite sym $ addAssoc ((k1+k2)*m) b d in
            Refl)

eqmodNeg : (x, y, m : Biz) -> eqmod x y m -> eqmod (-x) (-y) m
eqmodNeg _ y m (k**prf) =
  (-k ** rewrite prf in
         rewrite oppAddDistr (k*m) y in
         rewrite sym $ mulOppL k m in
         Refl)

eqmodSub : (a, b, c, d, m : Biz) -> eqmod a b m -> eqmod c d m -> eqmod (a - c) (b - d) m
eqmodSub a b c d m eq1 eq2 = eqmodAdd a b (-c) (-d) m eq1 $ eqmodNeg c d m eq2

eqmodMult : (a, b, c, d, m : Biz) -> eqmod a b m -> eqmod c d m -> eqmod (a * c) (b * d) m
eqmodMult a b c d m (k1**prf1) (k2**prf2) =
  (k1*k2*m+k1*d+b*k2 ** rewrite prf1 in
                        rewrite prf2 in
                        rewrite mulAddDistrR (k1*m) b (k2*m+d) in
                        rewrite mulAddDistrL (k1*m) (k2*m) d in
                        rewrite mulAddDistrL b (k2*m) d in
                        rewrite mulAssoc (k1*m) k2 m in
                        rewrite sym $ mulAssoc k1 m k2 in
                        rewrite mulComm m k2 in
                        rewrite mulAssoc k1 k2 m in
                        rewrite sym $ mulAssoc k1 m d in
                        rewrite mulComm m d in
                        rewrite mulAssoc k1 d m in
                        rewrite sym $ mulAddDistrR (k1*k2*m) (k1*d) m in
                        rewrite mulAssoc b k2 m in
                        rewrite addAssoc ((k1*k2*m+k1*d)*m) ((b*k2)*m) (b*d) in
                        rewrite sym $ mulAddDistrR (k1*k2*m+k1*d) (b*k2) m in
                        Refl)

eqmodDivides : (n, m, x, y : Biz) -> eqmod x y n -> bizDivides m n -> eqmod x y m
eqmodDivides n m x y (k**prf1) (p**prf2) =
  (k*p ** rewrite sym $ mulAssoc k p m in
          rewrite sym prf2 in
          prf1)

eqm : (x, y : Biz) -> (n : Nat) -> Type
eqm x y = eqmod x y . modulus

-- Properties of the coercions between [Z] and [int]

eqmSamerepr : (x, y : Biz) -> (n : Nat) -> eqm x y n -> repr x n = repr y n
eqmSamerepr x y n em =
  mkintEq (zModModulus x n) (zModModulus y n) n
          (fst $ zModModulusRange' x n)
          (snd $ zModModulusRange' x n)
          (fst $ zModModulusRange' y n)
          (snd $ zModModulusRange' y n) $
  rewrite zModModulusEq x n in
  rewrite zModModulusEq y n in
  eqmodModEq x y (modulus n) Refl em

eqmUnsignedRepr : (z : Biz) -> (n : Nat) -> eqm z (unsigned (repr z n)) n
eqmUnsignedRepr z n =
  (z `bizDiv` modulus n ** rewrite zModModulusEq z n in
                           divEuclEq z (modulus n) uninhabited)

eqmUnsignedReprL : (a, b : Biz) -> (n : Nat) -> eqm a b n -> eqm (unsigned (repr a n)) b n
eqmUnsignedReprL a b n =
  eqmodTrans (unsigned (repr a n)) a b (modulus n) $
  eqmodSym a (unsigned (repr a n)) (modulus n) $
  eqmUnsignedRepr a n

eqmUnsignedReprR : (a, b : Biz) -> (n : Nat) -> eqm a b n -> eqm a (unsigned (repr b n)) n
eqmUnsignedReprR a b n ab =
  eqmodTrans a b (unsigned (repr b n)) (modulus n) ab $
  eqmUnsignedRepr b n

eqmSignedUnsigned : (x : BizMod2 n) -> eqm (signed x) (unsigned x) n
eqmSignedUnsigned {n} x with (unsigned x < halfModulus n)
  | False = (-1 ** addComm (unsigned x) (-(modulus n)))
  | True  = (0  ** Refl)

unsignedRange : (x : BizMod2 n) -> (0 `Le` unsigned x, unsigned x `Lt` modulus n)
unsignedRange (MkBizMod2 i lo hi) =
  (ltSuccRTo 0 i $
   rewrite sym $ addCompareMonoR 0 (i+1) (-1) in
   rewrite sym $ addAssoc i 1 (-1) in
   rewrite add0R i in
   lo, hi)

unsignedRange2 : (x : BizMod2 n) -> (0 `Le` unsigned x, unsigned x `Le` maxUnsigned n)
unsignedRange2 {n} x =
  let (lo, hi) = unsignedRange x in
  (lo, ltSuccRTo (unsigned x) (maxUnsigned n) $
       rewrite sym $ addAssoc (modulus n) (-1) 1 in
       hi)

-- TODO add to Biz.Proofs

ltPredRTo : (n, m : Biz) -> n `Lt` m -> n `Le` bizPred m
ltPredRTo n m nltm =
  ltSuccRTo n (bizPred m) $
  rewrite sym $ addAssoc m (-1) 1 in
  rewrite add0R m in
  nltm

ltPredRFro : (n, m : Biz) -> n `Le` bizPred m -> n `Lt` m
ltPredRFro n m nlepm =
     ltSuccRFro n (bizPred m) nlepm
  |> replace {P = \x => n `Lt` x} (sym $ addAssoc m (-1) 1)
  |> replace {P = \x => n `Lt` x} (add0R m)

leSuccLFro : (p, q : Biz) -> p `Lt` q -> bizSucc p `Le` q
leSuccLFro p q pltq =
  ltSuccRTo (bizSucc p) q $
  rewrite addCompareMonoR p q 1 in
  pltq

lebLeTo' : (n, m : Biz) -> m < n = False -> n `Le` m
lebLeTo' n m prf nm with (m `compare` n) proof mn
  | LT = absurd prf
  | EQ = absurd $ replace (gtLt n m nm) mn
  | GT = absurd $ replace (gtLt n m nm) mn

lebLeFro' : (n, m : Biz) -> n `Le` m -> m < n = False
lebLeFro' n m nlem with (m `compare` n) proof mn
  | LT = absurd $ nlem $ ltGt m n (sym mn)
  | EQ = Refl
  | GT = Refl

signedRange : (x : BizMod2 n) -> Not (n=0) -> (minSigned n `Le` signed x, signed x `Le` maxSigned n)
signedRange {n} x nz with (unsigned x < halfModulus n) proof hx
  | False = let hm = halfModulus n
                ux = unsigned x
                m2 = cong {f = bizOpp} $ halfModulusModulus n nz
            in
            rewrite m2 in
            ( rewrite sym $ addCompareMonoR (-hm) (ux-(2*hm)) (2*hm) in
              rewrite sym $ addAssoc ux (-(2*hm)) (2*hm) in
              rewrite addOppDiagL (2*hm) in
              rewrite add0R ux in
              rewrite oppEqMulM1 hm in
              rewrite mulComm hm (-1) in
              rewrite sym $ mulAddDistrR (-1) 2 hm in
              rewrite mul1L hm in
              lebLeTo' hm ux (sym hx)
            , rewrite sym $ addCompareMonoR (ux-(2*hm)) (hm-1) (2*hm) in
              rewrite sym $ addAssoc ux (-(2*hm)) (2*hm) in
              rewrite addOppDiagL (2*hm) in
              rewrite add0R ux in
              rewrite addComm (hm-1) (2*hm) in
              rewrite addComm hm (-1) in
              rewrite addAssoc (2*hm) (-1) hm in
              leTrans ux (2*hm-1) (2*hm-1+hm)
                (ltPredRTo ux (2*hm) $
                 rewrite sym $ halfModulusModulus n nz in
                 snd $ unsignedRange x)
                (rewrite sym $ addCompareMonoL (-(2*hm-1)) (2*hm-1) (2*hm-1+hm) in
                 rewrite addAssoc (-(2*hm-1)) (2*hm-1) hm in
                 rewrite addOppDiagL (2*hm-1) in
                 ltLeIncl 0 hm $
                 halfModulusPos n nz)
            )
  | True  = let hm = halfModulus n
                ux = unsigned x
            in
            ( leTrans (-hm) 0 ux
                (rewrite sym $ compareOpp 0 hm in
                 ltLeIncl 0 hm $
                 halfModulusPos n nz)
                (fst $ unsignedRange x)
            , ltPredRTo ux hm $
              ltbLtTo ux hm (sym hx)
            )

reprUnsigned : (x : BizMod2 n) -> repr (unsigned x) n = x
reprUnsigned {n} (MkBizMod2 i lo hi) =
  mkintEq (zModModulus i n) i n (fst $ zModModulusRange' i n) (snd $ zModModulusRange' i n) lo hi $
  rewrite zModModulusEq i n in
  snd $ divModSmall i (modulus n) (leSuccLFro (-1) i lo) hi

reprSigned : (x : BizMod2 n) -> repr (signed x) n = x
reprSigned {n} x =
  trans
    (eqmSamerepr (signed x) (unsigned x) n (eqmSignedUnsigned x))
    (reprUnsigned x)

eqmReprEq : (x : Biz) -> (y : BizMod2 n) -> eqm x (unsigned y) n -> repr x n = y
eqmReprEq {n} x y eqxuy = rewrite sym $ reprUnsigned y in
                          eqmSamerepr x (unsigned y) n eqxuy

unsignedRepr : (x : Biz) -> (n : Nat) -> 0 `Le` x -> x `Le` maxUnsigned n -> unsigned (repr x n) = x
unsignedRepr x n zlex xlemu =
  rewrite zModModulusEq x n in
  snd $ divModSmall x (modulus n) zlex (ltPredRFro x (modulus n) xlemu)

-- TODO add to Biz.Proofs ?

mulCompareMonoR : (p, q, r : Biz) -> 0 `Lt` p -> (q*p) `compare` (r*p) = q `compare` r
mulCompareMonoR p q r zltp =
  rewrite mulComm q p in
  rewrite mulComm r p in
  mulCompareMonoL p q r zltp

-- a workaround for the fact that using `rewrite sym $ mul1L` is not practical
mulAddDistrR1 : (n, m : Biz) -> (n + 1) * m = n * m + m
mulAddDistrR1 n m = rewrite mulAddDistrR n 1 m in
                    rewrite mul1L m in
                    Refl

-- convenience lemma, look for other places to use it
addCompareMonoTransferL : (a, b, c : Biz) -> a `compare` (b+c) = ((-b)+a) `compare` c
addCompareMonoTransferL a b c =
  rewrite sym $ addCompareMonoL (-b) a (b+c) in
  rewrite addAssoc (-b) b c in
  rewrite addOppDiagL b in
  Refl

signedRepr : (x : Biz) -> (n : Nat) -> Not (n=0) -> minSigned n `Le` x -> x `Le` maxSigned n -> signed (repr x n) = x
signedRepr    BizO     Z    nz _     _     = absurd $ nz Refl
signedRepr    BizO    (S _) _  _     _     = Refl
signedRepr x@(BizP _)  n    _  _     xlema =
  rewrite unsignedRepr x n uninhabited $
            ltLeIncl x (maxUnsigned n) $
            leLtTrans x (maxSigned n) (maxUnsigned n) xlema (maxSignedUnsigned n) in
  rewrite ltbLtFro x (halfModulus n) $
            ltPredRFro x (halfModulus n) xlema in
  Refl
signedRepr   (BizM a)  n    nz milex _     =
  -- prove that we can substitute `repr x n` with `repr (x+(modulus n)) n`
  let xm = cong {f=signed} $ eqmSamerepr (BizM a) ((BizM a)+(modulus n)) n $
           eqmodAdd (BizM a) (BizM a) 0 (modulus n) (modulus n) (eqmodRefl (BizM a) (modulus n)) $
           (-1 ** sym $ posSubDiag (twoPowerNat n))
      mhm = cong {f=bizOpp} $ halfModulusModulus n nz
  in
  rewrite xm in
  rewrite unsignedRepr ((BizM a)+(modulus n)) n
            (rewrite addCompareMonoTransferL 0 (modulus n) (BizM a) in
             leTrans (-(modulus n)) (-(halfModulus n)) (BizM a)
               (rewrite mhm in
                rewrite sym $ compareOpp (halfModulus n) (2*(halfModulus n)) in
                rewrite sym $ mul1L (halfModulus n) in
                rewrite mulAssoc 2 1 (halfModulus n) in
                rewrite mulCompareMonoR (halfModulus n) 1 2 (halfModulusPos n nz) in
                uninhabited)
               milex
            )
            (rewrite addCompareMonoL (modulus n) (BizM a) (-1) in
             le1L a)
  in
  rewrite lebLeFro' (halfModulus n) ((modulus n)+(BizM a)) $
            rewrite addCompareMonoTransferL (halfModulus n) (modulus n) (BizM a) in
            rewrite mhm in
            rewrite sym $ mulOppL 2 (halfModulus n) in
            rewrite sym $ mulAddDistrR1 (-2) (halfModulus n) in
            rewrite mulOppL 1 (halfModulus n) in
            rewrite mul1L (halfModulus n) in
            milex
  in
  rewrite addComm ((modulus n)+(BizM a)) (-(modulus n)) in
  rewrite addAssoc (-(modulus n)) (modulus n) (BizM a)  in
  rewrite posSubDiag (twoPowerNat n) in
  Refl

signedEqUnsigned : (x : BizMod2 n) -> unsigned x `Le` maxSigned n -> signed x = unsigned x
signedEqUnsigned {n} x uxlema with ((unsigned x) < (halfModulus n)) proof uxhm
  | False = let hmgtux = ltGt (unsigned x) (halfModulus n) $
                         ltPredRFro (unsigned x) (halfModulus n) uxlema
                hmleux = lebLeTo' (halfModulus n) (unsigned x) (sym uxhm)
            in
            absurd $ hmleux hmgtux
  | True = Refl

-- TODO split into `to` and `fro`

signedPositiveTo : (x : BizMod2 n) -> 0 `Le` signed x -> unsigned x `Le` maxSigned n
signedPositiveTo {n} x zles uxgtma with ((unsigned x) < (halfModulus n)) proof uxhm
  | False = let uxgem = zles
                     |> replace {P = \x => Not (x=GT)} (sym $ compareSubR (modulus n) (unsigned x))
                     |> leGe (modulus n) (unsigned x)
            in
            absurd $ uxgem $ snd (unsignedRange x)
  | True  = let hmleux = uxgtma
                      |> gtLt (unsigned x) ((halfModulus n)-1)
                      |> leSuccLFro ((halfModulus n)-1) (unsigned x)
                      |> replace {P = \y => y `Le` unsigned x} (sym $ addAssoc (halfModulus n) (-1) 1)
                      |> replace {P = \y => y `Le` unsigned x} (add0R (halfModulus n))
                hmgtux = ltGt (unsigned x) (halfModulus n) $ ltbLtTo (unsigned x) (halfModulus n) (sym uxhm)
            in
            absurd $ hmleux hmgtux

signedPositiveFro : (x : BizMod2 n) -> unsigned x `Le` maxSigned n -> 0 `Le` signed x
signedPositiveFro {n} x uxlema zgts with ((unsigned x) < (halfModulus n)) proof uxhm
  | False = let hmgtux = ltGt (unsigned x) (halfModulus n) $
                         ltPredRFro (unsigned x) (halfModulus n) uxlema
                hmleux = lebLeTo' (halfModulus n) (unsigned x) (sym uxhm)
            in
            absurd $ hmleux hmgtux
  | True = let zleux = fst $ unsignedRange x in
           absurd $ zleux zgts

-- Properties of zero, one, minus one

-- unsignedZero is trivial

unsignedOne : (n : Nat) -> Not (n=0) -> unsigned {n} 1 = 1
unsignedOne  Z    nz = absurd $ nz Refl
unsignedOne (S _) _  = Refl

unsignedMone : (n : Nat) -> unsigned {n} (-1) = modulus n - 1
unsignedMone  Z    = Refl
unsignedMone (S _) = Refl

signedZero : (n : Nat) -> Not (n=0) -> signed {n} 0 = 0
signedZero n nz = rewrite ltbLtFro 0 (halfModulus n) $ halfModulusPos n nz in
                  Refl

signedOne : (n : Nat) -> 1 `Lt` toBizNat n -> signed {n} 1 = 1
signedOne  Z        ultn = absurd ultn
signedOne (S  Z)    ultn = absurd ultn
signedOne (S (S _)) _    = Refl

signedMone : (n : Nat) -> signed {n} (-1) = -1
signedMone  Z    = Refl
signedMone (S k) =
  let dmo = bipDMO (twoPowerNat k) in
  rewrite lebLeFro' (BizP $ twoPowerNat k) (BizP dmo) (leDMO $ twoPowerNat k) in
  rewrite sym $ succPredDouble (twoPowerNat k) in
  rewrite posSubLt dmo (bipSucc dmo) (ltSuccDiagR dmo) in
  rewrite sym $ add1R dmo in
  rewrite subMaskAddDiagL dmo 1 in
  Refl

oneNotZero : (n : Nat) -> Not (n=0) -> Not (repr 1 n = repr 0 n)
oneNotZero  Z    nz = absurd $ nz Refl
oneNotZero (S _) _  = absurd . MkBizMod2Inj

unsignedReprWordsize : (n : Nat) -> unsigned (repr (toBizNat n) n) = toBizNat n
unsignedReprWordsize n =
  rewrite zModModulusEq (toBizNat n) n in
  snd $ divModSmall (toBizNat n) (modulus n) (toBizNatIsNonneg n) $
  ltPredRFro (toBizNat n) (modulus n) (wordsizeMaxUnsigned n)