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
    -- bizPred (BizP a) `Lt` (BizP a)
    (rewrite compareSub (BizP pk - 1) (BizP pk) in
     rewrite sym $ addAssoc (BizP pk) (-1) (BizM pk) in
     rewrite addComm 1 pk in
     rewrite addAssoc (BizP pk) (BizM pk) (-1) in
     rewrite posSubDiag pk in
     Refl)
    (leDMO pk)