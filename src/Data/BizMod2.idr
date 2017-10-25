module Data.BizMod2

import public Data.Bip
import public Data.Bip.AddMul
import public Data.Bip.IterPow
import public Data.Bip.OrdSub

import Data.Bin.Proofs

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

-- we use two `Lt` proofs here so we could prove mkintEq below
data BizMod2 : (n : Nat) -> Type where
  MkBizMod2 : (intVal : Biz) -> (range : (-1 `Lt` intVal, intVal `Lt` modulus n)) -> BizMod2 n

MkBizMod2Inj : MkBizMod2 x rx = MkBizMod2 y ry -> x = y
MkBizMod2Inj Refl = Refl

bizMod2P0 : (x : BizMod2 0) -> x = MkBizMod2 0 (Refl, Refl)
bizMod2P0 (MkBizMod2  BizO    (Refl, Refl)) = Refl
bizMod2P0 (MkBizMod2 (BizP a) (_   , altu)) = absurd $ le1L a $ ltGt a U altu
bizMod2P0 (MkBizMod2 (BizM a) (altu, _   )) = absurd $ le1L a $ ltGt a U altu

-- Fast normalization modulo [2^wordsize]

bipMod2 : (p : Bip) -> (n : Nat) -> Biz
bipMod2  _     Z    = 0
bipMod2  U    (S _) = 1
bipMod2 (O a) (S k) = bizD (a `bipMod2` k)
bipMod2 (I a) (S k) = bizDPO (a `bipMod2` k)

bizMod2 : (x : Biz) -> (n : Nat) -> Biz
bizMod2  BizO    _ = 0
bizMod2 (BizP a) n = a `bipMod2` n
bizMod2 (BizM a) n = let r = a `bipMod2` n in
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

bipMod2Range : (n : Nat) -> (p : Bip) -> (0 `Le` (p `bipMod2` n), (p `bipMod2` n) `Lt` modulus n)
bipMod2Range  Z     _    = (uninhabited, Refl)
bipMod2Range (S _)  U    = (uninhabited, Refl)
bipMod2Range (S k) (O a) =
  let (lo, hi) = bipMod2Range k a in
  ( rewrite bizDCompare 0 (a `bipMod2` k) in
    lo
  , rewrite bizDCompare (a `bipMod2` k) (modulus k) in
    hi
  )
bipMod2Range (S k) (I a) =
  let (lo, hi) = bipMod2Range k a in
  ( rewrite bizDDPOCompare 0 (a `bipMod2` k) in
    case leLtOrEq 0 (a `bipMod2` k) lo of
      Left lprf => rewrite lprf in
                   uninhabited
      Right rprf => rewrite sym rprf in
                    uninhabited
  , rewrite bizDPODCompare (a `bipMod2` k) (modulus k) in
    rewrite hi in
    Refl
  )

bipMod2Eq : (n : Nat) -> (p : Bip) -> p `bipMod2` n = BizP p `bizMod` modulus n
bipMod2Eq n p = let (y**prf) = aux n p
                    (zlemt, mtltmod) = bipMod2Range n p
                 in
                 snd $ divModPos (BizP p) (modulus n) y (p `bipMod2` n) zlemt mtltmod prf
  where
  aux : (n : Nat) -> (p : Bip) -> (y ** BizP p = y * modulus n + (p `bipMod2` n))
  aux  Z     p    = (BizP p ** cong $ sym $ mul1R p)
  aux (S _)  U    = (0 ** Refl)
  aux (S k) (O a) = let (y**prf) = aux k a in
                    (y ** rewrite doubleSpec (a `bipMod2` k) in
                          rewrite mulAssoc y 2 (modulus k) in
                          rewrite mulComm y 2 in
                          rewrite sym $ mulAssoc 2 y (modulus k) in
                          rewrite sym $ mulAddDistrL 2 (y*(modulus k)) (a `bipMod2` k) in
                          cong {f = bizMult 2} prf)
  aux (S k) (I a) = let (y**prf) = aux k a in
                    (y ** rewrite succDoubleSpec (a `bipMod2` k) in
                          rewrite mulAssoc y 2 (modulus k) in
                          rewrite mulComm y 2 in
                          rewrite sym $ mulAssoc 2 y (modulus k) in
                          rewrite addAssoc (2*(y*(modulus k))) (2*(a `bipMod2` k)) 1 in
                          rewrite sym $ mulAddDistrL 2 (y*(modulus k)) (a `bipMod2` k) in
                          cong {f = \x => 2*x+1} prf)

bizMod2Range0 : (x : Biz) -> (n : Nat) -> (0 `Le` (x `bizMod2` n), (x `bizMod2` n) `Lt` modulus n)
bizMod2Range0  BizO    _ = (uninhabited, Refl)
bizMod2Range0 (BizP a) n = bipMod2Range n a
bizMod2Range0 (BizM a) n with ((a `bipMod2` n) == 0) proof zprf
  | False =
    let (lo, hi) = bipMod2Range n a in
    ( rewrite compareAntisym ((modulus n)-(a `bipMod2` n)) 0 in
      rewrite sym $ compareSub (modulus n) (a `bipMod2` n) in
      rewrite compareAntisym (a `bipMod2` n) (modulus n) in
      rewrite hi in
      uninhabited
    , case leLtOrEq 0 (a `bipMod2` n) lo of
        Left lprf =>
          rewrite addCompareMonoL (modulus n) (-(a `bipMod2` n)) 0 in
          rewrite sym $ compareOpp 0 (a `bipMod2` n) in
          lprf
        Right rprf =>
          let pmodeq0 = eqbEqFro (a `bipMod2` n) 0 $ sym rprf in
          absurd $ replace pmodeq0 zprf
    )
  | True = (uninhabited, Refl)

bizMod2Range : (x : Biz) -> (n : Nat) -> (-1 `Lt` (x `bizMod2` n), (x `bizMod2` n) `Lt` modulus n)
bizMod2Range x n =
  let lohi = bizMod2Range0 x n
      lo = fst lohi
      hi = snd lohi
  in
  ( rewrite sym $ addCompareMonoR (-1) (x `bizMod2` n) 1 in
    ltSuccRFro 0 (x `bizMod2` n) lo
  , hi)

-- TODO add to Biz.Proofs, look where it can be inserted

compareSubR : (n, m : Biz) -> n `compare` m = 0 `compare` (m-n)
compareSubR n m =
  rewrite compareAntisym (m-n) 0 in
  rewrite sym $ compareSub m n in
  compareAntisym m n

bizMod2Eq : (x : Biz) -> (n : Nat) -> x `bizMod2` n = x `bizMod` (modulus n)
bizMod2Eq  BizO    _ = Refl
bizMod2Eq (BizP a) n = bipMod2Eq n a
bizMod2Eq (BizM a) n with (a `bipMod2` n) proof pz
  | BizO =
    let
      deq = divEuclEq (BizM a) (modulus n) uninhabited
      pmodz = sym $ trans pz (bipMod2Eq n a)
      divmod = divModPos (BizM a) (modulus n) ((BizM a) `bizDiv` (modulus n)) 0 uninhabited Refl $
               replace {P=\x => BizM a = (((BizM a) `bizDiv` (modulus n)) * (modulus n)) + (snd (bizDivEuclidHelp1 (fst (bipzDivEuclid a (modulus n))) x (modulus n)))} pmodz deq
    in
    snd divmod
  | BizP b =
    let
      deq = divEuclEq (BizM a) (modulus n) uninhabited
      bmodz = sym $ trans pz (bipMod2Eq n a)
      divmod = divModPos (BizM a) (modulus n) ((BizM a) `bizDiv` (modulus n)) (bipMinusBiz (twoPowerNat n) b)
             (rewrite sym $ compareSubR (BizP b) (modulus n) in
              ltLeIncl b (twoPowerNat n) $
              replace {P = \x => x `Lt` modulus n} (sym pz) (snd $ bipMod2Range n a)
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
  | BizM b =
    let
      zlep = fst $ bipMod2Range n a
      zleneg = replace {P = \x => 0 `Le` x} (sym pz) zlep
    in
    -- TODO bug: we arrive at `zleneg:(GT=GT)->Void` but the following results in
    -- `zleneg does not have a function type ((\x => ([__])) (BizM b))`
    --absurd $ zleneg Refl
    really_believe_me zleneg

-- The [unsigned] and [signed] functions return a Biz corresponding to the given
-- machine integer, interpreted as unsigned or signed respectively.

unsigned : BizMod2 n -> Biz
unsigned (MkBizMod2 intVal _) = intVal

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
-- trivial case so that `repr` doesn't auto-normalize, allowing to use syntactic
-- rewrites, eg `addComm`
repr _    Z    = MkBizMod2 0 (Refl, Refl)
repr x n@(S _) = MkBizMod2 (x `bizMod2` n) (bizMod2Range x n)

mkintEq : (x, y : Biz) -> (n : Nat)
       -> (rx : (-1 `Lt` x, x `Lt` modulus n))
       -> (ry : (-1 `Lt` y, y `Lt` modulus n))
       -> x = y
       -> MkBizMod2 x rx = MkBizMod2 y ry
mkintEq y y n (lox, hix) (loy, hiy) Refl =
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
  decEq (MkBizMod2 x rx) (MkBizMod2 y ry) = case decEq x y of
    Yes prf => Yes (mkintEq x y n rx ry prf)
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

swapComparison : Comparison -> Comparison
swapComparison Ceq = Ceq
swapComparison Cne = Cne
swapComparison Clt = Cgt
swapComparison Cle = Cge
swapComparison Cgt = Clt
swapComparison Cge = Cle

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
    else let qr = bizDivEuclid ((unsigned nhi) * (modulus n) + (unsigned nlo)) (unsigned d)
             q = fst qr
             r = snd qr in
         if q <= maxUnsigned n then Just (repr q n, repr r n) else Nothing

divmods2 : (nhi, nlo, d : BizMod2 n) -> Maybe (BizMod2 n, BizMod2 n)
divmods2 {n} nhi nlo d =
  if d==0 then Nothing
    else let qr = bizQuotRem ((signed nhi) * (modulus n) + (unsigned nlo)) (signed d)
             q = fst qr
             r = snd qr in
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

-- TODO add to Biz.Proofs

divMod1 : (x : Biz) -> (x `bizDiv` 1 = x, x `bizMod` 1 = 0)
divMod1 x = let (dprf, mprf) = divModPos x 1 x 0 uninhabited Refl $
                                 rewrite mul1R x in
                                 sym $ add0R x
            in (sym dprf, sym mprf)

unsignedReprEq : (x : Biz) -> (n : Nat) -> unsigned (repr x n) = x `bizMod` modulus n
unsignedReprEq x  Z    = sym $ snd $ divMod1 x
unsignedReprEq x (S k) = bizMod2Eq x (S k)

signedReprEq : (x : Biz) -> (n : Nat) -> let m = modulus n
                                             xm = x `bizMod` m
                                        in signed (repr x n) = if xm < halfModulus n then xm else xm - m
signedReprEq x n = rewrite unsignedReprEq x n in
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

ltNotEq : (x, y : Biz) -> y `Lt` x -> Not (x=y)
ltNotEq x y yltx xy =
  absurd $ replace {P=\z=>z=LT} (compareEqIffFro y x (sym xy)) yltx

modPlus : (a, b, c : Biz) -> 0 `Lt` c -> (a + b * c) `bizMod` c = a `bizMod` c
modPlus a b c zltc =
  let (lom, him) = modPosBound a c zltc in
  sym $ snd $ divModPos (a + b * c) c (b + (a `bizDiv` c)) (a `bizMod` c) lom him $
  rewrite mulAddDistrR b (a `bizDiv` c) c in
  rewrite sym $ addAssoc (b*c) ((a `bizDiv` c)*c) (a `bizMod` c) in
  rewrite addComm a (b*c) in
  cong {f = bizPlus (b*c)} $ divEuclEq a c $ ltNotEq c 0 zltc

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
eqmSamerepr _ _    Z    _  = Refl
eqmSamerepr x y n@(S _) em =
  mkintEq (x `bizMod2` n) (y `bizMod2` n) n
          (bizMod2Range x n) (bizMod2Range y n) $
  rewrite bizMod2Eq x n in
  rewrite bizMod2Eq y n in
  eqmodModEq x y (modulus n) Refl em

eqmUnsignedRepr : (x : Biz) -> (n : Nat) -> eqm x (unsigned (repr x n)) n
eqmUnsignedRepr x    Z    = (x ** rewrite mul1R x in
                                  sym $ add0R x)
eqmUnsignedRepr x n@(S _) =
  (x `bizDiv` modulus n ** rewrite bizMod2Eq x n in
                           divEuclEq x (modulus n) uninhabited)

eqmUnsignedRepr' : (x : Biz) -> (n : Nat) -> eqm (unsigned (repr x n)) x n
eqmUnsignedRepr' x n = eqmodSym x (unsigned $ repr x n) (modulus n) $ eqmUnsignedRepr x n

eqmUnsignedReprL : (a, b : Biz) -> (n : Nat) -> eqm a b n -> eqm (unsigned $ repr a n) b n
eqmUnsignedReprL a b n =
  eqmodTrans (unsigned $ repr a n) a b (modulus n) $
  eqmUnsignedRepr' a n

eqmUnsignedReprR : (a, b : Biz) -> (n : Nat) -> eqm a b n -> eqm a (unsigned $ repr b n) n
eqmUnsignedReprR a b n ab =
  eqmodTrans a b (unsigned $ repr b n) (modulus n) ab $
  eqmUnsignedRepr b n

eqmSignedUnsigned : (x : BizMod2 n) -> eqm (signed x) (unsigned x) n
eqmSignedUnsigned {n} x with (unsigned x < halfModulus n)
  | False = (-1 ** addComm (unsigned x) (-(modulus n)))
  | True  = (0  ** Refl)

eqmUnsignedSigned : (x : BizMod2 n) -> eqm (unsigned x) (signed x) n
eqmUnsignedSigned {n} x = eqmodSym (signed x) (unsigned x) (modulus n) (eqmSignedUnsigned x)

unsignedRange : (x : BizMod2 n) -> (0 `Le` unsigned x, unsigned x `Lt` modulus n)
unsignedRange (MkBizMod2 i r) =
  (ltSuccRTo 0 i $
   rewrite sym $ addCompareMonoR 0 (i+1) (-1) in
   rewrite sym $ addAssoc i 1 (-1) in
   rewrite add0R i in
   fst r, snd r)

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

nltbLeTo : (n, m : Biz) -> m < n = False -> n `Le` m
nltbLeTo n m prf nm with (m `compare` n) proof mn
  | LT = absurd prf
  | EQ = absurd $ replace (gtLt n m nm) mn
  | GT = absurd $ replace (gtLt n m nm) mn

nltbLeFro : (n, m : Biz) -> n `Le` m -> m < n = False
nltbLeFro n m nlem with (m `compare` n) proof mn
  | LT = absurd $ nlem $ ltGt m n (sym mn)
  | EQ = Refl
  | GT = Refl

lebLeFro : (n, m : Biz) -> n `Le` m -> n <= m = True
lebLeFro n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = eqbEqFro n m $ compareEqIffTo n m (sym nm)
  | GT = absurd $ nlem Refl

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
              nltbLeTo hm ux (sym hx)
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
reprUnsigned {n=Z}    x              = sym $ bizMod2P0 x
reprUnsigned {n=S n} (MkBizMod2 i r) =
  mkintEq (i `bizMod2` (S n)) i (S n) (bizMod2Range i (S n)) r $
  rewrite bizMod2Eq i (S n) in
  snd $ divModSmall i (modulus (S n)) (leSuccLFro (-1) i (fst r)) (snd r)

unsignedInj : (x, y : BizMod2 n) -> unsigned x = unsigned y -> x = y
unsignedInj x y prf =
  rewrite sym $ reprUnsigned x in
  rewrite sym $ reprUnsigned y in
  cong {f = \z => repr z n} prf

reprSigned : (x : BizMod2 n) -> repr (signed x) n = x
reprSigned {n} x =
  trans
    (eqmSamerepr (signed x) (unsigned x) n (eqmSignedUnsigned x))
    (reprUnsigned x)

eqmReprEq : (x : Biz) -> (y : BizMod2 n) -> eqm x (unsigned y) n -> repr x n = y
eqmReprEq {n} x y eqxuy = rewrite sym $ reprUnsigned y in
                          eqmSamerepr x (unsigned y) n eqxuy

unsignedRepr : (x : Biz) -> (n : Nat) -> 0 `Le` x -> x `Le` maxUnsigned n -> unsigned (repr x n) = x
unsignedRepr  BizO       Z    _    _     = Refl
unsignedRepr (BizP _)    Z    _    xlemu = absurd $ xlemu Refl
unsignedRepr (BizM _)    Z    zlex _     = absurd $ zlex Refl
unsignedRepr  x       n@(S _) zlex xlemu =
  rewrite bizMod2Eq x n in
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
addCompareTransferL : (a, b, c : Biz) -> a `compare` (b+c) = ((-b)+a) `compare` c
addCompareTransferL a b c =
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
            (rewrite addCompareTransferL 0 (modulus n) (BizM a) in
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
  rewrite nltbLeFro (halfModulus n) ((modulus n)+(BizM a)) $
            rewrite addCompareTransferL (halfModulus n) (modulus n) (BizM a) in
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
                hmleux = nltbLeTo (halfModulus n) (unsigned x) (sym uxhm)
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
                hmleux = nltbLeTo (halfModulus n) (unsigned x) (sym uxhm)
            in
            absurd $ hmleux hmgtux
  | True = let zleux = fst $ unsignedRange x in
           absurd $ zleux zgts

-- Properties of zero, one, minus one

unsignedZero : (n : Nat) -> unsigned {n} 0 = 0
unsignedZero  Z    = Refl
unsignedZero (S _) = Refl

unsignedOne : (n : Nat) -> Not (n=0) -> unsigned {n} 1 = 1
unsignedOne  Z    nz = absurd $ nz Refl
unsignedOne (S _) _  = Refl

unsignedMone : (n : Nat) -> unsigned {n} (-1) = modulus n - 1
unsignedMone  Z    = Refl
unsignedMone (S _) = Refl

signedZero : (n : Nat) -> Not (n=0) -> signed {n} 0 = 0
signedZero  Z    nz = absurd $ nz Refl
signedZero (S _) _  = Refl

signedOne : (n : Nat) -> 1 `Lt` toBizNat n -> signed {n} 1 = 1
signedOne  Z        ultn = absurd ultn
signedOne (S  Z)    ultn = absurd ultn
signedOne (S (S _)) _    = Refl

signedMone : (n : Nat) -> signed {n} (-1) = -1
signedMone  Z    = Refl
signedMone (S k) =
  let dmo = bipDMO (twoPowerNat k) in
  rewrite nltbLeFro (BizP $ twoPowerNat k) (BizP dmo) (leDMO $ twoPowerNat k) in
  rewrite sym $ succPredDouble (twoPowerNat k) in
  rewrite posSubLt dmo (bipSucc dmo) (ltSuccDiagR dmo) in
  rewrite sym $ add1R dmo in
  rewrite subMaskAddDiagL dmo 1 in
  Refl

oneNotZero : (n : Nat) -> Not (n=0) -> Not (repr 1 n = repr 0 n)
oneNotZero  Z    nz = absurd $ nz Refl
oneNotZero (S _) _  = absurd . MkBizMod2Inj

unsignedReprWordsize : (n : Nat) -> unsigned (repr (toBizNat n) n) = toBizNat n
unsignedReprWordsize n = unsignedRepr (toBizNat n) n (toBizNatIsNonneg n) (wordsizeMaxUnsigned n)

-- TODO add to Biz.Proofs

neqbNeqTo : (n, m : Biz) -> n == m = False -> Not (n = m)
neqbNeqTo n m neq nm =
  absurd $ replace {P = \x => x = False} (eqbEqFro n m nm) neq

neqbNeqFro : (n, m : Biz) -> Not (n = m) -> n == m = False
neqbNeqFro n m neq with (n == m) proof nm
  | False = Refl
  | True  = absurd $ neq $ eqbEqTo n m $ sym nm

-- Properties of equality

eqSym : (x, y: BizMod2 n) -> x == y = y == x
eqSym x y with ((unsigned x) == (unsigned y)) proof uxy
  | False = sym $ neqbNeqFro (unsigned y) (unsigned x) $
            neqbNeqTo (unsigned x) (unsigned y) (sym uxy) . sym
  | True  = sym $ eqbEqFro (unsigned y) (unsigned x) $
            sym $ eqbEqTo (unsigned x) (unsigned y) $
            sym uxy

eqSpec : (x, y : BizMod2 n) -> if x == y then x = y else Not (x = y)
eqSpec {n} (MkBizMod2 x rx) (MkBizMod2 y ry) =
  case decEq (MkBizMod2 x rx) (MkBizMod2 y ry) of
    Yes prf => rewrite eqbEqFro x y (MkBizMod2Inj prf) in
               prf
    No contra => let xneqy = contra . mkintEq x y n rx ry in
                 rewrite neqbNeqFro x y xneqy in
                 contra

eqTrue : (x : BizMod2 n) -> x == x = True
eqTrue x with (x==x) proof xx
  | True  = Refl
  | False = let contra = replace {P = \z => if z then x = x else Not (x = x)} (sym xx) (eqSpec x x) in
            absurd $ contra Refl

eqFalse : (x, y : BizMod2 n) -> Not (x=y) -> x == y = False
eqFalse x y neq with (x==y) proof xeqby
  | True  = let xy = replace {P = \z => if z then x = y else Not (x = y)} (sym xeqby) (eqSpec x y) in
            absurd $ neq xy
  | False = Refl

eqSigned : (x, y : BizMod2 n) -> x == y = (signed x) == (signed y)
eqSigned {n=Z} x y =
  rewrite bizMod2P0 x in
  rewrite bizMod2P0 y in
  Refl
eqSigned {n=S n} x y with ((signed x) == (signed y)) proof sxy
  | False = neqbNeqFro (unsigned x) (unsigned y) $
            neqbNeqTo (signed x) (signed y) (sym sxy) . cong {f = signed} . unsignedInj x y
  | True = rewrite sym $ reprSigned x in
           rewrite sym $ reprSigned y in
           rewrite eqbEqTo (signed x) (signed y) (sym sxy) in
           eqbEqFro ((signed y) `bizMod2` (S n)) ((signed y) `bizMod2` (S n)) Refl

-- Properties of addition

-- addUnsigned is trivial

addSigned : (x, y : BizMod2 n) -> x + y = repr (signed x + signed y) n
addSigned {n} x y =
  eqmSamerepr (unsigned x + unsigned y) (signed x + signed y) n $
  eqmodAdd (unsigned x) (signed x) (unsigned y) (signed y) (modulus n)
    (eqmUnsignedSigned x)
    (eqmUnsignedSigned y)

addComm : (x, y : BizMod2 n) -> x + y = y + x
addComm x y = rewrite addComm (unsigned x) (unsigned y) in
              Refl

add0R : (x : BizMod2 n) -> x + 0 = x
add0R {n} x = rewrite unsignedZero n in
              rewrite add0R (unsigned x) in
              reprUnsigned x

add0L : (x : BizMod2 n) -> 0 + x = x
add0L x = rewrite addComm 0 x in
          add0R x

eqmUnsignedAdd : (x, y : BizMod2 n) -> eqm (unsigned x + unsigned y) (unsigned (x + y)) n
eqmUnsignedAdd {n=Z}   x y =
  rewrite bizMod2P0 x in
  rewrite bizMod2P0 y in
  (0 ** Refl)
eqmUnsignedAdd {n=S n} x y =
  rewrite bizMod2Eq (unsigned x + unsigned y) (S n) in
  eqmodMod (unsigned x + unsigned y) (modulus (S n)) uninhabited

addAssoc : (x, y, z : BizMod2 n) -> x + (y + z) = x + y + z
addAssoc {n} x y z =
  eqmSamerepr ((unsigned x) + unsigned (y + z)) (unsigned (x + y) + unsigned z) n $
  eqmodTrans ((unsigned x) + unsigned (y + z)) (unsigned x + unsigned y + unsigned z) (unsigned (x + y) + unsigned z) (modulus n)
    (rewrite sym $ addAssoc (unsigned x) (unsigned y) (unsigned z) in
     eqmodAdd (unsigned x) (unsigned x) (unsigned (y + z)) (unsigned y + unsigned z) (modulus n)
       (eqmodRefl (unsigned x) (modulus n))
       (eqmodSym (unsigned y + unsigned z) (unsigned (y + z)) (modulus n) $
        eqmUnsignedAdd y z)
    )
    (eqmodAdd (unsigned x + unsigned y) (unsigned (x+y)) (unsigned z) (unsigned z) (modulus n)
       (eqmUnsignedAdd x y)
       (eqmodRefl (unsigned z) (modulus n))
    )

addPermut : (x, y, z : BizMod2 n) -> x + (y + z) = y + (x + z)
addPermut x y z =
  rewrite addComm y z in
  rewrite addAssoc x z y in
  addComm (x + z) y

addNegZero : (x : BizMod2 n) -> x+(-x) = 0
addNegZero {n} x =
  eqmSamerepr (unsigned x + (unsigned $ repr (-unsigned x) n)) 0 n $
  rewrite unsignedReprEq (-unsigned x) n in
  rewrite sym $ addOppDiagR (unsigned x) in
  eqmodAdd (unsigned x) (unsigned x) (-unsigned x `bizMod` modulus n) (-unsigned x) (modulus n)
    (eqmodRefl (unsigned x) (modulus n))
    (eqmodSym (-unsigned x) (-unsigned x `bizMod` modulus n) (modulus n) $
     eqmodMod (-unsigned x) (modulus n) uninhabited)

-- TODO add to Biz.Proofs

leRefl : (x : Biz) -> x `Le` x
leRefl x = rewrite compareEqIffFro x x Refl in
           uninhabited

addLtMono : (p, q, r, s : Biz) -> p `Lt` q -> r `Lt` s -> (p+r) `Lt` (q+s)
addLtMono p q r s pltq rlts =
  let prqr = replace {P = \x => x=LT} (sym $ addCompareMonoR p q r) pltq
      qrqs = replace {P = \x => x=LT} (sym $ addCompareMonoL q r s) rlts in
  ltTrans (p+r) (q+r) (q+s) prqr qrqs

addLeMono : (p, q, r, s : Biz) -> p `Le` q -> r `Le` s -> (p+r) `Le` (q+s)
addLeMono p q r s pleq rles =
  let prqr = replace {P = \x => Not (x=GT)} (sym $ addCompareMonoR p q r) pleq
      qrqs = replace {P = \x => Not (x=GT)} (sym $ addCompareMonoL q r s) rles in
  leTrans (p+r) (q+r) (q+s) prqr qrqs

addLtLeMono : (p, q, r, s : Biz) -> p `Lt` q -> r `Le` s -> (p+r) `Lt` (q+s)
addLtLeMono p q r s pltq rles =
  let prqr = replace {P = \x => x=LT} (sym $ addCompareMonoR p q r) pltq
      qrqs = replace {P = \x => Not (x=GT)} (sym $ addCompareMonoL q r s) rles in
  ltLeTrans (p+r) (q+r) (q+s) prqr qrqs

addLeLtMono : (p, q, r, s : Biz) -> p `Le` q -> r `Lt` s -> (p+r) `Lt` (q+s)
addLeLtMono p q r s pleq rlts =
  let prqr = replace {P = \x => Not (x=GT)} (sym $ addCompareMonoR p q r) pleq
      qrqs = replace {P = \x => x=LT} (sym $ addCompareMonoL q r s) rlts in
  leLtTrans (p+r) (q+r) (q+s) prqr qrqs

unsignedAddCarry : (x, y : BizMod2 n) -> unsigned (x + y) = unsigned x + unsigned y - unsigned (addCarry x y 0) * (modulus n)
unsignedAddCarry {n} x y =
  rewrite unsignedZero n in
  rewrite add0R (unsigned x + unsigned y) in
  rewrite unsignedReprEq (unsigned x + unsigned y) n in
  aux n x y
  where
  aux : (n : Nat) -> (x, y : BizMod2 n) -> (unsigned x + unsigned y) `bizMod` (modulus n) = unsigned x + unsigned y - (unsigned $ if unsigned x + unsigned y < modulus n then (repr 0 n) else (repr 1 n)) * (modulus n)
  aux  Z    x y =
    -- TODO after 2 `bizMod2P0`s this becomes `0 mod 1 = 0` but there's apparently a bug preventing those rewrites
    -- TODO try `decEq n 0` instread of splitting
    -- rewrite bizMod2P0 x in
    -- rewrite bizMod2P0 y in
    really_believe_me Z
  aux (S n) x y with ((unsigned x + unsigned y) < (modulus (S n))) proof xym
    | False = sym $ snd $ divModPos (unsigned x + unsigned y) (modulus (S n)) 1 (unsigned x + unsigned y - modulus (S n))
                (rewrite sym $ compareSubR (modulus (S n)) (unsigned x + unsigned y) in
                 nltbLeTo (modulus (S n)) (unsigned x + unsigned y) (sym xym))
                (rewrite addComm (unsigned x + unsigned y) (-modulus (S n)) in
                 rewrite sym $ addCompareTransferL (unsigned x + unsigned y) (modulus (S n)) (modulus (S n)) in
                 addLtMono (unsigned x) (modulus (S n)) (unsigned y)  (modulus (S n)) (snd $ unsignedRange x) (snd $ unsignedRange y))
                (rewrite addComm (unsigned x + unsigned y) (-modulus (S n)) in
                 rewrite addAssoc (modulus (S n)) (-modulus (S n)) (unsigned x + unsigned y) in
                 rewrite posSubDiag (twoPowerNat n) in
                 Refl)
    | True = rewrite add0R (unsigned x + unsigned y) in
             snd $ divModSmall (unsigned x + unsigned y) (modulus (S n))
               (addLeMono 0 (unsigned x) 0 (unsigned y) (fst $ unsignedRange x) (fst $ unsignedRange y))
               (ltbLtTo (unsigned x + unsigned y) (modulus (S n)) (sym xym))

unsignedAddEither : (x, y : BizMod2 n) -> Either (unsigned (x + y) = unsigned x + unsigned y)
                                                 (unsigned (x + y) = unsigned x + unsigned y - modulus n)
unsignedAddEither {n} x y =
  rewrite unsignedAddCarry x y in
  rewrite unsignedZero n in
  rewrite add0R (unsigned x + unsigned y) in
  aux n x y
  where
  aux : (n : Nat) -> (x, y : BizMod2 n) -> let m = (unsigned $ if unsigned x + unsigned y < modulus n then repr 0 n else repr 1 n)*(modulus n) in
                                           Either (unsigned x + unsigned y - m = unsigned x + unsigned y)
                                                  (unsigned x + unsigned y - m = unsigned x + unsigned y - modulus n)
  aux  Z    x y =
    -- TODO same bug as above
    -- rewrite bizMod2P0 x in
    -- rewrite bizMod2P0 y in
      really_believe_me Z
  aux (S n) x y with ((unsigned x + unsigned y) < (modulus (S n)))
    | False = Right Refl
    | True  = rewrite add0R (unsigned x + unsigned y) in
              Left Refl

-- Properties of negation

negRepr : (z : Biz) -> (n : Nat) -> -(repr z n) = repr (-z) n
negRepr z n =
  sym $
  eqmSamerepr (-z) (-(unsigned $ repr z n)) n $
  eqmodNeg z (unsigned $ repr z n) (modulus n) $
  eqmUnsignedRepr z n

negZero : (n : Nat) -> -repr 0 n = repr 0 n
negZero n = rewrite unsignedZero n in
            Refl

negInvolutive : (x : BizMod2 n) -> -(-x) = x
negInvolutive {n} x =
  eqmReprEq (-(unsigned $ repr (-unsigned x) n)) x $
  eqmodTrans (-(unsigned $ repr (-unsigned x) n)) (-(-unsigned x)) (unsigned x) (modulus n)
    (eqmodNeg (unsigned $ repr (-unsigned x) n) (-unsigned x) (modulus n) $
     eqmUnsignedReprL (-unsigned x) (-unsigned x) n $
     eqmodRefl (-unsigned x) (modulus n))
    (eqmodRefl2 (-(-unsigned x)) (unsigned x) (modulus n) $
     oppInvolutive (unsigned x))

negAddDistr : (x, y : BizMod2 n) -> -(x + y) = (-x) + (-y)
negAddDistr x y =
  eqmSamerepr (-(unsigned $ repr (unsigned x + unsigned y) n)) ((unsigned $ repr (-unsigned x) n)+(unsigned $ repr (-unsigned y) n)) n $
  eqmodTrans (-(unsigned $ repr (unsigned x + unsigned y) n)) (-(unsigned x + unsigned y)) ((unsigned $ repr (-unsigned x) n)+(unsigned $ repr (-unsigned y) n)) (modulus n)
    (eqmodNeg (unsigned $ repr (unsigned x + unsigned y) n) (unsigned x + unsigned y) (modulus n) $
     eqmUnsignedRepr' (unsigned x + unsigned y) n)
    (rewrite oppAddDistr (unsigned x) (unsigned y) in
     eqmodAdd (-unsigned x) (unsigned $ repr (-unsigned x) n) (-unsigned y) (unsigned $ repr (-unsigned y) n) (modulus n)
       (eqmUnsignedRepr (-unsigned x) n)
       (eqmUnsignedRepr (-unsigned y) n))

-- Properties of subtraction

sub0L : (x : BizMod2 n) -> x - 0 = x
sub0L {n} x =
  rewrite unsignedZero n in
  rewrite add0R (unsigned x) in
  reprUnsigned x

sub0R : (x : BizMod2 n) -> 0 - x = -x
sub0R {n} x =
  rewrite unsignedZero n in
  Refl

subAddNeg : (x, y : BizMod2 n) -> x - y = x + (-y)
subAddNeg {n} x y =
  eqmSamerepr (unsigned x - unsigned y) ((unsigned x)+(unsigned $ repr (-(unsigned y)) n)) n $
  eqmodAdd (unsigned x) (unsigned x) (-(unsigned y)) (unsigned $ repr (-(unsigned y)) n) (modulus n)
    (eqmodRefl (unsigned x) (modulus n))
    (eqmUnsignedRepr (-(unsigned y)) n)

subIdem : (x : BizMod2 n) -> x - x = 0
subIdem x =
  rewrite addOppDiagR (unsigned x) in
  Refl

subAddL : (x, y, z : BizMod2 n) -> (x + y) - z = (x - z) + y
subAddL x y z =
  rewrite subAddNeg (x+y) z in
  rewrite subAddNeg x z in
  rewrite sym $ addAssoc x y (-z) in
  rewrite sym $ addAssoc x (-z) y in
  rewrite addComm y (-z) in
  Refl

subAddR : (x, y, z : BizMod2 n) -> x - (y + z) = (x - z) + (-y)
subAddR x y z =
  rewrite subAddNeg x (y+z) in
  rewrite subAddNeg x z in
  rewrite negAddDistr y z in
  rewrite addComm (-y) (-z) in
  addAssoc x (-z) (-y)

subShifted : (x, y, z : BizMod2 n) -> (x + z) - (y + z) = x - y
subShifted x y z =
  rewrite subAddNeg (x+z) (y+z) in
  rewrite negAddDistr y z in
  rewrite addComm (-y) (-z) in
  rewrite sym $ addAssoc x z ((-z)+(-y)) in
  rewrite addAssoc z (-z) (-y) in
  rewrite addNegZero z in
  rewrite add0L (-y) in
  rewrite subAddNeg x y in
  Refl

subSigned : (x, y : BizMod2 n) -> x - y = repr (signed x - signed y) n
subSigned {n} x y =
  eqmSamerepr (unsigned x - unsigned y) (signed x - signed y) n $
  eqmodSub (unsigned x) (signed x) (unsigned y) (signed y) (modulus n)
    (eqmUnsignedSigned x) (eqmUnsignedSigned y)

unsignedSubBorrow : (x, y : BizMod2 n) -> unsigned (x - y) = unsigned x - unsigned y + (unsigned $ subBorrow x y 0) * (modulus n)
unsignedSubBorrow {n} x y =
  rewrite unsignedZero n in
  rewrite add0R (unsigned x - unsigned y) in
  rewrite unsignedReprEq (unsigned x - unsigned y) n in
  aux n x y
  where
  aux : (n : Nat) -> (x, y : BizMod2 n)
     -> (unsigned x - unsigned y) `bizMod` (modulus n) = unsigned x - unsigned y + (unsigned $ if unsigned x - unsigned y < 0 then repr 1 n else repr 0 n) * (modulus n)
  aux  Z    x y =
    -- TODO same bug as in `unsignedAddCarry`
    -- rewrite bizMod2P0 x in
    -- rewrite bizMod2P0 y in
      really_believe_me Z
  aux (S n) x y with (unsigned x - unsigned y < 0) proof xy
    | False = rewrite add0R (unsigned x - unsigned y) in
              snd $ divModSmall (unsigned x - unsigned y) (modulus (S n))
                (nltbLeTo 0 (unsigned x - unsigned y) (sym xy))
                (addLtLeMono (unsigned x) (modulus (S n)) (-(unsigned y)) 0
                            (snd $ unsignedRange x)
                            (rewrite sym $ compareOpp 0 (unsigned y) in
                             fst $ unsignedRange y))
    | True = sym $ snd $ divModPos (unsigned x - unsigned y) (modulus (S n)) (-1) (unsigned x - unsigned y + modulus (S n))
                (rewrite addComm (unsigned x - unsigned y) (modulus (S n)) in
                 rewrite addCompareTransferL 0 (modulus (S n)) (unsigned x - unsigned y) in
                 ltLeIncl (-(modulus (S n))) (unsigned x - unsigned y) $
                 addLeLtMono 0 (unsigned x) (-(modulus (S n))) (-(unsigned y))
                   (fst $ unsignedRange x)
                   (rewrite sym $ compareOpp (unsigned y) (modulus (S n)) in
                    snd $ unsignedRange y))
                (rewrite addCompareMonoR (unsigned x - unsigned y) 0 (modulus (S n)) in
                 ltbLtTo (unsigned x - unsigned y) 0 (sym xy))
                (rewrite addComm (unsigned x - unsigned y) (modulus (S n)) in
                 rewrite addAssoc (-(modulus (S n))) (modulus (S n)) (unsigned x - unsigned y) in
                 rewrite addOppDiagL (modulus (S n)) in
                 Refl)

addTransferL : (x, y, z : BizMod2 n) -> x = y+z -> z = x-y
addTransferL x y z prf =
  rewrite prf in
  rewrite subAddL y z y in
  rewrite subIdem y in
  sym $ add0L z

-- Properties of multiplication

mulComm : (x, y : BizMod2 n) -> x * y = y * x
mulComm x y = rewrite mulComm (unsigned x) (unsigned y) in
              Refl

mul0R : (x : BizMod2 n) -> x * 0 = 0
mul0R {n} x = rewrite unsignedZero n in
              rewrite mul0R (unsigned x) in
              Refl

mul1R : (x : BizMod2 n) -> x * 1 = x
mul1R {n = Z}   x = sym $ bizMod2P0 x
mul1R {n = S _} x = rewrite mul1R (unsigned x) in
                    reprUnsigned x

mulM1R : (x : BizMod2 n) -> x * (-1) = -x
mulM1R {n} x =
  rewrite unsignedMone n in
  eqmSamerepr ((unsigned x)*((modulus n)-1)) (-unsigned x) n $
  rewrite mulAddDistrL (unsigned x) (modulus n) (-1) in
  rewrite sym $ oppEqMulM1 (unsigned x) in
  eqmodSub ((unsigned x)*(modulus n)) 0 (unsigned x) (unsigned x) (modulus n)
    (unsigned x ** sym $ add0R ((unsigned x)*(modulus n)))
    (eqmodRefl (unsigned x) (modulus n))

mulAssoc : (x, y, z : BizMod2 n) -> x * (y * z) = x * y * z
mulAssoc {n} x y z =
  let ux = unsigned x
      uy = unsigned y
      uz = unsigned z in
  eqmSamerepr (ux*(unsigned $ repr (uy*uz) n)) ((unsigned $ repr (ux*uy) n)*uz) n $
  eqmodTrans (ux*(unsigned $ repr (uy*uz) n)) (ux*(uy*uz)) ((unsigned $ repr (ux*uy) n)*uz) (modulus n)
    (eqmodMult ux ux (unsigned $ repr (uy*uz) n) (uy*uz) (modulus n)
       (eqmodRefl ux (modulus n))
       (eqmUnsignedRepr' (uy*uz) n))
    (rewrite mulAssoc ux uy uz in
     eqmodMult (ux*uy) (unsigned $ repr (ux*uy) n) uz uz (modulus n)
       (eqmUnsignedRepr (ux*uy) n)
       (eqmodRefl uz (modulus n)))

mulAddDistrL : (x, y, z : BizMod2 n) -> x * (y + z) = x * y + x * z
mulAddDistrL x y z =
  let ux = unsigned x
      uy = unsigned y
      uz = unsigned z in
  eqmSamerepr (ux*(unsigned $ repr (uy+uz) n)) ((unsigned $ repr (ux*uy) n)+(unsigned $ repr (ux*uz) n)) n $
  eqmodTrans (ux*(unsigned $ repr (uy+uz) n)) (ux*(uy+uz)) ((unsigned $ repr (ux*uy) n)+(unsigned $ repr (ux*uz) n)) (modulus n)
    (eqmodMult ux ux (unsigned $ repr (uy+uz) n) (uy+uz) (modulus n)
      (eqmodRefl ux (modulus n))
      (eqmUnsignedRepr' (uy+uz) n))
    (rewrite mulAddDistrL ux uy uz in
     eqmodAdd (ux*uy) (unsigned $ repr (ux*uy) n) (ux*uz) (unsigned $ repr (ux*uz) n) (modulus n)
      (eqmUnsignedRepr (ux*uy) n)
      (eqmUnsignedRepr (ux*uz) n))

mulAddDistrR : (x, y, z : BizMod2 n) -> (x + y) * z = x * z + y * z
mulAddDistrR x y z =
  rewrite mulComm (x+y) z in
  rewrite mulComm x z in
  rewrite mulComm y z in
  mulAddDistrL z x y

mulNegL : (x, y : BizMod2 n) -> (-x) * y = -(x * y)
mulNegL {n} x y =
  let ux = unsigned x
      uy = unsigned y in
  eqmSamerepr ((unsigned $ repr (-ux) n)*uy) (-(unsigned $ repr (ux*uy) n)) n $
  eqmodTrans ((unsigned $ repr (-ux) n)*uy) (-(ux*uy)) (-(unsigned $ repr (ux*uy) n)) (modulus n)
    (rewrite sym $ mulOppL ux uy in
     eqmodMult (unsigned $ repr (-ux) n) (-ux) uy uy (modulus n)
       (eqmUnsignedRepr' (-ux) n)
       (eqmodRefl uy (modulus n)))
    (eqmodNeg (ux*uy) (unsigned $ repr (ux*uy) n) (modulus n) $
     eqmUnsignedRepr (ux*uy) n)

mulNegR : (x, y : BizMod2 n) -> x * (-y) = -(x * y)
mulNegR x y =
  rewrite mulComm x (-y) in
  rewrite mulComm x y in
  mulNegL y x

mulSigned : (x, y : BizMod2 n) -> x * y = repr (signed x * signed y) n
mulSigned {n} x y =
  eqmSamerepr (unsigned x * unsigned y) (signed x * signed y) n $
  eqmodMult (unsigned x) (signed x) (unsigned y) (signed y) (modulus n)
    (eqmUnsignedSigned x)
    (eqmUnsignedSigned y)

-- Properties of division and modulus

moduDivuEuclid : (x, y : BizMod2 n) -> Not (y = 0) -> x = ((x `divu` y)*y)+(x `modu` y)
moduDivuEuclid {n} x y yz =
  let ux = unsigned x
      uy = unsigned y in
  trans (sym $ reprUnsigned x) $
  eqmSamerepr ux ((unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)+(unsigned $ repr (ux `bizMod` uy) n)) n $
  eqmodTrans ux ((ux `bizDiv` uy)*uy + (ux `bizMod` uy))
             ((unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)+(unsigned $ repr (ux `bizMod` uy) n))
             (modulus n)
    (eqmodRefl2 ux ((ux `bizDiv` uy)*uy + (ux `bizMod` uy)) (modulus n) $
     divEuclEq ux uy $
     yz . replace {P=\z=>z=0} (reprUnsigned y) . cong {f=\z=>repr z n})
    (eqmodAdd ((ux `bizDiv` uy)*uy) (unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)
              (ux `bizMod` uy) (unsigned $ repr (ux `bizMod` uy) n)
              (modulus n)
       (eqmodTrans ((ux `bizDiv` uy)*uy) ((unsigned $ repr (ux `bizDiv` uy) n)*uy)
                   (unsigned $ repr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n)
                   (modulus n)
          (eqmodMult (ux `bizDiv` uy) (unsigned $ repr (ux `bizDiv` uy) n) uy uy (modulus n)
             (eqmUnsignedRepr (ux `bizDiv` uy) n)
             (eqmodRefl uy (modulus n)))
          (eqmUnsignedRepr ((unsigned $ repr (ux `bizDiv` uy) n)*uy) n))
       (eqmUnsignedRepr (ux `bizMod` uy) n))

moduDivu : (x, y : BizMod2 n) -> Not (y = 0) -> x `modu` y = x - ((x `divu` y)*y)
moduDivu x y yz = addTransferL x ((x `divu` y)*y) (x `modu` y) $
                  moduDivuEuclid x y yz

modsDivsEuclid : (x, y : BizMod2 n) -> x = ((x `divs` y)*y)+(x `mods` y)
modsDivsEuclid {n} x y =
  let uy = unsigned y
      sx = signed x
      sy = signed y in
  trans (sym $ reprSigned x) $
  eqmSamerepr sx ((unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)+(unsigned $ repr (sx `bizRem` sy) n)) n $
  eqmodTrans sx ((sx `bizQuot` sy)*sy + (sx `bizRem` sy))
             ((unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)+(unsigned $ repr (sx `bizRem` sy) n))
             (modulus n)
    (eqmodRefl2 sx ((sx `bizQuot` sy)*sy + (sx `bizRem` sy)) (modulus n) $
     quotremEq sx sy)
    (eqmodAdd ((sx `bizQuot` sy)*sy) (unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)
              (sx `bizRem` sy) (unsigned $ repr (sx `bizRem` sy) n)
              (modulus n)
       (eqmodTrans ((sx `bizQuot` sy)*sy) ((unsigned $ repr (sx `bizQuot` sy) n)*uy)
                   (unsigned $ repr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n)
                   (modulus n)
          (eqmodMult (sx `bizQuot` sy) (unsigned $ repr (sx `bizQuot` sy) n) sy uy (modulus n)
             (eqmUnsignedRepr (sx `bizQuot` sy) n)
             (eqmSignedUnsigned y))
          (eqmUnsignedRepr ((unsigned $ repr (sx `bizQuot` sy) n)*uy) n))
       (eqmUnsignedRepr (sx `bizRem` sy) n))

modsDivs : (x, y : BizMod2 n) -> x `mods` y = x - ((x `divs` y)*y)
modsDivs x y = addTransferL x ((x `divs` y)*y) (x `mods` y) $
               modsDivsEuclid x y

divu1 : (x : BizMod2 n) -> x `divu` 1 = x
divu1 {n=Z}   x = sym $ bizMod2P0 x
divu1 {n=S n} x = rewrite fst $ divMod1 (unsigned x) in
                  reprUnsigned x

-- there are some weird problems if you just split n
modu1 : (x : BizMod2 n) -> x `modu` 1 = 0
modu1 {n} x with (decEq n 0)
  | Yes z = rewrite z in
            Refl
  | No nz =
    rewrite moduDivu x 1 (oneNotZero n nz) in
    rewrite divu1 x in
    rewrite mul1R x in
    subIdem x

-- TODO add to Bin.Proofs

bipDivEuclid1R : (a : Bip) -> a `bipDivEuclid` 1 = (BinP a, BinO)
bipDivEuclid1R  U    = Refl
bipDivEuclid1R (O a) = rewrite bipDivEuclid1R a in
                       Refl
bipDivEuclid1R (I a) = rewrite bipDivEuclid1R a in
                       Refl

-- TODO add to Biz.Proofs

remOppR : (a, b : Biz) -> a `bizRem` (-b) = a `bizRem` b
remOppR  BizO     _       = Refl
remOppR  _        BizO    = Refl
remOppR (BizP _) (BizP _) = Refl
remOppR (BizP _) (BizM _) = Refl
remOppR (BizM _) (BizP _) = Refl
remOppR (BizM _) (BizM _) = Refl

quotOppR : (a, b : Biz) -> Not (b = 0) -> a `bizQuot` (-b) = -(a `bizQuot` b)
quotOppR  BizO        _    _  = Refl
quotOppR  _        BizO    bz = absurd $ bz Refl
quotOppR (BizP _) (BizP _) _  = Refl
quotOppR (BizP a) (BizM b) _  = sym $ oppInvolutive (toBizBin $ fst $ bipDivEuclid a (BinP b))
quotOppR (BizM a) (BizP b) _  = sym $ oppInvolutive (toBizBin $ fst $ bipDivEuclid a (BinP b))
quotOppR (BizM _) (BizM _) _  = Refl

quot1R : (a : Biz) -> a `bizQuot` 1 = a
quot1R  BizO    = Refl
quot1R (BizP a) = rewrite bipDivEuclid1R a in
                  Refl
quot1R (BizM a) = rewrite bipDivEuclid1R a in
                  Refl

divLe : (x, y : Biz) -> 0 `Lt` y -> 0 `Le` x -> (x `bizDiv` y) `Le` x
divLe x y zlty zlex =
  rewrite sym $ mulCompareMonoR y (x `bizDiv` y) x zlty in
  rewrite sym $ addCompareMonoR ((x `bizDiv` y)*y) (x*y) (x `bizMod` y) in
  rewrite sym $ divEuclEq x y (ltNotEq y 0 zlty) in
  case leLtOrEq 0 x zlex of
    Left zltx => leTrans x (x*y) ((x*y)+(x `bizMod` y))
                   (rewrite sym $ mul1R x in
                    rewrite sym $ mulAssoc x 1 y in
                    rewrite mul1L y in
                    rewrite mulCompareMonoL x 1 y zltx in
                    leSuccLFro 0 y zlty)
                   (rewrite sym $ add0R (x*y) in
                    rewrite sym $ addAssoc (x*y) 0 (x `bizMod` y) in
                    rewrite addCompareMonoL (x*y) 0 (x `bizMod` y) in
                    fst $ modPosBound x y zlty)
    Right zx => rewrite sym zx in
                uninhabited

div2D : (x : Biz) -> bizDivTwo (bizD x) = x
div2D  BizO    = Refl
div2D (BizP _) = Refl
div2D (BizM _) = Refl

div2DPO : (x : Biz) -> bizDivTwo (bizDPO x) = x
div2DPO  BizO        = Refl
div2DPO (BizP  _)    = Refl
div2DPO (BizM  U)    = Refl
div2DPO (BizM (O a)) = rewrite succPredDouble a in
                       Refl
div2DPO (BizM (I _)) = Refl

divsM1 : (x : BizMod2 n) -> x `divs` (-1) = -x
divsM1 {n} x =
  rewrite signedMone n in
  rewrite quotOppR (signed x) 1 uninhabited in
  rewrite quot1R (signed x) in
  eqmSamerepr (-(signed x)) (-(unsigned x)) n $
  eqmodNeg (signed x) (unsigned x) (modulus n) $
  eqmSignedUnsigned x

modsM1 : (x : BizMod2 n) -> x `mods` (-1) = 0
modsM1 x =
  rewrite modsDivs x (-1) in
  rewrite divsM1 x in
  rewrite mulNegL x (-1) in
  rewrite mulM1R x in
  rewrite negInvolutive x in
  subIdem x

divmodu2DivuModu : (nl, d : BizMod2 n) -> Not (d = 0) -> divmodu2 0 nl d = Just (nl `divu` d, nl `modu` d)
divmodu2DivuModu {n} nl d dz =
  rewrite neqbNeqFro (unsigned d) (unsigned $ repr 0 n) (dz . unsignedInj d 0) in
  rewrite unsignedZero n in
  rewrite lebLeFro ((unsigned nl) `bizDiv` (unsigned d)) (maxUnsigned n) $
            ltPredRTo ((unsigned nl) `bizDiv` (unsigned d)) (modulus n) $
            leLtTrans ((unsigned nl) `bizDiv` (unsigned d)) (unsigned nl) (modulus n)
              (divLe (unsigned nl) (unsigned d)
                 (case leLtOrEq 0 (unsigned d) (fst $ unsignedRange d) of
                    Left zltd => zltd
                    Right zd => absurd $ aux d dz $ sym zd
                 )
                 (fst $ unsignedRange nl))
              (snd $ unsignedRange nl)
              in
  Refl
  where
  aux : (x : BizMod2 n) -> Not (x = 0) -> Not (unsigned x = 0)
  aux x xz = rewrite sym $ unsignedZero n in
             xz . unsignedInj x 0

-- TODO the normalized types explode so fast that it doesn't seem realistic to
-- prove manually in current Idris (1.1.1)
{-
-- when n=0 the condition in divmods2 becomes 0 <= q <= -1 so this won't hold
divmods2DivsMods : (nl, d : BizMod2 n) -> Not (n=0) -> Not (d = 0) -> Either (Not (nl = repr (minSigned n) n)) (Not (d = -1))
                 -> divmods2 (if nl < 0 then -1 else 0) nl d = Just (nl `divs` d, nl `mods` d)
divmods2DivsMods {n} nl d nz dz nlord =
  rewrite neqbNeqFro (unsigned d) (unsigned $ repr 0 n) (dz . unsignedInj d 0) in
  rewrite unsignedZero n in
  rewrite ltbLtFro 0 (halfModulus n) $ halfModulusPos n nz in
  rewrite aux nl nz in
  ?divmods2DivsMods
  where
  aux : (x : BizMod2 n) -> Not (n=0) -> signed (if x < 0 then -1 else 0) * (modulus n) + unsigned x = signed x
-}

-- Bit-level properties

-- TODO add to Biz.Proofs ?
-- Properties of bit-level operations over [Z]

testbit1L : (n : Biz) -> bizTestBit 1 n = n == 0
testbit1L  BizO    = Refl
testbit1L (BizP _) = Refl
testbit1L (BizM _) = Refl

testbitM1L : (n : Biz) -> 0 `Le` n -> bizTestBit (-1) n = True
testbitM1L  BizO    _    = Refl
testbitM1L (BizP _) _    = Refl
testbitM1L (BizM _) zlen = absurd $ zlen Refl

zShiftinSpec : (b : Bool) -> (x : Biz) -> zShiftin b x = 2 * x + (if b then 1 else 0)
zShiftinSpec False x = rewrite add0R (2*x) in
                       doubleSpec x
zShiftinSpec True x = succDoubleSpec x

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

zShiftinInj : (b1, b2 : Bool) -> (x1, x2 : Biz) -> zShiftin b1 x1 = zShiftin b2 x2 -> (b1 = b2, x1 = x2)
zShiftinInj True  True  x1 x2 prf = (Refl,    prf
                                           |> replace {P = \z => z = bizDPO x2} (succDoubleSpec x1)
                                           |> replace {P = \z => 2*x1 + 1 = z} (succDoubleSpec x2)
                                           |> addRegR 1 (2*x1) (2*x2)
                                           |> mulRegL x1 x2 2 uninhabited)
zShiftinInj True  False x1 x2 prf = absurd $ notDDPO x2 x1 (sym prf)
zShiftinInj False True  x1 x2 prf = absurd $ notDDPO x1 x2 prf
zShiftinInj False False x1 x2 prf = (Refl,    prf
                                           |> replace {P = \z => z = bizD x2} (doubleSpec x1)
                                           |> replace {P = \z => 2*x1 = z} (doubleSpec x2)
                                           |> mulRegL x1 x2 2 uninhabited)

zDecomp : (x : Biz) -> x = zShiftin (bizOdd x) (bizDivTwo x)
zDecomp  BizO        = Refl
zDecomp (BizP  U)    = Refl
zDecomp (BizP (O _)) = Refl
zDecomp (BizP (I _)) = Refl
zDecomp (BizM  U)    = Refl
zDecomp (BizM (O _)) = Refl
zDecomp (BizM (I a)) = cong $ sym $ predDoubleSucc a

leNeqLt : (x, y : Biz) -> y `Le` x -> Not (x=y) -> y `Lt` x
leNeqLt x y ylex nxy =
  case leLtOrEq y x ylex of
    Left yltx => yltx
    Right xy => absurd $ nxy $ sym xy

zTestbitShiftin : (b : Bool) -> (x, n : Biz) -> 0 `Le` n
               -> bizTestBit (zShiftin b x) n = if n == 0 then b else bizTestBit x (bizPred n)
zTestbitShiftin b x n zlen with (n==0) proof nz
  zTestbitShiftin False x n zlen | False =
      testbitEvenSucc x (bizPred n) (ltPredRTo 0 n $ leNeqLt n 0 zlen $ neqbNeqTo n 0 (sym nz))
   |> replace {P = \z => bizTestBit (bizD x) z = bizTestBit x (bizPred n)} (sym $ addAssoc n (-1) 1)
   |> replace {P = \z => bizTestBit (bizD x) z = bizTestBit x (bizPred n)} (add0R n)
  zTestbitShiftin True  x n zlen | False =
      testbitOddSucc x (bizPred n) (ltPredRTo 0 n $ leNeqLt n 0 zlen $ neqbNeqTo n 0 (sym nz))
   |> replace {P = \z => bizTestBit (bizDPO x) z = bizTestBit x (bizPred n)} (sym $ addAssoc n (-1) 1)
   |> replace {P = \z => bizTestBit (bizDPO x) z = bizTestBit x (bizPred n)} (add0R n)
  zTestbitShiftin False x n zlen | True  = rewrite eqbEqTo n 0 (sym nz) in
                                           testbitEven0 x
  zTestbitShiftin True  x n zlen | True  = rewrite eqbEqTo n 0 (sym nz) in
                                           testbitOdd0 x

zTestbitShiftinBase : (b : Bool) -> (x : Biz) -> bizTestBit (zShiftin b x) 0 = b
zTestbitShiftinBase b x =
  rewrite zTestbitShiftin b x 0 uninhabited in
  Refl

zTestbitShiftinSucc : (b : Bool) -> (x, n : Biz) -> 0 `Le` n -> bizTestBit (zShiftin b x) (bizSucc n) = bizTestBit x n
zTestbitShiftinSucc b x n zlen =
  rewrite zTestbitShiftin b x (bizSucc n) $ ltLeIncl 0 (n+1) $ ltSuccRFro 0 n zlen in
  rewrite neqbNeqFro (n+1) 0 $ ltNotEq (n+1) 0 $ ltSuccRFro 0 n zlen in
  rewrite sym $ addAssoc n 1 (-1) in
  rewrite add0R n in
  Refl

zTestbitEq : (x, n : Biz) -> 0 `Le` n -> bizTestBit x n = if n == 0 then bizOdd x else bizTestBit (bizDivTwo x) (bizPred n)
zTestbitEq x n zlen =
  rewrite sym $ zTestbitShiftin (bizOdd x) (bizDivTwo x) n zlen in
  rewrite sym $ zDecomp x in
  Refl

-- zTestbitBase is trivial

zTestbitSucc : (a, n : Biz) -> 0 `Le` n -> bizTestBit a (bizSucc n) = bizTestBit (bizDivTwo a) n
zTestbitSucc a n zlen =
  case evenOrOdd a of
    Left  (b**eprf) =>
      rewrite sym $ testbitEvenSucc (bizDivTwo a) n zlen in
      rewrite eprf in
      rewrite sym $ doubleSpec b in
      rewrite div2D b in
      Refl
    Right (b**oprf) =>
      rewrite sym $ testbitOddSucc (bizDivTwo a) n zlen in
      rewrite oprf in
      rewrite sym $ succDoubleSpec b in
      rewrite div2DPO b in
      Refl

eqmodSameBits : (n : Nat) -> (x, y : Biz)
             -> ((i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> bizTestBit x i = bizTestBit y i)
             -> eqmod x y (modulus n)
eqmodSameBits  Z    x y _ =
  (x-y ** rewrite mul1R (x-y) in
          rewrite sym $ addAssoc x (-y) y in
          rewrite addOppDiagL y in
          sym $ add0R x)
eqmodSameBits (S k) x y f =
  let (z**prf) = eqmodSameBits k (bizDivTwo x) (bizDivTwo y) $
                 \i,i0,ik =>
                   rewrite sym $ zTestbitSucc x i i0 in
                   rewrite sym $ zTestbitSucc y i i0 in
                   f (i+1)
                     (ltLeIncl 0 (i+1) $ leLtTrans 0 i (i+1) i0 $ ltSuccRFro i i $ leRefl i)
                     (rewrite toBizNatInjSucc k in
                      rewrite addCompareMonoR i (toBizNat k) 1 in
                      ik)
  in
  (z ** rewrite zDecomp x in
        rewrite zDecomp y in
        rewrite zShiftinSpec (bizOdd x) (bizDivTwo x) in
        rewrite zShiftinSpec (bizOdd y) (bizDivTwo y) in
        rewrite f 0 uninhabited Refl in    -- bizOdd x = bizOdd y
        -- TODO bug: can't simply write `if bizOdd y then ..` - INTERNAL ERROR: Unelaboratable syntactic form
        rewrite addAssoc (z*modulus (S k)) (2*bizDivTwo y) (ifThenElse (bizOdd y) (Delay (BizP U)) (Delay BizO)) in
        rewrite mulAssoc z 2 (modulus k) in
        rewrite mulComm z 2 in
        rewrite sym $ mulAssoc 2 z (modulus k) in
        rewrite sym $ mulAddDistrL 2 (z*modulus k) (bizDivTwo y) in
        cong {f = \a => 2*a + (ifThenElse (bizOdd y) (Delay (BizP U)) (Delay BizO))} prf)

oddNotEven : (x : Biz) -> bizOdd x = not (bizEven x)
oddNotEven  BizO        = Refl
oddNotEven (BizP  U)    = Refl
oddNotEven (BizP (O a)) = Refl
oddNotEven (BizP (I a)) = Refl
oddNotEven (BizM  U)    = Refl
oddNotEven (BizM (O a)) = Refl
oddNotEven (BizM (I a)) = Refl

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

sameBitsEqmod : (n : Nat) -> (x, y, i : Biz) -> eqmod x y (modulus n) -> 0 `Le` i -> i `Lt` toBizNat n
            -> bizTestBit x i = bizTestBit y i
sameBitsEqmod  Z    _ _ i    _       zlei iltn = absurd $ zlei $ ltGt i 0 iltn
sameBitsEqmod (S k) x y i (z**xy) zlei iltn    =
  case decEq i 0 of
    Yes i0 =>
      rewrite i0 in
      case evenOrOdd x of
        Left (a**eprf) =>
          let evy = xy
                 |> replace {P=\q=>x=q+y} (mulAssoc z 2 (modulus k))
                 |> replace {P=\q=>x=q*(modulus k)+y} (mulComm z 2)
                 |> replace {P=\q=>x=q+y} (sym $ mulAssoc 2 z (modulus k))
                 |> trans (sym eprf)
                 |> addTransferLZ (2*a) (2*(z*(modulus k))) y
                 |> replace {P=\q=>y=2*a+q} (sym $ mulOppR 2 (z*(modulus k)))
                 |> replace {P=\q=>y=q} (sym $ mulAddDistrL 2 a (-(z*(modulus k))))
          in
          rewrite oddNotEven x in
          rewrite oddNotEven y in
          rewrite evenSpecFro x (a**eprf) in
          rewrite evenSpecFro y (a-z*(modulus k)**evy) in
          Refl
        Right (a**oprf) =>
          let ody = xy
                 |> replace {P=\q=>x=q+y} (mulAssoc z 2 (modulus k))
                 |> replace {P=\q=>x=q*(modulus k)+y} (mulComm z 2)
                 |> replace {P=\q=>x=q+y} (sym $ mulAssoc 2 z (modulus k))
                 |> trans (sym oprf)
                 |> addTransferLZ (2*a+1) (2*(z*(modulus k))) y
                 |> replace {P=\q=>y=2*a+1+q} (sym $ mulOppR 2 (z*(modulus k)))
                 |> replace {P=\q=>y=q} (addComm (2*a+1) (2*(-(z*(modulus k)))))
                 |> replace {P=\q=>y=q} (addAssoc (2*(-(z*(modulus k)))) (2*a) 1)
                 |> replace {P=\q=>y=q+1} (sym $ mulAddDistrL 2 (-(z*(modulus k))) a)
          in
          rewrite oddSpecFro x (a**oprf) in
          rewrite oddSpecFro y (-(z*(modulus k))+a**ody) in
          Refl
    No in0 =>
      rewrite succPredZ i in
      let zleip = ltPredRTo 0 i $ leNeqLt i 0 zlei in0
          ih = sameBitsEqmod k (bizDivTwo x) (bizDivTwo y) (i-1)
                 (z ** snd $ zShiftinInj (bizOdd x) (bizOdd y) (bizDivTwo x) (z * (modulus k) + bizDivTwo y) aux)
                 zleip
                 (rewrite sym $ addCompareMonoR (i-1) (toBizNat k) 1 in
                  rewrite sym $ addAssoc i (-1) 1 in
                  rewrite add0R i in
                  rewrite sym $ toBizNatInjSucc k in
                  iltn)
      in
      rewrite zTestbitSucc x (bizPred i) zleip in
      rewrite zTestbitSucc y (bizPred i) zleip in
      ih
  where
  aux : zShiftin (bizOdd x) (bizDivTwo x) = zShiftin (bizOdd y) (z * (modulus k) + bizDivTwo y)
  aux =
    rewrite sym $ zDecomp x in
    rewrite zShiftinSpec (bizOdd y) (z * (modulus k) + bizDivTwo y) in
    rewrite mulAddDistrL 2 (z*(modulus k)) (bizDivTwo y) in
    rewrite sym $ addAssoc (2*(z*(modulus k))) (2*(bizDivTwo y)) (ifThenElse (bizOdd y) (Delay 1) (Delay 0)) in
    rewrite sym $ zShiftinSpec (bizOdd y) (bizDivTwo y) in
    rewrite sym $ zDecomp y in
    rewrite mulAssoc 2 z (modulus k) in
    rewrite mulComm 2 z in
    rewrite sym $ mulAssoc z 2 (modulus k) in
    xy

natlikeInd : (P : Biz -> Type) -> (f0 : P BizO)
          -> ((y : Biz) -> 0 `Le` y -> P y -> P (bizSucc y))
          -> (x : Biz) -> 0 `Le` x -> P x
natlikeInd _ f0 _  BizO    _    = f0
natlikeInd P f0 f (BizP a) zlex =
  peanoRect (P . BizP) (f 0 uninhabited f0) (\p => rewrite sym $ add1R p in
                                                   f (BizP p) uninhabited) a
natlikeInd _ _  _ (BizM _) zlex = absurd $ zlex Refl

modulusInfinity : (x : Biz) -> 0 `Le` x -> (n ** x `Lt` modulus n)
modulusInfinity x zlex =
  natlikeInd
    (\y => (n ** y `Lt` modulus n))
    (0 ** Refl)
    (\y, zley, (n ** prf) =>
      (S n ** case decEq y 0 of
                Yes y0 =>
                  rewrite y0 in
                  Refl
                No yn0 =>
                  leLtTrans (y+1) (2*y) (modulus (S n))
                    (rewrite mulAddDistrR 1 1 y in
                     rewrite mul1L y in
                     rewrite addCompareMonoL y 1 y in
                     leSuccLFro 0 y $ leNeqLt y 0 zley yn0)
                    (rewrite mulCompareMonoL 2 y (modulus n) Refl in
                     prf)
      )
    )
    x
    zlex

equalSameBits : (x, y : Biz) -> ((i : Biz) -> 0 `Le` i -> bizTestBit x i = bizTestBit y i) -> x = y
equalSameBits x y f with (x `compare` y) proof xy
  | LT =
    let zltyx = replace {P = \a => a = LT} (compareSubR x y) (sym xy)
        zleyx = ltLeIncl 0 (y-x) zltyx
        (n ** yxltm) = modulusInfinity (y-x) zleyx
        yxeqm0 = eqmodSameBits n x y (\i,zlei,_ => f i zlei)
              |> eqmodSub y y x y (modulus n) (eqmodRefl y (modulus n))
              |> replace {P = \a => eqmod (y-x) a (modulus n)} (addOppDiagR y)
        yx0 = eqmodSmallEq (y-x) 0 (modulus n) yxeqm0 zleyx yxltm uninhabited Refl
        contra = replace {P = \a => 0 `Lt` a} yx0 zltyx
    in absurd contra
  | EQ = compareEqIffTo x y (sym xy)
  | GT =
    let zltxy = replace {P = \a => a = LT} (compareSubR y x) (gtLt x y $ sym xy)
        zlexy = ltLeIncl 0 (x-y) zltxy
        (n ** xyltm) = modulusInfinity (x-y) zlexy
        xyeqm0 = eqmodSameBits n y x (\i,zlei,_ => sym $ f i zlei)
              |> eqmodSub x x y x (modulus n) (eqmodRefl x (modulus n))
              |> replace {P = \a => eqmod (x-y) a (modulus n)} (addOppDiagR x)
        xy0 = eqmodSmallEq (x-y) 0 (modulus n) xyeqm0 zlexy xyltm uninhabited Refl
        contra = replace {P = \a => 0 `Lt` a} xy0 zltxy
    in absurd contra

zOneComplement : (i, x : Biz) -> 0 `Le` i -> bizTestBit (-x-1) i = not (bizTestBit x i)
zOneComplement i x zlei =
  natlikeInd
    (\j => (y : Biz) -> bizTestBit (-y-1) j = not (bizTestBit y j))
    base
    (\j, zlej, pyj, y =>
        let zltj1 = ltSuccRFro 0 j zlej
            zlej1 = ltLeIncl 0 (j+1) zltj1 in
        rewrite zDecomp y in
        rewrite aux (bizOdd y) (bizDivTwo y) in
        rewrite zTestbitShiftin (not (bizOdd y)) (-(bizDivTwo y)-1) (j+1) zlej1 in
        rewrite zTestbitShiftin (bizOdd y) (bizDivTwo y) (j+1) zlej1 in
        rewrite neqbNeqFro (j+1) 0 $ ltNotEq (j+1) 0 zltj1 in
        rewrite sym $ addAssoc j 1 (-1) in
        rewrite add0R j in
        pyj (bizDivTwo y))
    i zlei x
  where
  base : (x : Biz) -> bizOdd (-x-1) = not (bizOdd x)
  base  BizO        = Refl
  base (BizP  U)    = Refl
  base (BizP (O _)) = Refl
  base (BizP (I _)) = Refl
  base (BizM  U)    = Refl
  base (BizM (O a)) =
    case succPredOr a of
      Left au  => rewrite au in
                  Refl
      Right as => rewrite sym as in
                  rewrite predDoubleSucc (bipPred a) in
                  Refl
  base (BizM (I _)) = Refl

  aux : (b : Bool) -> (x : Biz) -> -(zShiftin b x)-1 = zShiftin (not b) (-x-1)
  aux False  BizO        = Refl
  aux False (BizP  a)    = rewrite add1R a in
                           cong $ sym $ predDoubleSucc a
  aux False (BizM  U)    = Refl
  aux False (BizM (O _)) = Refl
  aux False (BizM (I _)) = Refl
  aux True   BizO        = Refl
  aux True  (BizP  a)    = cong {f = BizM . O} $ sym $ add1R a
  aux True  (BizM  U)    = Refl
  aux True  (BizM (O _)) = Refl
  aux True  (BizM (I _)) = Refl

div2Pos : (x : Biz) -> 0 `Le` x -> 0 `Le` bizDivTwo x
div2Pos  BizO        _    = uninhabited
div2Pos (BizP  U)    _    = uninhabited
div2Pos (BizP (O _)) _    = uninhabited
div2Pos (BizP (I _)) _    = uninhabited
div2Pos (BizM  _)    zlex = absurd $ zlex Refl

dDiv2Le : (x : Biz) -> 0 `Le` x -> 2*(bizDivTwo x) `Le` x
dDiv2Le  BizO        _    = uninhabited
dDiv2Le (BizP  U)    _    = uninhabited
dDiv2Le (BizP (O a)) _    = rewrite compareContRefl a EQ in
                            uninhabited
dDiv2Le (BizP (I a)) _    = rewrite compareContRefl a LT in
                            uninhabited
dDiv2Le (BizM  _)    zlex = absurd $ zlex Refl

zTestbitAbove : (n : Nat) -> (x, i : Biz) -> 0 `Le` x -> x `Lt` modulus n -> toBizNat n `Le` i -> bizTestBit x i = False
zTestbitAbove  Z     BizO    i _    _    _    = testbit0L i
zTestbitAbove  Z    (BizP a) _ _    xltm _    = absurd $ le1L a $ ltGt a 1 xltm
zTestbitAbove  Z    (BizM _) _ zlex _    _    = absurd $ zlex Refl
zTestbitAbove (S k)  x       i zlex xltm nlei =
  let zlti = ltLeTrans 0 (toBizNat (S k)) i Refl nlei in
  rewrite zTestbitEq x i $ ltLeIncl 0 i zlti in
  rewrite neqbNeqFro i 0 $ ltNotEq i 0 zlti in
  zTestbitAbove k (bizDivTwo x) (i-1)
    (div2Pos x zlex)
    (rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus k) Refl in
     leLtTrans (2*(bizDivTwo x)) x (modulus (S k))
       (dDiv2Le x zlex)
        xltm
    )
    (rewrite sym $ addCompareMonoR (toBizNat k) (i-1) 1 in
     rewrite sym $ succPredZ i in
     rewrite sym $ toBizNatInjSucc k in
     nlei)

ltPredLTo : (n, m : Biz) -> n `Le` m -> bizPred n `Lt` m
ltPredLTo n m nlem =
  ltPredRFro (bizPred n) m $
  rewrite addCompareMonoR n m (-1) in
  nlem

zTestbitAboveNeg : (n : Nat) -> (x, i : Biz) -> -(modulus n) `Le` x -> x `Lt` 0 -> toBizNat n `Le` i -> bizTestBit x i = True
zTestbitAboveNeg n x i mmlex xlt0 nlei =
  let notmxm1 = sym $ zOneComplement i x $ leTrans 0 (toBizNat n) i (toBizNatIsNonneg n) nlei
      mxm1false = zTestbitAbove n (-x-1) i
                    (ltPredRTo 0 (-x) $
                     rewrite sym $ compareOpp x 0 in
                     xlt0)
                    (ltPredLTo (-x) (modulus n) $
                     rewrite compareOpp (-x) (modulus n) in
                     rewrite oppInvolutive x in
                     mmlex)
                    nlei
  in
  rewrite sym $ notNot (bizTestBit x i) in
  rewrite trans notmxm1 mxm1false in
  Refl

-- TODO reformulate RHS as `modulus n <= x`
zSignBit : (n : Nat) -> (x : Biz) -> 0 `Le` x -> x `Lt` modulus (S n)
        -> bizTestBit x (toBizNat n) = if x < modulus n then False else True
zSignBit  Z     BizO        _    _     = Refl
zSignBit  Z    (BizP  U)    _    _     = Refl
zSignBit  Z    (BizP (O a)) _    xltsm = absurd $ nlt1R a xltsm
zSignBit  Z    (BizP (I a)) _    xltsm = absurd $ nlt1R a $ compareContGtLtTo a U xltsm
zSignBit  Z    (BizM _)     zlex _     = absurd $ zlex Refl
zSignBit (S k)  x           zlex xltsm =
  rewrite toBizNatInjSucc k in
  rewrite zTestbitSucc x (toBizNat k) (toBizNatIsNonneg k) in
  rewrite zSignBit k (bizDivTwo x)
            (div2Pos x zlex)
            (rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus (S k)) Refl in
             leLtTrans (2*(bizDivTwo x)) x (modulus (S (S k)))
               (dDiv2Le x zlex)
                xltsm
            ) in
  aux2
  where
  aux : (x : Biz) -> (k : Bip) -> BizP (O k) `Lt` x -> BizP k `Le` bizDivTwo x
  aux  BizO        _ dkltx = absurd dkltx
  aux (BizP  U)    _ dkltx = absurd dkltx
  aux (BizP (O a)) k dkltx = ltLeIncl k a dkltx
  aux (BizP (I a)) k dkltx = compareContLtLtTo k a dkltx
  aux (BizM  _)    _ dkltx = absurd dkltx
  aux2 : (if bizDivTwo x < modulus k then False else True) = (if x < modulus (S k) then False else True)
  aux2 with (x `compare` modulus (S k)) proof xsm
    | LT = rewrite ltbLtFro (bizDivTwo x) (modulus k) $
                     rewrite sym $ mulCompareMonoL 2 (bizDivTwo x) (modulus k) Refl in
                     leLtTrans (2*(bizDivTwo x)) x (modulus (S k))
                       (dDiv2Le x zlex)
                       (sym xsm)
                   in
           Refl
    | EQ = rewrite compareEqIffTo x (modulus (S k)) (sym xsm) in
           rewrite compareContRefl (twoPowerNat k) EQ in
           Refl
    | GT = let mlex2 = aux x (twoPowerNat k) $ gtLt x (modulus (S k)) (sym xsm) in
           rewrite nltbLeFro (modulus k) (bizDivTwo x) mlex2 in
           Refl

zShiftinInd : (P : Biz -> Type) -> (f0 : P 0)
           -> ((b : Bool) -> (x : Biz) -> 0 `Le` x -> P x -> P (zShiftin b x))
           -> (x : Biz) -> 0 `Le` x -> P x
zShiftinInd _ f0 _  BizO    _    = f0
zShiftinInd P f0 f (BizP a) _    = aux a
  where
  -- a workaround to convince totality checker that `BizP (O/I a) -> BizP a` is decreasing
  aux : (p : Bip) -> P (BizP p)
  aux  U    = f True 0 uninhabited f0
  aux (O a) = f False (BizP a) uninhabited $ aux a
  aux (I a) = f True (BizP a) uninhabited $ aux a
zShiftinInd _ _  _ (BizM _) zlex = absurd $ zlex Refl

zShiftinPosInd : (P : Biz -> Type) -> (f1 : P 1)
              -> ((b : Bool) -> (x : Biz) -> 0 `Lt` x -> P x -> P (zShiftin b x))
              -> (x : Biz) -> 0 `Lt` x -> P x
zShiftinPosInd _ _  _  BizO    zltx = absurd zltx
zShiftinPosInd P f1 f (BizP a) _    = aux a
  where
  -- a workaround to convince totality checker that `BizP (O/I a) -> BizP a` is decreasing
  aux : (p : Bip) -> P (BizP p)
  aux  U    = f1
  aux (O a) = f False (BizP a) Refl $ aux a
  aux (I a) = f True (BizP a) Refl $ aux a
zShiftinPosInd _ _  _ (BizM _) zltx = absurd zltx

notTrueIsFalse : (b : Bool) -> Not (b = True) -> b = False
notTrueIsFalse True  nbt = absurd $ nbt Refl
notTrueIsFalse False _   = Refl

trueOrFalse : (b : Bool) -> Either (b = False) (b = True)
trueOrFalse False = Left Refl
trueOrFalse True = Right Refl

zTestbitLe : (x, y : Biz) -> 0 `Le` y -> ((i : Biz) -> 0 `Le` i -> bizTestBit x i = True -> bizTestBit y i = True) -> x `Le` y
zTestbitLe x y zley =
  zShiftinInd
    (\q => (p : Biz) -> ((i : Biz) -> 0 `Le` i -> bizTestBit p i = True -> bizTestBit q i = True) -> p `Le` q)
    (\p, fInd =>
     rewrite equalSameBits p 0 $ \i, zlei =>
               rewrite testbit0L i in
               notTrueIsFalse (bizTestBit p i) $
               \btb => absurd $ trans (sym $ testbit0L i) (fInd i zlei btb)
     in
     uninhabited)
    (\b,q,zleq,ih,p,fInd =>
      rewrite zDecomp p in
      rewrite zShiftinSpec (bizOdd p) (bizDivTwo p) in
      rewrite zShiftinSpec b q in
      let p2leq = ih (bizDivTwo p) $ \i, zlei, btb2 =>
                    rewrite sym $ zTestbitShiftinSucc b q i zlei in
                    fInd (i+1)
                      (leTrans 0 i (i+1) zlei $ ltLeIncl i (i+1) $ ltSuccRFro i i $ leRefl i)
                      (rewrite zTestbitSucc p i zlei in
                       btb2)
      in
      case trueOrFalse (bizOdd p) of
        Left nod =>
          rewrite nod in
          rewrite add0R (2*(bizDivTwo p)) in
          leTrans (2*(bizDivTwo p)) (2*q) (2*q + (ifThenElse b (Delay 1) (Delay 0)))
            (rewrite mulCompareMonoL 2 (bizDivTwo p) q Refl in
             p2leq)
            (case b of
               False =>
                 rewrite add0R (2*q) in
                 leRefl (2*q)
               True =>
                 ltLeIncl (2*q) ((2*q)+1) $ ltSuccRFro (2*q) (2*q) $ leRefl (2*q)
            )
        Right od =>
          rewrite od in
          rewrite trans (sym $ zTestbitShiftinBase b q) (fInd 0 uninhabited od) in   -- b = True
          rewrite addCompareMonoR (2*(bizDivTwo p)) (2*q) 1 in
          rewrite mulCompareMonoL 2 (bizDivTwo p) q Refl in
          p2leq
    )
    y zley x

-- Bit-level reasoning over type [int]

testbit : (x : BizMod2 n) -> (i : Biz) -> Bool
testbit x i = bizTestBit (unsigned x) i

testbitRepr : (n : Nat) -> (x : Biz) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (repr x n) i = bizTestBit x i
testbitRepr n x i zlei iltn =
  sameBitsEqmod n (unsigned (repr x n)) x i (eqmUnsignedRepr' x n) zlei iltn

sameBitsEq : (x, y : BizMod2 n) -> ((i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit x i = testbit y i) -> x = y
sameBitsEq {n} x y f =
  rewrite sym $ reprUnsigned x in
  rewrite sym $ reprUnsigned y in
  eqmSamerepr (unsigned x) (unsigned y) n $
  eqmodSameBits n (unsigned x) (unsigned y) f

bitsAbove : (x : BizMod2 n) -> (i : Biz) -> toBizNat n `Le` i -> testbit x i = False
bitsAbove {n} x i nlei =
  let ur = unsignedRange x in
  zTestbitAbove n (unsigned x) i (fst ur) (snd ur) nlei

bitsZero : (i : Biz) -> testbit (repr 0 n) i = False
bitsZero {n} i = rewrite unsignedZero n in
                 testbit0L i

bitsOne : (n : Nat) -> (i : Biz) -> Not (n=0) -> testbit (repr 1 n) i = i == 0
bitsOne  Z    _ nz = absurd $ nz Refl
bitsOne (S _) i _  = testbit1L i

bitsMone : (n : Nat) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (repr (-1) n) i = True
bitsMone n i zlei iltn =
  rewrite testbitRepr n (-1) i zlei iltn in
  testbitM1L i zlei

-- TODO reformulate RHS as `halfModulus n <= unsigned x`
-- when `n=0` this becomes `bizTestBit 0 (-1) = True` which is wrong
signBitOfUnsigned : (x : BizMod2 n) -> Not (n=0) -> testbit x (toBizNat n - 1) = if unsigned x < halfModulus n then False else True
signBitOfUnsigned {n=Z}   _ nz = absurd $ nz Refl
signBitOfUnsigned {n=S n} x _  =
  rewrite aux n in
  let ur = unsignedRange x in
  zSignBit n (unsigned x) (fst ur) (snd ur)
  where
  aux : (n : Nat) -> bipMinusBiz (toBipNatSucc n) U = toBizNat n
  aux  Z    = Refl
  aux (S n) =
    rewrite sym $ add1R (toBipNatSucc n) in
    rewrite posSubAdd (toBipNatSucc n) 1 1 in
    Refl

-- TODO add to Prelude.Interfaces?
DecEq Ordering where
  decEq LT LT = Yes Refl
  decEq LT EQ = No uninhabited
  decEq LT GT = No uninhabited
  decEq EQ LT = No uninhabited
  decEq EQ EQ = Yes Refl
  decEq EQ GT = No uninhabited
  decEq GT LT = No uninhabited
  decEq GT EQ = No uninhabited
  decEq GT GT = Yes Refl

-- when `n=0` this becomes `bizTestBit (-1) i = False` which is wrong
bitsSigned : (x : BizMod2 n) -> (i : Biz) -> Not (n=0) -> 0 `Le` i -> bizTestBit (signed x) i = testbit x (if i < toBizNat n then i else toBizNat n - 1)
bitsSigned {n} x i nz zlei =
  case decEq (i `compare` toBizNat n) LT of
    Yes iltn =>
      rewrite ltbLtFro i (toBizNat n) iltn in
      sameBitsEqmod n (signed x) (unsigned x) i (eqmSignedUnsigned x) zlei iltn
    No igen =>
      let nlei = geLe i (toBizNat n) igen in
      rewrite nltbLeFro (toBizNat n) i nlei in
      rewrite signBitOfUnsigned x nz in
      case decEq ((unsigned x) `compare` (halfModulus n)) LT of
        Yes xltm2 =>
          rewrite ltbLtFro (unsigned x) (halfModulus n) xltm2 in
          bitsAbove x i nlei
        No xgem2 =>
          rewrite nltbLeFro (halfModulus n) (unsigned x) $ geLe (unsigned x) (halfModulus n) xgem2 in
          zTestbitAboveNeg n (unsigned x - modulus n) i
            (rewrite addCompareMonoR 0 (unsigned x) (-(modulus n)) in
             fst $ unsignedRange x)
            (rewrite sym $ compareSub (unsigned x) (modulus n) in
             snd $ unsignedRange x)
            nlei

bitsLe : (x, y : BizMod2 n) -> ((i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit x i = True -> testbit y i = True) -> unsigned x `Le` unsigned y
bitsLe {n} x y f =
  zTestbitLe (unsigned x) (unsigned y) (fst $ unsignedRange y) $ \i, zlei, tbxt =>
  case decEq (i `compare` toBizNat n) LT of
    Yes iltn =>
      f i zlei iltn tbxt
    No igen =>
      let tbxf = bitsAbove x i $ geLe i (toBizNat n) igen in
      absurd $ trans (sym tbxt) tbxf

-- Properties of bitwise and, or, xor

bitsAnd : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (x `and` y) i = testbit x i && testbit y i
bitsAnd {n} x y i zlei iltn =
  rewrite testbitRepr n ((unsigned x) `bizAnd` (unsigned y)) i zlei iltn in
  landSpec (unsigned x) (unsigned y) i

bitsOr : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (x `or` y) i = testbit x i || testbit y i
bitsOr {n} x y i zlei iltn =
  rewrite testbitRepr n ((unsigned x) `bizOr` (unsigned y)) i zlei iltn in
  lorSpec (unsigned x) (unsigned y) i

bitsXor : (x, y : BizMod2 n) -> (i : Biz) -> 0 `Le` i -> i `Lt` toBizNat n -> testbit (x `xor` y) i = testbit x i `xor` testbit y i
bitsXor {n} x y i zlei iltn =
  rewrite testbitRepr n ((unsigned x) `bizXor` (unsigned y)) i zlei iltn in
  lxorSpec (unsigned x) (unsigned y) i
