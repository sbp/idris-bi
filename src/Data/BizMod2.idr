module Data.BizMod2

import Data.Util

import Data.Bip.AddMul
import Data.Bip.Iter
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.DivMod

%default total
%access public export

-- TODO move these to Biz and make modulus a synonym?

||| 2^n

bipPow2 : Nat -> Bip
bipPow2  Z    = U
bipPow2 (S k) = O (bipPow2 k)

bizPow2 : (x : Biz) -> Biz
bizPow2  BizO = BizP U
bizPow2 (BizP y) = BizP $ bipIter O 1 y
bizPow2 (BizM _) = BizO

||| Modulo 2^n

bipMod2Biz : (p : Bip) -> (n : Nat) -> Biz
bipMod2Biz  _     Z    = BizO
bipMod2Biz  U    (S _) = BizP U
bipMod2Biz (O a) (S k) = bizD (bipMod2Biz a k)
bipMod2Biz (I a) (S k) = bizDPO (bipMod2Biz a k)

bizMod2 : (x : Biz) -> (n : Nat) -> Biz
bizMod2  BizO    _ = BizO
bizMod2 (BizP a) n = bipMod2Biz a n
bizMod2 (BizM a) n = let r = bipMod2Biz a n in
                     if r==BizO then BizO
                             else bizMinus (BizP $ bipPow2 n) r

-- TODO add %static on `n` everywhere to minimize recalculation

modulus : (n : Nat) -> Biz
modulus = BizP . bipPow2

halfModulus : (n : Nat) -> Biz
halfModulus = bizDivTwo . modulus

maxUnsigned : (n : Nat) -> Biz
maxUnsigned = bizPred . modulus

maxSigned : (n : Nat) -> Biz
maxSigned = bizPred . halfModulus

minSigned : (n : Nat) -> Biz
minSigned = bizOpp . halfModulus

export
modulusPower : (n : Nat) -> modulus n = bizPow2 (toBizNat n)
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

export
MkBizMod2Inj : MkBizMod2 x rx = MkBizMod2 y ry -> x = y
MkBizMod2Inj Refl = Refl

export
bizMod2P0 : (x : BizMod2 0) -> x = MkBizMod2 0 (Refl, Refl)
bizMod2P0 (MkBizMod2  BizO    (Refl, Refl)) = Refl
bizMod2P0 (MkBizMod2 (BizP a) (_   , altu)) = absurd $ le1L a $ ltGt a U altu
bizMod2P0 (MkBizMod2 (BizM a) (altu, _   )) = absurd $ le1L a $ ltGt a U altu

bipMod2BizRange : (n : Nat) -> (p : Bip) -> (0 `Le` (p `bipMod2Biz` n), (p `bipMod2Biz` n) `Lt` modulus n)
bipMod2BizRange  Z     _    = (uninhabited, Refl)
bipMod2BizRange (S _)  U    = (uninhabited, Refl)
bipMod2BizRange (S k) (O a) =
  let (lo, hi) = bipMod2BizRange k a in
  ( rewrite bizDCompare 0 (a `bipMod2Biz` k) in
    lo
  , rewrite bizDCompare (a `bipMod2Biz` k) (modulus k) in
    hi
  )
bipMod2BizRange (S k) (I a) =
  let (lo, hi) = bipMod2BizRange k a in
  ( rewrite bizDDPOCompare 0 (a `bipMod2Biz` k) in
    case leLtOrEq 0 (a `bipMod2Biz` k) lo of
      Left lprf => rewrite lprf in
                   uninhabited
      Right rprf => rewrite sym rprf in
                    uninhabited
  , rewrite bizDPODCompare (a `bipMod2Biz` k) (modulus k) in
    rewrite hi in
    Refl
  )

export
bipMod2BizEq : (n : Nat) -> (p : Bip) -> bipMod2Biz p n = BizP p `bizMod` modulus n
bipMod2BizEq n p = let (y**prf) = aux n p
                       (zlemt, mtltmod) = bipMod2BizRange n p
                   in
                   snd $ divModPos (BizP p) (modulus n) y (p `bipMod2Biz` n) zlemt mtltmod prf
  where
  aux : (n : Nat) -> (p : Bip) -> (y ** BizP p = y * modulus n + (p `bipMod2Biz` n))
  aux  Z     p    = (BizP p ** cong $ sym $ mul1R p)
  aux (S _)  U    = (0 ** Refl)
  aux (S k) (O a) = let (y**prf) = aux k a in
                    (y ** rewrite doubleSpec (a `bipMod2Biz` k) in
                          rewrite mulAssoc y 2 (modulus k) in
                          rewrite mulComm y 2 in
                          rewrite sym $ mulAssoc 2 y (modulus k) in
                          rewrite sym $ mulAddDistrL 2 (y*(modulus k)) (a `bipMod2Biz` k) in
                          cong {f = bizMult 2} prf)
  aux (S k) (I a) = let (y**prf) = aux k a in
                    (y ** rewrite succDoubleSpec (a `bipMod2Biz` k) in
                          rewrite mulAssoc y 2 (modulus k) in
                          rewrite mulComm y 2 in
                          rewrite sym $ mulAssoc 2 y (modulus k) in
                          rewrite addAssoc (2*(y*(modulus k))) (2*(a `bipMod2Biz` k)) 1 in
                          rewrite sym $ mulAddDistrL 2 (y*(modulus k)) (a `bipMod2Biz` k) in
                          cong {f = \x => 2*x+1} prf)

bizMod2Range0 : (x : Biz) -> (n : Nat) -> (0 `Le` (x `bizMod2` n), (x `bizMod2` n) `Lt` modulus n)
bizMod2Range0  BizO    _ = (uninhabited, Refl)
bizMod2Range0 (BizP a) n = bipMod2BizRange n a
bizMod2Range0 (BizM a) n with ((a `bipMod2Biz` n) == 0) proof zprf
  | False =
    let (lo, hi) = bipMod2BizRange n a in
    ( rewrite compareAntisym ((modulus n)-(a `bipMod2Biz` n)) 0 in
      rewrite sym $ compareSub (modulus n) (a `bipMod2Biz` n) in
      rewrite compareAntisym (a `bipMod2Biz` n) (modulus n) in
      rewrite hi in
      uninhabited
    , case leLtOrEq 0 (a `bipMod2Biz` n) lo of
        Left lprf =>
          rewrite addCompareMonoL (modulus n) (-(a `bipMod2Biz` n)) 0 in
          rewrite sym $ compareOpp 0 (a `bipMod2Biz` n) in
          lprf
        Right rprf =>
          let pmodeq0 = eqbEqFro (a `bipMod2Biz` n) 0 $ sym rprf in
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

export
bizMod2Eq : (x : Biz) -> (n : Nat) -> x `bizMod2` n = x `bizMod` (modulus n)
bizMod2Eq  BizO    _ = Refl
bizMod2Eq (BizP a) n = bipMod2BizEq n a
bizMod2Eq (BizM a) n with (a `bipMod2Biz` n) proof pz
  | BizO =
    let
      deq = divEuclEq (BizM a) (modulus n) uninhabited
      pmodz = sym $ trans pz (bipMod2BizEq n a)
      divmod = divModPos (BizM a) (modulus n) ((BizM a) `bizDiv` (modulus n)) 0 uninhabited Refl $
               replace {P=\x => BizM a = (((BizM a) `bizDiv` (modulus n)) * (modulus n)) + (snd (bizDivEuclidHelp1 (fst (bipzDivEuclid a (modulus n))) x (modulus n)))} pmodz deq
    in
    snd divmod
  | BizP b =
    let
      deq = divEuclEq (BizM a) (modulus n) uninhabited
      bmodz = sym $ trans pz (bipMod2BizEq n a)
      divmod = divModPos (BizM a) (modulus n) ((BizM a) `bizDiv` (modulus n)) (bipMinusBiz (bipPow2 n) b)
             (rewrite sym $ compareSubR (BizP b) (modulus n) in
              ltLeIncl b (bipPow2 n) $
              replace {P = \x => x `Lt` modulus n} (sym pz) (snd $ bipMod2BizRange n a)
             )
             (rewrite compareSubR ((modulus n)-(BizP b)) (modulus n) in
              rewrite oppAddDistr (modulus n) (BizM b) in
              rewrite addAssoc (modulus n) (-modulus n) (BizP b) in
              rewrite posSubDiag (bipPow2 n) in
              Refl
             ) $
             replace {P=\x => BizM a = (((BizM a) `bizDiv` (modulus n)) * (modulus n)) + (snd (bizDivEuclidHelp1 (fst (bipzDivEuclid a (modulus n))) x (modulus n)))} bmodz deq
    in
    snd divmod
  | BizM b =
    let
      zlep = fst $ bipMod2BizRange n a
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

iwordsize : (n : Nat) -> BizMod2 n
iwordsize n = repr (toBizNat n) n

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
  negate x = repr (-unsigned x) n
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

-- aka logical right shift
shru : (x, y : BizMod2 n) -> BizMod2 n
shru {n} x y = repr ((unsigned x) `bizShiftR` (unsigned y)) n

-- aka arithmetic right shift
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

-- TODO should these change the word size?

zeroExt : (m : Biz) -> (x : BizMod2 n) -> BizMod2 n
zeroExt {n} m x = repr (bizZeroExt m (unsigned x)) n

signExt : (m : Biz) -> (x : BizMod2 n) -> BizMod2 n
signExt {n} m x = repr (bizSignExt m (unsigned x)) n

-- Decomposition of a number as a sum of powers of two.
-- TODO move to Biz?
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