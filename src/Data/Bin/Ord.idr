module Data.Bin.Ord

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub

import Data.Bin
import Data.Bin.Iter
import Data.Bin.AddSubMul

%access public export
%default total

-- Specification of boolean comparisons (using <->)

-- eqb_eq
-- TODO split into `to` and `fro`
eqbEqTo : (p, q : Bin) -> p == q = True -> p = q
eqbEqTo  BinO     BinO    = const Refl
eqbEqTo  BinO    (BinP a) = absurd
eqbEqTo (BinP a)  BinO    = absurd
eqbEqTo (BinP a) (BinP b) = cong . eqbEqTo a b

eqbEqFro : (p, q : Bin) -> p = q -> p == q = True
eqbEqFro  BinO     BinO    _   = Refl
eqbEqFro  BinO    (BinP _) Refl impossible
eqbEqFro (BinP _)  BinO    Refl impossible
eqbEqFro (BinP a) (BinP b) prf = eqbEqFro a b (binPInj prf)

Lt : (x, y : Bin) -> Type
Lt x y = x `compare` y = LT

Gt : (x, y : Bin) -> Type
Gt x y = x `compare` y = GT

Le : (x, y : Bin) -> Type
Le x y = Not (x `compare` y = GT)

Ge : (x, y : Bin) -> Type
Ge x y = Not (x `compare` y = LT)

zeroLt1 : (n : Bin) -> n `Lt` 1 -> n = 0
zeroLt1  BinO    Refl = Refl
zeroLt1 (BinP a) nlt1 = absurd $ nlt1R a $ nlt1

-- ltb_lt
-- TODO split into `to` and `fro`

ltbLtTo : (p, q : Bin) -> p < q = True -> p `Lt` q
ltbLtTo p q prf with (p `compare` q)
  | LT = Refl
  | EQ = absurd prf
  | GT = absurd prf

ltbLtFro : (p, q : Bin) -> p `Lt` q -> p < q = True
ltbLtFro _ _ pltq = rewrite pltq in Refl

-- leb_le
-- TODO split into `to` and `fro`

lebLeTo : (p, q : Bin) -> p > q = False -> p `Le` q
lebLeTo p q prf pq with (p `compare` q)
  | LT = absurd pq
  | EQ = absurd pq
  | GT = absurd prf

lebLeFro : (p, q : Bin) -> p `Le` q -> p > q = False
lebLeFro p q pleq with (p `compare` q)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ pleq Refl

-- Basic properties of comparison (using <->)

compareSuccSucc : (n, m : Bin) -> binSucc n `compare` binSucc m = n `compare` m
compareSuccSucc  BinO     BinO    = Refl
compareSuccSucc  BinO    (BinP a) = lt1Succ a
compareSuccSucc (BinP a)  BinO    = ltGt U (bipSucc a) $ lt1Succ a
compareSuccSucc (BinP a) (BinP b) = compareSuccSucc a b

-- compare_eq_iff
-- TODO split into `to` and `fro`

compareEqIffTo : (p, q : Bin) -> p `compare` q = EQ -> p = q
compareEqIffTo  BinO     BinO    = const Refl
compareEqIffTo  BinO    (BinP _) = absurd
compareEqIffTo (BinP _)  BinO    = absurd
compareEqIffTo (BinP a) (BinP b) = cong . compareEqIffTo a b

compareEqIffFro : (p, q : Bin) -> p = q -> p `compare` q = EQ
compareEqIffFro  BinO     BinO    = const Refl
compareEqIffFro  BinO    (BinP _) = absurd
compareEqIffFro (BinP _)  BinO    = absurd
compareEqIffFro (BinP a) (BinP b) = compareEqIffFro a b . binPInj

-- compare_lt_iff is trivial

-- compare_le_iff is trivial

-- compare_antisym

compareAntisym : (p, q : Bin) -> q `compare` p = compareOp (p `compare` q)
compareAntisym  BinO     BinO    = Refl
compareAntisym  BinO    (BinP _) = Refl
compareAntisym (BinP _)  BinO    = Refl
compareAntisym (BinP a) (BinP b) = compareAntisym a b

-- Some more advanced properties of comparison and orders

dpoLt : (a, b : Bin) -> binDPO a `Lt` b -> binD a `Lt` b
dpoLt  BinO     BinO    = absurd
dpoLt  BinO    (BinP _) = const Refl
dpoLt (BinP _)  BinO    = absurd
dpoLt (BinP a) (BinP b) = leSuccLTo (O a) b . ltLeIncl (I a) b

ltLeIncl : (n, m : Bin) -> n `Lt` m -> n `Le` m
ltLeIncl n m nltm ngtm with (n `compare` m)
  | LT = uninhabited ngtm
  | EQ = uninhabited ngtm
  | GT = uninhabited nltm

ltGt : (p, q : Bin) -> p `Lt` q -> q `Gt` p
ltGt p q pltq =
  rewrite compareAntisym p q in
  rewrite pltq in
  Refl

gtLt : (p, q : Bin) -> p `Gt` q -> q `Lt` p
gtLt p q pgtq =
  rewrite compareAntisym p q in
  rewrite pgtq in
  Refl

-- le_0_l

leZeroL : (a : Bin) -> BinO `Le` a
leZeroL  BinO    = uninhabited
leZeroL (BinP _) = uninhabited

-- leb_spec

-- TODO move to Bip.Proofs?

gtNotEqP : (p, q : Bip) -> p `Gt` q -> p == q = False
gtNotEqP  U     U    = absurd
gtNotEqP  U    (O _) = absurd
gtNotEqP  U    (I _) = absurd
gtNotEqP (O _)  U    = const Refl
gtNotEqP (O a) (O b) = gtNotEqP a b
gtNotEqP (O a) (I b) = const Refl
gtNotEqP (I _)  U    = const Refl
gtNotEqP (I a) (O b) = const Refl
gtNotEqP (I a) (I b) = gtNotEqP a b

gtNotEqN : (p, q : Bin) -> p `Gt` q -> p == q = False
gtNotEqN  BinO     BinO    = absurd
gtNotEqN  BinO    (BinP _) = absurd
gtNotEqN (BinP _)  BinO    = const Refl
gtNotEqN (BinP a) (BinP b) = gtNotEqP a b

-- add_lt_cancel_l

addLtCancelL : (p, q, r : Bin) -> r+p `Lt` r+q -> p `Lt` q
addLtCancelL  p        q        BinO    = rewrite addZeroL p in
                                          rewrite addZeroL q in
                                          id
addLtCancelL  BinO     BinO    (BinP c) = rewrite compareContRefl c EQ in
                                          absurd
addLtCancelL  BinO    (BinP _) (BinP _) = const Refl
addLtCancelL (BinP a)  BinO    (BinP c) = absurd . ltNotAddL c a
addLtCancelL (BinP a) (BinP b) (BinP c) = addLtMonoLFro c a b

-- sub_add

subAdd : (p, q : Bin) -> p `Le` q -> (q-p)+p = q
subAdd  BinO     BinO    _    = Refl
subAdd  BinO    (BinP _) _    = Refl
subAdd (BinP _)  BinO    pleq = absurd $ pleq Refl
subAdd (BinP a) (BinP b) pleq = case subMaskSpec a b of
  SubIsNul     Refl _ => rewrite subMaskDiag a in
                         Refl
  SubIsPos {r} Refl _ => absurd $ pleq $ ltGt b (b+r) $ ltAddDiagR b r
  SubIsNeg {r} Refl _ => rewrite subMaskAddDiagL a r in
                         rewrite addComm a r in
                         Refl

-- Specification of lt and le

-- lt_succ_r

-- TODO split into `to` and `fro`

ltSuccRTo : (p, q : Bin) -> p `Lt` binSucc q -> p `Le` q
ltSuccRTo  BinO     BinO    Refl  = uninhabited
ltSuccRTo  BinO    (BinP _) Refl  = uninhabited
ltSuccRTo (BinP a)  BinO    pltsq = absurd $ nlt1R a pltsq
ltSuccRTo (BinP a) (BinP b) pltsq = ltSuccRTo a b pltsq

ltSuccRFro : (p, q : Bin) -> p `Le` q -> p `Lt` binSucc q
ltSuccRFro  BinO     BinO    pleq = Refl
ltSuccRFro  BinO    (BinP _) pleq = Refl
ltSuccRFro (BinP _)  BinO    pleq = absurd $ pleq Refl
ltSuccRFro (BinP a) (BinP b) pleq = ltSuccRFro a b pleq

succLePos : (x, y : Bin) -> binSucc x `Le` y -> (a ** y = BinP a)
succLePos x  BinO    sxley = absurd $ sxley $ ltGt 0 (binSucc x) $ ltSuccRFro 0 x $ leZeroL x
succLePos _ (BinP a) _     = (a**Refl)

leSuccLTo : (p, q : Bin) -> binSucc p `Le` q -> p `Lt` q
leSuccLTo  BinO     BinO    prf = absurd $ prf Refl
leSuccLTo  BinO    (BinP _) _   = Refl
leSuccLTo (BinP _)  BinO    prf = absurd $ prf Refl
leSuccLTo (BinP a) (BinP b) prf = leSuccLTo a b prf

leSuccLFro : (p, q : Bin) -> p `Lt` q -> binSucc p `Le` q
leSuccLFro  BinO     BinO    = absurd
leSuccLFro  BinO    (BinP b) = const $ le1L b
leSuccLFro (BinP _)  BinO    = absurd
leSuccLFro (BinP a) (BinP b) = leSuccLFro a b

-- succ_double_lt

succDoubleLt : (n, m : Bin) -> n `Lt` m -> binDPO n `Lt` binD m
succDoubleLt  BinO     BinO    = absurd
succDoubleLt  BinO    (BinP _) = const Refl
succDoubleLt (BinP _)  BinO    = absurd
succDoubleLt (BinP a) (BinP b) = compareContGtLtFro a b

leLtOrEq : (x, y : Bin) -> x `Le` y -> Either (x `Lt` y) (x=y)
leLtOrEq x y xley with (x `compare` y) proof xy
  | LT = Left Refl
  | EQ = Right $ compareEqIffTo x y (sym xy)
  | GT = absurd $ xley Refl

ltTrans : (p, q, r : Bin) -> p `Lt` q -> q `Lt` r -> p `Lt` r
ltTrans p q r =
  peanoRect
    (\x => (s, t : Bin) -> s `Lt` t -> t `Lt` x -> s `Lt` x)
    base
    (\x,prf,s,t,sltt,tltsx =>
      case leLtOrEq t x $ ltSuccRTo t x tltsx of
        Left tltx =>
          ltSuccRFro s x $
          ltLeIncl s x $
          prf s t sltt tltx
        Right teqx =>
          rewrite sym teqx in
          ltSuccRFro s t $
          ltLeIncl s t sltt
    )
    r p q
    where
    base : (n, m : Bin) -> n `Lt` m -> m `Lt` 0 -> n `Lt` 0
    base  _        BinO    _    mltz = absurd mltz
    base  _       (BinP _) _    mltz = absurd mltz

-- Specification of minimum and maximum

-- min_l

minL : (n, m : Bin) -> n `Le` m -> min n m = n
minL n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = sym $ compareEqIffTo n m $ sym nm
  | GT = absurd $ nlem Refl

-- min_r

minR : (n, m : Bin) -> m `Le` n -> min n m = m
minR n m mlen with (m `compare` n) proof mn
  | LT = rewrite compareAntisym m n in
         rewrite sym mn in
         Refl
  | EQ = rewrite compareAntisym m n in
         rewrite sym mn in
         Refl
  | GT = absurd $ mlen Refl

-- max_l

maxL : (n, m : Bin) -> m `Le` n -> max n m = n
maxL n m mlen with (m `compare` n) proof mn
  | LT = rewrite compareAntisym m n in
         rewrite sym mn in
         Refl
  | EQ = rewrite compareAntisym m n in
         rewrite sym mn in
         compareEqIffTo m n $ sym mn
  | GT = absurd $ mlen Refl

-- max_r

maxR : (n, m : Bin) -> n `Le` m -> max n m = m
maxR n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ nlem Refl

-- 0 is the least natural number

-- compare_0_r

compare0R : (n : Bin) -> Not (n `Lt` 0)
compare0R  BinO    = uninhabited
compare0R (BinP _) = uninhabited

-- ge_le

geLe : (n, m : Bin) -> n `Ge` m -> m `Le` n
geLe n m ngem = rewrite compareAntisym n m in
                aux
  where
  aux : Not (compareOp (n `compare` m) = GT)
  aux prf with (n `compare` m)
    | LT = ngem Refl
    | EQ = uninhabited prf
    | GT = ngem $ sym prf

-- le_ge

leGe : (n, m : Bin) -> n `Le` m -> m `Ge` n
leGe n m nlem = rewrite compareAntisym n m in
                aux
  where
  aux : Not (compareOp (n `compare` m) = LT)
  aux prf with (n `compare` m)
    | LT = nlem $ sym prf
    | EQ = uninhabited prf
    | GT = nlem Refl
