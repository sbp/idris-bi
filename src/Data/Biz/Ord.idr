module Data.Biz.Ord

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Iter

%access public export
%default total

-- Specification of comparisons and order

-- eqb_eq

-- TODO split into `to` and `fro`

eqbEqTo : (n, m : Biz) -> n == m = True -> n = m
eqbEqTo  BizO     BizO    = const Refl
eqbEqTo  BizO    (BizP _) = absurd
eqbEqTo  BizO    (BizM _) = absurd
eqbEqTo (BizP _)  BizO    = absurd
eqbEqTo (BizP a) (BizP b) = cong . eqbEqTo a b
eqbEqTo (BizP _) (BizM _) = absurd
eqbEqTo (BizM _)  BizO    = absurd
eqbEqTo (BizM _) (BizP _) = absurd
eqbEqTo (BizM a) (BizM b) = cong . eqbEqTo a b

eqbEqFro : (n, m : Biz) -> n = m -> n == m = True
eqbEqFro  BizO     BizO    = const Refl
eqbEqFro  BizO    (BizP _) = absurd
eqbEqFro  BizO    (BizM _) = absurd
eqbEqFro (BizP _)  BizO    = absurd
eqbEqFro (BizP a) (BizP b) = eqbEqFro a b . bizPInj
eqbEqFro (BizP _) (BizM _) = absurd
eqbEqFro (BizM _)  BizO    = absurd
eqbEqFro (BizM _) (BizP _) = absurd
eqbEqFro (BizM a) (BizM b) = eqbEqFro a b . bizMInj

Lt : (x, y : Biz) -> Type
Lt x y = x `compare` y = LT

Gt : (x, y : Biz) -> Type
Gt x y = x `compare` y = GT

Le : (x, y : Biz) -> Type
Le x y = Not (x `compare` y = GT)

Ge : (x, y : Biz) -> Type
Ge x y = Not (x `compare` y = LT)

-- ltb_lt

-- TODO split into `to` and `fro`

ltbLtTo : (n, m : Biz) -> n < m = True -> n `Lt` m
ltbLtTo n m prf with (n `compare` m)
  | LT = Refl
  | EQ = absurd prf
  | GT = absurd prf

ltbLtFro : (n, m : Biz) -> n `Lt` m -> n < m = True
ltbLtFro _ _ nltm = rewrite nltm in
                    Refl

-- leb_le

-- TODO split into `to` and `fro`

ngtbLeTo : (n, m : Biz) -> n > m = False -> n `Le` m
ngtbLeTo n m prf nm with (n `compare` m)
  | LT = absurd nm
  | EQ = absurd nm
  | GT = absurd prf

ngtbLeFro : (n, m : Biz) -> n `Le` m -> n > m = False
ngtbLeFro n m nlem with (n `compare` m)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ nlem Refl

ltLeIncl : (n, m : Biz) -> n `Lt` m -> n `Le` m
ltLeIncl n m nltm ngtm with (n `compare` m)
  | LT = uninhabited ngtm
  | EQ = uninhabited ngtm
  | GT = uninhabited nltm

-- compare_eq_iff
-- TODO split into `to` and `fro`

compareEqIffTo : (n, m : Biz) -> n `compare` m = EQ -> n = m
compareEqIffTo  BizO     BizO    = const Refl
compareEqIffTo  BizO    (BizP _) = absurd
compareEqIffTo  BizO    (BizM _) = absurd
compareEqIffTo (BizP _)  BizO    = absurd
compareEqIffTo (BizP a) (BizP b) = cong . compareEqIffTo a b
compareEqIffTo (BizP _) (BizM _) = absurd
compareEqIffTo (BizM _)  BizO    = absurd
compareEqIffTo (BizM _) (BizP _) = absurd
compareEqIffTo (BizM a) (BizM b) = sym . cong . compareEqIffTo b a

compareEqIffFro : (n, m : Biz) -> n = m -> n `compare` m = EQ
compareEqIffFro  BizO     BizO    = const Refl
compareEqIffFro  BizO    (BizP _) = absurd
compareEqIffFro  BizO    (BizM _) = absurd
compareEqIffFro (BizP _)  BizO    = absurd
compareEqIffFro (BizP a) (BizP b) = compareEqIffFro a b . bizPInj
compareEqIffFro (BizP _) (BizM _) = absurd
compareEqIffFro (BizM _)  BizO    = absurd
compareEqIffFro (BizM _) (BizP _) = absurd
compareEqIffFro (BizM a) (BizM b) = compareEqIffFro b a . bizMInj . sym

-- compare_sub

compareSub : (n, m : Biz) -> n `compare` m = (n - m) `compare` 0
compareSub  BizO     BizO    = Refl
compareSub  BizO    (BizP _) = Refl
compareSub  BizO    (BizM _) = Refl
compareSub (BizP _)  BizO    = Refl
compareSub (BizP a) (BizP b) = rewrite posSubSpec a b in
                               aux
  where
  aux : a `compare` b = (posSubSpecHelp a b (a `compare` b)) `compare` 0
  aux with (a `compare` b)
    | LT = Refl
    | EQ = Refl
    | GT = Refl
compareSub (BizP _) (BizM _) = Refl
compareSub (BizM _)  BizO    = Refl
compareSub (BizM _) (BizP _) = Refl
compareSub (BizM a) (BizM b) = rewrite posSubSpec b a in
                               aux
  where
  aux : b `compare` a = (posSubSpecHelp b a (b `compare` a)) `compare` 0
  aux with (b `compare` a)
    | LT = Refl
    | EQ = Refl
    | GT = Refl

-- compare_antisym

compareAntisym : (n, m : Biz) -> m `compare` n = compareOp (n `compare` m)
compareAntisym  BizO     BizO    = Refl
compareAntisym  BizO    (BizP _) = Refl
compareAntisym  BizO    (BizM _) = Refl
compareAntisym (BizP _)  BizO    = Refl
compareAntisym (BizP a) (BizP b) = compareAntisym a b
compareAntisym (BizP _) (BizM _) = Refl
compareAntisym (BizM _)  BizO    = Refl
compareAntisym (BizM _) (BizP _) = Refl
compareAntisym (BizM a) (BizM b) = compareAntisym b a

-- Comparison and opposite
-- compare_opp
compareOpp : (n, m : Biz) -> n `compare` m = (-m) `compare` (-n)
compareOpp n m =
  rewrite compareSub n m in
  rewrite compareSub (-m) (-n) in
  rewrite oppInvolutive n in
  rewrite addComm n (-m) in
  Refl

-- gt_lt

gtLt : (p, q : Biz) -> p `Gt` q -> q `Lt` p
gtLt p q pgtq =
  rewrite compareAntisym p q in
  rewrite pgtq in
  Refl

-- lt_gt

ltGt : (p, q : Biz) -> p `Lt` q -> q `Gt` p
ltGt p q pltq =
  rewrite compareAntisym p q in
  rewrite pltq in
  Refl

-- ge_le

geLe : (n, m : Biz) -> n `Ge` m -> m `Le` n
geLe n m ngem = rewrite compareAntisym n m in
                aux
  where
  aux : Not (compareOp (n `compare` m) = GT)
  aux prf with (n `compare` m)
    | LT = ngem Refl
    | EQ = uninhabited prf
    | GT = ngem $ sym prf

-- le_ge

leGe : (n, m : Biz) -> n `Le` m -> m `Ge` n
leGe n m nlem = rewrite compareAntisym n m in
                aux
  where
  aux : Not (compareOp (n `compare` m) = LT)
  aux prf with (n `compare` m)
    | LT = nlem $ sym prf
    | EQ = uninhabited prf
    | GT = nlem Refl

-- compare_lt_iff is trivial
-- compare_le_iff is trivial

-- Some more advanced properties of comparison and orders, including
-- [compare_spec] and [lt_irrefl] and [lt_eq_cases].

mulCompareMonoL : (p, q, r : Biz) -> 0 `Lt` p -> (p*q) `compare` (p*r) = q `compare` r
mulCompareMonoL  BizO     _        _       zltp = absurd zltp
mulCompareMonoL (BizM _)  _        _       zltp = absurd zltp
mulCompareMonoL (BizP _)  BizO     BizO    _    = Refl
mulCompareMonoL (BizP _)  BizO    (BizP _) _    = Refl
mulCompareMonoL (BizP _)  BizO    (BizM _) _    = Refl
mulCompareMonoL (BizP _) (BizP _)  BizO    _    = Refl
mulCompareMonoL (BizP a) (BizP b) (BizP c) _    = mulCompareMonoL a b c
mulCompareMonoL (BizP _) (BizP _) (BizM _) _    = Refl
mulCompareMonoL (BizP _) (BizM _)  BizO    _    = Refl
mulCompareMonoL (BizP _) (BizM _) (BizP _) _    = Refl
mulCompareMonoL (BizP a) (BizM b) (BizM c) _    = mulCompareMonoL a c b

-- Remaining specification of [lt] and [le]

leLtOrEq : (x, y : Biz) -> x `Le` y -> Either (x `Lt` y) (x=y)
leLtOrEq x y xley with (x `compare` y) proof xy
  | LT = Left Refl
  | EQ = Right $ compareEqIffTo x y (sym xy)
  | GT = absurd $ xley Refl

-- lt_succ_r
-- TODO split into `to` and `fro`

ltSuccRTo : (n, m : Biz) -> n `Lt` bizSucc m -> n `Le` m
ltSuccRTo n m =
  rewrite compareSub n (m+1) in
  rewrite subSuccR n m in
  rewrite compareSub n m in
  aux
  where
  aux : (n-m)-1 `Lt` 0 -> n-m `Gt` 0 -> Void
  aux nm1lt0 nmgt0 with (n-m)
    | BizO       = absurd nmgt0
    | BizP  U    = absurd nm1lt0
    | BizP (O _) = absurd nm1lt0
    | BizP (I _) = absurd nm1lt0
    | BizM  _    = absurd nmgt0

ltSuccRFro : (n, m : Biz) -> n `Le` m -> n `Lt` bizSucc m
ltSuccRFro n m =
  rewrite compareSub n (m+1) in
  rewrite subSuccR n m in
  rewrite compareSub n m in
  aux
  where
  aux : n-m `Le` 0 -> (n-m)-1 `Lt` 0
  aux nmle0 with (n-m)
    | BizO   = Refl
    | BizP _ = absurd $ nmle0 Refl
    | BizM _ = Refl

-- Specification of minimum and maximum

--max_l

maxL : (n, m : Biz) -> m `Le` n -> n `max` m = n
maxL n m mlen = rewrite compareAntisym m n in
                aux
  where
  aux : bizMinMaxHelp n m (compareOp (m `compare` n)) = n
  aux with (m `compare` n)
    | LT = Refl
    | EQ = Refl
    | GT = absurd $ mlen Refl

-- max_r

maxR : (n, m : Biz) -> n `Le` m -> n `max` m = m
maxR n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = compareEqIffTo n m $ sym nm
  | GT = absurd $ nlem Refl

-- min_l

minL : (n, m : Biz) -> n `Le` m -> n `min` m = n
minL n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = sym $ compareEqIffTo n m $ sym nm
  | GT = absurd $ nlem Refl

-- min_r

minR : (n, m : Biz) -> m `Le` n -> n `min` m = m
minR n m mlen = rewrite compareAntisym m n in
                aux
  where
  aux : bizMinMaxHelp m n (compareOp (m `compare` n)) = m
  aux with (m `compare` n)
    | LT = Refl
    | EQ = Refl
    | GT = absurd $ mlen Refl

-- Specification of absolute value

absNonneg : (a : Biz) -> 0 `Le` abs a
absNonneg  BizO    = uninhabited
absNonneg (BizP _) = uninhabited
absNonneg (BizM _) = uninhabited

absOpp : (n : Biz) -> abs (-n) = abs n
absOpp  BizO    = Refl
absOpp (BizP _) = Refl
absOpp (BizM _) = Refl

-- abs_eq

absEq : (n : Biz) -> 0 `Le` n -> abs n = n
absEq  BizO    _    = Refl
absEq (BizP _) _    = Refl
absEq (BizM _) zlen = absurd $ zlen Refl

-- abs_neq

absNeq : (n : Biz) -> n `Le` 0 -> abs n = -n
absNeq  BizO    _    = Refl
absNeq (BizP _) nle0 = absurd $ nle0 Refl
absNeq (BizM _) _    = Refl

-- Specification of sign

-- sgn_null n

sgnNull : (n : Biz) -> n = 0 -> bizSign n = 0
sgnNull  BizO    = const Refl
sgnNull (BizP _) = absurd
sgnNull (BizM _) = absurd

-- sgn_pos

sgnPos : (n : Biz) -> 0 `Lt` n -> bizSign n = 1
sgnPos  BizO    = absurd
sgnPos (BizP _) = const Refl
sgnPos (BizM _) = absurd

-- sgn_neg

sgnNeg : (n : Biz) -> n `Lt` 0 -> bizSign n = -1
sgnNeg  BizO    = absurd
sgnNeg (BizP _) = absurd
sgnNeg (BizM _) = const Refl

-- Comparison and addition
-- add_compare_mono_l
addCompareMonoL : (n, m, p : Biz) -> (n + m) `compare` (n + p) = m `compare` p
addCompareMonoL n m p =
  rewrite compareSub (n+m) (n+p) in
  rewrite oppAddDistr n p in
  rewrite addAssoc (n+m) (-n) (-p) in
  rewrite addComm (n+m) (-n) in
  rewrite addAssoc (-n) n m in
  rewrite addOppDiagL n in
  sym $ compareSub m p

addCompareMonoR : (n, m, p : Biz) -> (n + p) `compare` (m + p) = n `compare` m
addCompareMonoR n m p =
  rewrite addComm n p in
  rewrite addComm m p in
  addCompareMonoL p n m

ltTrans : (p, q, r : Biz) -> p `Lt` q -> q `Lt` r -> p `Lt` r
ltTrans p q r =
  biInduction
    (\x => (s, t : Biz) -> s `Lt` t -> t `Lt` x -> s `Lt` x)
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
    (\x,prf,s,t,sltt,tltx =>
      let tltsx = ltSuccRFro t x $ ltLeIncl t x tltx
          slex = ltSuccRTo s x $ prf s t sltt tltsx
      in
      case leLtOrEq s x slex of
        Left sltx => sltx
        Right seqx =>
          let xltt = replace {P=\x=>x `Lt` t} seqx sltt
              xget = leGe t x $ ltLeIncl t x tltx in
          absurd $ xget xltt
    )
    r p q
  where
  base : (n, m : Biz) -> n `Lt` m -> m `Lt` 0 -> n `Lt` 0
  base  _        BizO    _    mltz = absurd mltz
  base  _       (BizP _) _    mltz = absurd mltz
  base  BizO    (BizM _) nltm _    = absurd nltm
  base (BizP _) (BizM _) nltm _    = absurd nltm
  base (BizM _) (BizM _) _    _    = Refl

leLtTrans : (p, q, r : Biz) -> p `Le` q -> q `Lt` r -> p `Lt` r
leLtTrans p q r pleq qltr with (p `compare` q) proof pq
  | LT = ltTrans p q r (sym pq) qltr
  | EQ = rewrite compareEqIffTo p q (sym pq) in
         qltr
  | GT = absurd $ pleq Refl

leTrans : (p, q, r : Biz) -> p `Le` q -> q `Le` r -> p `Le` r
leTrans p q r pleq qler pgtr with (q `compare` r) proof qr
  | LT = uninhabited $ the (GT=LT) $
           rewrite sym pgtr in
           leLtTrans p q r pleq (sym qr)
  | EQ = pleq $ rewrite compareEqIffTo q r (sym qr) in
                pgtr
  | GT = absurd $ qler Refl

-- TODO can't move to AddSubMul because of resulting cyclic dependency

-- mul_reg_l

mulRegL : (n, m, p : Biz) -> Not (p = 0) -> p * n = p * m -> n = m
mulRegL n m p pnz prf with (p `compare` 0) proof pz
  | LT =    compareEqIffFro (p*n) (p*m) prf
         |> replace {P=\x=>x=EQ}                      (compareOpp (p*n) (p*m))
         |> replace {P=\x=>(-(p*m)) `compare` x = EQ} (sym $ mulOppL p n)
         |> replace {P=\x=>x `compare` ((-p)*n) = EQ} (sym $ mulOppL p m)
         |> replace {P=\x=>x=EQ}                      (mulCompareMonoL (-p) m n $
                                                         rewrite compareOpp 0 (-p) in
                                                         rewrite oppInvolutive p in
                                                         sym pz)
         |> compareEqIffTo m n
         |> sym
  | EQ = absurd $ pnz $ compareEqIffTo p 0 $ sym pz
  | GT =    compareEqIffFro (p*n) (p*m) prf
         |> replace {P=\x=>x=EQ} (mulCompareMonoL p n m $ gtLt p 0 $ sym pz)
         |> compareEqIffTo n m

-- mul_reg_r

mulRegR : (n, m, p : Biz) -> Not (p = 0) -> n * p = m * p -> n = m
mulRegR n m p =
  rewrite mulComm n p in
  rewrite mulComm m p in
  mulRegL n m p
