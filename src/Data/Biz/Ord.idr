module Data.Biz.Ord

import Data.Util

import Data.Bip.AddMul
import Data.Bip.Iter
import Data.Bip.OrdSub

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Iter

%access export
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

neqbNeqTo : (n, m : Biz) -> n == m = False -> Not (n = m)
neqbNeqTo n m neq nm =
  absurd $ replace {P = \x => x = False} (eqbEqFro n m nm) neq

neqbNeqFro : (n, m : Biz) -> Not (n = m) -> n == m = False
neqbNeqFro n m neq with (n == m) proof nm
  | False = Refl
  | True  = absurd $ neq $ eqbEqTo n m $ sym nm

public export
Lt : (x, y : Biz) -> Type
Lt x y = x `compare` y = LT

public export
Gt : (x, y : Biz) -> Type
Gt x y = x `compare` y = GT

public export
Le : (x, y : Biz) -> Type
Le x y = Not (x `compare` y = GT)

public export
Ge : (x, y : Biz) -> Type
Ge x y = Not (x `compare` y = LT)

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

-- TODO look where it can be inserted
compareSubR : (n, m : Biz) -> n `compare` m = 0 `compare` (m-n)
compareSubR n m =
  rewrite compareAntisym (m-n) 0 in
  rewrite sym $ compareSub m n in
  compareAntisym m n

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

nltbLeTo : (n, m : Biz) -> m < n = False -> n `Le` m
nltbLeTo n m prf nm with (m `compare` n) proof mn
  | LT = absurd prf
  | EQ = absurd $ trans mn (gtLt n m nm)
  | GT = absurd $ trans mn (gtLt n m nm)

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

geGtOrEq : (x, y : Biz) -> x `Ge` y -> Either (x `Gt` y) (x=y)
geGtOrEq x y xgey with (x `compare` y) proof xy
  | LT = absurd $ xgey Refl
  | EQ = Right $ compareEqIffTo x y (sym xy)
  | GT = Left Refl

ltLeTotal : (p, q : Biz) -> Either (p `Lt` q) (q `Le` p)
ltLeTotal p q with (p `compare` q) proof pq
  | LT = Left Refl
  | EQ = Right $ rewrite compareAntisym p q in
                 rewrite sym pq in
                 uninhabited
  | GT = Right $ rewrite compareAntisym p q in
                 rewrite sym pq in
                 uninhabited

leAntisym : (x, y : Biz) -> x `Le` y -> y `Le` x -> x = y
leAntisym x y xley ylex =
  case leLtOrEq x y xley of
    Left xlty => absurd $ ylex $ ltGt x y xlty
    Right xy => xy

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

-- TODO look for places to use these
ltSucc : (x : Biz) -> x `Lt` bizSucc x
ltSucc x =
  rewrite addComm x 1 in
  rewrite addCompareMonoR 0 1 x in
  Refl

ltPred : (x : Biz) -> bizPred x `Lt` x
ltPred x =
  rewrite addComm x (-1) in
  rewrite addCompareMonoR (-1) 0 x in
  Refl

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

-- TODO rewrite as ltLeTrans below
leLtTrans : (p, q, r : Biz) -> p `Le` q -> q `Lt` r -> p `Lt` r
leLtTrans p q r pleq qltr with (p `compare` q) proof pq
  | LT = ltTrans p q r (sym pq) qltr
  | EQ = rewrite compareEqIffTo p q (sym pq) in
         qltr
  | GT = absurd $ pleq Refl

ltLeTrans : (p, q, r : Biz) -> p `Lt` q -> q `Le` r -> p `Lt` r
ltLeTrans p q r pltq qler =
  case leLtOrEq q r qler of
    Left qltr => ltTrans p q r pltq qltr
    Right qeqr => rewrite sym qeqr in pltq

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

ltNotEq : (x, y : Biz) -> y `Lt` x -> Not (x=y)
ltNotEq x y yltx xy =
  absurd $ replace {P=\z=>z=LT} (compareEqIffFro y x (sym xy)) yltx

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

leSuccLTo : (p, q : Biz) -> bizSucc p `Le` q -> p `Lt` q
leSuccLTo p q spleq =
  trans (sym $ addCompareMonoR p q 1) (ltSuccRFro (bizSucc p) q spleq)

leSuccLFro : (p, q : Biz) -> p `Lt` q -> bizSucc p `Le` q
leSuccLFro p q pltq =
  ltSuccRTo (bizSucc p) q $
  rewrite addCompareMonoR p q 1 in
  pltq

ltPredLTo : (n, m : Biz) -> n `Le` m -> bizPred n `Lt` m
ltPredLTo n m nlem =
  ltPredRFro (bizPred n) m $
  rewrite addCompareMonoR n m (-1) in
  nlem

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

leRefl : (x : Biz) -> x `Le` x
leRefl x = rewrite compareEqIffFro x x Refl in
           uninhabited

-- TODO look where else this can be applied
leSuccR : (x, y : Biz) -> x `Le` y -> x `Le` bizSucc y
leSuccR x y xley =
  leTrans x y (bizSucc y) xley $
  rewrite addComm y 1 in
  rewrite addCompareMonoR 0 1 y in
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

leNeqLt : (x, y : Biz) -> y `Le` x -> Not (x=y) -> y `Lt` x
leNeqLt x y ylex nxy =
  case leLtOrEq y x ylex of
    Left yltx => yltx
    Right xy => absurd $ nxy $ sym xy

-- TODO can't put the following in Iter because of cycle (we use biInduction for ltTrans)
natlikeInd : (P : Biz -> Type) -> (f0 : P BizO)
          -> ((y : Biz) -> 0 `Le` y -> P y -> P (bizSucc y))
          -> (x : Biz) -> 0 `Le` x -> P x
natlikeInd _ f0 _  BizO    _    = f0
natlikeInd P f0 f (BizP a) zlex =
  peanoRect (P . BizP) (f 0 uninhabited f0) (\p => rewrite sym $ add1R p in
                                                   f (BizP p) uninhabited) a
natlikeInd _ _  _ (BizM _) zlex = absurd $ zlex Refl

iterBaseZ : (f : a -> a) -> (n : Biz) -> (x : a) -> n `Le` 0 -> bizIter f n x = x
iterBaseZ _  BizO    _ _    = Refl
iterBaseZ _ (BizP _) _ nle0 = absurd $ nle0 Refl
iterBaseZ _ (BizM _) _ _    = Refl

iterSuccZ : (f : a -> a) -> (n : Biz) -> (x : a) -> 0 `Le` n -> bizIter f (bizSucc n) x = f (bizIter f n x)
iterSuccZ f  BizO    x zlen = Refl
iterSuccZ f (BizP p) x zlen = rewrite add1R p in
                             iterSucc f x p
iterSuccZ f (BizM _) x zlen = absurd $ zlen Refl

natlikeIndM : (P : Biz -> Type) -> (f0 : P BizO)
         -> ((y : Biz) -> y `Le` 0 -> P y)
         -> ((y : Biz) -> 0 `Le` y -> P y -> P (bizSucc y))
         -> (x : Biz) -> P x
natlikeIndM P f0 fM fP x =
  case ltLeTotal x 0 of
    Left xlt0 => fM x (ltLeIncl x 0 xlt0)
    Right zlex => natlikeInd P f0 fP x zlex