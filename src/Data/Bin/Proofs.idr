module Data.Bin.Proofs

import Data.Bin
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub

%access public export
%default total

-- Following NArith/BinNat.v

-- Peano induction

-- peano_rect

peanoRect : (P : Bin -> Type) -> (f0 : P BinO) ->
            (f: (n : Bin) -> P n -> P (binSucc n)) ->
            (n : Bin) -> P n
peanoRect _ f0 _  BinO    = f0
peanoRect P f0 f (BinP a) = peanoRect (P . BinP) (f BinO f0) (\p => f $ BinP p) a

-- peano_rect_base is trivial

-- TODO
-- peano_rect_succ
-- peano_rec_base
-- peano_rec_succ

-- Properties of mixed successor and predecessor

-- pos_pred_spec
posPredSpec : (a : Bip) -> bipPredBin a = binPred (BinP a)
posPredSpec  U    = Refl
posPredSpec (O _) = Refl
posPredSpec (I _) = Refl

-- succ_pos_spec
succPosSpec : (a : Bin) -> BinP (binSuccBip a) = binSucc a
succPosSpec  BinO    = Refl
succPosSpec (BinP _) = Refl

-- pos_pred_succ
posPredSucc : (a : Bin) -> bipPredBin (binSuccBip a) = a
posPredSucc  BinO     = Refl
posPredSucc (BinP a') = rewrite predBinSucc a' in Refl

-- succ_pos_pred
succPosPred : (a : Bip) -> binSucc (bipPredBin a) = BinP a
succPosPred  U     = Refl
succPosPred (O a') = rewrite succPredDouble a' in Refl
succPosPred (I _ ) = Refl

-- Properties of successor and predecessor

-- pred_succ
predSucc : (a : Bin) -> binPred (binSucc a) = a
predSucc  BinO     = Refl
predSucc (BinP a') = rewrite predBinSucc a' in Refl

-- pred_sub
predSub : (a : Bin) -> binPred a = a-(BinP U)
predSub  BinO         = Refl
predSub (BinP  U    ) = Refl
predSub (BinP (O a')) = Refl
predSub (BinP (I a')) = Refl

-- succ_0_discr
succZeroDiscr : (a : Bin) -> Not (binSucc a = 0)
succZeroDiscr  BinO     = uninhabited
succZeroDiscr (BinP a') = uninhabited

-- Specification of addition

-- add_0_l
addZeroL : (a : Bin) -> BinO + a = a
addZeroL  BinO    = Refl
addZeroL (BinP _) = Refl

-- add_succ_l
addSuccL : (a, b : Bin) -> (binSucc a) + b = binSucc (a+b)
addSuccL  BinO      BinO        = Refl
addSuccL  BinO     (BinP  U   ) = Refl
addSuccL  BinO     (BinP (O _)) = Refl
addSuccL  BinO     (BinP (I _)) = Refl
addSuccL (BinP _ )  BinO        = Refl
addSuccL (BinP a') (BinP  b'  ) = rewrite addSuccL a' b' in Refl

-- Specification of subtraction

-- sub_0_r
subZeroR : (a : Bin) -> a-0 = a
subZeroR  BinO    = Refl
subZeroR (BinP _) = Refl

-- Helper for sub_succ_r
subSuccPred : (p, q : Bip) -> bimMinus p (bipSucc q) = bimPred (bimMinus p q)
subSuccPred a b = rewrite subMaskSuccR a b in
                  rewrite subMaskCarrySpec a b in Refl

-- Helper for sub_succ_r
bimAndBin : (a : Bim) -> bimToBin (bimPred a) = binPred (bimToBin a)
bimAndBin (BimP  U   ) = Refl
bimAndBin (BimP (O _)) = Refl
bimAndBin (BimP (I _)) = Refl
bimAndBin  BimO        = Refl
bimAndBin  BimM        = Refl

-- sub_succ_r
subSuccR : (a, b : Bin) -> a-(binSucc b) = binPred (a-b)
subSuccR  BinO         BinO     = Refl
subSuccR (BinP  U   )  BinO     = Refl
subSuccR (BinP (O _))  BinO     = Refl
subSuccR (BinP (I _))  BinO     = Refl
subSuccR  BinO        (BinP _ ) = Refl
subSuccR (BinP  a'  ) (BinP b') =
  rewrite subSuccPred a' b' in
  rewrite bimAndBin (bimMinus a' b') in Refl

-- Specification of multiplication

-- mul_0_l

mulZeroL : (a : Bin) -> BinO * a = BinO
mulZeroL  BinO    = Refl
mulZeroL (BinP _) = Refl

-- mul_succ_l

mulSuccL : (a, b : Bin) -> (binSucc a) * b = b + a * b
mulSuccL  BinO      BinO     = Refl
mulSuccL  BinO     (BinP _ ) = Refl
mulSuccL (BinP _ )  BinO     = Refl
mulSuccL (BinP a') (BinP b') = cong $ mulSuccL a' b'

-- Specification of boolean comparisons (using <->)

-- eqb_eq
-- TODO split into `to` and `fro`
eqbEqTo : (p, q : Bin) -> (p == q = True) -> p=q
eqbEqTo  BinO     BinO    = const Refl
eqbEqTo  BinO    (BinP a) = absurd
eqbEqTo (BinP a)  BinO    = absurd
eqbEqTo (BinP a) (BinP b) = cong . eqbEqTo a b

eqbEqFro : (p, q : Bin) -> p=q -> (p == q = True)
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

-- add_0_r

addZeroR : (a : Bin) -> a + BinO = a
addZeroR  BinO    = Refl
addZeroR (BinP _) = Refl

-- add_comm

addComm : (a, b : Bin) -> a + b = b + a
addComm  BinO      BinO     = Refl
addComm  BinO     (BinP _ ) = Refl
addComm (BinP _ )  BinO     = Refl
addComm (BinP a') (BinP b') = cong $ addComm a' b'

-- add_assoc

addAssoc : (a, b, c : Bin) -> a + (b + c) = a + b + c
addAssoc  BinO      BinO      BinO     = Refl
addAssoc  BinO      BinO     (BinP _ ) = Refl
addAssoc  BinO     (BinP _ )  BinO     = Refl
addAssoc  BinO     (BinP _ ) (BinP _ ) = Refl
addAssoc (BinP _ )  BinO      BinO     = Refl
addAssoc (BinP _ )  BinO     (BinP _ ) = Refl
addAssoc (BinP _ ) (BinP _ )  BinO     = Refl
addAssoc (BinP a') (BinP b') (BinP c') = cong $ addAssoc a' b' c'

-- sub_add

subAdd : (p, q : Bin) -> p `Lt` q -> (q-p)+p = q
subAdd  BinO     BinO    pltq = absurd pltq
subAdd  BinO    (BinP _) Refl = Refl
subAdd (BinP _)  BinO    pltq = absurd pltq
subAdd (BinP a) (BinP b) pltq = case subMaskSpec a b of
  SubIsNul     Refl _ => rewrite subMaskDiag a in
                         Refl
  SubIsPos {r} Refl _ => absurd $ ltNotAddL b r pltq
  SubIsNeg {r} Refl _ => rewrite subMaskAddDiagL a r in
                         rewrite addComm a r in
                         Refl

-- mul_comm

mulComm : (a, b : Bin) -> a * b = b * a
mulComm  BinO      BinO     = Refl
mulComm  BinO     (BinP _ ) = Refl
mulComm (BinP _ )  BinO     = Refl
mulComm (BinP a') (BinP b') = cong $ mulComm a' b'

-- le_0_l

leZeroL : (a : Bin) ->
  Either (BinO `compare` a = EQ) (BinO `compare` a = LT)
leZeroL  BinO    = Left Refl
leZeroL (BinP _) = Right Refl

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

-- TODO contribute to Prelude.Bool?

data BoolSpec : (p, q : Type) -> Bool -> Type where
  BoolSpecT : p -> BoolSpec p q True
  BoolSpecF : q -> BoolSpec p q False

lebSpec : (p, q : Bin) -> BoolSpec (p `Le` q) (q `Lt` p) (p <= q)
lebSpec p q with (p `compare` q) proof pq
  | LT = BoolSpecT uninhabited
  | EQ = rewrite eqbEqFro p q $ compareEqIffTo p q $ sym pq in
         BoolSpecT uninhabited
  | GT = rewrite gtNotEqN p q $ sym pq in
         BoolSpecF $ rewrite compareAntisym p q in
                     rewrite sym pq in
                     Refl

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

-- Properties of double and succ_double

-- double_spec

doubleSpec : (a : Bin) -> binD a = 2 * a
doubleSpec  BinO    = Refl
doubleSpec (BinP _) = Refl

-- succ_double_spec

succDoubleSpec : (a : Bin) -> binDPO a = 2 * a + 1
succDoubleSpec  BinO    = Refl
succDoubleSpec (BinP _) = Refl

-- double_add

doubleAdd : (a, b : Bin) -> binD (a + b) = binD a + binD b
doubleAdd  BinO     BinO    = Refl
doubleAdd  BinO    (BinP _) = Refl
doubleAdd (BinP _)  BinO    = Refl
doubleAdd (BinP _) (BinP _) = Refl

-- succ_double_add

succDoubleAdd : (a, b : Bin) -> binDPO (a + b) = binD a + binDPO b
succDoubleAdd  BinO     BinO    = Refl
succDoubleAdd  BinO    (BinP _) = Refl
succDoubleAdd (BinP _)  BinO    = Refl
succDoubleAdd (BinP _) (BinP _) = Refl

-- double_mul

doubleMul : (a, b : Bin) -> binD (a * b) = binD a * b
doubleMul  BinO     BinO    = Refl
doubleMul  BinO    (BinP _) = Refl
doubleMul (BinP _)  BinO    = Refl
doubleMul (BinP _) (BinP _) = Refl

-- succ_double_mul

succDoubleMul : (a, b : Bin) -> binDPO a * b = binD a * b + b
succDoubleMul  BinO      BinO     = Refl
succDoubleMul  BinO     (BinP _)  = Refl
succDoubleMul (BinP _)   BinO     = Refl
succDoubleMul (BinP a') (BinP b') =
  rewrite addComm (O (bipMult a' b')) b' in Refl

-- div2_double

divTwoDouble : (a : Bin) -> binDivTwo (binD a) = a
divTwoDouble  BinO    = Refl
divTwoDouble (BinP _) = Refl

-- div2_succ_double

divTwoSuccDouble : (a : Bin) -> binDivTwo (binDPO a) = a
divTwoSuccDouble  BinO    = Refl
divTwoSuccDouble (BinP _) = Refl

-- double_inj

doubleInj : (n, m : Bin) -> binD n = binD m -> n = m
doubleInj n m prf =
  rewrite sym $ divTwoDouble n in
  rewrite sym $ divTwoDouble m in
  rewrite prf in
  Refl

-- succ_double_inj

succDoubleInj : (n, m : Bin) -> binDPO n = binDPO m -> n = m
succDoubleInj n m prf =
  rewrite sym $ divTwoSuccDouble n in
  rewrite sym $ divTwoSuccDouble m in
  rewrite prf in
  Refl

-- succ_double_lt

succDoubleLt : (n, m : Bin) -> n `Lt` m -> binDPO n `Lt` binD m
succDoubleLt  BinO     BinO    = absurd
succDoubleLt  BinO    (BinP _) = const Refl
succDoubleLt (BinP _)  BinO    = absurd
succDoubleLt (BinP a) (BinP b) = compareContGtLtFro a b

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

-- Specifications of power

-- pow_0_r
-- pow_succ_r
-- pow_neg_r
-- TODO

-- Specification of square

-- square_spec
-- TODO

-- Specification of Base-2 logarithm

-- size_log2
-- size_gt
-- size_le
-- log2_spec
-- log2_nonpos
-- TODO

-- Specification of parity functions

-- even_spec
-- odd_spec
-- TODO

-- Specification of the euclidean division

-- pos_div_eucl_spec
-- div_eucl_spec
-- div_mod'
-- div_mod
-- pos_div_eucl_remainder
-- mod_lt
-- mod_bound_pos
-- TODO

-- Specification of square root

-- sqrtrem_sqrt
-- sqrtrem_spec
-- sqrt_spec
-- sqrt_neg
-- TODO

-- Specification of gcd

-- ggcd_gcd
-- ggcd_correct_divisors
-- gcd_divide_l
-- gcd_divide_r
-- gcd_greatest
-- gcd_nonneg
-- TODO

-- Specification of bitwise functions

-- testbit_even_0
-- testbit_odd_0
-- testbit_succ_r_div2
-- testbit_odd_succ
-- testbit_even_succ
-- testbit_neg_r
-- TODO

-- Correctness proofs for shifts

-- shiftr_succ_r
-- shiftl_succ_r
-- shiftr_spec
-- shiftl_spec_high
-- shiftl_spec_low
-- div2_spec
-- TODO

-- Semantics of bitwise operations

-- pos_lxor_spec
-- lxor_spec
-- pos_lor_spec
-- lor_spec
-- pos_land_spec
-- land_spec
-- pos_ldiff_spec
-- ldiff_spec
-- TODO

-- Specification of constants

-- one_succ
-- two_succ
-- pred_0
-- TODO

-- Generic induction / recursion

-- bi_induction
-- recursion_wd
-- recursion_0
-- recursion_succ
-- TODO

-- Instantiation of generic properties of natural numbers

-- gt_lt_iff
-- gt_lt
-- lt_gt
-- ge_le_iff
-- ge_le
-- le_ge
-- TODO

-- Auxiliary results about right shift on positive numbers

-- pos_pred_shiftl_low
-- pos_pred_shiftl_high
-- pred_div2_up
-- TODO

-- More complex compatibility facts

-- Nplus_reg_l
-- Nmult_Sn_m
-- Nmult_plus_distr_l
-- Nmult_reg_r
-- Ncompare_antisym
-- TODO
