module Data.Bin.Proofs

import Data.Bin
import Data.Bip.Proofs

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
posPredSpec : (a: Bip) -> bipPredBin a = binPred (BinP a)
posPredSpec  U    = Refl
posPredSpec (O _) = Refl
posPredSpec (I _) = Refl

-- succ_pos_spec
succPosSpec : (a: Bin) -> BinP (binSuccBip a) = binSucc a
succPosSpec  BinO    = Refl
succPosSpec (BinP _) = Refl

-- pos_pred_succ
posPredSucc : (a: Bin) -> bipPredBin (binSuccBip a) = a
posPredSucc  BinO     = Refl
posPredSucc (BinP a') = rewrite predBinSucc a' in Refl

-- succ_pos_pred
succPosPred : (a: Bip) -> binSucc (bipPredBin a) = BinP a
succPosPred  U     = Refl
succPosPred (O a') = rewrite succPredDouble a' in Refl
succPosPred (I _ ) = Refl

-- Properties of successor and predecessor

-- pred_succ
predSucc : (a: Bin) -> binPred (binSucc a) = a
predSucc  BinO     = Refl
predSucc (BinP a') = rewrite predBinSucc a' in Refl

-- pred_sub
predSub : (a: Bin) -> binPred a = a-(BinP U)
predSub  BinO         = Refl
predSub (BinP  U    ) = Refl
predSub (BinP (O a')) = Refl
predSub (BinP (I a')) = Refl

-- succ_0_discr
succZeroDiscr : (a: Bin) -> Not (binSucc a = 0)
succZeroDiscr  BinO     = uninhabited
succZeroDiscr (BinP a') = uninhabited

-- Specification of addition

-- add_0_l
addZeroL : (a: Bin) -> BinO + a = a
addZeroL  BinO    = Refl
addZeroL (BinP _) = Refl

-- add_succ_l
addSuccL : (a, b: Bin) -> (binSucc a) + b = binSucc (a+b)
addSuccL  BinO      BinO        = Refl
addSuccL  BinO     (BinP  U   ) = Refl
addSuccL  BinO     (BinP (O _)) = Refl
addSuccL  BinO     (BinP (I _)) = Refl
addSuccL (BinP _ )  BinO        = Refl
addSuccL (BinP a') (BinP  b'  ) = rewrite addSuccL a' b' in Refl

-- Specification of subtraction

-- sub_0_r
subZeroR : (a: Bin) -> a-0 = a
subZeroR  BinO    = Refl
subZeroR (BinP _) = Refl

-- Helper for sub_succ_r
subSuccPred : (p, q: Bip) -> bimMinus p (bipSucc q) = bimPred (bimMinus p q)
subSuccPred a b = rewrite subMaskSuccR a b in
                  rewrite subMaskCarrySpec a b in Refl

-- Helper for sub_succ_r
bimAndBin : (a: Bim) -> bimToBin (bimPred a) = binPred (bimToBin a)
bimAndBin (BimP  U   ) = Refl
bimAndBin (BimP (O _)) = Refl
bimAndBin (BimP (I _)) = Refl
bimAndBin  BimO        = Refl
bimAndBin  BimM        = Refl

-- sub_succ_r
subSuccR : (a, b: Bin) -> a-(binSucc b) = binPred (a-b)
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

mulZeroL : (a: Bin) -> BinO * a = BinO
mulZeroL  BinO    = Refl
mulZeroL (BinP _) = Refl

-- mul_succ_l

mulSuccL : (a, b: Bin) -> (binSucc a) * b = b + a * b
mulSuccL  BinO      BinO      = Refl
mulSuccL  BinO     (BinP _)   = Refl
mulSuccL (BinP _)   BinO      = Refl
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

-- compare_lt_iff
-- compare_le_iff
-- compare_antisym
-- TODO

-- Some more advanced properties of comparison and orders

-- add_0_r

addZeroR : (a, b: Bin) -> a + BinO = a
addZeroR  BinO     BinO    = Refl
addZeroR  BinO    (BinP _) = Refl
addZeroR (BinP _)  BinO    = Refl
addZeroR (BinP _) (BinP _) = Refl

-- add_comm

addComm : (a, b: Bin) -> a + b = b + a
addComm  BinO     BinO      = Refl
addComm  BinO    (BinP _)   = Refl
addComm (BinP _)  BinO      = Refl
addComm (BinP a') (BinP b') = cong $ addComm a' b'

-- add_assoc

addAssoc : (a, b, c: Bin) -> a + (b + c) = a + b + c
addAssoc  BinO      BinO      BinO     = Refl
addAssoc  BinO      BinO     (BinP _)  = Refl
addAssoc  BinO     (BinP _)   BinO     = Refl
addAssoc  BinO     (BinP _)  (BinP _)  = Refl
addAssoc (BinP _)   BinO      BinO     = Refl
addAssoc (BinP _)   BinO     (BinP _)  = Refl
addAssoc (BinP _)  (BinP _)   BinO     = Refl
addAssoc (BinP a') (BinP b') (BinP c') = cong $ addAssoc a' b' c'

-- sub_add
-- TODO

-- mul_comm

mulComm : (a, b: Bin) -> a * b = b * a
mulComm  BinO     BinO      = Refl
mulComm  BinO    (BinP _)   = Refl
mulComm (BinP _)  BinO      = Refl
mulComm (BinP a') (BinP b') = cong $ mulComm a' b'

-- le_0_l

leZeroL : (a: Bin) ->
  Either (BinO `compare` a = EQ) (BinO `compare` a = LT)
leZeroL  BinO    = Left Refl
leZeroL (BinP _) = Right Refl

-- leb_spec
-- add_lt_cancel_l
-- TODO

-- Specification of lt and le

-- lt_succ_r
-- TODO

-- Properties of double and succ_double

-- double_spec

doubleSpec : (a: Bin) -> binD a = 2 * a
doubleSpec  BinO    = Refl
doubleSpec (BinP _) = Refl

-- succ_double_spec

succDoubleSpec : (a: Bin) -> binDPO a = 2 * a + 1
succDoubleSpec  BinO    = Refl
succDoubleSpec (BinP _) = Refl

-- double_add

doubleAdd : (a, b: Bin) -> binD (a + b) = binD a + binD b
doubleAdd  BinO     BinO    = Refl
doubleAdd  BinO    (BinP _) = Refl
doubleAdd (BinP _)  BinO    = Refl
doubleAdd (BinP _) (BinP _) = Refl

-- succ_double_add

succDoubleAdd : (a, b: Bin) -> binDPO (a + b) = binD a + binDPO b
succDoubleAdd  BinO     BinO    = Refl
succDoubleAdd  BinO    (BinP _) = Refl
succDoubleAdd (BinP _)  BinO    = Refl
succDoubleAdd (BinP _) (BinP _) = Refl

-- double_mul

doubleMul : (a, b: Bin) -> binD (a * b) = binD a * b
doubleMul  BinO     BinO    = Refl
doubleMul  BinO    (BinP _) = Refl
doubleMul (BinP _)  BinO    = Refl
doubleMul (BinP _) (BinP _) = Refl

-- succ_double_mul

succDoubleMul : (a, b: Bin) -> binDPO a * b = binD a * b + b
succDoubleMul  BinO      BinO     = Refl
succDoubleMul  BinO     (BinP _)  = Refl
succDoubleMul (BinP _)   BinO     = Refl
succDoubleMul (BinP a') (BinP b') =
  rewrite addComm (O (bipMult a' b')) b' in Refl

-- div2_double

divTwoDouble : (a: Bin) -> binDivTwo (binD a) = a
divTwoDouble  BinO    = Refl
divTwoDouble (BinP _) = Refl

-- div2_succ_double

divTwoSuccDouble : (a: Bin) -> binDivTwo (binDPO a) = a
divTwoSuccDouble  BinO    = Refl
divTwoSuccDouble (BinP _) = Refl

-- double_inj
-- succ_double_inj
-- succ_double_lt
-- TODO

-- Specification of minimum and maximum

-- min_l
-- min_r
-- max_l
-- max_r
-- TODO

-- 0 is the least natural number

-- compare_0_r
-- TODO

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
