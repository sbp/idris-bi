module Data.Biz.Nat

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.Nat

import Data.Bin
import Data.Bin.Proofs
import Data.Bin.Nat

import Data.Biz
import Data.Biz.Proofs

%default total
%access public export

-- Chains of conversions

-- nat_N_Z

natNZ : (n : Nat) -> toBizBin (toBinNat n) = toBizNat n
natNZ  Z    = Refl
natNZ (S _) = Refl

-- N_nat_Z

nNatZ : (n : Bin) -> toBizNat (toNatBin n) = toBizBin n
nNatZ  BinO    = Refl
nNatZ (BinP a) =
  let (n**prf) = isSucc a in
  rewrite prf in
  cong $ toBipSuccInv n a prf

-- positive_nat_Z

positiveNatZ : (p : Bip) -> toBizNat (toNatBip p) = BizP p
positiveNatZ p =
  let (n**prf) = isSucc p in
  rewrite prf in
  cong $ toBipSuccInv n p prf

-- positive_N_Z is trivial

-- positive_N_nat is trivial

-- positive_nat_N

positiveNatN : (p : Bip) -> toBinNat (toNatBip p) = BinP p
positiveNatN p =
  let (n**prf) = isSucc p in
  rewrite prf in
  cong $ toBipSuccInv n p prf

-- Z_N_nat

zNNat : (n : Biz) -> toNatBin (toBinBiz n) = toNatBiz n
zNNat  BizO    = Refl
zNNat (BizP _) = Refl
zNNat (BizM _) = Refl

-- Z_nat_N

zNatN : (n : Biz) -> toBinNat (toNatBiz n) = toBinBiz n
zNatN  BizO    = Refl
zNatN (BizP a) = positiveNatN a
zNatN (BizM _) = Refl

-- Zabs_N_nat

zAbsNNat : (n : Biz) -> toNatBin (bizAbsBin n) = bizAbsNat n
zAbsNNat  BizO    = Refl
zAbsNNat (BizP _) = Refl
zAbsNNat (BizM _) = Refl

-- Zabs_nat_N

zAbsNatN : (n : Biz) -> toBinNat (bizAbsNat n) = bizAbsBin n
zAbsNatN  BizO    = Refl
zAbsNatN (BizP a) = positiveNatN a
zAbsNatN (BizM a) = positiveNatN a

-- Conversions between [Z] and [N]

-- [Z.of_N] is a bijection between [N] and non-negative [Z], with [Z.to_N] (or
-- [Z.abs_N]) as reciprocal.

-- id

toBizBinId : (n : Bin) -> toBinBiz (toBizBin n) = n
toBizBinId  BinO    = Refl
toBizBinId (BinP _) = Refl

-- [Z.of_N] is hence injective

-- inj

toBizBinInj : (n, m : Bin) -> toBizBin n = toBizBin m -> n = m
toBizBinInj  BinO     BinO    = const Refl
toBizBinInj  BinO    (BinP _) = absurd
toBizBinInj (BinP _)  BinO    = absurd
toBizBinInj (BinP _) (BinP _) = cong . bizPInj

-- inj_iff is just inj+cong

-- [Z.of_N] produce non-negative integers

-- is_nonneg

isNonneg : (n : Bin) -> 0 `Le` toBizBin n
isNonneg  BinO    = uninhabited
isNonneg (BinP _) = uninhabited

-- [Z.of_N], basic equations

-- inj_0 is trivial

-- inj_pos is trivial

-- [Z.of_N] and usual operations

-- inj_compare

injCompare : (n, m : Bin) -> toBizBin n `compare` toBizBin m = n `compare` m
injCompare  BinO     BinO    = Refl
injCompare  BinO    (BinP _) = Refl
injCompare (BinP _)  BinO    = Refl
injCompare (BinP _) (BinP _) = Refl

-- inj_le
-- TODO split into `to` and `fro`

injLeTo : (n, m : Bin) -> n `Le` m -> toBizBin n `Le` toBizBin m
injLeTo n m nlem = rewrite injCompare n m in
                   nlem

injLeFro : (n, m : Bin) -> toBizBin n `Le` toBizBin m -> n `Le` m
injLeFro n m nlem = rewrite sym $ injCompare n m in
                    nlem

-- inj_lt
-- TODO split into `to` and `fro`

injLtTo : (n, m : Bin) -> n `Lt` m -> toBizBin n `Lt` toBizBin m
injLtTo n m nltm = rewrite injCompare n m in
                   nltm

injLtFro : (n, m : Bin) -> toBizBin n `Lt` toBizBin m -> n `Lt` m
injLtFro n m nltm = rewrite sym $ injCompare n m in
                    nltm

-- inj_ge
-- TODO split into `to` and `fro`

injGeTo : (n, m : Bin) -> n `Ge` m -> toBizBin n `Ge` toBizBin m
injGeTo n m ngem = rewrite injCompare n m in
                   ngem

injGeFro : (n, m : Bin) -> toBizBin n `Ge` toBizBin m -> n `Ge` m
injGeFro n m ngem = rewrite sym $ injCompare n m in
                    ngem

-- inj_gt
-- TODO split into `to` and `fro`

injGtTo : (n, m : Bin) -> n `Gt` m -> toBizBin n `Gt` toBizBin m
injGtTo n m ngtm = rewrite injCompare n m in
                   ngtm

injGtFro : (n, m : Bin) -> toBizBin n `Gt` toBizBin m -> n `Gt` m
injGtFro n m ngtm = rewrite sym $ injCompare n m in
                    ngtm

-- inj_abs_N

injAbsN : (z : Biz) -> toBizBin (bizAbsBin z) = bizAbs z
injAbsN  BizO    = Refl
injAbsN (BizP _) = Refl
injAbsN (BizM _) = Refl

-- inj_add

injAdd : (n, m : Bin) -> toBizBin (n+m) = toBizBin n + toBizBin m
injAdd  BinO     BinO    = Refl
injAdd  BinO    (BinP _) = Refl
injAdd (BinP _)  BinO    = Refl
injAdd (BinP _) (BinP _) = Refl

-- inj_mul

injMul : (n, m : Bin) -> toBizBin (n*m) = toBizBin n * toBizBin m
injMul  BinO     BinO    = Refl
injMul  BinO    (BinP _) = Refl
injMul (BinP _)  BinO    = Refl
injMul (BinP _) (BinP _) = Refl

-- inj_sub_max

injSubMax : (n, m : Bin) -> toBizBin (n-m) = 0 `max` (toBizBin n - toBizBin m)
injSubMax  BinO     BinO    = Refl
injSubMax  BinO    (BinP _) = Refl
injSubMax (BinP _)  BinO    = Refl
injSubMax (BinP a) (BinP b) =
  rewrite posSubSpec a b in
  rewrite compareSubMask a b in
  aux
  where
  aux : toBizBin (bimToBin (bimMinus a b)) = bizMinMaxHelp 0 (posSubSpecHelp a b (mask2cmp (bimMinus a b))) (bizCompare 0 (posSubSpecHelp a b (mask2cmp (bimMinus a b))))
  aux with (bimMinus a b) proof ab
    | BimO   = Refl
    | BimP _ = rewrite sym ab in
               Refl
    | BimM   = Refl

-- inj_sub

injSub : (n, m : Bin) -> m `Le` n -> toBizBin (n-m) = toBizBin n - toBizBin m
injSub n m mlen =
  rewrite injSubMax n m in
  maxR 0 (toBizBin n - toBizBin m) $
  rewrite compareAntisym (toBizBin n - toBizBin m) 0 in
  rewrite sym $ compareSub (toBizBin n) (toBizBin m) in
  rewrite sym $ compareAntisym (toBizBin n) (toBizBin m) in
  injLeTo m n mlen

-- inj_succ

injSucc : (n : Bin) -> toBizBin (binSucc n) = bizSucc (toBizBin n)
injSucc  BinO    = Refl
injSucc (BinP a) = cong $ sym $ add1R a

-- inj_pred_max

injPredMax : (n : Bin) -> toBizBin (binPred n) = 0 `max` bizPred (toBizBin n)
injPredMax n = rewrite predSub n in
               injSubMax n 1

-- inj_pred

injPred : (n : Bin) -> 0 `Lt` n -> toBizBin (binPred n) = bizPred (toBizBin n)
injPred n zltn = rewrite predSub n in
                 injSub n 1 $ leSuccLFro 0 n zltn

-- inj_min

injMin : (n, m : Bin) -> toBizBin (n `binMin` m) = toBizBin n `min` toBizBin m
injMin n m =
  rewrite injCompare n m in
  aux
  where
  aux : toBizBin (n `binMin` m) = bizMinMaxHelp (toBizBin m) (toBizBin n) (n `compare` m)
  aux with (n `compare` m) proof nm
    | LT = Refl
    | EQ = cong $ compareEqIffTo n m $ sym nm  -- this is needed because binMin and bizMin use different arguments for the EQ case
    | GT = Refl

-- inj_max

injMax : (n, m : Bin) -> toBizBin (n `binMax` m) = toBizBin n `max` toBizBin m
injMax n m =
  rewrite injCompare n m in
  aux
  where
  aux : toBizBin (n `binMax` m) = bizMinMaxHelp (toBizBin n) (toBizBin m) (n `compare` m)
  aux with (n `compare` m) proof nm
    | LT = Refl
    | EQ = cong $ sym $ compareEqIffTo n m $ sym nm  -- this is needed because binMax and bizMax use different arguments for the EQ case
    | GT = Refl