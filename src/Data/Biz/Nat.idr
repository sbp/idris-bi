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

toBizBinInjCompare : (n, m : Bin) -> toBizBin n `compare` toBizBin m = n `compare` m
toBizBinInjCompare  BinO     BinO    = Refl
toBizBinInjCompare  BinO    (BinP _) = Refl
toBizBinInjCompare (BinP _)  BinO    = Refl
toBizBinInjCompare (BinP _) (BinP _) = Refl

-- inj_le
-- TODO split into `to` and `fro`

toBizBinInjLeTo : (n, m : Bin) -> n `Le` m -> toBizBin n `Le` toBizBin m
toBizBinInjLeTo n m nlem = rewrite toBizBinInjCompare n m in
                           nlem

toBizBinInjLeFro : (n, m : Bin) -> toBizBin n `Le` toBizBin m -> n `Le` m
toBizBinInjLeFro n m nlem = rewrite sym $ toBizBinInjCompare n m in
                            nlem

-- inj_lt
-- TODO split into `to` and `fro`

toBizBinInjLtTo : (n, m : Bin) -> n `Lt` m -> toBizBin n `Lt` toBizBin m
toBizBinInjLtTo n m nltm = rewrite toBizBinInjCompare n m in
                           nltm

toBizBinInjLtFro : (n, m : Bin) -> toBizBin n `Lt` toBizBin m -> n `Lt` m
toBizBinInjLtFro n m nltm = rewrite sym $ toBizBinInjCompare n m in
                            nltm

-- inj_ge
-- TODO split into `to` and `fro`

toBizBinInjGeTo : (n, m : Bin) -> n `Ge` m -> toBizBin n `Ge` toBizBin m
toBizBinInjGeTo n m ngem = rewrite toBizBinInjCompare n m in
                           ngem

toBizBinInjGeFro : (n, m : Bin) -> toBizBin n `Ge` toBizBin m -> n `Ge` m
toBizBinInjGeFro n m ngem = rewrite sym $ toBizBinInjCompare n m in
                            ngem

-- inj_gt
-- TODO split into `to` and `fro`

toBizBinInjGtTo : (n, m : Bin) -> n `Gt` m -> toBizBin n `Gt` toBizBin m
toBizBinInjGtTo n m ngtm = rewrite toBizBinInjCompare n m in
                           ngtm

toBizBinInjGtFro : (n, m : Bin) -> toBizBin n `Gt` toBizBin m -> n `Gt` m
toBizBinInjGtFro n m ngtm = rewrite sym $ toBizBinInjCompare n m in
                            ngtm

-- inj_abs_N

injAbsN : (z : Biz) -> toBizBin (bizAbsBin z) = bizAbs z
injAbsN  BizO    = Refl
injAbsN (BizP _) = Refl
injAbsN (BizM _) = Refl

-- inj_add

toBizBinInjAdd : (n, m : Bin) -> toBizBin (n+m) = toBizBin n + toBizBin m
toBizBinInjAdd  BinO     BinO    = Refl
toBizBinInjAdd  BinO    (BinP _) = Refl
toBizBinInjAdd (BinP _)  BinO    = Refl
toBizBinInjAdd (BinP _) (BinP _) = Refl

-- inj_mul

toBizBinInjMul : (n, m : Bin) -> toBizBin (n*m) = toBizBin n * toBizBin m
toBizBinInjMul  BinO     BinO    = Refl
toBizBinInjMul  BinO    (BinP _) = Refl
toBizBinInjMul (BinP _)  BinO    = Refl
toBizBinInjMul (BinP _) (BinP _) = Refl

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

toBizBinInjSub : (n, m : Bin) -> m `Le` n -> toBizBin (n-m) = toBizBin n - toBizBin m
toBizBinInjSub n m mlen =
  rewrite injSubMax n m in
  maxR 0 (toBizBin n - toBizBin m) $
  rewrite compareAntisym (toBizBin n - toBizBin m) 0 in
  rewrite sym $ compareSub (toBizBin n) (toBizBin m) in
  rewrite sym $ compareAntisym (toBizBin n) (toBizBin m) in
  toBizBinInjLeTo m n mlen

-- inj_succ

toBizBinInjSucc : (n : Bin) -> toBizBin (binSucc n) = bizSucc (toBizBin n)
toBizBinInjSucc  BinO    = Refl
toBizBinInjSucc (BinP a) = cong $ sym $ add1R a

-- inj_pred_max

toBizBinInjPredMax : (n : Bin) -> toBizBin (binPred n) = 0 `max` bizPred (toBizBin n)
toBizBinInjPredMax n = rewrite predSub n in
                       injSubMax n 1

-- inj_pred

toBizBinInjPred : (n : Bin) -> 0 `Lt` n -> toBizBin (binPred n) = bizPred (toBizBin n)
toBizBinInjPred n zltn = rewrite predSub n in
                         toBizBinInjSub n 1 $ leSuccLFro 0 n zltn

-- inj_min

toBizBinInjMin : (n, m : Bin) -> toBizBin (n `binMin` m) = toBizBin n `min` toBizBin m
toBizBinInjMin n m =
  rewrite toBizBinInjCompare n m in
  aux
  where
  aux : toBizBin (n `binMin` m) = bizMinMaxHelp (toBizBin m) (toBizBin n) (n `compare` m)
  aux with (n `compare` m) proof nm
    | LT = Refl
    | EQ = cong $ compareEqIffTo n m $ sym nm  -- this is needed because binMin and bizMin use different arguments for the EQ case
    | GT = Refl

-- inj_max

toBizBinInjMax : (n, m : Bin) -> toBizBin (n `binMax` m) = toBizBin n `max` toBizBin m
toBizBinInjMax n m =
  rewrite toBizBinInjCompare n m in
  aux
  where
  aux : toBizBin (n `binMax` m) = bizMinMaxHelp (toBizBin n) (toBizBin m) (n `compare` m)
  aux with (n `compare` m) proof nm
    | LT = Refl
    | EQ = cong $ sym $ compareEqIffTo n m $ sym nm  -- this is needed because binMax and bizMax use different arguments for the EQ case
    | GT = Refl

-- TODO inj_div
-- TODO inj_mod
-- TODO inj_quot
-- TODO inj_rem
-- these require `div_mod_unique` lemma

-- inj_div2

toBizBinInjDiv2 : (n : Bin) -> toBizBin (binDivTwo n) = bizDivTwo (toBizBin n)
toBizBinInjDiv2  BinO        = Refl
toBizBinInjDiv2 (BinP  U   ) = Refl
toBizBinInjDiv2 (BinP (O _)) = Refl
toBizBinInjDiv2 (BinP (I _)) = Refl

-- inj_quot2

toBizBinInjQuot2 : (n : Bin) -> toBizBin (binDivTwo n) = bizQuotTwo (toBizBin n)
toBizBinInjQuot2  BinO        = Refl
toBizBinInjQuot2 (BinP  U   ) = Refl
toBizBinInjQuot2 (BinP (O _)) = Refl
toBizBinInjQuot2 (BinP (I _)) = Refl

-- inj_pow

toBizBinInjPow : (n, m : Bin) -> toBizBin (binPow n m) = bizPow (toBizBin n) (toBizBin m)
toBizBinInjPow  BinO     BinO    = Refl
toBizBinInjPow  BinO    (BinP a) = sym $ pow0L (BizP a) uninhabited
toBizBinInjPow (BinP _)  BinO    = Refl
toBizBinInjPow (BinP a) (BinP b) = sym $ powZpos a b

-- [Z.to_N] is a bijection between non-negative [Z] and [N], with [Pos.of_N] as
-- reciprocal

-- id

toBinBizId : (n : Biz) -> 0 `Le` n -> toBizBin (toBinBiz n) = n
toBinBizId  BizO    _    = Refl
toBinBizId (BizP _) _    = Refl
toBinBizId (BizM _) zlen = absurd $ zlen Refl

-- [Z.to_N] is hence injective for non-negative integers

-- inj

toBinBizInj : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n = toBinBiz m -> n = m
toBinBizInj n m zlen zlem prf =
  rewrite sym $ toBinBizId n zlen in
  rewrite sym $ toBinBizId m zlem in
  cong prf

-- inj_iff is just inj+cong

-- [Z.to_N], basic equations

-- inj_0 is trivial
-- inj_pos is trivial
-- inj_neg is trivial

-- [Z.to_N] and operations

-- inj_add

toBinBizInjAdd : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz (n+m) = (toBinBiz n + toBinBiz m)
toBinBizInjAdd  BizO     BizO    _    _    = Refl
toBinBizInjAdd  BizO    (BizP a) _    _    = Refl
toBinBizInjAdd (BizP a)  BizO    _    _    = Refl
toBinBizInjAdd (BizP a) (BizP b) _    _    = Refl
toBinBizInjAdd (BizM _)  _       zlen _    = absurd $ zlen Refl
toBinBizInjAdd _        (BizM a) _    zlem = absurd $ zlem Refl

-- inj_mul

toBinBizInjMul : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz (n*m) = (toBinBiz n * toBinBiz m)
toBinBizInjMul  BizO     BizO    _    _    = Refl
toBinBizInjMul  BizO    (BizP a) _    _    = Refl
toBinBizInjMul (BizP a)  BizO    _    _    = Refl
toBinBizInjMul (BizP a) (BizP b) _    _    = Refl
toBinBizInjMul (BizM _)  _       zlen _    = absurd $ zlen Refl
toBinBizInjMul _        (BizM a) _    zlem = absurd $ zlem Refl

-- inj_succ

toBinBizInjSucc : (n : Biz) -> 0 `Le` n -> toBinBiz (bizSucc n) = binSucc (toBinBiz n)
toBinBizInjSucc  BizO    _    = Refl
toBinBizInjSucc (BizP a) _    = cong $ add1R a
toBinBizInjSucc (BizM _) zlen = absurd $ zlen Refl

-- inj_sub

toBinBizInjSub : (n, m : Biz) -> 0 `Le` m -> toBinBiz (n-m) = toBinBiz n - toBinBiz m
toBinBizInjSub  n        BizO    _    =
  rewrite add0R n in
  rewrite subZeroR $ toBinBiz n in
  Refl
toBinBizInjSub  BizO    (BizP _) _    = Refl
toBinBizInjSub (BizP a) (BizP b) _    =
  rewrite posSubSpec a b in
  rewrite compareSubMask a b in
  aux
  where
  aux : toBinBiz $ posSubSpecHelp a b $ mask2cmp $ bimMinus a b = bimToBin $ bimMinus a b
  aux with (bimMinus a b) proof ab
    | BimO   = Refl
    | BimP _ = rewrite sym ab in
               Refl
    | BimM   = Refl
toBinBizInjSub (BizM _) (BizP _) _    = Refl
toBinBizInjSub  _       (BizM _) zlem = absurd $ zlem Refl

-- inj_pred

toBinBizInjPred : (n : Biz) -> toBinBiz (bizPred n) = binPred (toBinBiz n)
toBinBizInjPred n = rewrite predSub (toBinBiz n) in
                    toBinBizInjSub n 1 uninhabited

-- inj_compare

toBinBizInjСompare : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n `compare` toBinBiz m = n `compare` m
toBinBizInjСompare n m zlen zlem =
  rewrite sym $ toBizBinInjCompare (toBinBiz n) (toBinBiz m) in
  rewrite toBinBizId n zlen in
  rewrite toBinBizId m zlem in
  Refl

-- inj_le
-- TODO split into `to` and `fro`

toBinBizInjLeTo : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> n `Le` m -> toBinBiz n `Le` toBinBiz m
toBinBizInjLeTo n m zlen zlem nlem = rewrite toBinBizInjСompare n m zlen zlem in
                                     nlem

toBinBizInjLeFro : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n `Le` toBinBiz m -> n `Le` m
toBinBizInjLeFro n m zlen zlem nlem = rewrite sym $ toBinBizInjСompare n m zlen zlem in
                                      nlem

-- inj_lt
-- TODO split into `to` and `fro`

toBinBizInjLtTo : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> n `Lt` m -> toBinBiz n `Lt` toBinBiz m
toBinBizInjLtTo n m zlen zlem nltm = rewrite toBinBizInjСompare n m zlen zlem in
                                     nltm

toBinBizInjLtFro : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n `Lt` toBinBiz m -> n `Lt` m
toBinBizInjLtFro n m zlen zlem nltm = rewrite sym $ toBinBizInjСompare n m zlen zlem in
                                      nltm

-- inj_min

toBinBizInjMin : (n, m : Biz) -> toBinBiz (n `min` m) = (toBinBiz n) `binMin` (toBinBiz m)
toBinBizInjMin  BizO     BizO    = Refl
toBinBizInjMin  BizO    (BizP _) = Refl
toBinBizInjMin  BizO    (BizM _) = Refl
toBinBizInjMin (BizP _)  BizO    = Refl
toBinBizInjMin (BizP a) (BizP b) with (a `compare` b) proof ab
  | LT = Refl
  | EQ = cong $ sym $ compareEqIffTo a b $ sym ab
  | GT = Refl
toBinBizInjMin (BizP _) (BizM _) = Refl
toBinBizInjMin (BizM _)  BizO    = Refl
toBinBizInjMin (BizM _) (BizP _) = Refl
toBinBizInjMin (BizM a) (BizM b) with (b `compare` a)
  | LT = Refl
  | EQ = Refl
  | GT = Refl

-- inj_max

toBinBizInjMax : (n, m : Biz) -> toBinBiz (n `max` m) = (toBinBiz n) `binMax` (toBinBiz m)
toBinBizInjMax  BizO     BizO    = Refl
toBinBizInjMax  BizO    (BizP _) = Refl
toBinBizInjMax  BizO    (BizM _) = Refl
toBinBizInjMax (BizP _)  BizO    = Refl
toBinBizInjMax (BizP a) (BizP b) with (a `compare` b) proof ab
  | LT = Refl
  | EQ = cong $ compareEqIffTo a b $ sym ab
  | GT = Refl
toBinBizInjMax (BizP _) (BizM _) = Refl
toBinBizInjMax (BizM _)  BizO    = Refl
toBinBizInjMax (BizM _) (BizP _) = Refl
toBinBizInjMax (BizM a) (BizM b)with (b `compare` a)
  | LT = Refl
  | EQ = Refl
  | GT = Refl

-- TODO inj_div
-- TODO inj_mod
-- TODO inj_quot
-- TODO inj_rem
-- these require `toBizBin` versions above and `div_mod_unique` lemma

-- inj_div2

toBinBizInjDiv2 : (n : Biz) -> toBinBiz (bizDivTwo n) = binDivTwo (toBinBiz n)
toBinBizInjDiv2  BizO        = Refl
toBinBizInjDiv2 (BizP  U   ) = Refl
toBinBizInjDiv2 (BizP (O _)) = Refl
toBinBizInjDiv2 (BizP (I _)) = Refl
toBinBizInjDiv2 (BizM  _   ) = Refl

-- inj_quot2

toBinBizInjQuot2 : (n : Biz) -> toBinBiz (bizQuotTwo n) = binDivTwo (toBinBiz n)
toBinBizInjQuot2  BizO        = Refl
toBinBizInjQuot2 (BizP  U   ) = Refl
toBinBizInjQuot2 (BizP (O _)) = Refl
toBinBizInjQuot2 (BizP (I _)) = Refl
toBinBizInjQuot2 (BizM  U   ) = Refl
toBinBizInjQuot2 (BizM (O _)) = Refl
toBinBizInjQuot2 (BizM (I _)) = Refl

-- inj_pow

toBinBizInjPow : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz (bizPow n m) = binPow (toBinBiz n) (toBinBiz m)
toBinBizInjPow _  BizO    _    _    = Refl
toBinBizInjPow n (BizP a) zlen _    =
  rewrite sym $ toBizBinId (binPow (toBinBiz n) (BinP a)) in
  rewrite toBizBinInjPow (toBinBiz n) (BinP a) in
  rewrite toBinBizId n zlen in
  Refl
toBinBizInjPow _ (BizM _) _    zlem = absurd $ zlem Refl