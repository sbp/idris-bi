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

-- N2Z

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

toBizBinIsNonneg : (n : Bin) -> 0 `Le` toBizBin n
toBizBinIsNonneg  BinO    = uninhabited
toBizBinIsNonneg (BinP _) = uninhabited

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

injAbsN : (z : Biz) -> toBizBin (bizAbsBin z) = abs z
injAbsN  BizO    = Refl
injAbsN (BizP _) = Refl
injAbsN (BizM _) = Refl

-- inj_add
-- inj_mul
-- TODO defined in Biz.Proofs for now

-- inj_sub_max

toBizBinInjSubMax : (n, m : Bin) -> toBizBin (n-m) = 0 `max` (toBizBin n - toBizBin m)
toBizBinInjSubMax  BinO     BinO    = Refl
toBizBinInjSubMax  BinO    (BinP _) = Refl
toBizBinInjSubMax (BinP _)  BinO    = Refl
toBizBinInjSubMax (BinP a) (BinP b) =
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
  rewrite toBizBinInjSubMax n m in
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
                       toBizBinInjSubMax n 1

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

-- Z2N

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

toBinBizInjCompare : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n `compare` toBinBiz m = n `compare` m
toBinBizInjCompare n m zlen zlem =
  rewrite sym $ toBizBinInjCompare (toBinBiz n) (toBinBiz m) in
  rewrite toBinBizId n zlen in
  rewrite toBinBizId m zlem in
  Refl

-- inj_le
-- TODO split into `to` and `fro`

toBinBizInjLeTo : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> n `Le` m -> toBinBiz n `Le` toBinBiz m
toBinBizInjLeTo n m zlen zlem nlem = rewrite toBinBizInjCompare n m zlen zlem in
                                     nlem

toBinBizInjLeFro : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n `Le` toBinBiz m -> n `Le` m
toBinBizInjLeFro n m zlen zlem nlem = rewrite sym $ toBinBizInjCompare n m zlen zlem in
                                      nlem

-- inj_lt
-- TODO split into `to` and `fro`

toBinBizInjLtTo : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> n `Lt` m -> toBinBiz n `Lt` toBinBiz m
toBinBizInjLtTo n m zlen zlem nltm = rewrite toBinBizInjCompare n m zlen zlem in
                                     nltm

toBinBizInjLtFro : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toBinBiz n `Lt` toBinBiz m -> n `Lt` m
toBinBizInjLtFro n m zlen zlem nltm = rewrite sym $ toBinBizInjCompare n m zlen zlem in
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

-- Zabs2N

-- Results about [Z.abs_N], converting absolute values of [Z] integers to [N].

-- abs_N_spec

absNSpec : (n : Biz) -> bizAbsBin n = toBinBiz (abs n)
absNSpec  BizO    = Refl
absNSpec (BizP _) = Refl
absNSpec (BizM _) = Refl

-- abs_N_nonneg

absNNonneg : (n : Biz) -> 0 `Le` n -> bizAbsBin n = toBinBiz n
absNNonneg  BizO    _    = Refl
absNNonneg (BizP _) _    = Refl
absNNonneg (BizM _) zlen = absurd $ zlen Refl

-- id_abs

idAbsBin : (n : Biz) -> toBizBin (bizAbsBin n) = abs n
idAbsBin  BizO    = Refl
idAbsBin (BizP _) = Refl
idAbsBin (BizM _) = Refl

-- id

bizAbsBinId : (n : Bin) -> bizAbsBin (toBizBin n) = n
bizAbsBinId  BinO    = Refl
bizAbsBinId (BinP _) = Refl

-- [Z.abs_N], basic equations

-- inj_0 is trivial
-- inj_pos is trivial
-- inj_neg is trivial

-- [Z.abs_N] and usual operations, with non-negative integers

-- inj_opp

injOpp : (n : Biz) -> bizAbsBin (-n) = bizAbsBin n
injOpp  BizO    = Refl
injOpp (BizP _) = Refl
injOpp (BizM _) = Refl

-- inj_succ

bizAbsBinInjSucc : (n : Biz) -> 0 `Le` n -> bizAbsBin (bizSucc n) = binSucc (bizAbsBin n)
bizAbsBinInjSucc n zlen =
  rewrite absNNonneg n zlen in
  rewrite absNNonneg (n+1) $ ltLeIncl 0 (n+1) $ ltSuccRFro 0 n zlen in
  toBinBizInjSucc n zlen

-- inj_add

bizAbsBinInjAdd : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsBin (n+m) = bizAbsBin n + bizAbsBin m
bizAbsBinInjAdd n m zlen zlem =
  rewrite absNNonneg n zlen in
  rewrite absNNonneg m zlem in
  let nltnm = zlem
           |> replace {P=\x=>Not (x=GT)}    (sym $ addCompareMonoL n 0 m)
           |> replace {P=\x=> x `Le` (n+m)} (add0R n)
   in
  rewrite absNNonneg (n+m) (leTrans 0 n (n+m) zlen nltnm) in
  toBinBizInjAdd n m zlen zlem

-- inj_mul

bizAbsBinInjMul : (n, m : Biz) -> bizAbsBin (n*m) = bizAbsBin n * bizAbsBin m
bizAbsBinInjMul  BizO     m       = sym $ mulZeroL (bizAbsBin m)
bizAbsBinInjMul  n        BizO    = rewrite mul0R n in
                                    sym $ mulZeroR (bizAbsBin n)
bizAbsBinInjMul (BizP _) (BizP _) = Refl
bizAbsBinInjMul (BizP _) (BizM _) = Refl
bizAbsBinInjMul (BizM _) (BizP _) = Refl
bizAbsBinInjMul (BizM _) (BizM _) = Refl

-- inj_sub

bizAbsBinInjSub : (n, m : Biz) -> 0 `Le` m -> m `Le` n -> bizAbsBin (n-m) = bizAbsBin n - bizAbsBin m
bizAbsBinInjSub n m zlem mlen =
  rewrite absNNonneg n $ leTrans 0 m n zlem mlen in
  rewrite absNNonneg m zlem in
  let zlenm = mlen
           |> replace {P=\x=>Not (x=GT)}   (sym $ addCompareMonoR m n (-m))
           |> replace {P=\x=>x `Le` (n-m)} (addOppDiagR m)
  in
  rewrite absNNonneg (n-m) zlenm in
  toBinBizInjSub n m zlem

-- inj_pred

bizAbsBinInjPred : (n : Biz) -> 0 `Lt` n -> bizAbsBin (bizPred n) = binPred (bizAbsBin n)
bizAbsBinInjPred n zltn =
  rewrite absNNonneg n $ ltLeIncl 0 n zltn in
  rewrite absNNonneg (bizPred n) $
            ltSuccRTo 0 (n-1) $
            rewrite sym $ addAssoc n (-1) 1 in
            rewrite add0R n in
            zltn
    in
  toBinBizInjPred n

-- inj_compare

bizAbsBinInjCompare : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsBin n `compare` bizAbsBin m = n `compare` m
bizAbsBinInjCompare n m zlen zlem =
  rewrite absNNonneg n zlen in
  rewrite absNNonneg m zlem in
  toBinBizInjCompare n m zlen zlem

-- inj_le
-- TODO split into `to` and `fro`

bizAbsBinInjLeTo : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> n `Le` m -> bizAbsBin n `Le` bizAbsBin m
bizAbsBinInjLeTo n m zlen zlem nlem = rewrite bizAbsBinInjCompare n m zlen zlem in
                                      nlem

bizAbsBinInjLeFro : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsBin n `Le` bizAbsBin m -> n `Le` m
bizAbsBinInjLeFro n m zlen zlem nlem = rewrite sym $ bizAbsBinInjCompare n m zlen zlem in
                                       nlem

-- inj_lt
-- TODO split into `to` and `fro`

bizAbsBinInjLtTo : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> n `Lt` m -> bizAbsBin n `Lt` bizAbsBin m
bizAbsBinInjLtTo n m zlen zlem nltm = rewrite bizAbsBinInjCompare n m zlen zlem in
                                      nltm

bizAbsBinInjLtFro : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsBin n `Lt` bizAbsBin m -> n `Lt` m
bizAbsBinInjLtFro n m zlen zlem nltm = rewrite sym $ bizAbsBinInjCompare n m zlen zlem in
                                       nltm

-- inj_min

bizAbsBinInjMin : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsBin (n `min` m) = bizAbsBin n `binMin` bizAbsBin m
bizAbsBinInjMin n m zlen zlem =
  rewrite absNNonneg n zlen in
  rewrite absNNonneg m zlem in
  rewrite absNNonneg (n `min` m) aux in
  toBinBizInjMin n m
  where
  aux : 0 `Le` (n `min` m)
  aux prf with (n `compare` m)
    | LT = absurd $ zlen prf
    | EQ = absurd $ zlem prf
    | GT = absurd $ zlem prf

-- inj_max

bizAbsBinInjMax : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsBin (n `max` m) = bizAbsBin n `binMax` bizAbsBin m
bizAbsBinInjMax n m zlen zlem =
  rewrite absNNonneg n zlen in
  rewrite absNNonneg m zlem in
  rewrite absNNonneg (n `max` m) aux in
  toBinBizInjMax n m
  where
  aux : 0 `Le` (n `max` m)
  aux prf with (n `compare` m)
    | LT = absurd $ zlem prf
    | EQ = absurd $ zlen prf
    | GT = absurd $ zlen prf

-- TODO inj_quot
-- TODO inj_rem
-- these require `toBinBiz` versions above

-- inj_pow

bizAbsBinInjPow : (n, m : Biz) -> 0 `Le` m -> bizAbsBin (bizPow n m) = (binPow (bizAbsBin n) (bizAbsBin m))
bizAbsBinInjPow n m zlem =
  rewrite absNNonneg m zlem in
  rewrite absNSpec n in
  rewrite absNSpec (bizPow n m) in
  rewrite absPow n m in
  toBinBizInjPow (abs n) m (absNonneg n) zlem

-- [Z.abs_N] and usual operations, statements with [Z.abs]

-- inj_succ_abs

bizAbsBinInjSuccAbs : (n : Biz) -> bizAbsBin (bizSucc (abs n)) = binSucc (bizAbsBin n)
bizAbsBinInjSuccAbs  BizO    = Refl
bizAbsBinInjSuccAbs (BizP a) = cong $ add1R a
bizAbsBinInjSuccAbs (BizM a) = cong $ add1R a

-- inj_add_abs

bizAbsBinInjAddAbs : (n, m : Biz) -> bizAbsBin (abs n + abs m) = bizAbsBin n + bizAbsBin m
bizAbsBinInjAddAbs  BizO     m       =
  rewrite addZeroL (bizAbsBin m) in
  rewrite absNNonneg (abs m) (absNonneg m) in
  sym $ absNSpec m
bizAbsBinInjAddAbs  n        BizO    =
  rewrite add0R (abs n) in
  rewrite addZeroR (bizAbsBin n) in
  rewrite absNNonneg (abs n) (absNonneg n) in
  sym $ absNSpec n
bizAbsBinInjAddAbs (BizP _) (BizP _) = Refl
bizAbsBinInjAddAbs (BizP _) (BizM _) = Refl
bizAbsBinInjAddAbs (BizM _) (BizP _) = Refl
bizAbsBinInjAddAbs (BizM _) (BizM _) = Refl

-- inj_mul_abs

bizAbsBinInjMulAbs : (n, m : Biz) -> bizAbsBin (abs n * abs m) = bizAbsBin n * bizAbsBin m
bizAbsBinInjMulAbs  BizO     m       = sym $ mulZeroL (bizAbsBin m)
bizAbsBinInjMulAbs  n        BizO    = rewrite mul0R (abs n) in
                                       sym $ mulZeroR (bizAbsBin n)
bizAbsBinInjMulAbs (BizP _) (BizP _) = Refl
bizAbsBinInjMulAbs (BizP _) (BizM _) = Refl
bizAbsBinInjMulAbs (BizM _) (BizP _) = Refl
bizAbsBinInjMulAbs (BizM _) (BizM _) = Refl

-- Conversions between [Z] and [nat]

-- Nat2Z

-- [Z.of_nat]

-- inj_0 is trivial

-- inj_succ

toBizNatInjSucc : (n : Nat) -> toBizNat (S n) = bizSucc (toBizNat n)
toBizNatInjSucc  Z    = Refl
toBizNatInjSucc (S k) = cong $ sym $ add1R (toBipNatSucc k)

-- [Z.of_N] produce non-negative integers

-- is_nonneg

toBizNatIsNonneg : (n : Nat) -> 0 `Le` toBizNat n
toBizNatIsNonneg  Z    = uninhabited
toBizNatIsNonneg (S _) = uninhabited

-- [Z.of_nat] is a bijection between [nat] and non-negative [Z], with [Z.to_nat]
-- (or [Z.abs_nat]) as reciprocal.

-- id

toBizNatId : (n : Nat) -> toNatBiz (toBizNat n) = n
toBizNatId n =
  rewrite sym $ natNZ n in
  rewrite sym $ zNNat (toBizBin $ toBinNat n) in
  rewrite toBizBinId (toBinNat n) in
  toBinId n

-- [Z.of_nat] is hence injective

-- inj

toBizNatInj : (n, m : Nat) -> toBizNat n = toBizNat m -> n = m
toBizNatInj n m prf =
  rewrite sym $ toBizNatId n in
  rewrite sym $ toBizNatId m in
  cong prf

-- inj_iff is just inj + cong

-- [Z.of_nat] and usual operations

-- inj_compare

toBizNatInjCompare : (n, m : Nat) -> toBizNat n `compare` toBizNat m = n `compare` m
toBizNatInjCompare n m =
  rewrite sym $ natNZ n in
  rewrite sym $ natNZ m in
  rewrite toBizBinInjCompare (toBinNat n) (toBinNat m) in
  sym $ toBinInjCompare n m

-- inj_le
-- inj_lt
-- inj_ge
-- inj_gt
-- TODO `Lt`/`Le`/etc are not defined for Nats, but these are pretty simple anyway

-- inj_abs_nat

toBizNatInjAbsNat : (z : Biz) -> toBizNat (bizAbsNat z) = abs z
toBizNatInjAbsNat  BizO    = Refl
toBizNatInjAbsNat (BizP a) =
  let (b**prf) = isSucc a in
  rewrite prf in
  cong $ toBipSuccInv b a prf
toBizNatInjAbsNat (BizM a) =
  let (b**prf) = isSucc a in
  rewrite prf in
  cong $ toBipSuccInv b a prf

-- inj_add

toBizNatInjAdd : (n, m : Nat) -> toBizNat (n+m) = toBizNat n + toBizNat m
toBizNatInjAdd n m =
  rewrite sym $ natNZ (n+m) in
  rewrite toBinInjAdd n m in
  rewrite sym $ natNZ n in
  rewrite sym $ natNZ m in
  toBizBinInjAdd (toBinNat n) (toBinNat m)

-- inj_mul

toBizNatInjMul : (n, m : Nat) -> toBizNat (n*m) = toBizNat n * toBizNat m
toBizNatInjMul n m =
  rewrite sym $ natNZ (n*m) in
  rewrite toBinInjMul n m in
  rewrite sym $ natNZ n in
  rewrite sym $ natNZ m in
  toBizBinInjMul (toBinNat n) (toBinNat m)

-- inj_sub_max

toBizNatInjSubMax : (n, m : Nat) -> toBizNat (n `minus` m) = 0 `max` (toBizNat n - toBizNat m)
toBizNatInjSubMax n m =
  rewrite sym $ natNZ (n `minus` m) in
  rewrite toBinInjSub n m in
  rewrite sym $ natNZ n in
  rewrite sym $ natNZ m in
  toBizBinInjSubMax (toBinNat n) (toBinNat m)

-- inj_sub

toBizNatInjSub : (n, m : Nat) -> m `LTE` n -> toBizNat (n `minus` m) = toBizNat n - toBizNat m
toBizNatInjSub n m mlen =
  rewrite sym $ natNZ (n `minus` m) in
  rewrite toBinInjSub n m in
  rewrite sym $ natNZ n in
  rewrite sym $ natNZ m in
  toBizBinInjSub (toBinNat n) (toBinNat m) (natBinLe m n mlen)

-- inj_pred_max

toBizNatInjPredMax : (n : Nat) -> toBizNat (pred n) = 0 `max` bizPred (toBizNat n)
toBizNatInjPredMax n =
  rewrite sym $ natNZ (pred n) in
  rewrite toBinInjPred n in
  rewrite sym $ natNZ n in
  toBizBinInjPredMax (toBinNat n)

-- inj_pred
-- TODO using 1 `LTE` here instead of 0 `LT` because it clashes with Ord
toBizNatInjPred : (n : Nat) -> 1 `LTE` n -> toBizNat (pred n) = bizPred (toBizNat n)
toBizNatInjPred n ulen =
  rewrite sym $ natNZ (pred n) in
  rewrite toBinInjPred n in
  rewrite sym $ natNZ n in
  toBizBinInjPred (toBinNat n) (leSuccLTo 0 (toBinNat n) $ natBinLe 1 n ulen)

-- inj_min
-- inj_max
-- TODO these depend on `toBinInj` versions, see Bin.Nat

-- Z2Nat

-- [Z.to_nat] is a bijection between non-negative [Z] and [nat], with
-- [Pos.of_nat] as reciprocal

-- id

toNatBizId : (n : Biz) -> 0 `Le` n -> toBizNat (toNatBiz n) = n
toNatBizId n zlen =
  rewrite sym $ zNNat n in
  rewrite sym $ natNZ (toNatBin $ toBinBiz n) in
  rewrite toNatId (toBinBiz n) in
  toBinBizId n zlen

-- [Z.to_nat] is hence injective for non-negative integers

-- inj

toNatBizInj : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toNatBiz n = toNatBiz m -> n = m
toNatBizInj n m zlen zlem prf =
  rewrite sym $ toNatBizId n zlen in
  rewrite sym $ toNatBizId m zlem in
  cong prf

-- inj_iff is just inj + cong

-- [Z.to_nat], basic equations

-- inj_0 is trivial
-- inj_pos is trivial
-- inj_neg is trivial

-- [Z.to_nat] and operations

-- inj_add

toNatBizInjAdd : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toNatBiz (n+m) = toNatBiz n + toNatBiz m
toNatBizInjAdd n m zlen zlem =
  rewrite sym $ zNNat (n+m) in
  rewrite toBinBizInjAdd n m zlen zlem in
  rewrite sym $ zNNat n in
  rewrite sym $ zNNat m in
  toNatInjAdd (toBinBiz n) (toBinBiz m)

-- inj_mul

toNatBizInjMul : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toNatBiz (n*m) = toNatBiz n * toNatBiz m
toNatBizInjMul n m zlen zlem =
  rewrite sym $ zNNat (n*m) in
  rewrite toBinBizInjMul n m zlen zlem in
  rewrite sym $ zNNat n in
  rewrite sym $ zNNat m in
  toNatInjMul (toBinBiz n) (toBinBiz m)

-- inj_succ

toNatBizInjSucc : (n : Biz) -> 0 `Le` n -> toNatBiz (bizSucc n) = S (toNatBiz n)
toNatBizInjSucc n zlen =
  rewrite sym $ zNNat (bizSucc n) in
  rewrite toBinBizInjSucc n zlen in
  rewrite sym $ zNNat n in
  toNatInjSucc (toBinBiz n)

-- inj_sub

toNatBizInjSub : (n, m : Biz) -> 0 `Le` m -> toNatBiz (n - m) = toNatBiz n `minus` toNatBiz m
toNatBizInjSub n m zlem =
  rewrite sym $ zNNat (n-m) in
  rewrite toBinBizInjSub n m zlem in
  rewrite sym $ zNNat n in
  rewrite sym $ zNNat m in
  toNatInjSub (toBinBiz n) (toBinBiz m)

-- inj_pred

toNatBizInjPred : (n : Biz) -> toNatBiz (bizPred n) = pred (toNatBiz n)
toNatBizInjPred n =
  rewrite sym $ zNNat (bizPred n) in
  rewrite toBinBizInjPred n in
  rewrite sym $ zNNat n in
  toNatInjPred (toBinBiz n)

-- inj_compare

toNatBizInjCompare : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> toNatBiz n `compare` toNatBiz m = n `compare` m
toNatBizInjCompare n m zlen zlem =
  rewrite sym $ toBizNatInjCompare (toNatBiz n) (toNatBiz m) in
  rewrite toNatBizId n zlen in
  rewrite toNatBizId m zlem in
  Refl

-- inj_le
-- inj_lt
-- TODO `Lt`/`Le` are not defined for Nats, but these are pretty simple anyway

-- inj_min
-- inj_max
-- TODO these depend on `toNatInj` versions, see Bin.Nat

-- Zabs2Nat

-- Results about [Z.abs_nat], converting absolute values of [Z] integers to
-- [nat].

-- abs_nat_spec

absNatSpec : (n : Biz) -> bizAbsNat n = toNatBiz (abs n)
absNatSpec  BizO    = Refl
absNatSpec (BizP _) = Refl
absNatSpec (BizM _) = Refl

-- abs_nat_nonneg

absNatNonneg : (n : Biz) -> 0 `Le` n -> bizAbsNat n = toNatBiz n
absNatNonneg  BizO    _    = Refl
absNatNonneg (BizP _) _    = Refl
absNatNonneg (BizM _) zlen = absurd $ zlen Refl

-- id_abs

idAbsNat : (n : Biz) -> toBizNat (bizAbsNat n) = abs n
idAbsNat n =
  rewrite sym $ zAbsNNat n in
  rewrite nNatZ (bizAbsBin n) in
  injAbsN n

-- id

bizAbsNatId : (n : Nat) -> bizAbsNat (toBizNat n) = n
bizAbsNatId n =
  rewrite sym $ zAbsNNat (toBizNat n) in
  rewrite sym $ natNZ n in
  rewrite bizAbsBinId (toBinNat n) in
  toBinId n

-- [Z.abs_nat], basic equations

-- inj_0 is trivial
-- inj_pos is trivial
-- inj_neg is trivial

-- [Z.abs_nat] and usual operations, with non-negative integers

-- inj_succ

bizAbsNatInjSucc : (n : Biz) -> 0 `Le` n -> bizAbsNat (bizSucc n) = S (bizAbsNat n)
bizAbsNatInjSucc n zlen =
  rewrite sym $ zAbsNNat (bizSucc n) in
  rewrite bizAbsBinInjSucc n zlen in
  rewrite sym $ zAbsNNat n in
  toNatInjSucc (bizAbsBin n)

-- inj_add

bizAbsNatInjAdd : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsNat (n+m) = bizAbsNat n + bizAbsNat m
bizAbsNatInjAdd n m zlen zlem =
  rewrite sym $ zAbsNNat (n+m) in
  rewrite bizAbsBinInjAdd n m zlen zlem in
  rewrite sym $ zAbsNNat n in
  rewrite sym $ zAbsNNat m in
  toNatInjAdd (bizAbsBin n) (bizAbsBin m)

-- inj_mul

bizAbsNatInjMul : (n, m : Biz) -> bizAbsNat (n*m) = bizAbsNat n * bizAbsNat m
bizAbsNatInjMul n m =
  rewrite sym $ zAbsNNat (n*m) in
  rewrite bizAbsBinInjMul n m in
  rewrite sym $ zAbsNNat n in
  rewrite sym $ zAbsNNat m in
  toNatInjMul (bizAbsBin n) (bizAbsBin m)

-- inj_sub

bizAbsNatInjSub : (n, m : Biz) -> 0 `Le` m -> m `Le` n -> bizAbsNat (n-m) = bizAbsNat n `minus` bizAbsNat m
bizAbsNatInjSub n m zlem mlen =
  rewrite sym $ zAbsNNat (n-m) in
  rewrite bizAbsBinInjSub n m zlem mlen in
  rewrite sym $ zAbsNNat n in
  rewrite sym $ zAbsNNat m in
  toNatInjSub (bizAbsBin n) (bizAbsBin m)

-- inj_pred

bizAbsNatInjPred : (n : Biz) -> 0 `Lt` n -> bizAbsNat (bizPred n) = pred (bizAbsNat n)
bizAbsNatInjPred n zltn =
  rewrite sym $ zAbsNNat (bizPred n) in
  rewrite bizAbsBinInjPred n zltn in
  rewrite sym $ zAbsNNat n in
  toNatInjPred (bizAbsBin n)

-- inj_compare

bizAbsNatInjCompare : (n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizAbsNat n `compare` bizAbsNat m = n `compare` m
bizAbsNatInjCompare n m zlen zlem =
  rewrite sym $ zAbsNNat n in
  rewrite sym $ zAbsNNat m in
  rewrite sym $ toNatInjCompare (bizAbsBin n) (bizAbsBin m) in
  bizAbsBinInjCompare n m zlen zlem

-- inj_le
-- inj_lt
-- TODO `Lt`/`Le` are not defined for Nats

-- inj_min
-- inj_max
-- TODO these depend on `toNatInj` versions, see Bin.Nat

-- [Z.abs_nat] and usual operations, statements with [Z.abs]

-- inj_succ_abs

bizAbsNatInjSuccAbs : (n : Biz) -> bizAbsNat (bizSucc (abs n)) = S (bizAbsNat n)
bizAbsNatInjSuccAbs n =
  rewrite sym $ zAbsNNat (bizSucc (abs n)) in
  rewrite bizAbsBinInjSuccAbs n in
  rewrite sym $ zAbsNNat n in
  toNatInjSucc (bizAbsBin n)

-- inj_add_abs

bizAbsNatInjAddAbs : (n, m : Biz) -> bizAbsNat (abs n + abs m) = bizAbsNat n + bizAbsNat m
bizAbsNatInjAddAbs n m =
  rewrite sym $ zAbsNNat (abs n + abs m) in
  rewrite bizAbsBinInjAddAbs n m  in
  rewrite sym $ zAbsNNat n in
  rewrite sym $ zAbsNNat m in
  toNatInjAdd (bizAbsBin n) (bizAbsBin m)

-- inj_mul_abs

bizAbsNatInjMulAbs : (n, m : Biz) -> bizAbsNat (abs n * abs m) = bizAbsNat n * bizAbsNat m
bizAbsNatInjMulAbs n m =
  rewrite sym $ zAbsNNat (abs n * abs m) in
  rewrite bizAbsBinInjMulAbs n m  in
  rewrite sym $ zAbsNNat n in
  rewrite sym $ zAbsNNat m in
  toNatInjMul (bizAbsBin n) (bizAbsBin m)