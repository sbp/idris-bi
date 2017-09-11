module Data.Bin.Nat

import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.Nat

import Data.Bin
import Data.Bin.Proofs

%access public export
%default total

-- N2Nat
-- Conversions from [N] to [nat]

-- [N.to_nat] is a bijection between [N] and [nat], with [Pos.of_nat] as reciprocal

-- id

id : (a : Bin) -> toBinNat (toNatBin a) = a
id  BinO    = Refl
id (BinP a) =
  let (n**prf) = isSucc a in
  rewrite prf in
  cong $
  toNatInj (toBipNatSucc n) a $
  rewrite prf in
  toNatIdSucc n

-- [N.to_nat] is hence injective

-- inj

inj : (a, a1 : Bin) -> toNatBin a = toNatBin a1 -> a = a1
inj a a1 prf =
  rewrite sym $ id a in
  rewrite sym $ id a1 in
  cong prf

-- inj_iff is just inj + cong

-- Interaction of this translation and usual operations.

-- inj_double

injDouble : (a : Bin) -> toNatBin (binD a) = 2*(toNatBin a)
injDouble  BinO    = Refl
injDouble (BinP a) = injXO a

-- inj_succ_double

injSuccDouble : (a : Bin) -> toNatBin (binDPO a) = S (2*(toNatBin a))
injSuccDouble BinO = Refl
injSuccDouble (BinP a) = injXI a

-- inj_succ

injSucc : (a : Bin) -> toNatBin (binSucc a) = S (toNatBin a)
injSucc BinO = Refl
injSucc (BinP a) = toNatInjSucc a

-- inj_add

injAdd : (a, a1 : Bin) -> toNatBin (a + a1) = toNatBin a + toNatBin a1
injAdd  BinO     BinO    = Refl
injAdd  BinO    (BinP _) = Refl
injAdd (BinP a)  BinO    = sym $ plusZeroRightNeutral (toNatBip a)
injAdd (BinP a) (BinP b) = toNatInjAdd a b

-- inj_mul

injMul : (a, a1 : Bin) -> toNatBin (a * a1) = toNatBin a * toNatBin a1
injMul  BinO     BinO    = Refl
injMul  BinO    (BinP _) = Refl
injMul (BinP a)  BinO    = sym $ multZeroRightZero (toNatBip a)
injMul (BinP a) (BinP b) = toNatInjMul a b

-- inj_sub

injSub : (a, a1 : Bin) -> toNatBin (a - a1) = toNatBin a `minus` toNatBin a1
injSub  BinO     BinO    = Refl
injSub  BinO    (BinP _) = Refl
injSub (BinP a)  BinO    = sym $ minusZeroRight (toNatBip a)
injSub (BinP a) (BinP b) =
  case ltTotal a b of
    Left $ Left altb =>
      rewrite subMaskNeg a b altb in
      sym $ minusLtZ (toNatBip a) (toNatBip b) (injLt a b altb)
    Left $ Right blta =>
      let (r**(prf, prf1)) = subMaskPos' a b blta in
      rewrite prf in
      plusRightCancel (toNatBip r) ((toNatBip a) `minus` (toNatBip b)) (toNatBip b) $
      rewrite minusPlus (toNatBip a) (toNatBip b) (injLt b a blta) in
      rewrite sym prf1 in
      rewrite addComm b r in
      sym $ toNatInjAdd r b
    Right aeqb =>
      rewrite aeqb in
      rewrite subMaskDiag b in
      minusZeroN $ toNatBip b
  where
  minusLtZ : (a, b : Nat) -> a `compare` b = LT -> a `minus` b = Z
  minusLtZ  Z     Z    = absurd
  minusLtZ  Z    (S _) = const Refl
  minusLtZ (S _)  Z    = absurd
  minusLtZ (S k) (S j) = minusLtZ k j
  minusPlus : (a, b : Nat) -> b `compare` a = LT -> (a `minus` b)+b = a
  minusPlus  Z     Z    prf = absurd prf
  minusPlus  Z    (S _) prf = absurd prf
  minusPlus (S k)  Z    prf = cong $ plusZeroRightNeutral k
  minusPlus (S k) (S j) prf = rewrite sym $ plusSuccRightSucc (k `minus` j) j in
                              cong $ minusPlus k j prf

-- inj_pred

-- TODO add to Prelude.Nat ?
predOfMinus : (n : Nat) -> pred n = n `minus` 1
predOfMinus  Z    = Refl
predOfMinus (S k) = sym $ minusZeroRight k

injPred : (a : Bin) -> toNatBin (binPred a) = pred (toNatBin a)
injPred a = rewrite predOfMinus (toNatBin a) in
            rewrite predSub a in
            injSub a 1

-- inj_div2
-- TODO there's no div2 on Nats, use divNatNZ?

-- inj_compare

injCompare : (a, a1 : Bin) -> a `compare` a1 = (toNatBin a) `compare` (toNatBin a1)
injCompare  BinO     BinO    = Refl
injCompare  BinO    (BinP b) = rewrite snd $ isSucc b in
                               Refl
injCompare (BinP a)  BinO    = rewrite snd $ isSucc a in
                               Refl
injCompare (BinP a) (BinP b) = toNatInjCompare a b

-- inj_max
-- inj_min
-- TODO can't figure out signatures for aux after rewriting with injCompare

-- inj_iter

injIter : (f : a -> a) -> (x : a) -> (n : Bin) -> binIter f n x = natIter f x (toNatBin n)
injIter _ _ BinO = Refl
injIter f x (BinP a) = injIter f x a



