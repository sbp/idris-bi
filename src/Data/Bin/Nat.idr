module Data.Bin.Nat

import Data.Bin

import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.Nat

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
      sym $ help (toNatBip a) (toNatBip b) (injLt a b altb)
    Left $ Right blta =>
      let (r**(prf, prf1)) = subMaskPos' a b blta in
      rewrite prf in
      plusRightCancel (toNatBip r) ((toNatBip a) `minus` (toNatBip b)) (toNatBip b) $
      rewrite help2 (toNatBip a) (toNatBip b) (injLt b a blta) in
      rewrite sym prf1 in
      rewrite addComm b r in
      sym $ toNatInjAdd r b
    Right aeqb =>
      rewrite aeqb in
      rewrite subMaskDiag b in
      minusZeroN (toNatBip b)
  where
  help : (a,b : Nat) -> a `compare` b = LT -> a `minus` b = Z
  help  Z     Z    = absurd
  help  Z    (S _) = const Refl
  help (S _)  Z    = absurd
  help (S k) (S j) = help k j
  help2 : (a, b : Nat) -> b `compare` a = LT -> (a `minus` b)+b = a
  help2  Z     Z    prf = absurd prf
  help2  Z    (S _) prf = absurd prf
  help2 (S k)  Z    prf = cong $ plusZeroRightNeutral k
  help2 (S k) (S j) prf = rewrite sym $ plusSuccRightSucc (k `minus` j) j in
                          cong $ help2 k j prf
