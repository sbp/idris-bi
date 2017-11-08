module Data.Bin.Nat

import Data.Util

import Data.Bip.AddMul
import Data.Bip.OrdSub
import Data.Bip.Nat

import Data.Bin
import Data.Bin.AddSubMul
import Data.Bin.Ord

%access public export
%default total

-- N2Nat
-- Conversions from [N] to [nat]

-- [N.to_nat] is a bijection between [N] and [nat], with [Pos.of_nat] as reciprocal

-- id

toNatId : (a : Bin) -> toBinNat (toNatBin a) = a
toNatId  BinO    = Refl
toNatId (BinP a) =
  let (n**prf) = isSucc a in
  rewrite prf in
  cong $
  toNatInj (toBipNatSucc n) a $
  rewrite prf in
  toNatIdSucc n

-- [N.to_nat] is hence injective

-- inj

toNatInj : (a, a1 : Bin) -> toNatBin a = toNatBin a1 -> a = a1
toNatInj a a1 prf =
  rewrite sym $ toNatId a in
  rewrite sym $ toNatId a1 in
  cong prf

-- inj_iff is just inj + cong

-- Interaction of this translation and usual operations.

-- inj_double

toNatInjDouble : (a : Bin) -> toNatBin (binD a) = 2*(toNatBin a)
toNatInjDouble  BinO    = Refl
toNatInjDouble (BinP a) = injXO a

-- inj_succ_double

toNatInjSuccDouble : (a : Bin) -> toNatBin (binDPO a) = S (2*(toNatBin a))
toNatInjSuccDouble BinO = Refl
toNatInjSuccDouble (BinP a) = injXI a

-- inj_succ

toNatInjSucc : (a : Bin) -> toNatBin (binSucc a) = S (toNatBin a)
toNatInjSucc BinO = Refl
toNatInjSucc (BinP a) = toNatInjSucc a

-- inj_add

toNatInjAdd : (a, a1 : Bin) -> toNatBin (a + a1) = toNatBin a + toNatBin a1
toNatInjAdd  BinO     BinO    = Refl
toNatInjAdd  BinO    (BinP _) = Refl
toNatInjAdd (BinP a)  BinO    = sym $ plusZeroRightNeutral (toNatBip a)
toNatInjAdd (BinP a) (BinP b) = toNatInjAdd a b

-- inj_mul

toNatInjMul : (a, a1 : Bin) -> toNatBin (a * a1) = toNatBin a * toNatBin a1
toNatInjMul  BinO     BinO    = Refl
toNatInjMul  BinO    (BinP _) = Refl
toNatInjMul (BinP a)  BinO    = sym $ multZeroRightZero (toNatBip a)
toNatInjMul (BinP a) (BinP b) = toNatInjMul a b

-- inj_sub

toNatInjSub : (a, a1 : Bin) -> toNatBin (a - a1) = toNatBin a `minus` toNatBin a1
toNatInjSub  BinO     BinO    = Refl
toNatInjSub  BinO    (BinP _) = Refl
toNatInjSub (BinP a)  BinO    = sym $ minusZeroRight (toNatBip a)
toNatInjSub (BinP a) (BinP b) =
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

toNatInjPred : (a : Bin) -> toNatBin (binPred a) = pred (toNatBin a)
toNatInjPred a = rewrite predOfMinus (toNatBin a) in
                 rewrite predSub a in
                  toNatInjSub a 1

-- inj_div2
-- TODO there's no div2 on Nats, use divNatNZ?

-- inj_compare

toNatInjCompare : (a, a1 : Bin) -> a `compare` a1 = toNatBin a `compare` toNatBin a1
toNatInjCompare  BinO     BinO    = Refl
toNatInjCompare  BinO    (BinP b) = rewrite snd $ isSucc b in
                                    Refl
toNatInjCompare (BinP a)  BinO    = rewrite snd $ isSucc a in
                                    Refl
toNatInjCompare (BinP a) (BinP b) = toNatInjCompare a b

-- inj_max
-- inj_min
-- TODO can't figure out signatures for aux after rewriting with injCompare

-- inj_iter

toNatInjIter : (f : a -> a) -> (x : a) -> (n : Bin) -> binIter f n x = natIter f x (toNatBin n)
toNatInjIter _ _  BinO    = Refl
toNatInjIter f x (BinP a) = injIter f x a

-- Nat2N
-- Conversions from [nat] to [N]

-- id

toBinId : (n : Nat) -> toNatBin (toBinNat n) = n
toBinId  Z    = Refl
toBinId (S k) = toNatIdSucc k

-- [N.of_nat] is hence injective
-- inj

toBinInj : (n, n1 : Nat) -> toBinNat n = toBinNat n1 -> n = n1
toBinInj n n1 prf =
  rewrite sym $ toBinId n in
  rewrite sym $ toBinId n1 in
  cong prf

-- inj_iff is just inj + cong

-- Interaction of this translation and usual operations.

-- inj_double

toBinInjDouble : (n : Nat) -> toBinNat (2*n) = binD (toBinNat n)
toBinInjDouble n = toNatInj (toBinNat $ 2*n) (binD $ toBinNat n) $
                   rewrite toBinId (2*n) in
                   rewrite toNatInjDouble (toBinNat n) in
                   rewrite toBinId n in
                   Refl

-- inj_succ_double

toBinInjSuccDouble : (n : Nat) -> toBinNat (S (2*n)) = binDPO (toBinNat n)
toBinInjSuccDouble n = toNatInj (toBinNat $ S (2*n)) (binDPO $ toBinNat n) $
                       rewrite toBinId $ S (2*n) in
                       rewrite toNatInjSuccDouble (toBinNat n) in
                       rewrite toBinId n in
                       Refl

-- inj_succ

toBinInjSucc : (n : Nat) -> toBinNat (S n) = binSucc (toBinNat n)
toBinInjSucc n = toNatInj (toBinNat $ S n) (binSucc $ toBinNat n) $
                 rewrite toBinId $ S n in
                 rewrite toNatInjSucc (toBinNat n) in
                 rewrite toBinId n in
                 Refl

-- inj_pred

toBinInjPred : (n : Nat) -> toBinNat (pred n) = binPred (toBinNat n)
toBinInjPred n = toNatInj (toBinNat $ pred n) (binPred $ toBinNat n) $
                 rewrite toBinId $ pred n in
                 rewrite toNatInjPred (toBinNat n) in
                 rewrite toBinId n in
                 Refl

-- inj_add

toBinInjAdd : (n, n1 : Nat) -> toBinNat (n + n1) = toBinNat n + toBinNat n1
toBinInjAdd n n1 = toNatInj (toBinNat $ n + n1) (toBinNat n + toBinNat n1) $
                   rewrite toBinId $ n + n1 in
                   rewrite toNatInjAdd (toBinNat n) (toBinNat n1) in
                   rewrite toBinId n in
                   rewrite toBinId n1 in
                   Refl

-- inj_sub

toBinInjSub : (n, n1 : Nat) -> toBinNat (n `minus` n1) = toBinNat n - toBinNat n1
toBinInjSub n n1 = toNatInj (toBinNat $ n `minus` n1) (toBinNat n - toBinNat n1) $
                   rewrite toBinId $ n `minus` n1 in
                   rewrite toNatInjSub (toBinNat n) (toBinNat n1) in
                   rewrite toBinId n in
                   rewrite toBinId n1 in
                   Refl

-- inj_mul

toBinInjMul : (n, n1 : Nat) -> toBinNat (n * n1) = toBinNat n * toBinNat n1
toBinInjMul n n1 = toNatInj (toBinNat $ n * n1) (toBinNat n * toBinNat n1) $
                   rewrite toBinId $ n * n1 in
                   rewrite toNatInjMul (toBinNat n) (toBinNat n1) in
                   rewrite toBinId n in
                   rewrite toBinId n1 in
                   Refl

-- inj_div2
-- TODO see above

-- inj_compare

toBinInjCompare : (n, n1 : Nat) -> n `compare` n1 = toBinNat n `compare` toBinNat n1
toBinInjCompare n n1 = rewrite toNatInjCompare (toBinNat n) (toBinNat n1) in
                       rewrite toBinId n in
                       rewrite toBinId n1 in
                       Refl

-- inj_min
-- inj_max
-- TODO see above

-- inj_iter

toBinInjIter : (f : a -> a) -> (x : a) -> (n : Nat) -> natIter f x n = binIter f (toBinNat n) x
toBinInjIter f x n = rewrite toNatInjIter f x (toBinNat n) in
                     rewrite toBinId n in
                     Refl

natBinLe : (n, m : Nat) -> n `LTE` m -> toBinNat n `Le` toBinNat m
natBinLe  Z     Z    _    = uninhabited
natBinLe  Z    (S _) _    = uninhabited
natBinLe (S _)  Z    nlem = absurd $ succNotLTEzero nlem
natBinLe (S k) (S l) nlem = rewrite sym $ toBinInjCompare (S k) (S l) in
                            replace {P=\x=> Not (x=GT)} (sym $ toBinInjCompare k l) (natBinLe k l $ fromLteSucc nlem)