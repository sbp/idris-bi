module Data.Biz.Nat

import Data.Bip
import Data.Bip.Nat

import Data.Bin
import Data.Bin.Nat

import Data.Biz

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
