module Data.Bin.Nat

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub

%access public export
%default total

-- TODO move to other toBipNat proofs lower

-- of_nat_succ

ofNatSucc : (n : Nat) -> toBipNatSucc n = toBipNat (S n)
ofNatSucc  Z    = Refl
ofNatSucc (S k) = cong $ ofNatSucc k

--- pred_of_succ_nat

predOfSuccNat : (n : Nat) -> bipPred (toBipNatSucc n) = toBipNat n
predOfSuccNat Z = Refl
predOfSuccNat (S k) = rewrite predSucc (toBipNatSucc k) in
                      ofNatSucc k

-- succ_of_nat

succOfNat : (n : Nat) -> Not (n=Z) -> bipSucc (toBipNat n) = toBipNatSucc n
succOfNat  Z    contra = absurd $ contra Refl
succOfNat (S k) _      = cong $ sym $ ofNatSucc k


-- Properties of the injection from binary positive numbers to Peano natural
-- numbers

-- inj_succ

bipMultNatSucc : (p : Bip) -> (n : Nat) -> bipMultNat (bipSucc p) n = n + bipMultNat p n
bipMultNatSucc  U    _ = Refl
bipMultNatSucc (O _) _ = Refl
bipMultNatSucc (I a) n = rewrite plusAssociative n n (bipMultNat a (n+n)) in
                         bipMultNatSucc a (n+n)

injSucc : (p : Bip) -> toNatBip (bipSucc p) = S (toNatBip p)
injSucc p = bipMultNatSucc p 1

-- inj_add

bipMultNatAdd : (p, q : Bip) -> (n : Nat) -> bipMultNat (p+q) n = bipMultNat p n + bipMultNat q n
bipMultNatAdd p q n =
  peanoRect
  (\x => bipMultNat (x+q) n = bipMultNat x n + bipMultNat q n)
  (rewrite add1L q in
   bipMultNatSucc q n)
  (\p', prf =>
    rewrite addSuccL p' q in
    rewrite bipMultNatSucc (p'+q) n in
    rewrite bipMultNatSucc p' n in
    rewrite sym $ plusAssociative n (bipMultNat p' n) (bipMultNat q n) in
    cong prf
  )
  p

injAdd : (p, q : Bip) -> toNatBip (p+q) = toNatBip p + toNatBip q
injAdd p q = bipMultNatAdd p q 1

-- inj_mul

injMul : (p, q : Bip) -> toNatBip (p*q) = toNatBip p * toNatBip q
injMul p q =
  peanoRect
    (\x => toNatBip (x*q) = toNatBip x * toNatBip q)
    (rewrite plusZeroRightNeutral $ toNatBip q in
     Refl)
    (\p',prf =>
      rewrite mulSuccL p' q in
      rewrite injSucc p' in
      rewrite injAdd q (p'*q) in
      cong {f=plus (toNatBip q)} prf
    )
    p

-- inj_1 is trivial

-- inj_xO

injXO : (p : Bip) -> toNatBip (O p) = 2 * toNatBip p
injXO p = rewrite plusZeroRightNeutral $ toNatBip p in
          rewrite sym $ injAdd p p in
          rewrite addDiag p in
          Refl

-- inj_xI

injXI : (p : Bip) -> toNatBip (I p) = S (2 * toNatBip p)
injXI p = cong $ injXO p

-- is_succ

isSucc : (p : Bip) -> (n ** toNatBip p = S n)
isSucc =
  peanoRect
    (\x => (n ** toNatBip x = S n))
    (Z ** Refl)
    (\p, (n**prf) =>
      rewrite injSucc p in
      (S n ** cong prf)
    )

-- is_pos
-- TODO can't use Nat.LT here, it clashes

isPos : (p : Bip) -> 1 `LTE` (toNatBip p)
isPos p = rewrite snd $ isSucc p in
          LTESucc LTEZero

-- id

toNatBipId : (p : Bip) -> toBipNat $ toNatBip p = p
toNatBipId p =
  peanoRect
    (\x => toBipNat $ toNatBip x = x)
    Refl
    (\p',prf =>
      rewrite injSucc p' in
      let (_**prfn) = isSucc p' in
      rewrite prfn in
      rewrite sym prfn in
      cong prf
    )
    p

-- inj

toNatBipInj : (p, q : Bip) -> toNatBip p = toNatBip q -> p = q
toNatBipInj p q prf =
  rewrite sym $ toNatBipId p in
  rewrite sym $ toNatBipId q in
  rewrite prf in
  Refl

-- inj_iff: `fro` is just `cong`

------------------------------ Nat utility proofs ------------------------------
-- TODO add to Prelude?

ltPlusNZ : (a,b : Nat) -> a `compare` (a+(S b)) = LT
ltPlusNZ  Z    _ = Refl
ltPlusNZ (S k) b = ltPlusNZ k b

compareRefl : (a : Nat) -> a `compare` a = EQ
compareRefl  Z    = Refl
compareRefl (S k) = compareRefl k

ltGt : (a,b : Nat) -> a `compare` b = LT -> b `compare` a = GT
ltGt  Z     Z    = absurd
ltGt  Z    (S _) = const Refl
ltGt (S _)  Z    = absurd
ltGt (S k) (S j) = ltGt k j

plusMinus : (a, b : Nat) -> b `compare` a = LT -> (a `minus` b)+b = a
plusMinus  Z     Z    blta = absurd blta
plusMinus  Z    (S _) blta = absurd blta
plusMinus (S k)  Z    blta = rewrite plusZeroRightNeutral k in Refl
plusMinus (S k) (S j) blta = rewrite sym $ plusSuccRightSucc (k `minus` j) j in
                             cong $ plusMinus k j blta

minusNeg : (p, q : Nat) -> p `compare` q = LT -> p `minus` q = Z
minusNeg  Z     Z    = absurd
minusNeg  Z    (S _) = const Refl
minusNeg (S _)  Z    = absurd
minusNeg (S k) (S j) = minusNeg k j

minusPos : (p, q : Nat) -> q `compare` p = LT -> 1 `LTE` (p `minus` q)
minusPos  Z     Z    = absurd
minusPos  Z    (S _) = absurd
minusPos (S _)  Z    = const $ LTESucc LTEZero
minusPos (S k) (S j) = minusPos k j

maxLTE : (p, q : Nat) -> p `LTE` q -> maximum p q = q
maxLTE  Z     Z    = const Refl
maxLTE  Z    (S _) = const Refl
maxLTE (S _)  Z    = absurd
maxLTE (S k) (S j) = cong . maxLTE k j . fromLteSucc

sub1R : (p : Nat) -> p `minus` 1 = pred p
sub1R  Z    = Refl
sub1R (S k) = minusZeroRight k

maxLt : (p, q : Nat) -> q `compare` p = LT -> maximum p q = p
maxLt  Z     Z    = absurd
maxLt  Z    (S _) = absurd
maxLt (S _)  Z    = const Refl
maxLt (S k) (S j) = cong . maxLt k j

minLt : (p, q : Nat) -> p `compare` q = LT -> minimum p q = p
minLt  Z     Z    = absurd
minLt  Z    (S _) = const Refl
minLt (S _)  Z    = absurd
minLt (S k) (S j) = cong . minLt k j

--------------------------------------------------------------------------------

-- inj_lt

injLt : (p, q : Bip) -> p `Lt` q -> toNatBip p `compare` toNatBip q = LT
injLt p q pltq =
  let (r**prq) = ltIffAddTo p q pltq in
  rewrite sym prq in
  rewrite injAdd p r in
  let (s**prf) = isSucc r in
  rewrite prf in
  ltPlusNZ (toNatBip p) s

-- inj_gt

injGt : (p, q : Bip) -> p `Gt` q -> toNatBip p `compare` toNatBip q = GT
injGt p q pgtq = ltGt (toNatBip q) (toNatBip p) $
                 injLt q p $
                 gtLt p q pgtq

-- inj_compare

injCompare : (p, q : Bip) -> p `compare` q = toNatBip p `compare` toNatBip q
injCompare p q with (p `compare` q) proof pq
  | LT = sym $ injLt p q $ sym pq
  | EQ = rewrite compareEqIffTo p q $ sym pq in
         sym $ compareRefl (toNatBip q)
  | GT = sym $ injGt p q $ sym pq

-- inj_le

injLe : (p, q : Bip) -> p `Le` q -> Not (toNatBip p `compare` toNatBip q = GT)
injLe p q pleq = rewrite sym $ injCompare p q in
                 pleq

-- inj_ge

injGe : (p, q : Bip) -> p `Ge` q -> Not (toNatBip p `compare` toNatBip q = LT)
injGe p q pgeq = rewrite sym $ injCompare p q in
                 pgeq

-- inj_sub

injSub : (p, q : Bip) -> q `Lt` p -> toNatBip (p-q) = toNatBip p `minus` toNatBip q
injSub p q qltp =
  plusRightCancel (toNatBip (p-q)) (toNatBip p `minus` toNatBip q) (toNatBip q) $
  rewrite plusMinus (toNatBip p) (toNatBip q) (injLt q p qltp) in
  rewrite sym $ injAdd (p-q) q in
  rewrite subAdd p q qltp in
  Refl

-- inj_sub_max

injSubMax : (p, q : Bip) -> toNatBip (p-q) = maximum 1 (toNatBip p `minus` toNatBip q)
injSubMax p q = case ltTotal p q of
  Left $ Left pltq =>
    rewrite subMaskNeg p q pltq in
    rewrite minusNeg (toNatBip p) (toNatBip q) $ injLt p q pltq in
    Refl
  Left $ Right qltp =>
    rewrite injSub p q qltp in
    sym $ maxLTE 1 (toNatBip p `minus` toNatBip q) $
          minusPos (toNatBip p) (toNatBip q) $
          injLt q p qltp
  Right eq =>
    rewrite eq in
    rewrite subMaskDiag q in
    rewrite sym $ minusZeroN (toNatBip q) in
    Refl

-- inj_pred

injPred : (p : Bip) -> (U `Lt` p) -> toNatBip (bipPred p) = pred (toNatBip p)
injPred p ultp =
  rewrite sym $ sub1R p in
  rewrite injSub p U ultp in
  sub1R (toNatBip p)

-- inj_pred_max

injPredMax : (p : Bip) -> toNatBip (bipPred p) = maximum 1 (pred $ toNatBip p)
injPredMax p =
  rewrite sym $ sub1R p in
  rewrite sym $ sub1R (toNatBip p) in
  injSubMax p U

-- inj_min

injMin : (p, q : Bip) -> toNatBip (p `min` q) = minimum (toNatBip p) (toNatBip q)
injMin p q with (p `compare` q) proof pq
  | LT = sym $ minLt (toNatBip p) (toNatBip q) $ injLt p q $ sym pq
  | EQ = rewrite compareEqIffTo p q $ sym pq in
         sym $ minimumIdempotent (toNatBip q)
  | GT = rewrite minimumCommutative (toNatBip p) (toNatBip q) in
         sym $ minLt (toNatBip q) (toNatBip p) $ injLt q p $ gtLt p q $ sym pq

-- inj_max

injMax : (p, q : Bip) -> toNatBip (p `max` q) = maximum (toNatBip p) (toNatBip q)
injMax p q with (p `compare` q) proof pq
  | LT = rewrite maximumCommutative (toNatBip p) (toNatBip q) in
         sym $ maxLt (toNatBip q) (toNatBip p) $ injLt p q $ sym pq
  | EQ = rewrite compareEqIffTo p q $ sym pq in
         sym $ maximumIdempotent $ toNatBip q
  | GT = sym $ maxLt (toNatBip p) (toNatBip q) $ injLt q p $ gtLt p q $ sym pq