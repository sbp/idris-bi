module Data.Bin.Nat

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub

%access public export
%default total

----------------------- Nat utility proofs and functions -----------------------
-- TODO add to Prelude?

ltPlusNZ : (a,b : Nat) -> a `compare` (a+(S b)) = LT
ltPlusNZ  Z    _ = Refl
ltPlusNZ (S k) b = ltPlusNZ k b

compareRefl : (a : Nat) -> a `compare` a = EQ
compareRefl  Z    = Refl
compareRefl (S k) = compareRefl k

compareEq : (a, b : Nat) -> a `compare` b = EQ -> a = b
compareEq  Z     Z    = const Refl
compareEq  Z    (S _) = absurd
compareEq (S _)  Z    = absurd
compareEq (S k) (S j) = cong . compareEq k j

ltGt : (a,b : Nat) -> a `compare` b = LT -> b `compare` a = GT
ltGt  Z     Z    = absurd
ltGt  Z    (S _) = const Refl
ltGt (S _)  Z    = absurd
ltGt (S k) (S j) = ltGt k j

gtLt : (a,b : Nat) -> a `compare` b = GT -> b `compare` a = LT
gtLt  Z     Z    = absurd
gtLt  Z    (S _) = absurd
gtLt (S _)  Z    = const Refl
gtLt (S k) (S j) = gtLt k j

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

natIter : (f : a -> a) -> (x : a) -> (n : Nat) -> a
natIter _ x  Z    = x
natIter f x (S k) = f (natIter f x k)

--------------------------------------------------------------------------------

-- Properties of the injection from binary positive numbers to Peano natural
-- numbers

-- Bip -> Nat

-- inj_succ

bipMultNatSucc : (p : Bip) -> (n : Nat) -> bipMultNat (bipSucc p) n = n + bipMultNat p n
bipMultNatSucc  U    _ = Refl
bipMultNatSucc (O _) _ = Refl
bipMultNatSucc (I a) n = rewrite plusAssociative n n (bipMultNat a (n+n)) in
                         bipMultNatSucc a (n+n)

toNatInjSucc : (p : Bip) -> toNatBip (bipSucc p) = S (toNatBip p)
toNatInjSucc p = bipMultNatSucc p 1

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

toNatInjAdd : (p, q : Bip) -> toNatBip (p+q) = toNatBip p + toNatBip q
toNatInjAdd p q = bipMultNatAdd p q 1

-- inj_mul

toNatInjMul : (p, q : Bip) -> toNatBip (p*q) = toNatBip p * toNatBip q
toNatInjMul p q =
  peanoRect
    (\x => toNatBip (x*q) = toNatBip x * toNatBip q)
    (rewrite plusZeroRightNeutral $ toNatBip q in
     Refl)
    (\p',prf =>
      rewrite mulSuccL p' q in
      rewrite toNatInjSucc p' in
      rewrite toNatInjAdd q (p'*q) in
      cong {f=plus (toNatBip q)} prf
    )
    p

-- inj_1 is trivial

-- inj_xO

injXO : (p : Bip) -> toNatBip (O p) = 2 * toNatBip p
injXO p = rewrite plusZeroRightNeutral $ toNatBip p in
          rewrite sym $ toNatInjAdd p p in
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
      rewrite toNatInjSucc p in
      (S n ** cong prf)
    )

-- is_pos
-- TODO can't use Nat.LT here, it clashes

isPos : (p : Bip) -> 1 `LTE` (toNatBip p)
isPos p = rewrite snd $ isSucc p in
          LTESucc LTEZero

-- id

toNatId : (p : Bip) -> toBipNat $ toNatBip p = p
toNatId p =
  peanoRect
    (\x => toBipNat $ toNatBip x = x)
    Refl
    (\p',prf =>
      rewrite toNatInjSucc p' in
      let (_**prfn) = isSucc p' in
      rewrite prfn in
      rewrite sym prfn in
      cong prf
    )
    p

-- inj

toNatInj : (p, q : Bip) -> toNatBip p = toNatBip q -> p = q
toNatInj p q prf =
  rewrite sym $ toNatId p in
  rewrite sym $ toNatId q in
  rewrite prf in
  Refl

-- inj_iff: `fro` is just `cong`

-- inj_lt

injLt : (p, q : Bip) -> p `Lt` q -> toNatBip p `compare` toNatBip q = LT
injLt p q pltq =
  let (r**prq) = ltIffAddTo p q pltq in
  rewrite sym prq in
  rewrite toNatInjAdd p r in
  let (s**prf) = isSucc r in
  rewrite prf in
  ltPlusNZ (toNatBip p) s

-- inj_gt

injGt : (p, q : Bip) -> p `Gt` q -> toNatBip p `compare` toNatBip q = GT
injGt p q pgtq = ltGt (toNatBip q) (toNatBip p) $
                 injLt q p $
                 gtLt p q pgtq

-- inj_compare

toNatInjCompare : (p, q : Bip) -> p `compare` q = toNatBip p `compare` toNatBip q
toNatInjCompare p q with (p `compare` q) proof pq
  | LT = sym $ injLt p q $ sym pq
  | EQ = rewrite compareEqIffTo p q $ sym pq in
         sym $ compareRefl (toNatBip q)
  | GT = sym $ injGt p q $ sym pq

-- inj_le

injLe : (p, q : Bip) -> p `Le` q -> Not (toNatBip p `compare` toNatBip q = GT)
injLe p q pleq = rewrite sym $ toNatInjCompare p q in
                 pleq

-- inj_ge

injGe : (p, q : Bip) -> p `Ge` q -> Not (toNatBip p `compare` toNatBip q = LT)
injGe p q pgeq = rewrite sym $ toNatInjCompare p q in
                 pgeq

-- inj_sub

toNatInjSub : (p, q : Bip) -> q `Lt` p -> toNatBip (p-q) = toNatBip p `minus` toNatBip q
toNatInjSub p q qltp =
  plusRightCancel (toNatBip (p-q)) (toNatBip p `minus` toNatBip q) (toNatBip q) $
  rewrite plusMinus (toNatBip p) (toNatBip q) (injLt q p qltp) in
  rewrite sym $ toNatInjAdd (p-q) q in
  rewrite subAdd p q qltp in
  Refl

-- inj_sub_max

toNatInjSubMax : (p, q : Bip) -> toNatBip (p-q) = maximum 1 (toNatBip p `minus` toNatBip q)
toNatInjSubMax p q = case ltTotal p q of
  Left $ Left pltq =>
    rewrite subMaskNeg p q pltq in
    rewrite minusNeg (toNatBip p) (toNatBip q) $ injLt p q pltq in
    Refl
  Left $ Right qltp =>
    rewrite toNatInjSub p q qltp in
    sym $ maxLTE 1 (toNatBip p `minus` toNatBip q) $
          minusPos (toNatBip p) (toNatBip q) $
          injLt q p qltp
  Right eq =>
    rewrite eq in
    rewrite subMaskDiag q in
    rewrite sym $ minusZeroN (toNatBip q) in
    Refl

-- inj_pred

toNatInjPred : (p : Bip) -> (U `Lt` p) -> toNatBip (bipPred p) = pred (toNatBip p)
toNatInjPred p ultp =
  rewrite sym $ sub1R p in
  rewrite toNatInjSub p U ultp in
  sub1R (toNatBip p)

-- inj_pred_max

injPredMax : (p : Bip) -> toNatBip (bipPred p) = maximum 1 (pred $ toNatBip p)
injPredMax p =
  rewrite sym $ sub1R p in
  rewrite sym $ sub1R (toNatBip p) in
  toNatInjSubMax p U

-- inj_min

toNatInjMin : (p, q : Bip) -> toNatBip (p `min` q) = minimum (toNatBip p) (toNatBip q)
toNatInjMin p q with (p `compare` q) proof pq
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

-- inj_iter

injIter : (f : a -> a) -> (x : a) -> (p : Bip) -> bipIter f x p = natIter f x (toNatBip p)
injIter f x =
  peanoRect
   (\q => bipIter f x q = natIter f x (toNatBip q))
   Refl
   (\p', prf =>
     rewrite toNatInjSucc p' in
     rewrite iterSucc f x p' in
     cong prf
   )

-- Nat -> Bip

-- id

toBipId : (n : Nat) -> Not (n=Z) -> toNatBip $ toBipNat n = n
toBipId  Z        nz = absurd $ nz Refl
toBipId (S  Z   ) _  = Refl
toBipId (S (S k)) _  = rewrite toNatInjSucc $ toBipNat (S k) in
                          cong $ toBipId (S k) $ uninhabited . sym

-- id_max

toBipIdMax : (n : Nat) -> toNatBip $ toBipNat n = maximum 1 n
toBipIdMax Z = Refl
toBipIdMax (S k) = toBipId (S k) $ uninhabited . sym

-- inj

toBipInj : (n, m : Nat) -> Not (n=Z) -> Not (m=Z) -> toBipNat n = toBipNat m -> n = m
toBipInj n m nz mz prf =
  rewrite sym $ toBipId n nz in
  rewrite sym $ toBipId m mz in
  rewrite prf in
  Refl

-- inj_iff: again, `fro` is just `cong`

-- inj_succ

toBipInjSucc : (n : Nat) -> Not (n=Z) -> toBipNat (S n) = bipSucc (toBipNat n)
toBipInjSucc n nz =
  toNatInj (toBipNat $ S n) (bipSucc $ toBipNat n) $
  rewrite toNatInjSucc $ toBipNat n in
  rewrite toBipId (S n) (uninhabited . sym) in
  cong $ sym $ toBipId n nz

-- inj_pred

toBipInjPred : (n : Nat) -> toBipNat (pred n) = bipPred (toBipNat n)
toBipInjPred  Z        = Refl
toBipInjPred (S  Z   ) = Refl
toBipInjPred (S (S k)) = sym $ predSucc $ toBipNat (S k)

-- inj_add

toBipInjAdd : (n, m : Nat) -> Not (n=Z) -> Not (m=Z) -> toBipNat (n+m) = toBipNat n + toBipNat m
toBipInjAdd n m nz mz =
  toNatInj (toBipNat $ n+m) (toBipNat n + toBipNat m) $
  rewrite toNatInjAdd (toBipNat n) (toBipNat m) in
  rewrite toBipId n nz in
  rewrite toBipId m mz in
  toBipId (n+m) $ notSumZ n m nz mz
  where
    notSumZ : (n, m : Nat) -> Not (n=Z) -> Not (m=Z) -> Not (n+m = Z)
    notSumZ  Z     _    nz _  = absurd $ nz Refl
    notSumZ  _     Z    _  mz = absurd $ mz Refl
    notSumZ (S _) (S _) _  _  = uninhabited . sym

-- inj_mul

toBipInjMul : (n, m : Nat) -> Not (n=Z) -> Not (m=Z) -> toBipNat (n*m) = toBipNat n * toBipNat m
toBipInjMul n m nz mz =
  toNatInj (toBipNat $ n*m) (toBipNat n * toBipNat m) $
  rewrite toNatInjMul (toBipNat n) (toBipNat m) in
  rewrite toBipId n nz in
  rewrite toBipId m mz in
  toBipId (n*m) $ notMulZ n m nz mz
  where
    notMulZ : (n, m : Nat) -> Not (n=Z) -> Not (m=Z) -> Not (n*m = Z)
    notMulZ  Z     _    nz _  = absurd $ nz Refl
    notMulZ  _     Z    _  mz = absurd $ mz Refl
    notMulZ (S _) (S _) _  _  = uninhabited . sym

-- inj_compare

toBipInjCompare : (n, m : Nat) -> Not (n=Z) -> Not (m=Z) -> n `compare` m = toBipNat n `compare` toBipNat m
toBipInjCompare n m nz mz =
  rewrite toNatInjCompare (toBipNat n) (toBipNat m) in
  rewrite sym $ toBipId n nz in
  rewrite sym $ toBipId m mz in
  Refl

-- inj_sub

toBitInjSub : (n, m : Nat) -> Not (m=Z) -> toBipNat (n `minus` m) = toBipNat n - toBipNat m
toBitInjSub n m mz =
  toNatInj (toBipNat $ n `minus` m) (toBipNat n - toBipNat m) $
  rewrite toNatInjSubMax (toBipNat n) (toBipNat m) in
  rewrite toBipId m mz in
  rewrite sym $ toBipIdMax $ (toNatBip $ toBipNat n) `minus` m in
  aux n m mz
  where
    aux : (n, m : Nat) -> Not (m=Z) -> toNatBip $ toBipNat $ n `minus` m = toNatBip $ toBipNat $ (toNatBip $ toBipNat n) `minus` m
    aux  _     Z    mz = absurd $ mz Refl
    aux  Z    (S k) _  = Refl
    aux (S k) (S j) mz = rewrite toBipId (S k) (uninhabited . sym) in
                         Refl

-- inj_min

toBipInjMin : (n, m : Nat) -> toBipNat (minimum n m) = (toBipNat n) `min` (toBipNat m)
toBipInjMin Z Z = Refl
toBipInjMin Z (S j) = sym $ minL U (toBipNat (S j)) $ le1L (toBipNat (S j))
toBipInjMin (S k) Z = sym $ minR (toBipNat (S k)) U $ le1L (toBipNat (S k))
toBipInjMin (S k) (S j) =
  rewrite toNatInjCompare (toBipNat (S k)) (toBipNat (S j)) in
  rewrite toBipId (S k) (uninhabited . sym) in
  rewrite toBipId (S j) (uninhabited . sym) in
  aux
  where
    aux : toBipNat (S (minimum k j)) = bipMinMaxHelp (toBipNat (S k)) (toBipNat (S j)) (k `compare` j)
    aux with (k `compare` j) proof kj
      | LT = rewrite minLt k j $ sym kj in
             Refl
      | EQ = rewrite compareEq k j $ sym kj in
             rewrite minimumIdempotent j in
             Refl
      | GT = rewrite minimumCommutative k j in
             rewrite minLt j k $ gtLt k j $ sym kj in
             Refl

-- inj_max

toBipInjMax : (n, m : Nat) -> toBipNat (maximum n m) = (toBipNat n) `max` (toBipNat m)
toBipInjMax Z Z = Refl
toBipInjMax Z (S j) = sym $ maxR U (toBipNat (S j)) $ le1L (toBipNat (S j))
toBipInjMax (S k) Z = sym $ maxL (toBipNat (S k)) U $ le1L (toBipNat (S k))
toBipInjMax (S k) (S j) =
  rewrite toNatInjCompare (toBipNat (S k)) (toBipNat (S j)) in
  rewrite toBipId (S k) (uninhabited . sym) in
  rewrite toBipId (S j) (uninhabited . sym) in
  aux
  where
    aux : toBipNat (S (maximum k j)) = bipMinMaxHelp (toBipNat (S j)) (toBipNat (S k)) (k `compare` j)
    aux with (k `compare` j) proof kj
      | LT = rewrite maximumCommutative k j in
             rewrite maxLt j k $ sym kj in
             Refl
      | EQ = rewrite compareEq k j $ sym kj in
             rewrite maximumIdempotent j in
             Refl
      | GT = rewrite maxLt k j $ gtLt k j $ sym kj in
             Refl

-- Properties of the shifted injection from Peano natural numbers to binary
-- positive numbers

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
succOfNat  Z    nz = absurd $ nz Refl
succOfNat (S k) _  = cong $ sym $ ofNatSucc k