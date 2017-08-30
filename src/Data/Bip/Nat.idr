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

-- inj_compare

-- Nat comparison proofs
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

gtLt : (a,b : Nat) -> a `compare` b = GT -> b `compare` a = LT
gtLt  Z     Z    = absurd
gtLt  Z    (S _) = absurd
gtLt (S _)  Z    = const Refl
gtLt (S k) (S j) = gtLt k j

ltSucc : (a,b : Nat) -> a `compare` b = LT -> a `compare` S b = LT
ltSucc  Z     Z    = absurd
ltSucc  Z    (S _) = const Refl
ltSucc (S _)  Z    = absurd
ltSucc (S k) (S j) = ltSucc k j

plusOneSuccL : (left : Nat) -> left + 1 = S left
plusOneSuccL left = rewrite plusCommutative left 1 in Refl

plusMinus : (a, b : Nat) -> b `compare` a = LT -> (a `minus` b)+b = a
plusMinus  Z     Z    blta = absurd blta
plusMinus  Z    (S _) blta = absurd blta
plusMinus (S k)  Z    blta = rewrite plusZeroRightNeutral k in Refl
plusMinus (S k) (S j) blta = rewrite sym $ plusSuccRightSucc (k `minus` j) j in
                             cong $ plusMinus k j blta

--

isSuccSucc : (a : Bip) -> (n ** bipMultNat a 2 = S (S n))
isSuccSucc a =
  peanoRect
    (\x => (n ** bipMultNat x 2 = S (S n)))
    (Z ** Refl)
    (\a', (n**prf) =>
      rewrite bipMultNatSucc a' 2 in
      (S (S n) ** cong {f = S . S} prf)
    )
    a

ltMonoM2 : (p, q : Bip) -> p `Lt` q -> bipMultNat p 2 `compare` bipMultNat q 2 = LT
ltMonoM2 p q pltq =
  let (r**prq) = ltIffAddTo p q pltq in
  rewrite sym prq in
  rewrite bipMultNatAdd p r 2 in
  let (s**prf) = isSuccSucc r in
  rewrite prf in
  ltPlusNZ (bipMultNat p 2) (S s)

ltMonoM2Succ : (p, q : Bip) -> p `Lt` q -> S (bipMultNat p 2) `compare` bipMultNat q 2 = LT
ltMonoM2Succ p q pltq =
  let (r**prq) = ltIffAddTo p q pltq in
  rewrite sym prq in
  rewrite bipMultNatAdd p r 2 in
  let (s**prf) = isSuccSucc r in
  rewrite prf in
  rewrite sym $ plusSuccRightSucc (bipMultNat p 2) (S s) in
    ltPlusNZ (bipMultNat p 2) s

injCompareM2 : (p, q : Bip) -> p `compare` q = bipMultNat p 2 `compare` bipMultNat q 2
injCompareM2 p q with (p `compare` q) proof pq
  | LT = sym $ ltMonoM2 p q $ sym pq
  | EQ = rewrite compareEqIffTo p q $ sym pq in
         sym $ compareRefl (bipMultNat q 2)
  | GT = let nqltnp = ltMonoM2 q p $ gtLt p q $ sym pq in
         sym $ ltGt (bipMultNat q 2) (bipMultNat p 2) nqltnp

injCompare : (p, q : Bip) -> p `compare` q = toNatBip p `compare` toNatBip q
injCompare  U     U    = Refl
injCompare  U    (O b) = rewrite snd $ isSuccSucc b in
                         Refl
injCompare  U    (I b) = rewrite snd $ isSuccSucc b in
                         Refl
injCompare (O a)  U    = rewrite snd $ isSuccSucc a in
                         Refl
injCompare (I a)  U    = rewrite snd $ isSuccSucc a in
                         Refl
injCompare (O a) (O b) = injCompareM2 a b
injCompare (O a) (I b) with (bipCompare a b LT) proof abl
  | LT = case leLtOrEq a b $ compareContLtLtTo a b $ sym abl of
           Left altb  => let ma2ltmb2 = ltMonoM2 a b altb in
                         sym $ ltSucc (bipMultNat a 2) (bipMultNat b 2) ma2ltmb2
           Right aeqb => rewrite aeqb in
                         rewrite sym $ plusOneSuccL (bipMultNat b 2) in
                         sym $ ltPlusNZ (bipMultNat b 2) Z
  | EQ = absurd $ compLtNotEq a b $ sym abl
  | GT = let tt = gtLt a b $ compareContLtGtTo a b $ sym abl
             tt2 = ltMonoM2Succ b a tt
         in
           sym $ ltGt (S (bipMultNat b 2)) (bipMultNat a 2) tt2
injCompare (I a) (O b) with (bipCompare a b GT) proof abg
  | LT = let tt = compareContGtLtTo a b $ sym abg
         in
         sym $ ltMonoM2Succ a b tt
  | EQ = absurd $ compGtNotEq a b $ sym abg
  | GT = case leLtOrEq b a $ geLe a b $ compareContGtGtTo a b $ sym abg of
           Left blta  => let mb2ltma2 = ltMonoM2 b a blta in
                         sym $ ltGt (bipMultNat b 2) (S (bipMultNat a 2)) $
                         ltSucc (bipMultNat b 2) (bipMultNat a 2) mb2ltma2
           Right beqa => rewrite beqa in
                         rewrite sym $ plusOneSuccL (bipMultNat a 2) in
                         sym $ ltGt (bipMultNat a 2) ((bipMultNat a 2)+1) $
                         ltPlusNZ (bipMultNat a 2) Z
injCompare (I a) (I b) = injCompareM2 a b

-- inj_lt

injLt : (p, q : Bip) -> p `Lt` q -> toNatBip p `compare` toNatBip q = LT
injLt p q pltq = rewrite sym $ injCompare p q in
                 pltq

-- inj_le

injLe : (p, q : Bip) -> p `Le` q -> Not (toNatBip p `compare` toNatBip q = GT)
injLe p q pleq = rewrite sym $ injCompare p q in
                 pleq

-- inj_gt

injGt : (p, q : Bip) -> p `Gt` q -> toNatBip p `compare` toNatBip q = GT
injGt p q pgtq = rewrite sym $ injCompare p q in
                 pgtq

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