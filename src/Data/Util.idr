module Data.Util

import Data.List
import Data.List.Elem
import Data.Nat
import Data.So
import Decidable.Equality

%default total

%hide Data.Nat.GT
%hide Data.Nat.LT

cong2 : {f : x -> y -> z} -> a = b -> c = d -> f a c = f b d
cong2 Refl Refl = Refl

-------- List properties ----------

listElemMapInv : (f : a -> b) -> (y : b) -> (l : List a) -> Elem y (map f l) -> (x : a ** (y = f x, Elem x l))
listElemMapInv _  _     []       prf       = absurd prf
listElemMapInv f (f h) (h :: _)  Here      = (h ** (Refl, Here))
listElemMapInv f  y    (_ :: t) (There th) = let (x ** (yfx, el)) = listElemMapInv f y t th in
                                             (x ** (yfx, There el))

-------- Comparison properties ----

------ TODO add to Prelude.Interfaces

Uninhabited (LT = EQ) where
  uninhabited Refl impossible

Uninhabited (EQ = LT) where
  uninhabited Refl impossible

Uninhabited (LT = GT) where
  uninhabited Refl impossible

Uninhabited (GT = LT) where
  uninhabited Refl impossible

Uninhabited (GT = EQ) where
  uninhabited Refl impossible

Uninhabited (EQ = GT) where
  uninhabited Refl impossible

DecEq Ordering where
  decEq LT LT = Yes Refl
  decEq LT EQ = No uninhabited
  decEq LT GT = No uninhabited
  decEq EQ LT = No uninhabited
  decEq EQ EQ = Yes Refl
  decEq EQ GT = No uninhabited
  decEq GT LT = No uninhabited
  decEq GT EQ = No uninhabited
  decEq GT GT = Yes Refl

compareOp : Ordering -> Ordering
compareOp LT = GT
compareOp EQ = EQ
compareOp GT = LT

compareOpInj : (o1, o2 : Ordering) -> compareOp o1 = compareOp o2 -> o1 = o2
compareOpInj LT LT Refl = Refl
compareOpInj LT EQ Refl impossible
compareOpInj LT GT Refl impossible
compareOpInj EQ LT Refl impossible
compareOpInj EQ EQ Refl = Refl
compareOpInj EQ GT Refl impossible
compareOpInj GT LT Refl impossible
compareOpInj GT EQ Refl impossible
compareOpInj GT GT Refl = Refl

thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare LT y = LT
thenCompare EQ y = y
thenCompare GT y = GT

opThenDistribute : (o1, o2 : Ordering) -> compareOp (thenCompare o1 o2) = thenCompare (compareOp o1) (compareOp o2)
opThenDistribute LT _ = Refl
opThenDistribute EQ _ = Refl
opThenDistribute GT _ = Refl

------- Nat properties -------

-- TODO contribute to Prelude.Nat

ltPlusNZ : (a,b : Nat) -> a `compare` (a+(S b)) = LT
ltPlusNZ  Z    _ = Refl
ltPlusNZ (S k) b = ltPlusNZ k b

compareRefl : (a : Nat) -> a `compare` a = EQ
compareRefl  Z    = Refl
compareRefl (S k) = compareRefl k

compareEq : (a, b : Nat) -> a `compare` b = EQ -> a = b
compareEq  Z     Z    p = Refl
compareEq (S k) (S j) p = cong S $ compareEq k j p

ltGt : (a,b : Nat) -> a `compare` b = LT -> b `compare` a = GT
ltGt  Z    (S _) _ = Refl
ltGt (S k) (S j) p = ltGt k j p

gtLt : (a,b : Nat) -> a `compare` b = GT -> b `compare` a = LT
gtLt  Z     Z    p = absurd p
gtLt  Z    (S _) p = absurd p
gtLt (S _)  Z    p = Refl
gtLt (S k) (S j) p = gtLt k j p

plusMinus : (a, b : Nat) -> b `compare` a = LT -> (a `minus` b)+b = a
plusMinus  Z     Z    blta = absurd blta
plusMinus  Z    (S _) blta = absurd blta
plusMinus (S k)  Z    blta = rewrite plusZeroRightNeutral k in Refl
plusMinus (S k) (S j) blta = rewrite sym $ plusSuccRightSucc (k `minus` j) j in
                             cong S $ plusMinus k j blta

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
maxLTE (S k) (S j) = cong S . maxLTE k j . fromLteSucc

sub1R : (p : Nat) -> p `minus` 1 = pred p
sub1R  Z    = Refl
sub1R (S k) = minusZeroRight k

maxLt : (p, q : Nat) -> q `compare` p = LT -> maximum p q = p
maxLt  Z     Z    = absurd
maxLt  Z    (S _) = absurd
maxLt (S _)  Z    = const Refl
maxLt (S k) (S j) = cong S . maxLt k j

minLt : (p, q : Nat) -> p `compare` q = LT -> minimum p q = p
minLt  Z     Z    = absurd
minLt  Z    (S _) = const Refl
minLt (S _)  Z    = absurd
minLt (S k) (S j) = cong S . minLt k j

natIter : (f : a -> a) -> (x : a) -> (n : Nat) -> a
natIter _ x  Z    = x
natIter f x (S k) = f (natIter f x k)

predOfMinus : (n : Nat) -> pred n = n `minus` 1
predOfMinus  Z    = Refl
predOfMinus (S k) = sym $ minusZeroRight k

plusLTEMonoR : (p, q, r : Nat) -> q `LTE` r -> (q+p) `LTE` (r+p)
plusLTEMonoR p  Z     r     LTEZero    = rewrite plusCommutative r p in
                                         lteAddRight p
plusLTEMonoR p (S b) (S c) (LTESucc l) = LTESucc $ plusLTEMonoR p b c l

------- Boolean properties ------

-- TODO contribute to Prelude.Bool

notEq : (a, b : Bool) -> (not a) == b = a /= b
notEq False False = Refl
notEq False True  = Refl
notEq True  False = Refl
notEq True  True  = Refl

andbTrueIffTo : (a, b : Bool) -> a && b = True -> (a = True, b = True)
andbTrueIffTo False False prf  = absurd prf
andbTrueIffTo False True  prf  = absurd prf
andbTrueIffTo True  False prf  = absurd prf
andbTrueIffTo True  True  Refl = (Refl, Refl)

-- De Morgan's laws

notTrueIsFalse : (b : Bool) -> Not (b = True) -> b = False
notTrueIsFalse True  nbt = absurd $ nbt Refl
notTrueIsFalse False _   = Refl

--trueOrFalse : (b : Bool) -> Either (b = False) (b = True)
--trueOrFalse False = Left Refl
--trueOrFalse True = Right Refl

ifSame : (x : a) -> (b : Bool) -> (if b then x else x) = x
ifSame _ True = Refl
ifSame _ False = Refl
