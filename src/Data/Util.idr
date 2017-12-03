module Data.Util

import Data.List

%default total
%access public export

%hide Prelude.Nat.GT
%hide Prelude.Nat.LT

-- TODO import Control.Pipeline from contrib
infixl 9 |>
(|>) : a -> (a -> b) -> b
a |> f = f a

cong2 : {f : x -> y -> z} -> a = b -> c = d -> f a c = f b d
cong2 Refl Refl = Refl

Uninhabited (Nothing = Just _) where
  uninhabited Refl impossible

Uninhabited (Just _ = Nothing) where
  uninhabited Refl impossible

-------- List properties ----------

listElemMapInv : (f : a -> b) -> (l : List a) -> (y : b) -> Elem y (map f l) -> (x : a ** (y = f x, Elem x l))
listElemMapInv _ []        _     prf       = absurd prf
listElemMapInv f (e :: _) (f e)  Here      = (e ** (Refl, Here))
listElemMapInv f (_ :: l)  y    (There lr) = let (x ** (yfx, el)) = listElemMapInv f l y lr in
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

-- switch_Eq
-- TODO use `thenCompare`?

switchEq : (c, c' : Ordering) -> Ordering
switchEq _ LT = LT
switchEq c EQ = c
switchEq _ GT = GT

opSwitch : (o, o1 : Ordering) -> compareOp (switchEq o o1) = switchEq (compareOp o) (compareOp o1)
opSwitch _ LT = Refl
opSwitch _ EQ = Refl
opSwitch _ GT = Refl

------- Nat properties -------

-- TODO Remove in the next release

Uninhabited (S n = Z) where
  uninhabited Refl impossible

-- TODO contribute to Prelude.Nat

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

predOfMinus : (n : Nat) -> pred n = n `minus` 1
predOfMinus  Z    = Refl
predOfMinus (S k) = sym $ minusZeroRight k

plusLTEMonoR : (p, q, r : Nat) -> q `LTE` r -> (q+p) `LTE` (r+p)
plusLTEMonoR p  Z     r     LTEZero    = rewrite plusCommutative r p in
                                         lteAddRight p
plusLTEMonoR p (S b) (S c) (LTESucc l) = LTESucc $ plusLTEMonoR p b c l

------- Boolean properties ------

-- TODO contribute to Prelude.Bool

xor : Bool -> Bool -> Bool
xor = (/=)

xorDiag : (b : Bool) -> xor b b = False
xorDiag False = Refl
xorDiag True = Refl

xorComm : (a, b : Bool) -> xor a b = xor b a
xorComm False False = Refl
xorComm False True  = Refl
xorComm True  False = Refl
xorComm True  True  = Refl

xorFalse : (b : Bool) -> xor False b = b
xorFalse False = Refl
xorFalse True = Refl

orDiag : (b : Bool) -> b || b = b
orDiag False = Refl
orDiag True = Refl

orFalse : (b : Bool) -> b || False = b
orFalse False = Refl
orFalse True = Refl

andDiag : (b : Bool) -> b && b = b
andDiag False = Refl
andDiag True = Refl

andFalse : (b : Bool) -> b && False = False
andFalse False = Refl
andFalse True = Refl

andTrue : (b : Bool) -> b && True = b
andTrue False = Refl
andTrue True = Refl

andNot : (b : Bool) -> b && not b = False
andNot False = Refl
andNot True = Refl

notAnd : (x, y : Bool) -> not (x && y) = (not x) || (not y)
notAnd True  True  = Refl
notAnd True  False = Refl
notAnd False True  = Refl
notAnd False False = Refl

notNot : (x : Bool) -> not (not x) = x
notNot True  = Refl
notNot False = Refl

orComm : (x, y : Bool) -> x || y = y || x
orComm True  True  = Refl
orComm True  False = Refl
orComm False True  = Refl
orComm False False = Refl

andComm : (x, y : Bool) -> x && y = y && x
andComm True  True  = Refl
andComm True  False = Refl
andComm False True  = Refl
andComm False False = Refl

notOr : (x, y : Bool) -> not (x || y) = (not x) && (not y)
notOr True  True  = Refl
notOr True  False = Refl
notOr False True  = Refl
notOr False False = Refl

notXorR : (x, y : Bool) -> not (x `xor` y) = x `xor` (not y)
notXorR True  True  = Refl
notXorR True  False = Refl
notXorR False True  = Refl
notXorR False False = Refl

notXorL : (x, y : Bool) -> not (x `xor` y) = (not x) `xor` y
notXorL True  True  = Refl
notXorL True  False = Refl
notXorL False True  = Refl
notXorL False False = Refl

notXor2 : (x, y : Bool) -> x `xor` y = (not x) `xor` (not y)
notXor2 True  True  = Refl
notXor2 True  False = Refl
notXor2 False True  = Refl
notXor2 False False = Refl

andbAssoc : (x, y, z : Bool) -> (x && y) && z = x && (y && z)
andbAssoc False _ _ = Refl
andbAssoc True  _ _ = Refl

orbAssoc : (x, y, z : Bool) -> (x || y) || z = x || (y || z)
orbAssoc False _ _ = Refl
orbAssoc True  _ _ = Refl

xorTrue : (b : Bool) -> True `xor` b = not b
xorTrue False = Refl
xorTrue True  = Refl

xorTrueR : (b : Bool) -> b `xor` True = not b
xorTrueR False = Refl
xorTrueR True  = Refl

andbIdem : (x : Bool) -> x && x = x
andbIdem False = Refl
andbIdem True = Refl

orbTrue : (b : Bool) -> b || True = True
orbTrue False = Refl
orbTrue True = Refl

orbIdem : (b : Bool) -> b || b = b
orbIdem False = Refl
orbIdem True = Refl

andbOrbDistribR : (b1, b2, b3 : Bool) -> b1 && (b2 || b3) = (b1 && b2) || (b1 && b3)
andbOrbDistribR False b2 b3 = Refl
andbOrbDistribR True  b2 b3 = Refl

orbAndbDistribR : (b1, b2, b3 : Bool) -> b1 || (b2 && b3) = (b1 || b2) && (b1 || b3)
orbAndbDistribR False _ _ = Refl
orbAndbDistribR True  _ _ = Refl

notEq : (a, b : Bool) -> (not a) == b = a /= b
notEq False False = Refl
notEq False True  = Refl
notEq True  False = Refl
notEq True  True  = Refl

xorbAssoc : (x, y, z : Bool) -> (x `xor` y) `xor` z = x `xor` (y `xor` z)
xorbAssoc False y z =
  rewrite xorFalse y in
  rewrite xorFalse (y `xor` z) in
  Refl
xorbAssoc True y z =
  rewrite xorTrue y in
  rewrite xorTrue (y `xor` z) in
  rewrite notEq y z in
  Refl

andbTrueIffTo : (a, b : Bool) -> a && b = True -> (a = True, b = True)
andbTrueIffTo False False prf  = absurd prf
andbTrueIffTo False True  prf  = absurd prf
andbTrueIffTo True  False prf  = absurd prf
andbTrueIffTo True  True  Refl = (Refl, Refl)

-- De Morgan's laws

negbOrb : (a, b : Bool) -> not (a || b) = (not a) && (not b)
negbOrb False _ = Refl
negbOrb True  _ = Refl

negbAndb : (a, b : Bool) -> not (a && b) = (not a) || (not b)
negbAndb False _ = Refl
negbAndb True  _ = Refl

andbNotSelf : (a : Bool) -> a && (not a) = False
andbNotSelf False = Refl
andbNotSelf True  = Refl

orbNotSelf : (a : Bool) -> a || (not a) = True
orbNotSelf False = Refl
orbNotSelf True  = Refl

xorbNotSelf : (a : Bool) -> a `xor` (not a) = True
xorbNotSelf False = Refl
xorbNotSelf True  = Refl

notTrueIsFalse : (b : Bool) -> Not (b = True) -> b = False
notTrueIsFalse True  nbt = absurd $ nbt Refl
notTrueIsFalse False _   = Refl

trueOrFalse : (b : Bool) -> Either (b = False) (b = True)
trueOrFalse False = Left Refl
trueOrFalse True = Right Refl

ifSame : (x : a) -> (b : Bool) -> (if b then x else x) = x
ifSame _ True = Refl
ifSame _ False = Refl