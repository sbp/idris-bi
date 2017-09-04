module Data.Bin.Proofs

import Data.Bin
import Data.Bip.AddMul
import Data.Bip.IterPow
import Data.Bip.OrdSub
import Data.Bip.SqrtDiv

%access public export
%default total

-- Following NArith/BinNat.v

-- Peano induction

-- peano_rect

peanoRect : (P : Bin -> Type) -> (f0 : P BinO) ->
            (f: (n : Bin) -> P n -> P (binSucc n)) ->
            (n : Bin) -> P n
peanoRect _ f0 _  BinO    = f0
peanoRect P f0 f (BinP a) = peanoRect (P . BinP) (f BinO f0) (\p => f $ BinP p) a

-- peano_rect_base is trivial

-- TODO
-- peano_rect_succ
-- peano_rec_base
-- peano_rec_succ

-- Properties of mixed successor and predecessor

-- pos_pred_spec
posPredSpec : (a : Bip) -> bipPredBin a = binPred (BinP a)
posPredSpec  U    = Refl
posPredSpec (O _) = Refl
posPredSpec (I _) = Refl

-- succ_pos_spec
succPosSpec : (a : Bin) -> BinP (binSuccBip a) = binSucc a
succPosSpec  BinO    = Refl
succPosSpec (BinP _) = Refl

-- pos_pred_succ
posPredSucc : (a : Bin) -> bipPredBin (binSuccBip a) = a
posPredSucc  BinO     = Refl
posPredSucc (BinP a') = rewrite predBinSucc a' in Refl

-- succ_pos_pred
succPosPred : (a : Bip) -> binSucc (bipPredBin a) = BinP a
succPosPred  U     = Refl
succPosPred (O a') = rewrite succPredDouble a' in Refl
succPosPred (I _ ) = Refl

-- Properties of successor and predecessor

succPred : (a : Bin) -> Not (a=0) -> binSucc (binPred a) = a
succPred  BinO    az = absurd $ az Refl
succPred (BinP a) _  = succPosPred a

-- pred_succ
predSucc : (a : Bin) -> binPred (binSucc a) = a
predSucc  BinO     = Refl
predSucc (BinP a') = rewrite predBinSucc a' in Refl

-- pred_sub
predSub : (a : Bin) -> binPred a = a-(BinP U)
predSub  BinO         = Refl
predSub (BinP  U    ) = Refl
predSub (BinP (O a')) = Refl
predSub (BinP (I a')) = Refl

-- succ_0_discr
succZeroDiscr : (a : Bin) -> Not (binSucc a = 0)
succZeroDiscr  BinO     = uninhabited
succZeroDiscr (BinP a') = uninhabited

-- Specification of addition

-- add_0_l
addZeroL : (a : Bin) -> BinO + a = a
addZeroL  BinO    = Refl
addZeroL (BinP _) = Refl

-- add_succ_l
addSuccL : (a, b : Bin) -> (binSucc a) + b = binSucc (a+b)
addSuccL  BinO      BinO        = Refl
addSuccL  BinO     (BinP  U   ) = Refl
addSuccL  BinO     (BinP (O _)) = Refl
addSuccL  BinO     (BinP (I _)) = Refl
addSuccL (BinP _ )  BinO        = Refl
addSuccL (BinP a') (BinP  b'  ) = rewrite addSuccL a' b' in Refl

-- Specification of subtraction

-- sub_0_r
subZeroR : (a : Bin) -> a-0 = a
subZeroR  BinO    = Refl
subZeroR (BinP _) = Refl

-- Helper for sub_succ_r
subSuccPred : (p, q : Bip) -> bimMinus p (bipSucc q) = bimPred (bimMinus p q)
subSuccPred a b = rewrite subMaskSuccR a b in
                  rewrite subMaskCarrySpec a b in Refl

-- Helper for sub_succ_r
bimAndBin : (a : Bim) -> bimToBin (bimPred a) = binPred (bimToBin a)
bimAndBin (BimP  U   ) = Refl
bimAndBin (BimP (O _)) = Refl
bimAndBin (BimP (I _)) = Refl
bimAndBin  BimO        = Refl
bimAndBin  BimM        = Refl

-- sub_succ_r
subSuccR : (a, b : Bin) -> a-(binSucc b) = binPred (a-b)
subSuccR  BinO         BinO     = Refl
subSuccR (BinP  U   )  BinO     = Refl
subSuccR (BinP (O _))  BinO     = Refl
subSuccR (BinP (I _))  BinO     = Refl
subSuccR  BinO        (BinP _ ) = Refl
subSuccR (BinP  a'  ) (BinP b') =
  rewrite subSuccPred a' b' in
  rewrite bimAndBin (bimMinus a' b') in Refl

-- Specification of multiplication

-- mul_0_l

mulZeroL : (a : Bin) -> BinO * a = BinO
mulZeroL  BinO    = Refl
mulZeroL (BinP _) = Refl

mulZeroR : (a : Bin) -> a * BinO = BinO
mulZeroR  BinO    = Refl
mulZeroR (BinP _) = Refl

-- mul_succ_l

mulSuccL : (a, b : Bin) -> (binSucc a) * b = b + a * b
mulSuccL  BinO      BinO     = Refl
mulSuccL  BinO     (BinP _ ) = Refl
mulSuccL (BinP _ )  BinO     = Refl
mulSuccL (BinP a') (BinP b') = cong $ mulSuccL a' b'

-- Specification of boolean comparisons (using <->)

-- eqb_eq
-- TODO split into `to` and `fro`
eqbEqTo : (p, q : Bin) -> (p == q = True) -> p=q
eqbEqTo  BinO     BinO    = const Refl
eqbEqTo  BinO    (BinP a) = absurd
eqbEqTo (BinP a)  BinO    = absurd
eqbEqTo (BinP a) (BinP b) = cong . eqbEqTo a b

eqbEqFro : (p, q : Bin) -> p=q -> (p == q = True)
eqbEqFro  BinO     BinO    _   = Refl
eqbEqFro  BinO    (BinP _) Refl impossible
eqbEqFro (BinP _)  BinO    Refl impossible
eqbEqFro (BinP a) (BinP b) prf = eqbEqFro a b (binPInj prf)

Lt : (x, y : Bin) -> Type
Lt x y = x `compare` y = LT

Gt : (x, y : Bin) -> Type
Gt x y = x `compare` y = GT

Le : (x, y : Bin) -> Type
Le x y = Not (x `compare` y = GT)

Ge : (x, y : Bin) -> Type
Ge x y = Not (x `compare` y = LT)

-- ltb_lt
-- TODO split into `to` and `fro`

ltbLtTo : (p, q : Bin) -> p < q = True -> p `Lt` q
ltbLtTo p q prf with (p `compare` q)
  | LT = Refl
  | EQ = absurd prf
  | GT = absurd prf

ltbLtFro : (p, q : Bin) -> p `Lt` q -> p < q = True
ltbLtFro _ _ pltq = rewrite pltq in Refl

-- leb_le
-- TODO split into `to` and `fro`

lebLeTo : (p, q : Bin) -> p > q = False -> p `Le` q
lebLeTo p q prf pq with (p `compare` q)
  | LT = absurd pq
  | EQ = absurd pq
  | GT = absurd prf

lebLeFro : (p, q : Bin) -> p `Le` q -> p > q = False
lebLeFro p q pleq with (p `compare` q)
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ pleq Refl

-- Basic properties of comparison (using <->)

compareSuccSucc : (n, m : Bin) -> binSucc n `compare` binSucc m = n `compare` m
compareSuccSucc  BinO     BinO    = Refl
compareSuccSucc  BinO    (BinP a) = lt1Succ a
compareSuccSucc (BinP a)  BinO    = ltGt U (bipSucc a) $ lt1Succ a
compareSuccSucc (BinP a) (BinP b) = compareSuccSucc a b

-- compare_eq_iff
-- TODO split into `to` and `fro`

compareEqIffTo : (p, q : Bin) -> p `compare` q = EQ -> p = q
compareEqIffTo  BinO     BinO    = const Refl
compareEqIffTo  BinO    (BinP _) = absurd
compareEqIffTo (BinP _)  BinO    = absurd
compareEqIffTo (BinP a) (BinP b) = cong . compareEqIffTo a b

compareEqIffFro : (p, q : Bin) -> p = q -> p `compare` q = EQ
compareEqIffFro  BinO     BinO    = const Refl
compareEqIffFro  BinO    (BinP _) = absurd
compareEqIffFro (BinP _)  BinO    = absurd
compareEqIffFro (BinP a) (BinP b) = compareEqIffFro a b . binPInj

-- compare_lt_iff is trivial

-- compare_le_iff is trivial

-- compare_antisym

compareAntisym : (p, q : Bin) -> q `compare` p = compareOp (p `compare` q)
compareAntisym  BinO     BinO    = Refl
compareAntisym  BinO    (BinP _) = Refl
compareAntisym (BinP _)  BinO    = Refl
compareAntisym (BinP a) (BinP b) = compareAntisym a b

-- Some more advanced properties of comparison and orders

dpoLt : (a, b : Bin) -> binDPO a `Lt` b -> binD a `Lt` b
dpoLt  BinO     BinO    = absurd
dpoLt  BinO    (BinP _) = const Refl
dpoLt (BinP _)  BinO    = absurd
dpoLt (BinP a) (BinP b) = leSuccLTo (O a) b . ltLeIncl (I a) b

ltLeIncl : (n, m : Bin) -> n `Lt` m -> n `Le` m
ltLeIncl n m nltm ngtm with (n `compare` m)
  | LT = uninhabited ngtm
  | EQ = uninhabited ngtm
  | GT = uninhabited nltm

ltGt : (p, q : Bin) -> p `Lt` q -> q `Gt` p
ltGt p q pltq =
  rewrite compareAntisym p q in
  rewrite pltq in
  Refl

gtLt : (p, q : Bin) -> p `Gt` q -> q `Lt` p
gtLt p q pgtq =
  rewrite compareAntisym p q in
  rewrite pgtq in
  Refl

-- add_0_r

addZeroR : (a : Bin) -> a + BinO = a
addZeroR  BinO    = Refl
addZeroR (BinP _) = Refl

-- add_comm

addComm : (a, b : Bin) -> a + b = b + a
addComm  BinO      BinO     = Refl
addComm  BinO     (BinP _ ) = Refl
addComm (BinP _ )  BinO     = Refl
addComm (BinP a') (BinP b') = cong $ addComm a' b'

-- add_assoc

addAssoc : (a, b, c : Bin) -> a + (b + c) = a + b + c
addAssoc  BinO      BinO      BinO     = Refl
addAssoc  BinO      BinO     (BinP _ ) = Refl
addAssoc  BinO     (BinP _ )  BinO     = Refl
addAssoc  BinO     (BinP _ ) (BinP _ ) = Refl
addAssoc (BinP _ )  BinO      BinO     = Refl
addAssoc (BinP _ )  BinO     (BinP _ ) = Refl
addAssoc (BinP _ ) (BinP _ )  BinO     = Refl
addAssoc (BinP a') (BinP b') (BinP c') = cong $ addAssoc a' b' c'

subDiag : (n : Bin) -> n-n = 0
subDiag  BinO    = Refl
subDiag (BinP a) = rewrite subMaskDiag a in
                   Refl

-- sub_add

subAdd : (p, q : Bin) -> p `Le` q -> (q-p)+p = q
subAdd  BinO     BinO    _    = Refl
subAdd  BinO    (BinP _) _    = Refl
subAdd (BinP _)  BinO    pleq = absurd $ pleq Refl
subAdd (BinP a) (BinP b) pleq = case subMaskSpec a b of
  SubIsNul     Refl _ => rewrite subMaskDiag a in
                         Refl
  SubIsPos {r} Refl _ => absurd $ pleq $ ltGt b (b+r) $ ltAddDiagR b r
  SubIsNeg {r} Refl _ => rewrite subMaskAddDiagL a r in
                         rewrite addComm a r in
                         Refl

addSub : (p, q : Bin) -> (p+q)-q = p
addSub BinO BinO = Refl
addSub BinO (BinP a) = rewrite subMaskDiag a in
                       Refl
addSub (BinP _) BinO = Refl
addSub (BinP a) (BinP b) =
  rewrite addComm a b in
  rewrite subMaskAddDiagL b a in
  Refl


-- mul_comm

mulComm : (a, b : Bin) -> a * b = b * a
mulComm  BinO      BinO     = Refl
mulComm  BinO     (BinP _ ) = Refl
mulComm (BinP _ )  BinO     = Refl
mulComm (BinP a') (BinP b') = cong $ mulComm a' b'

-- le_0_l

leZeroL : (a : Bin) -> BinO `Le` a
leZeroL  BinO    = uninhabited
leZeroL (BinP _) = uninhabited

-- leb_spec

-- TODO move to Bip.Proofs?

gtNotEqP : (p, q : Bip) -> p `Gt` q -> p == q = False
gtNotEqP  U     U    = absurd
gtNotEqP  U    (O _) = absurd
gtNotEqP  U    (I _) = absurd
gtNotEqP (O _)  U    = const Refl
gtNotEqP (O a) (O b) = gtNotEqP a b
gtNotEqP (O a) (I b) = const Refl
gtNotEqP (I _)  U    = const Refl
gtNotEqP (I a) (O b) = const Refl
gtNotEqP (I a) (I b) = gtNotEqP a b

gtNotEqN : (p, q : Bin) -> p `Gt` q -> p == q = False
gtNotEqN  BinO     BinO    = absurd
gtNotEqN  BinO    (BinP _) = absurd
gtNotEqN (BinP _)  BinO    = const Refl
gtNotEqN (BinP a) (BinP b) = gtNotEqP a b

-- TODO contribute to Prelude.Bool?

data BoolSpec : (p, q : Type) -> Bool -> Type where
  BoolSpecT : p -> BoolSpec p q True
  BoolSpecF : q -> BoolSpec p q False

lebSpec : (p, q : Bin) -> BoolSpec (p `Le` q) (q `Lt` p) (p <= q)
lebSpec p q with (p `compare` q) proof pq
  | LT = BoolSpecT uninhabited
  | EQ = rewrite eqbEqFro p q $ compareEqIffTo p q $ sym pq in
         BoolSpecT uninhabited
  | GT = rewrite gtNotEqN p q $ sym pq in
         BoolSpecF $ rewrite compareAntisym p q in
                     rewrite sym pq in
                     Refl

-- add_lt_cancel_l

addLtCancelL : (p, q, r : Bin) -> r+p `Lt` r+q -> p `Lt` q
addLtCancelL  p        q        BinO    = rewrite addZeroL p in
                                          rewrite addZeroL q in
                                          id
addLtCancelL  BinO     BinO    (BinP c) = rewrite compareContRefl c EQ in
                                          absurd
addLtCancelL  BinO    (BinP _) (BinP _) = const Refl
addLtCancelL (BinP a)  BinO    (BinP c) = absurd . ltNotAddL c a
addLtCancelL (BinP a) (BinP b) (BinP c) = addLtMonoLFro c a b

-- Specification of lt and le

-- lt_succ_r

-- TODO split into `to` and `fro`

ltSuccRTo : (p, q : Bin) -> p `Lt` binSucc q -> p `Le` q
ltSuccRTo  BinO     BinO    Refl  = uninhabited
ltSuccRTo  BinO    (BinP _) Refl  = uninhabited
ltSuccRTo (BinP a)  BinO    pltsq = absurd $ nlt1R a pltsq
ltSuccRTo (BinP a) (BinP b) pltsq = ltSuccRTo a b pltsq

ltSuccRFro : (p, q : Bin) -> p `Le` q -> p `Lt` binSucc q
ltSuccRFro  BinO     BinO    pleq = Refl
ltSuccRFro  BinO    (BinP _) pleq = Refl
ltSuccRFro (BinP _)  BinO    pleq = absurd $ pleq Refl
ltSuccRFro (BinP a) (BinP b) pleq = ltSuccRFro a b pleq

-- Properties of double and succ_double

-- double_spec

doubleSpec : (a : Bin) -> binD a = 2 * a
doubleSpec  BinO    = Refl
doubleSpec (BinP _) = Refl

-- succ_double_spec

succDoubleSpec : (a : Bin) -> binDPO a = 2 * a + 1
succDoubleSpec  BinO    = Refl
succDoubleSpec (BinP _) = Refl

-- double_add

doubleAdd : (a, b : Bin) -> binD (a + b) = binD a + binD b
doubleAdd  BinO     BinO    = Refl
doubleAdd  BinO    (BinP _) = Refl
doubleAdd (BinP _)  BinO    = Refl
doubleAdd (BinP _) (BinP _) = Refl

-- succ_double_add

succDoubleAdd : (a, b : Bin) -> binDPO (a + b) = binD a + binDPO b
succDoubleAdd  BinO     BinO    = Refl
succDoubleAdd  BinO    (BinP _) = Refl
succDoubleAdd (BinP _)  BinO    = Refl
succDoubleAdd (BinP _) (BinP _) = Refl

-- double_mul

doubleMul : (a, b : Bin) -> binD (a * b) = binD a * b
doubleMul  BinO     BinO    = Refl
doubleMul  BinO    (BinP _) = Refl
doubleMul (BinP _)  BinO    = Refl
doubleMul (BinP _) (BinP _) = Refl

-- succ_double_mul

succDoubleMul : (a, b : Bin) -> binDPO a * b = binD a * b + b
succDoubleMul  BinO      BinO     = Refl
succDoubleMul  BinO     (BinP _)  = Refl
succDoubleMul (BinP _)   BinO     = Refl
succDoubleMul (BinP a') (BinP b') =
  rewrite addComm (O (bipMult a' b')) b' in Refl

-- div2_double

divTwoDouble : (a : Bin) -> binDivTwo (binD a) = a
divTwoDouble  BinO    = Refl
divTwoDouble (BinP _) = Refl

-- div2_succ_double

divTwoSuccDouble : (a : Bin) -> binDivTwo (binDPO a) = a
divTwoSuccDouble  BinO    = Refl
divTwoSuccDouble (BinP _) = Refl

-- double_inj

doubleInj : (n, m : Bin) -> binD n = binD m -> n = m
doubleInj n m prf =
  rewrite sym $ divTwoDouble n in
  rewrite sym $ divTwoDouble m in
  rewrite prf in
  Refl

-- succ_double_inj

succDoubleInj : (n, m : Bin) -> binDPO n = binDPO m -> n = m
succDoubleInj n m prf =
  rewrite sym $ divTwoSuccDouble n in
  rewrite sym $ divTwoSuccDouble m in
  rewrite prf in
  Refl

-- succ_double_lt

succDoubleLt : (n, m : Bin) -> n `Lt` m -> binDPO n `Lt` binD m
succDoubleLt  BinO     BinO    = absurd
succDoubleLt  BinO    (BinP _) = const Refl
succDoubleLt (BinP _)  BinO    = absurd
succDoubleLt (BinP a) (BinP b) = compareContGtLtFro a b

-- Specification of minimum and maximum

-- min_l

minL : (n, m : Bin) -> n `Le` m -> min n m = n
minL n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = sym $ compareEqIffTo n m $ sym nm
  | GT = absurd $ nlem Refl

-- min_r

minR : (n, m : Bin) -> m `Le` n -> min n m = m
minR n m mlen with (m `compare` n) proof mn
  | LT = rewrite compareAntisym m n in
         rewrite sym mn in
         Refl
  | EQ = rewrite compareAntisym m n in
         rewrite sym mn in
         Refl
  | GT = absurd $ mlen Refl

-- max_l

maxL : (n, m : Bin) -> m `Le` n -> max n m = n
maxL n m mlen with (m `compare` n) proof mn
  | LT = rewrite compareAntisym m n in
         rewrite sym mn in
         Refl
  | EQ = rewrite compareAntisym m n in
         rewrite sym mn in
         compareEqIffTo m n $ sym mn
  | GT = absurd $ mlen Refl

-- max_r

maxR : (n, m : Bin) -> n `Le` m -> max n m = m
maxR n m nlem with (n `compare` m) proof nm
  | LT = Refl
  | EQ = Refl
  | GT = absurd $ nlem Refl

-- 0 is the least natural number

-- compare_0_r

compare0R : (n : Bin) -> Not (n `Lt` 0)
compare0R  BinO    = uninhabited
compare0R (BinP _) = uninhabited

-- Specifications of power

-- pow_0_r is trivial

-- pow_succ_r
-- dropped the `0<=p` requirement as it's trivial
powSuccR : (n, p : Bin) -> binPow n (binSucc p) = n * binPow n p
powSuccR  BinO     BinO    = Refl
powSuccR (BinP _)  BinO    = Refl
powSuccR  BinO    (BinP _) = Refl
powSuccR (BinP a) (BinP b) = cong $ powSuccR a b

-- pow_neg_r doesn't make sense: as Bin, p can't ever be <0

-- Specification of square

-- square_spec

squareSpec : (n : Bin) -> binSquare n = n * n
squareSpec  BinO    = Refl
squareSpec (BinP a) = cong $ squareSpec a

-- Specification of Base-2 logarithm

-- size_log2

sizeLog2 : (n : Bin) -> Not (n=0) -> binDigits n = binSucc (binLogTwo n)
sizeLog2  BinO        nz = absurd $ nz Refl
sizeLog2 (BinP  U   ) _  = Refl
sizeLog2 (BinP (O _)) _  = Refl
sizeLog2 (BinP (I _)) _  = Refl

-- size_gt

sizeGt : (n : Bin) -> n `Lt` binPow 2 (binDigits n)
sizeGt  BinO    = Refl
sizeGt (BinP a) = sizeGt a

-- size_le

sizeLe : (n : Bin) -> binPow 2 (binDigits n) `Le` binDPO n
sizeLe BinO = uninhabited
sizeLe (BinP a) =
  ltLeIncl (bipPow 2 (bipDigits a)) (I a) $
  ltSuccRFro (bipPow 2 (bipDigits a)) (O a) $
  sizeLe a

-- log2_spec
-- TODO replace requirement with `Not (n=0)`?
log2Spec : (n : Bin) -> 0 `Lt` n -> ( binPow 2 (binLogTwo n) `Le` n
                                    , n `Lt` binPow 2 (binSucc (binLogTwo n))
                                    )
log2Spec  BinO        zltn = absurd zltn
log2Spec (BinP  U   ) _    = (uninhabited, Refl)
log2Spec (BinP (O a)) _    = (sizeLe a, sizeGt $ BinP $ O a)
log2Spec (BinP (I a)) _    = (sizeLe $ BinP a, sizeGt $ BinP $ I a)

-- log2_nonpos doesn't make sense too (and is trivial when n=0)

-- Specification of parity functions

-- even_spec
-- TODO split into `to` and `fro`
-- TODO make a synonym for Even?
evenSpecTo : (n : Bin) -> binEven n = True -> (m ** n = 2*m)
evenSpecTo  BinO        _   = (0 ** Refl)
evenSpecTo (BinP  U   ) prf = absurd prf
evenSpecTo (BinP (O a)) _   = (BinP a ** Refl)
evenSpecTo (BinP (I _)) prf = absurd prf

evenSpecFro : (n : Bin) -> (m ** n = 2*m) -> binEven n = True
evenSpecFro  BinO         _         = Refl
evenSpecFro (BinP  U   ) (m ** prf) = case m of
  BinO   => absurd prf
  BinP _ => absurd $ binPInj prf
evenSpecFro (BinP (O _))  _         = Refl
evenSpecFro (BinP (I _)) (m ** prf) = case m of
  BinO   => absurd prf
  BinP _ => absurd $ binPInj prf

-- odd_spec
-- TODO split into `to` and `fro`
-- TODO make a synonym for Odd?
oddSpecTo : (n : Bin) -> binOdd n = True -> (m ** n = 2*m+1)
oddSpecTo  BinO        prf = absurd prf
oddSpecTo (BinP  U   ) _   = (0 ** Refl)
oddSpecTo (BinP (O _)) prf = absurd prf
oddSpecTo (BinP (I a)) _   = (BinP a ** Refl)

oddSpecFro : (n : Bin) -> (m ** n = 2*m+1) -> binOdd n = True
oddSpecFro  BinO        (m ** prf) = case m of
  BinO   => absurd prf
  BinP _ => absurd prf
oddSpecFro (BinP  U   )  _ = Refl
oddSpecFro (BinP (O _)) (m ** prf) = case m of
  BinO   => absurd $ binPInj prf
  BinP _ => absurd $ binPInj prf
oddSpecFro (BinP (I _))  _ = Refl

-- Specification of the euclidean division

-- pos_div_eucl_spec

posDivEuclSpec : (a : Bip) -> (b : Bin) -> let qr = bipDivEuclid a b
                                               q = fst qr
                                               r = snd qr
                                           in
                                           BinP a = q * b + r
posDivEuclSpec  U     BinO        = Refl
posDivEuclSpec  U    (BinP  U   ) = Refl
posDivEuclSpec  U    (BinP (O _)) = Refl
posDivEuclSpec  U    (BinP (I _)) = Refl
posDivEuclSpec (O a)  b           =
  -- BUG? can't directly rewrite with cong ..
  let ih = cong {f=binD} $ posDivEuclSpec a b
      qr = bipDivEuclid a b
      q = fst qr
      r = snd qr
    in
  rewrite ih in
  rewrite doubleAdd (q*b) r in
  rewrite doubleMul q b in
  aux q r
  where
  aux : (q, r : Bin) -> let res = bipDivEuclidHelp q (binD r) b (b `compare` binD r)
                       in ((binD q)*b)+(binD r) = ((fst res)*b)+(snd res)
  aux q r with (b `compare` binD r) proof cmp
    | LT = rewrite succDoubleMul q b in
           rewrite sym $ addAssoc ((binD q)*b) b ((binD r)-b) in
           rewrite addComm b ((binD r)-b) in
           rewrite subAdd b (binD r) $ ltLeIncl b (binD r) $ sym cmp in
           Refl
    | EQ = rewrite sym $ compareEqIffTo b (binD r) $ sym cmp in
           rewrite subDiag b in
           rewrite addZeroR ((binDPO q)*b) in
           sym $ succDoubleMul q b
    | GT = Refl
posDivEuclSpec (I a)  b           =
  let ih = cong {f=binDPO} $ posDivEuclSpec a b
      qr = bipDivEuclid a b
      q = fst qr
      r = snd qr
   in
  rewrite ih in
  rewrite succDoubleAdd (q*b) r in
  rewrite doubleMul q b in
  aux q r
  where
  aux : (q, r : Bin) -> let res = bipDivEuclidHelp q (binDPO r) b (b `compare` binDPO r)
                       in ((binD q)*b)+(binDPO r) = ((fst res)*b)+(snd res)
  aux q r with (b `compare` binDPO r) proof cmp
    | LT = rewrite succDoubleMul q b in
           rewrite sym $ addAssoc ((binD q)*b) b ((binDPO r)-b) in
           rewrite addComm b ((binDPO r)-b) in
           rewrite subAdd b (binDPO r) $ ltLeIncl b (binDPO r) $ sym cmp in
           Refl
    | EQ = rewrite sym $ compareEqIffTo b (binDPO r) $ sym cmp in
           rewrite subDiag b in
           rewrite addZeroR ((binDPO q)*b) in
           sym $ succDoubleMul q b
    | GT = Refl

-- div_eucl_spec
-- why is q*b flipped here?
divEuclSpec : (a, b : Bin) -> let qr = binDivEuclid a b
                                  q = fst qr
                                  r = snd qr
                              in a = b * q + r
divEuclSpec  BinO     BinO    = Refl
divEuclSpec  BinO    (BinP _) = Refl
divEuclSpec (BinP _)  BinO    = Refl
divEuclSpec (BinP a) (BinP b) =
  rewrite mulComm (BinP b) (fst (bipDivEuclid a (BinP b))) in
  posDivEuclSpec a (BinP b)

-- div_mod'
-- this looks redundant
divMod' : (a, b : Bin) -> a = b * (a `div` b) + (a `mod` b)
divMod' = divEuclSpec

-- div_mod looks even more redundant

-- pos_div_eucl_remainder

posDivEuclRemainder : (a : Bip) -> (b : Bin) -> Not (b=0) -> (snd $ bipDivEuclid a b) `Lt` b
posDivEuclRemainder  _     BinO        bz = absurd $ bz Refl
posDivEuclRemainder  U    (BinP  U   ) _  = Refl
posDivEuclRemainder  U    (BinP (O _)) _  = Refl
posDivEuclRemainder  U    (BinP (I _)) _  = Refl
posDivEuclRemainder (O a) (BinP  y   ) bz with ((BinP y) `compare` (binD $ snd $ bipDivEuclid a (BinP y))) proof cmp
  | LT = let b = BinP y
             r = snd $ bipDivEuclid a b
         in
         addLtCancelL ((binD r)-b) b b $
         rewrite addComm b ((binD r)-b) in
         rewrite subAdd b (binD r) $ ltLeIncl b (binD r) $ sym cmp in
         rewrite addDiag y in
         let ih = posDivEuclRemainder a b bz in
         dpoLt (snd $ bipDivEuclid a b) (BinP (O y)) $
         succDoubleLt r b ih
  | EQ = rewrite sym $ compareEqIffTo (BinP y) (binD $ snd $ bipDivEuclid a (BinP y)) $ sym cmp in
         rewrite subDiag (BinP y) in
         Refl
  | GT = gtLt (BinP y) (binD $ snd $ bipDivEuclid a (BinP y)) $ sym cmp
posDivEuclRemainder (I a) (BinP  y   ) bz with ((BinP y) `compare` (binDPO $ snd $ bipDivEuclid a (BinP y))) proof cmp
  | LT = let b = BinP y
             r = snd $ bipDivEuclid a b
         in
         addLtCancelL ((binDPO r)-b) b b $
         rewrite addComm b ((binDPO r)-b) in
         rewrite subAdd b (binDPO r) $ ltLeIncl b (binDPO r) $ sym cmp in
         rewrite addDiag y in
         let ih = posDivEuclRemainder a b bz in
         succDoubleLt r b ih
  | EQ = rewrite sym $ compareEqIffTo (BinP y) (binDPO $ snd $ bipDivEuclid a (BinP y)) $ sym cmp in
         rewrite subDiag (BinP y) in
         Refl
  | GT = gtLt (BinP y) (binDPO $ snd $ bipDivEuclid a (BinP y)) $ sym cmp

-- mod_lt

modLt : (a, b : Bin) -> Not (b=0) -> (a `mod` b) `Lt` b
modLt  _        BinO    bz = absurd $ bz Refl
modLt  BinO    (BinP _) _  = Refl
modLt (BinP a) (BinP b) bz = posDivEuclRemainder a (BinP b) bz

-- mod_bound_pos is just mod_lt + le_0_l

-- Specification of square root

-- sqrtrem_sqrt

sqrtremSqrt : (n : Bin) -> fst (binSqrtRem n) = binSqrt n
sqrtremSqrt  BinO    = Refl
sqrtremSqrt (BinP a) with (snd $ bipSqrtRem a)
  | BimP _ = Refl
  | BimO   = Refl
  | BimM   = Refl

-- sqrtrem_spec

sqrtremSpec : (n : Bin) -> let sr = binSqrtRem n
                               s = fst sr
                               r = snd sr
                           in (n = s*s + r, r `Le` 2*s)
sqrtremSpec  BinO    = (Refl, uninhabited)
sqrtremSpec (BinP a) = case sqrtremSpec a of
  SqrtExact  prf     srprf =>
    rewrite srprf in
    (cong prf, uninhabited)
  SqrtApprox prf rle srprf =>
    rewrite srprf in
    (cong prf, rle)

-- sqrt_spec
-- removed redundant constraint on `n`
sqrtSpec : (n : Bin) -> let s = binSqrt n in
  (s*s `Le` n, n `Lt` (binSucc s)*(binSucc s))
sqrtSpec BinO = (uninhabited, Refl)
sqrtSpec (BinP a) = sqrtSpec a

-- sqrt_neg doesn't make sense

-- Specification of gcd

-- ggcd_gcd
-- The first component of binGGCD is binGCD
ggcdGcd : (a, b : Bin) -> fst (binGGCD a b) = binGCD a b
ggcdGcd  BinO     BinO    = Refl
ggcdGcd  BinO    (BinP _) = Refl
ggcdGcd (BinP _)  BinO    = Refl
ggcdGcd (BinP a) (BinP b) = cong $ ggcdGcd a b

-- ggcd_correct_divisors
-- The other components of binGGCD are indeed the correct factors
ggcdCorrectDivisors : (a, b : Bin) -> let gaabb = binGGCD a b
                                          g = fst gaabb
                                          aa = fst $ snd gaabb
                                          bb = snd $ snd gaabb in
                                        (a=g*aa, b=g*bb)
ggcdCorrectDivisors  BinO     BinO    = (Refl, Refl)
ggcdCorrectDivisors  BinO    (BinP b) = (Refl, rewrite mul1R b in
                                               Refl)
ggcdCorrectDivisors (BinP a)  BinO    = (rewrite mul1R a in
                                         Refl, Refl)
ggcdCorrectDivisors (BinP a) (BinP b) = let (prf1, prf2) = ggcdCorrectDivisors a b in
                                        (cong prf1, cong prf2)

binDivides : (a, b : Bin) -> Type
binDivides a b = (c ** b = c*a)

-- gcd_divide_l

gcdDivideL : (a, b : Bin) -> binDivides (binGCD a b) a
gcdDivideL a b =
  let (aprf, _) = ggcdCorrectDivisors a b
      x = binGGCD a b in
  rewrite sym $ ggcdGcd a b in
  (fst $ snd x **
    rewrite mulComm (fst $ snd x) (fst x) in
    aprf)

-- gcd_divide_r

gcdDivideR : (a, b : Bin) -> binDivides (binGCD a b) b
gcdDivideR a b =
  let (_, bprf) = ggcdCorrectDivisors a b
      x = binGGCD a b in
  rewrite sym $ ggcdGcd a b in
  (snd $ snd x **
    rewrite mulComm (snd $ snd x) (fst x) in
    bprf)

-- gcd_greatest

gcdGreatest : (a, b, c : Bin) -> binDivides c a -> binDivides c b
                              -> binDivides c (binGCD a b)
gcdGreatest  BinO     BinO     c       _        _        = (0 ** rewrite mulZeroL c in Refl)
gcdGreatest  BinO    (BinP _)  _       _        cb       = cb
gcdGreatest (BinP _)  BinO     _       ca       _        = ca
gcdGreatest (BinP _) (BinP _)  BinO    (d**pca) _        = absurd $ replace (mulZeroR d) pca
gcdGreatest (BinP a) (BinP b) (BinP c) (d**pca) (e**pcb) = aux d e pca pcb
  where
  aux : (d, e : Bin) -> BinP a = binMult d (BinP c) -> BinP b = binMult e (BinP c)
                     -> (z ** BinP (bipGCD a b) = z*(BinP c))
  aux  BinO     _       pca _   = absurd pca
  aux  _        BinO    _   pcb = absurd pcb
  aux (BinP x) (BinP y) pca pcb =
    let (r**prf) = gcdGreatest a b c (x**binPInj pca) (y**binPInj pcb)
    in
    (BinP r ** cong prf)

-- gcd_nonneg is just le_0_l

-- Specification of bitwise functions

-- testbit_even_0

testbitEven0 : (a : Bin) -> binTestBit (2*a) 0 = False
testbitEven0  BinO    = Refl
testbitEven0 (BinP _) = Refl

-- testbit_odd_0

testbitOdd0 : (a : Bin) -> binTestBit (2*a+1) 0 = True
testbitOdd0  BinO    = Refl
testbitOdd0 (BinP _) = Refl

-- testbit_succ_r_div2

-- removed redundant constraint on `n`
testbitSuccRDiv2 : (a, n : Bin) -> binTestBit a (binSucc n) = binTestBit (binDivTwo a) n
testbitSuccRDiv2  BinO         _       = Refl
testbitSuccRDiv2 (BinP  U   )  BinO    = Refl
testbitSuccRDiv2 (BinP  U   ) (BinP _) = Refl
testbitSuccRDiv2 (BinP (O _))  BinO    = Refl
testbitSuccRDiv2 (BinP (O a)) (BinP b) = cong {f=bipTestBit a} $ predBinSucc b
testbitSuccRDiv2 (BinP (I _))  BinO    = Refl
testbitSuccRDiv2 (BinP (I a)) (BinP b) = cong {f=bipTestBit a} $ predBinSucc b

-- testbit_odd_succ
-- removed redundant constraint on `n`
testbitOddSucc : (a, n : Bin) -> binTestBit (2*a+1) (binSucc n) = binTestBit a n
testbitOddSucc a n = rewrite testbitSuccRDiv2 (2*a+1) n in
                     rewrite sym $ succDoubleSpec a in
                     rewrite divTwoSuccDouble a in
                     Refl

-- testbit_even_succ
-- removed redundant constraint on `n`
testbitEvenSucc : (a, n : Bin) -> binTestBit (2*a) (binSucc n) = binTestBit a n
testbitEvenSucc a n = rewrite testbitSuccRDiv2 (2*a) n in
                      rewrite sym $ doubleSpec a in
                      rewrite divTwoDouble a in
                      Refl

-- testbit_neg_r doesn't make sense

-- Correctness proofs for shifts

shiftlZero : (a : Bin) -> binShiftL a 0 = a
shiftlZero  BinO    = Refl
shiftlZero (BinP _) = Refl

-- shiftr_succ_r

shiftrSuccR : (a, n : Bin) -> binShiftR a (binSucc n) = binDivTwo (binShiftR a n)
shiftrSuccR _  BinO    = Refl
shiftrSuccR a (BinP b) = iterSucc binDivTwo a b

-- shiftl_succ_r

shiftlSuccR : (a, n : Bin) -> binShiftL a (binSucc n) = binD (binShiftL a n)
shiftlSuccR BinO _ = Refl
shiftlSuccR (BinP a) BinO = Refl
shiftlSuccR (BinP a) (BinP b) = cong $ iterSucc O a b

-- shiftr_spec
-- removed redundant constraint on `m`
shiftrSpec : (a, n, m : Bin) -> binTestBit (binShiftR a n) m = binTestBit a (m+n)
shiftrSpec a n =
  peanoRect
    -- a trick to emulate Coq's `revert`, otherwise you get stuck on `binSucc m`
    (\x => (y : Bin) -> binTestBit (binShiftR a x) y = binTestBit a (y+x))
    (\y => rewrite addZeroR y in Refl)
    (\n',fprf,y =>
     rewrite shiftrSuccR a n' in
     rewrite sym $ testbitSuccRDiv2 (binShiftR a n') y in
     rewrite fprf (binSucc y) in
     rewrite addComm y (binSucc n') in
     rewrite addSuccL n' y in
     rewrite addSuccL y n' in
     rewrite addComm n' y in
     Refl)
    n

-- shiftl_spec_high
-- removed redundant constraint on `m`
shiftlSpecHigh : (a, n, m : Bin) -> n `Le` m -> binTestBit (binShiftL a n) m = binTestBit a (m-n)
shiftlSpecHigh a n m nlem =
  rewrite sym $ subAdd n m nlem in
  rewrite addSub (m-n) n in
  Proofs.peanoRect
    (\x => (y : Bin) -> binTestBit (binShiftL a x) (y+x) = binTestBit a y)
    (\y => rewrite addZeroR y in
           rewrite shiftlZero a in
           Refl)
    (\n',fprf,y =>
      rewrite shiftlSuccR a n' in
      rewrite addComm y (binSucc n') in
      rewrite addSuccL n' y in
      rewrite doubleSpec (binShiftL a n') in
      rewrite testbitEvenSucc (binShiftL a n') (n'+y) in
      rewrite addComm n' y in
      fprf y)
    n
    (m-n)

-- shiftl_spec_low

shiftlSpecLow : (a, n, m : Bin) -> m `Lt` n -> binTestBit (binShiftL a n) m = False
shiftlSpecLow a BinO m mltn = absurd $ leZeroL m $ ltGt m 0 mltn
shiftlSpecLow a (BinP b) m mltn =
  peanoRect
    (\x => (y : Bin) -> y `Lt` (BinP x) -> binTestBit (binShiftL a (BinP x)) y = False)
    (\y,yltx => rewrite zeroLt1 y yltx in
                rewrite shiftlSuccR a 0 in
                rewrite doubleSpec (binShiftL a 0) in
                testbitEven0 (binShiftL a 0)
    )
    (\b',prf,y,yltx =>
      rewrite shiftlSuccR a (BinP b') in
      case y of
        BinO   => rewrite doubleSpec (binShiftL a (BinP b')) in
                  testbitEven0 (binShiftL a (BinP b'))
        BinP z => rewrite sym $ succPred (BinP z) uninhabited in
                  rewrite doubleSpec (binShiftL a (BinP b')) in
                  rewrite testbitEvenSucc (binShiftL a (BinP b')) (bipPredBin z) in
                  prf (bipPredBin z) $
                    rewrite sym $ compareSuccSucc (bipPredBin z) (BinP b') in
                    rewrite succPosPred z in
                    yltx
      )
    b
    m mltn
  where
  zeroLt1 : (n : Bin) -> n `Lt` 1 -> n = 0
  zeroLt1  BinO    Refl = Refl
  zeroLt1 (BinP a) nlt1 = absurd $ nlt1R a $ nlt1

-- div2_spec
-- TODO

-- Semantics of bitwise operations

-- pos_lxor_spec
-- lxor_spec
-- pos_lor_spec
-- lor_spec
-- pos_land_spec
-- land_spec
-- pos_ldiff_spec
-- ldiff_spec
-- TODO

-- Specification of constants

-- one_succ
-- two_succ
-- pred_0
-- TODO

-- Generic induction / recursion

-- bi_induction
-- recursion_wd
-- recursion_0
-- recursion_succ
-- TODO

-- Instantiation of generic properties of natural numbers

-- gt_lt_iff
-- gt_lt
-- lt_gt
-- ge_le_iff
-- ge_le
-- le_ge
-- TODO

-- Auxiliary results about right shift on positive numbers

-- pos_pred_shiftl_low
-- pos_pred_shiftl_high
-- pred_div2_up
-- TODO

-- More complex compatibility facts

-- Nplus_reg_l
-- Nmult_Sn_m
-- Nmult_plus_distr_l
-- Nmult_reg_r
-- Ncompare_antisym
-- TODO
