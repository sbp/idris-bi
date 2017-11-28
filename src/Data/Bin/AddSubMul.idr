module Data.Bin.AddSubMul

import Data.Bin
import Data.Bip.AddMul
import Data.Bip.OrdSub

%access export
%default total

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

dmoDiv2 : (a : Bip) -> bipPredBin a = binDivTwo (BinP $ bipDMO a)
dmoDiv2  U    = Refl
dmoDiv2 (O _) = Refl
dmoDiv2 (I _) = Refl

-- Properties of successor and predecessor

succPred : (a : Bin) -> Not (a=0) -> binSucc (binPred a) = a
succPred  BinO    az = absurd $ az Refl
succPred (BinP a) _  = succPosPred a

-- pred_succ
predSucc : (a : Bin) -> binPred (binSucc a) = a
predSucc  BinO     = Refl
predSucc (BinP a') = rewrite predBinSucc a' in Refl

-- pred_sub
predSub : (a : Bin) -> binPred a = a-1
predSub  BinO        = Refl
predSub (BinP  U   ) = Refl
predSub (BinP (O _)) = Refl
predSub (BinP (I _)) = Refl

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

subDiag : (n : Bin) -> n-n = 0
subDiag  BinO    = Refl
subDiag (BinP a) = rewrite subMaskDiag a in
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

-- mul_comm

mulComm : (a, b : Bin) -> a * b = b * a
mulComm  BinO      BinO     = Refl
mulComm  BinO     (BinP _ ) = Refl
mulComm (BinP _ )  BinO     = Refl
mulComm (BinP a') (BinP b') = cong $ mulComm a' b'

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

-- pred_div2_up

predDiv2Up : (p : Bip) -> bipPredBin (bipDivTwoCeil p) = binDivTwo (bipPredBin p)
predDiv2Up  U    = Refl
predDiv2Up (O a) = dmoDiv2 a
predDiv2Up (I a) = predBinSucc a

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

-- some unfortunate duplication, see idris-bi/16
doubleSpec2 : (a : Bin) -> binDouble a = 2 * a
doubleSpec2  BinO    = Refl
doubleSpec2 (BinP _) = Refl

succDoubleSpec2 : (a : Bin) -> binDoubleSucc a = 2 * a + 1
succDoubleSpec2  BinO    = Refl
succDoubleSpec2 (BinP _) = Refl
