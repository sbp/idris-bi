module Data.Bin.Bitwise

import Data.Util

import Data.Bin

import Data.Bip.AddMul
import Data.Bip.Iter
import Data.Bip.OrdSub

import Data.Bin.AddSubMul
import Data.Bin.Iter
import Data.Bin.Ord

%access export
%default total

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
  peanoRect
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
shiftlSpecLow _  BinO    m mltn = absurd $ leZeroL m $ ltGt m 0 mltn
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

-- div2_spec is trivial

-- Semantics of bitwise operations

-- pos_lxor_spec

-- TODO there's a lot of repetition here, most likely it can be broken into lemmas and simplified
posLxorSpec : (p, p1: Bip) -> (n : Bin) -> binTestBit (bipXor p p1) n = xor (bipTestBit p n) (bipTestBit p1 n)
posLxorSpec  U     U     n       = sym $ xorDiag (bipTestBit U n)
posLxorSpec  U    (O _)  BinO    = Refl
posLxorSpec  U    (O a) (BinP b) = sym $ xorFalse (bipTestBit a (bipPredBin b))
posLxorSpec  U    (I _)  BinO    = Refl
posLxorSpec  U    (I a) (BinP b) = sym $ xorFalse (bipTestBit a (bipPredBin b))
posLxorSpec (O _)  U     BinO    = Refl
posLxorSpec (O a)  U    (BinP b) = rewrite xorComm (bipTestBit a (bipPredBin b)) False in
                                   sym $ xorFalse (bipTestBit a (bipPredBin b))
posLxorSpec (I _)  U     BinO    = Refl
posLxorSpec (I a)  U    (BinP b) = rewrite xorComm (bipTestBit a (bipPredBin b)) False in
                                   sym $ xorFalse (bipTestBit a (bipPredBin b))
posLxorSpec (O a) (O b)  BinO    = rewrite doubleSpec2 (bipXor a b) in
                                   testbitEven0 (bipXor a b)
posLxorSpec (O a) (O b) (BinP c) =
  rewrite doubleSpec2 (bipXor a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipXor a b) (bipPredBin c) in
  posLxorSpec a b (bipPredBin c)
posLxorSpec (O a) (I b)  BinO    = rewrite succDoubleSpec2 (bipXor a b) in
                                   testbitOdd0 (bipXor a b)
posLxorSpec (O a) (I b) (BinP c) =
  rewrite succDoubleSpec2 (bipXor a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitOddSucc (bipXor a b) (bipPredBin c) in
  posLxorSpec a b (bipPredBin c)
posLxorSpec (I a) (O b)  BinO    = rewrite succDoubleSpec2 (bipXor a b) in
                                   testbitOdd0 (bipXor a b)
posLxorSpec (I a) (O b) (BinP c) =
  rewrite succDoubleSpec2 (bipXor a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitOddSucc (bipXor a b) (bipPredBin c) in
  posLxorSpec a b (bipPredBin c)
posLxorSpec (I a) (I b)  BinO    = rewrite doubleSpec2 (bipXor a b) in
                                   testbitEven0 (bipXor a b)
posLxorSpec (I a) (I b) (BinP c) =
  rewrite doubleSpec2 (bipXor a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipXor a b) (bipPredBin c) in
  posLxorSpec a b (bipPredBin c)

-- lxor_spec

lxorSpec : (a, a1, n : Bin) -> binTestBit (binXor a a1) n = xor (binTestBit a n) (binTestBit a1 n)
lxorSpec  BinO     BinO     _ = Refl
lxorSpec  BinO    (BinP b1) n = sym $ xorFalse (bipTestBit b1 n)
lxorSpec (BinP b)  BinO     n = rewrite xorComm (bipTestBit b n) False in
                                sym $ xorFalse (bipTestBit b n)
lxorSpec (BinP b) (BinP b1) n = posLxorSpec b b1 n

-- pos_lor_spec

posLorSpec : (p, p1: Bip) -> (n : Bin) -> bipTestBit (bipOr p p1) n = (bipTestBit p n) || (bipTestBit p1 n)
posLorSpec  U     U     n       = sym $ orDiag $ bipTestBit U n
posLorSpec  U    (O _)  BinO    = Refl
posLorSpec  U    (O _) (BinP _) = Refl
posLorSpec  U    (I _)  BinO    = Refl
posLorSpec  U    (I _) (BinP _) = Refl
posLorSpec (O _)  U     BinO    = Refl
posLorSpec (O a)  U    (BinP c) = sym $ orFalse $ bipTestBit a (bipPredBin c)
posLorSpec (O _) (O _)  BinO    = Refl
posLorSpec (O a) (O b) (BinP c) = posLorSpec a b (bipPredBin c)
posLorSpec (O a) (I b)  BinO    = Refl
posLorSpec (O a) (I b) (BinP c) = posLorSpec a b (bipPredBin c)
posLorSpec (I a)  U     BinO    = Refl
posLorSpec (I a)  U    (BinP c) = sym $ orFalse $ bipTestBit a (bipPredBin c)
posLorSpec (I a) (O b)  BinO    = Refl
posLorSpec (I a) (O b) (BinP c) = posLorSpec a b (bipPredBin c)
posLorSpec (I a) (I b)  BinO    = Refl
posLorSpec (I a) (I b) (BinP c) = posLorSpec a b (bipPredBin c)

-- lor_spec

lorSpec : (a, a1, n : Bin) -> binTestBit (binOr a a1) n = (binTestBit a n) || (binTestBit a1 n)
lorSpec  BinO     _        _ = Refl
lorSpec (BinP b)  BinO     n = sym $ orFalse $ bipTestBit b n
lorSpec (BinP b) (BinP b1) n = posLorSpec b b1 n

-- pos_land_spec

posLandSpec : (p, p1 : Bip) -> (n : Bin) -> binTestBit (bipAnd p p1) n = (bipTestBit p n) && (bipTestBit p1 n)
posLandSpec  U     U     n       = sym $ andDiag $ bipTestBit U n
posLandSpec  U    (O _)  BinO    = Refl
posLandSpec  U    (O _) (BinP _) = Refl
posLandSpec  U    (I _)  BinO    = Refl
posLandSpec  U    (I _) (BinP _) = Refl
posLandSpec (O _)  U     BinO    = Refl
posLandSpec (O a)  U    (BinP c) = sym $ andFalse $ bipTestBit a (bipPredBin c)
posLandSpec (O a) (O b)  BinO    = rewrite doubleSpec2 (bipAnd a b) in
                                   testbitEven0 (bipAnd a b)
posLandSpec (O a) (O b) (BinP c) =
  rewrite doubleSpec2 (bipAnd a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipAnd a b) (bipPredBin c) in
  posLandSpec a b (bipPredBin c)
posLandSpec (O a) (I b)  BinO    = rewrite doubleSpec2 (bipAnd a b) in
                                   testbitEven0 (bipAnd a b)
posLandSpec (O a) (I b) (BinP c) =
  rewrite doubleSpec2 (bipAnd a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipAnd a b) (bipPredBin c) in
  posLandSpec a b (bipPredBin c)
posLandSpec (I a)  U     BinO    = Refl
posLandSpec (I a)  U    (BinP c) = sym $ andFalse $ bipTestBit a (bipPredBin c)
posLandSpec (I a) (O b)  BinO    = rewrite doubleSpec2 (bipAnd a b) in
                                   testbitEven0 (bipAnd a b)
posLandSpec (I a) (O b) (BinP c) =
  rewrite doubleSpec2 (bipAnd a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipAnd a b) (bipPredBin c) in
  posLandSpec a b (bipPredBin c)
posLandSpec (I a) (I b)  BinO    = rewrite succDoubleSpec2 (bipAnd a b) in
                                   testbitOdd0 (bipAnd a b)
posLandSpec (I a) (I b) (BinP c) =
  rewrite succDoubleSpec2 (bipAnd a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitOddSucc (bipAnd a b) (bipPredBin c) in
  posLandSpec a b (bipPredBin c)

-- land_spec

landSpec : (a, a1, n : Bin) -> binTestBit (binAnd a a1) n = (binTestBit a n) && (binTestBit a1 n)
landSpec  BinO     _        _ = Refl
landSpec (BinP b)  BinO     n = sym $ andFalse $ bipTestBit b n
landSpec (BinP b) (BinP b1) n = posLandSpec b b1 n

-- pos_ldiff_spec

posLdiffSpec : (p, p1 : Bip) -> (n : Bin) -> binTestBit (bipDiff p p1) n = (bipTestBit p n) && not (bipTestBit p1 n)
posLdiffSpec  U     U     n       = sym $ andNot $ bipTestBit U n
posLdiffSpec  U    (O _)  BinO    = Refl
posLdiffSpec  U    (O _) (BinP _) = Refl
posLdiffSpec  U    (I _)  BinO    = Refl
posLdiffSpec  U    (I _) (BinP _) = Refl
posLdiffSpec (O _)  U     BinO    = Refl
posLdiffSpec (O a)  U    (BinP c) = sym $ andTrue $ bipTestBit a (bipPredBin c)
posLdiffSpec (O a) (O b)  BinO    = rewrite doubleSpec2 (bipDiff a b) in
                                    testbitEven0 (bipDiff a b)
posLdiffSpec (O a) (O b) (BinP c) =
  rewrite doubleSpec2 (bipDiff a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipDiff a b) (bipPredBin c) in
  posLdiffSpec a b (bipPredBin c)
posLdiffSpec (O a) (I b)  BinO    = rewrite doubleSpec2 (bipDiff a b) in
                                    testbitEven0 (bipDiff a b)
posLdiffSpec (O a) (I b) (BinP c) =
  rewrite doubleSpec2 (bipDiff a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipDiff a b) (bipPredBin c) in
  posLdiffSpec a b (bipPredBin c)
posLdiffSpec (I a)  U     BinO    = Refl
posLdiffSpec (I a)  U    (BinP c) = sym $ andTrue $ bipTestBit a (bipPredBin c)
posLdiffSpec (I a) (O b)  BinO    = rewrite succDoubleSpec2 (bipDiff a b) in
                                    testbitOdd0 (bipDiff a b)
posLdiffSpec (I a) (O b) (BinP c) =
  rewrite succDoubleSpec2 (bipDiff a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitOddSucc (bipDiff a b) (bipPredBin c) in
  posLdiffSpec a b (bipPredBin c)
posLdiffSpec (I a) (I b)  BinO    = rewrite doubleSpec2 (bipDiff a b) in
                                    testbitEven0 (bipDiff a b)
posLdiffSpec (I a) (I b) (BinP c) =
  rewrite doubleSpec2 (bipDiff a b) in
  rewrite sym $ succPosPred c in
  rewrite testbitEvenSucc (bipDiff a b) (bipPredBin c) in
  posLdiffSpec a b (bipPredBin c)

-- ldiff_spec

ldiffSpec : (a, a1, n : Bin) -> binTestBit (binDiff a a1) n = (binTestBit a n) && not (binTestBit a1 n)
ldiffSpec  BinO     _        _ = Refl
ldiffSpec (BinP b)  BinO     n = sym $ andTrue $ bipTestBit b n
ldiffSpec (BinP b) (BinP b1) n = posLdiffSpec b b1 n


-- Instantiation of generic properties of natural numbers

-- Auxiliary results about right shift on positive numbers

zeroBitDMO : (p : Bip) -> bipTestBit (bipDMO p) 0 = True
zeroBitDMO  U    = Refl
zeroBitDMO (O _) = Refl
zeroBitDMO (I _) = Refl

-- pos_pred_shiftl_low

posPredShiftlLow : (p : Bip) -> (n, m : Bin) -> m `Lt` n -> binTestBit (bipPredBin (bipShiftL p n)) m = True
posPredShiftlLow _  BinO    m mltn = absurd $ compare0R m mltn
posPredShiftlLow p (BinP a) m mltn =
  peanoRect
    (\x => (y : Bin) -> y `Lt` (BinP x) -> binTestBit (bipPredBin (bipIter O p x)) y = True)
    (\y, yltx =>
     rewrite zeroLt1 y yltx in
     zeroBitDMO p)
    (\x',prf,y,yltx =>
      case y of
        BinO   => rewrite iterSucc O p x' in
                  zeroBitDMO (bipIter O p x')
        BinP z => rewrite sym $ succPred (BinP z) uninhabited in
                  rewrite testbitSuccRDiv2 (bipPredBin (bipIter O p (bipSucc x'))) (bipPredBin z) in
                  rewrite iterSucc O p x' in
                  rewrite sym $ dmoDiv2 (bipIter O p x') in
                  prf (bipPredBin z) $
                     rewrite sym $ compareSuccSucc (bipPredBin z) (BinP x') in
                     rewrite succPosPred z in
                     yltx
    )
    a
    m mltn

-- pos_pred_shiftl_high

dmoPredDPO : (a : Bip) -> BinP (bipDMO a) = binDPO (bipPredBin a)
dmoPredDPO  U    = Refl
dmoPredDPO (O _) = Refl
dmoPredDPO (I _) = Refl

posPredShiftlHigh  : (p : Bip) -> (n, m : Bin) -> n `Le` m -> binTestBit (bipPredBin (bipShiftL p n)) m = binTestBit (binShiftL (bipPredBin p) n) m
posPredShiftlHigh p n m nlem =
  peanoRect
    (\x => (y : Bin) -> x `Le` y -> binTestBit (bipPredBin (bipShiftL p x)) y = binTestBit (binShiftL (bipPredBin p) x) y)
    (\_,_ => rewrite shiftlZero (bipPredBin p) in
     Refl)
    (\n',prf,y,xley =>
     let (a**prfa) = succLePos n' y xley in
     rewrite prfa in
     rewrite sym $ succPred (BinP a) uninhabited in
     rewrite shiftlSuccR (bipPredBin p) n' in
     rewrite aux p n' in
     rewrite doubleSpec (binShiftL (bipPredBin p) n') in
     rewrite succDoubleSpec (bipPredBin (bipShiftL p n')) in
     rewrite testbitEvenSucc (binShiftL (bipPredBin p) n') (bipPredBin a) in
     rewrite testbitOddSucc (bipPredBin (bipShiftL p n')) (bipPredBin a) in
     prf (bipPredBin a) $
       rewrite sym $ compareSuccSucc n' (bipPredBin a) in
       rewrite succPosPred a in
       rewrite sym prfa in
       xley
    )
    n
    m nlem
  where
  aux : (a : Bip) -> (n : Bin) -> bipPredBin $ bipShiftL a (binSucc n) = binDPO $ bipPredBin (bipShiftL a n)
  aux a BinO = dmoPredDPO a
  aux a (BinP b) = rewrite iterSucc O a b in
                   dmoPredDPO (bipIter O a b)