module Data.Biz.Bitwise

import Control.Pipeline

import Data.Util

import Data.Bip.AddMul
import Data.Bip.Iter
import Data.Bip.OrdSub

import Data.Bin.AddSubMul
import Data.Bin.Ord
import Data.Bin.Bitwise

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Iter
import Data.Biz.Ord

%default total
%access export

-- these seem to only be used here, if we move them to divMod there's a cyclic dependency

div2D : (x : Biz) -> bizDivTwo (bizD x) = x
div2D  BizO    = Refl
div2D (BizP _) = Refl
div2D (BizM _) = Refl

div2DPO : (x : Biz) -> bizDivTwo (bizDPO x) = x
div2DPO  BizO        = Refl
div2DPO (BizP  _)    = Refl
div2DPO (BizM  U)    = Refl
div2DPO (BizM (O a)) = rewrite succPredDouble a in
                       Refl
div2DPO (BizM (I _)) = Refl

div2Pos : (x : Biz) -> 0 `Le` x -> 0 `Le` bizDivTwo x
div2Pos  BizO        _    = uninhabited
div2Pos (BizP  U)    _    = uninhabited
div2Pos (BizP (O _)) _    = uninhabited
div2Pos (BizP (I _)) _    = uninhabited
div2Pos (BizM  _)    zlex = absurd $ zlex Refl

dDiv2Le : (x : Biz) -> 0 `Le` x -> 2*(bizDivTwo x) `Le` x
dDiv2Le  BizO        _    = uninhabited
dDiv2Le (BizP  U)    _    = uninhabited
dDiv2Le (BizP (O a)) _    = rewrite compareContRefl a EQ in
                            uninhabited
dDiv2Le (BizP (I a)) _    = rewrite compareContRefl a LT in
                            uninhabited
dDiv2Le (BizM  _)    zlex = absurd $ zlex Refl

-- Specification of parity functions

public export
Even : Biz -> Type
Even a = (b ** a = 2*b)

public export
Odd : Biz -> Type
Odd a = (b ** a = 2*b+1)

-- even_spec
-- TODO split into `to` and `fro`

evenSpecTo : (n : Biz) -> bizEven n = True -> Even n
evenSpecTo  BizO        _   = (0 ** Refl)
evenSpecTo (BizP  U   ) prf = absurd prf
evenSpecTo (BizP (O a)) _   = (BizP a ** Refl)
evenSpecTo (BizP (I _)) prf = absurd prf
evenSpecTo (BizM  U   ) prf = absurd prf
evenSpecTo (BizM (O a)) _   = (BizM a ** Refl)
evenSpecTo (BizM (I _)) prf = absurd prf

evenSpecFro : (n : Biz) -> Even n -> bizEven n = True
evenSpecFro _ (BizO   ** prf) = rewrite prf in
                                Refl
evenSpecFro _ (BizP _ ** prf) = rewrite prf in
                                Refl
evenSpecFro _ (BizM _ ** prf) = rewrite prf in
                                Refl

-- odd_spec
-- TODO split into `to` and `fro`

oddSpecTo : (n : Biz) -> bizOdd n = True -> Odd n
oddSpecTo  BizO        prf = absurd prf
oddSpecTo (BizP  U   ) _   = (0 ** Refl)
oddSpecTo (BizP (O _)) prf = absurd prf
oddSpecTo (BizP (I a)) _   = (BizP a ** Refl)
oddSpecTo (BizM  U   ) _   = (-1 ** Refl)
oddSpecTo (BizM (O _)) prf = absurd prf
oddSpecTo (BizM (I a)) _   = (BizM (bipSucc a) ** rewrite predDoubleSucc a in
                                                  Refl)

oddSpecFro : (n : Biz) -> Odd n -> bizOdd n = True
oddSpecFro _ (BizO       ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizP  _    ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizM  U    ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizM (O _) ** prf) = rewrite prf in
                                   Refl
oddSpecFro _ (BizM (I _) ** prf) = rewrite prf in
                                   Refl

-- Even_or_Odd

evenOrOdd : (a : Biz) -> Either (Even a) (Odd a)
evenOrOdd =
  biInduction
    (\x => Either (Even x) (Odd x))
    (Left (0 ** Refl))
    (\x, prf =>
      case prf of
        Left  (b ** prf) => Right (b ** cong {f=\x=>x+1} prf)
        Right (b ** prf) => Left ((b+1) ** rewrite prf in
                                           rewrite mulAddDistrL 2 b 1 in
                                           rewrite sym $ addAssoc (2*b) 1 1 in
                                           Refl)
    )
    (\x, prf =>
      case prf of
        Left  (b ** prf) => Right ((b-1) ** addRegR 1 x (2*(b-1)+1) $
                                            rewrite mulAddDistrL 2 b (-1) in
                                            rewrite sym $ addAssoc (2*b) (-2) 1 in
                                            rewrite sym $ addAssoc (2*b) (-1) 1 in
                                            rewrite add0R (2*b) in
                                            prf)
        Right (b ** prf) => Left  (b ** addRegR 1 x (2*b) prf)
    )

oddNotEven : (x : Biz) -> bizOdd x = not (bizEven x)
oddNotEven  BizO        = Refl
oddNotEven (BizP  U)    = Refl
oddNotEven (BizP (O _)) = Refl
oddNotEven (BizP (I _)) = Refl
oddNotEven (BizM  U)    = Refl
oddNotEven (BizM (O _)) = Refl
oddNotEven (BizM (I _)) = Refl

-- Conversions between [Z.testbit] and [N.testbit]

-- testbit_of_N

testbitOfN : (a, n : Bin) -> bizTestBit (toBizBin a) (toBizBin n) = binTestBit a n
testbitOfN  BinO         BinO    = Refl
testbitOfN  BinO        (BinP _) = Refl
testbitOfN (BinP  U   )  BinO    = Refl
testbitOfN (BinP (O _))  BinO    = Refl
testbitOfN (BinP (I _))  BinO    = Refl
testbitOfN (BinP  _   ) (BinP _) = Refl

-- testbit_of_N'

testbitOfN1 : (a : Bin) -> (n : Biz) -> 0 `Le` n -> bizTestBit (toBizBin a) n = binTestBit a (toBinBiz n)
testbitOfN1 a  BizO    _    = testbitOfN a BinO
testbitOfN1 a (BizP b) _    = testbitOfN a (BinP b)
testbitOfN1 _ (BizM _) zlen = absurd $ zlen Refl

-- testbit_Zpos

testbitZpos : (a : Bip) -> (n : Biz) -> 0 `Le` n -> bizTestBit (BizP a) n = binTestBit (BinP a) (toBinBiz n)
testbitZpos a = testbitOfN1 (BinP a)

-- testbit_Zneg

testbitZneg : (a : Bip) -> (n : Biz) -> 0 `Le` n -> bizTestBit (BizM a) n = not (binTestBit (bipPredBin a) (toBinBiz n))
testbitZneg  U     BizO    _    = Refl
testbitZneg (O a)  BizO    _    = rewrite zeroBitDMO a in
                                  Refl
testbitZneg (I _)  BizO    _    = Refl
testbitZneg  _    (BizP _) _    = Refl
testbitZneg  _    (BizM _) zlen = absurd $ zlen Refl

-- Proofs of specifications for bitwise operations

-- div2_spec is trivial

-- testbit_0_l

testbit0L : (n : Biz) -> bizTestBit 0 n = False
testbit0L  BizO    = Refl
testbit0L (BizP _) = Refl
testbit0L (BizM _) = Refl

testbit1L : (n : Biz) -> bizTestBit 1 n = n == 0
testbit1L  BizO    = Refl
testbit1L (BizP _) = Refl
testbit1L (BizM _) = Refl

testbitM1L : (n : Biz) -> 0 `Le` n -> bizTestBit (-1) n = True
testbitM1L  BizO    _    = Refl
testbitM1L (BizP _) _    = Refl
testbitM1L (BizM _) zlen = absurd $ zlen Refl

-- testbit_neg_r

testbitNegR : (a, n : Biz) -> n `Lt` 0 -> bizTestBit a n = False
testbitNegR  _        BizO    nlt0 = absurd nlt0
testbitNegR  _       (BizP _) nlt0 = absurd nlt0
testbitNegR  BizO    (BizM _) _    = Refl
testbitNegR (BizP _) (BizM _) _    = Refl
testbitNegR (BizM _) (BizM _) _    = Refl

-- testbit_odd_0

testbitOdd0 : (a : Biz) -> bizTestBit (bizDPO a) 0 = True
testbitOdd0  BizO        = Refl
testbitOdd0 (BizP  _   ) = Refl
testbitOdd0 (BizM  U   ) = Refl
testbitOdd0 (BizM (O _)) = Refl
testbitOdd0 (BizM (I _)) = Refl

-- testbit_even_0

testbitEven0 : (a : Biz) -> bizTestBit (bizD a) 0 = False
testbitEven0  BizO    = Refl
testbitEven0 (BizP _) = Refl
testbitEven0 (BizM _) = Refl

-- testbit_odd_succ

testbitOddSucc : (a, n : Biz) -> 0 `Le` n -> bizTestBit (bizDPO a) (bizSucc n) = bizTestBit a n
testbitOddSucc  BizO         BizO    _    = Refl
testbitOddSucc (BizP  U   )  BizO    _    = Refl
testbitOddSucc (BizP (O _))  BizO    _    = Refl
testbitOddSucc (BizP (I _))  BizO    _    = Refl
testbitOddSucc (BizM  U   )  BizO    _    = Refl
testbitOddSucc (BizM (O a))  BizO    _    = rewrite zeroBitDMO a in
                                            Refl
testbitOddSucc (BizM (I _))  BizO    _    = Refl
testbitOddSucc  BizO        (BizP _) _    = Refl
testbitOddSucc (BizP  U   ) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizP (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizP (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizM  U   ) (BizP _) _    = Refl
testbitOddSucc (BizM (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc (BizM (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitOddSucc  _           (BizM _) zlen = absurd $ zlen Refl

-- testbit_even_succ

testbitEvenSucc : (a, n : Biz) -> 0 `Le` n -> bizTestBit (bizD a) (bizSucc n) = bizTestBit a n
testbitEvenSucc  BizO         BizO    _    = Refl
testbitEvenSucc (BizP  U   )  BizO    _    = Refl
testbitEvenSucc (BizP (O _))  BizO    _    = Refl
testbitEvenSucc (BizP (I _))  BizO    _    = Refl
testbitEvenSucc (BizM  U   )  BizO    _    = Refl
testbitEvenSucc (BizM (O a))  BizO    _    = rewrite zeroBitDMO a in
                                             Refl
testbitEvenSucc (BizM (I _))  BizO    _    = Refl
testbitEvenSucc  BizO        (BizP _) _    = Refl
testbitEvenSucc (BizP  U   ) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizP (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizP (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizM  U   ) (BizP _) _    = Refl
testbitEvenSucc (BizM (O _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc (BizM (I _)) (BizP b) _    =
  rewrite add1R b in
  rewrite predBinSucc b in
  Refl
testbitEvenSucc  _           (BizM _) zlen = absurd $ zlen Refl

-- Correctness proofs about [Z.shiftr] and [Z.shiftl]

div2BizBin : (x : Bin) -> toBizBin (binDivTwo x) = bizDivTwo (toBizBin x)
div2BizBin  BinO        = Refl
div2BizBin (BinP  U   ) = Refl
div2BizBin (BinP (O _)) = Refl
div2BizBin (BinP (I _)) = Refl

div2BipBin : (x : Bip) -> bipPredBin (bipDivTwoCeil x) = binDivTwo (bipPredBin x)
div2BipBin  U    = Refl
div2BipBin (O a) = rewrite dmoPredDPO a in
                   sym $ divTwoSuccDouble (bipPredBin a)
div2BipBin (I a) = predBinSucc a

-- shiftr_spec_aux

shiftrSpecAux : (a, n, m : Biz) -> 0 `Le` n -> 0 `Le` m -> bizTestBit (bizShiftR a n) m = bizTestBit a (m+n)
shiftrSpecAux  _       (BizM _)  _       zlen _    = absurd $ zlen Refl
shiftrSpecAux  _        _       (BizM _) _    zlem = absurd $ zlem Refl
shiftrSpecAux  _        BizO     BizO    _    _    = Refl
shiftrSpecAux  _        BizO    (BizP _) _    _    = Refl
shiftrSpecAux  BizO    (BizP b)  m       _    _    =
  let zeroIterDiv2 = iterInvariant bizDivTwo (\x=>x=0) b (\_,prf => rewrite prf in Refl) 0 Refl in
  rewrite zeroIterDiv2 in
  rewrite testbit0L (m+(BizP b)) in
  testbit0L m
shiftrSpecAux (BizP a) (BizP b)  BizO    _    _    =
  rewrite sym $ iterSwapGen toBizBin binDivTwo bizDivTwo div2BizBin (BinP a) b in
  rewrite testbitOfN1 (bipIter binDivTwo (BinP a) b) 0 uninhabited in
  shiftrSpec (BinP a) (BinP b) 0
shiftrSpecAux (BizP a) (BizP b) (BizP c) _    _    =
  rewrite sym $ iterSwapGen toBizBin binDivTwo bizDivTwo div2BizBin (BinP a) b in
  rewrite testbitOfN1 (bipIter binDivTwo (BinP a) b) (BizP c) uninhabited in
  shiftrSpec (BinP a) (BinP b) (BinP c)
shiftrSpecAux (BizM a) (BizP b)  BizO    _    _    =
  rewrite sym $ iterSwapGen BizM bipDivTwoCeil bizDivTwo (\_ => Refl) a b in
  rewrite testbitZneg (bipIter bipDivTwoCeil a b) 0 uninhabited in
  rewrite iterSwapGen bipPredBin bipDivTwoCeil binDivTwo div2BipBin a b in
  cong $ shiftrSpec (bipPredBin a) (BinP b) 0
shiftrSpecAux (BizM a) (BizP b) (BizP c) _    _    =
  rewrite sym $ iterSwapGen BizM bipDivTwoCeil bizDivTwo (\_ => Refl) a b in
  rewrite iterSwapGen bipPredBin bipDivTwoCeil binDivTwo div2BipBin a b in
  cong $ shiftrSpec (bipPredBin a) (BinP b) (BinP c)

-- shiftl_spec_low

shiftlSpecLow : (a, n, m : Biz) -> m `Lt` n -> bizTestBit (bizShiftL a n) m = False
shiftlSpecLow  _        BizO     BizO    mltn = absurd mltn
shiftlSpecLow  _        BizO    (BizP _) mltn = absurd mltn
shiftlSpecLow  a        n       (BizM c) _    = testbitNegR (bizShiftL a n) (BizM c) Refl
shiftlSpecLow  a       (BizP b)  BizO    _    =
  case succPredOr b of
    Left  lprf =>
      rewrite lprf in
      rewrite sym $ doubleSpec a in
      testbitEven0 a
    Right rprf =>
      rewrite sym rprf in
      rewrite iterSucc (bizMult 2) a (bipPred b) in
      rewrite sym $ doubleSpec (bipIter (bizMult 2) a (bipPred b)) in
      testbitEven0 (bipIter (bizMult 2) a (bipPred b))
shiftlSpecLow  BizO    (BizP b) (BizP c) _    =
  let zeroIterMul2 = iterInvariant (bizMult 2) (\x=>x=0) b (\_,prf => rewrite prf in Refl) 0 Refl in
  rewrite zeroIterMul2 in
  Refl
shiftlSpecLow (BizP a) (BizP b) (BizP c) mltn =
  rewrite sym $ iterSwapGen BizP O (bizMult 2) (\_ => Refl) a b in
  shiftlSpecLow (BinP a) (BinP b) (BinP c) mltn
shiftlSpecLow (BizM a) (BizP b) (BizP c) mltn =
  rewrite sym $ iterSwapGen BizM O (bizMult 2) (\_ => Refl) a b in
  cong {f=not} $ posPredShiftlLow a (BinP b) (BinP c) mltn
shiftlSpecLow  _       (BizM _)  BizO    mltn = absurd mltn
shiftlSpecLow  _       (BizM _) (BizP _) mltn = absurd mltn

-- shiftl_spec_high

shiftlSpecHigh : (a, n, m : Biz) -> 0 `Le` m -> n `Le` m -> bizTestBit (bizShiftL a n) m = bizTestBit a (m-n)
shiftlSpecHigh  _        BizO     m       _    _    = rewrite add0R m in
                                                      Refl
shiftlSpecHigh  a       (BizM b)  m       zlem _    = shiftrSpecAux a (BizP b) m uninhabited zlem
shiftlSpecHigh  _       (BizP _)  BizO    _    nlem = absurd $ nlem Refl
shiftlSpecHigh  BizO    (BizP b) (BizP c) _    _    =
  let zeroIterMul2 = iterInvariant (bizMult 2) (\x=>x=0) b (\_,prf => rewrite prf in Refl) 0 Refl in
  rewrite zeroIterMul2 in
  sym $ testbit0L (bipMinusBiz c b)
shiftlSpecHigh (BizP a) (BizP b) (BizP c) _    nlem =
  rewrite sym $ iterSwapGen BizP O (bizMult 2) (\_ => Refl) a b in
  rewrite shiftlSpecHigh (BinP a) (BinP b) (BinP c) nlem in
  rewrite testbitZpos a (bipMinusBiz c b) $
            geLe (bipMinusBiz c b) 0 $
            rewrite sym $ compareSub (BizP c) (BizP b) in
            leGe b c nlem
    in
  cong $ minusBiz c b
shiftlSpecHigh (BizM a) (BizP b) (BizP c) _    nlem =
  rewrite sym $ iterSwapGen BizM O (bizMult 2) (\_ => Refl) a b in
  rewrite posPredShiftlHigh a (BinP b) (BinP c) nlem in
  rewrite testbitZneg a (bipMinusBiz c b) $
            geLe (bipMinusBiz c b) 0 $
            rewrite sym $ compareSub (BizP c) (BizP b) in
            leGe b c nlem
    in
  rewrite shiftlSpecHigh (bipPredBin a) (BinP b) (BinP c) nlem in
  cong {f = not . binTestBit (bipPredBin a)} $ minusBiz c b
shiftlSpecHigh  _        _       (BizM _) zlem _    = absurd $ zlem Refl

-- shiftr_spec

shiftrSpec : (a, n, m : Biz) -> 0 `Le` m -> bizTestBit (bizShiftR a n) m = bizTestBit a (m+n)
shiftrSpec a    BizO    m zlem = shiftrSpecAux a 0 m uninhabited zlem
shiftrSpec a n@(BizP _) m zlem = shiftrSpecAux a n m uninhabited zlem
shiftrSpec a   (BizM b) m zlem with ((BizP b) `compare` m) proof nm
  | LT = shiftlSpecHigh a (BizP b) m zlem $ ltLeIncl (BizP b) m $ sym nm
  | EQ = shiftlSpecHigh a (BizP b) m zlem $ rewrite sym nm in
                                            uninhabited
  | GT = rewrite shiftlSpecLow a (BizP b) m $ gtLt (BizP b) m $ sym nm in
         sym $ testbitNegR a (m-BizP b) $
           rewrite sym $ compareSub m (BizP b) in
           gtLt (BizP b) m $ sym nm

-- Correctness proofs for bitwise operations

-- lor_spec

or0R : (n : Biz) -> bizOr n BizO = n
or0R  BizO    = Refl
or0R (BizP _) = Refl
or0R (BizM _) = Refl

lorSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizOr a b) n = bizTestBit a n || bizTestBit b n
lorSpecNonneg  BizO     _       n _    = rewrite testbit0L n in
                                         Refl
lorSpecNonneg  a        BizO    n _    =
  rewrite or0R a in
  rewrite testbit0L n in
  sym $ orFalse (bizTestBit a n)
lorSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitZpos (bipOr a b) n zlen in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  posLorSpec a b (toBinBiz n)
lorSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binDiff (bipPredBin b) (BinP a))) n zlen in
  rewrite posPredSucc (binDiff (bipPredBin b) (BinP a)) in
  rewrite ldiffSpec (bipPredBin b) (BinP a) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  rewrite notAnd (binTestBit (bipPredBin b) (toBinBiz n)) (not (bipTestBit a (toBinBiz n))) in
  rewrite notNot (bipTestBit a (toBinBiz n)) in
  orComm (not (binTestBit (bipPredBin b) (toBinBiz n))) (bipTestBit a (toBinBiz n))
lorSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitZneg (binSuccBip (binDiff (bipPredBin a) (BinP b))) n zlen in
  rewrite posPredSucc (binDiff (bipPredBin a) (BinP b)) in
  rewrite ldiffSpec (bipPredBin a) (BinP b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  rewrite notAnd (binTestBit (bipPredBin a) (toBinBiz n)) (not (bipTestBit b (toBinBiz n))) in
  rewrite notNot (bipTestBit b (toBinBiz n)) in
  Refl
lorSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binAnd (bipPredBin a) (bipPredBin b))) n zlen in
  rewrite posPredSucc (binAnd (bipPredBin a) (bipPredBin b)) in
  rewrite landSpec (bipPredBin a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  notAnd (binTestBit (bipPredBin a) (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))

lorSpec : (a, b, n : Biz) -> bizTestBit (bizOr a b) n = bizTestBit a n || bizTestBit b n
lorSpec a b    BizO    = lorSpecNonneg a b 0 uninhabited
lorSpec a b n@(BizP _) = lorSpecNonneg a b n uninhabited
lorSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  rewrite testbitNegR b n Refl in
  testbitNegR (bizOr a b) n Refl

-- land_spec

and0R : (n : Biz) -> bizAnd n BizO = BizO
and0R  BizO    = Refl
and0R (BizP _) = Refl
and0R (BizM _) = Refl

landSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizAnd a b) n = bizTestBit a n && bizTestBit b n
landSpecNonneg  BizO     _       n _    = rewrite testbit0L n in
                                          Refl
landSpecNonneg  a        BizO    n _    =
  rewrite and0R a in
  rewrite testbit0L n in
  sym $ andFalse (bizTestBit a n)
landSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitOfN1 (bipAnd a b) n zlen in
  rewrite landSpec (BinP a) (BinP b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  Refl
landSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitOfN1 (binDiff (BinP a) (bipPredBin b)) n zlen in
  rewrite ldiffSpec (BinP a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  Refl
landSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitOfN1 (binDiff (BinP b) (bipPredBin a)) n zlen in
  rewrite ldiffSpec (BinP b) (bipPredBin a) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  andComm (bipTestBit b (toBinBiz n)) (not (binTestBit (bipPredBin a) (toBinBiz n)))
landSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binOr (bipPredBin a) (bipPredBin b))) n zlen in
  rewrite posPredSucc (binOr (bipPredBin a) (bipPredBin b)) in
  rewrite lorSpec (bipPredBin a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  notOr (binTestBit (bipPredBin a) (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))

landSpec : (a, b, n : Biz) -> bizTestBit (bizAnd a b) n = bizTestBit a n && bizTestBit b n
landSpec a b    BizO    = landSpecNonneg a b 0 uninhabited
landSpec a b n@(BizP _) = landSpecNonneg a b n uninhabited
landSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  testbitNegR (bizAnd a b) n Refl

-- ldiff_spec

diff0R : (n : Biz) -> bizDiff n BizO = n
diff0R  BizO    = Refl
diff0R (BizP _) = Refl
diff0R (BizM _) = Refl

ldiffSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizDiff a b) n = bizTestBit a n && not (bizTestBit b n)
ldiffSpecNonneg  BizO     _       n _    = rewrite testbit0L n in
                                           Refl

ldiffSpecNonneg  a        BizO    n _    =
  rewrite diff0R a in
  rewrite testbit0L n in
  sym $ andTrue (bizTestBit a n)
ldiffSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitOfN1 (bipDiff a b) n zlen in
  rewrite ldiffSpec (BinP a) (BinP b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  Refl
ldiffSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitOfN1 (binAnd (BinP a) (bipPredBin b)) n zlen in
  rewrite landSpec (BinP a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  rewrite notNot (binTestBit (bipPredBin b) (toBinBiz n)) in
  Refl
ldiffSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitZneg (binSuccBip (binOr (bipPredBin a) (BinP b))) n zlen in
  rewrite posPredSucc (binOr (bipPredBin a) (BinP b)) in
  rewrite lorSpec (bipPredBin a) (BinP b)  (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  notOr (binTestBit (bipPredBin a) (toBinBiz n)) (bipTestBit b (toBinBiz n))
ldiffSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitOfN1 (binDiff (bipPredBin b) (bipPredBin a)) n zlen in
  rewrite ldiffSpec (bipPredBin b) (bipPredBin a) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  rewrite notNot (binTestBit (bipPredBin b) (toBinBiz n)) in
  andComm (binTestBit (bipPredBin b) (toBinBiz n)) (not (binTestBit (bipPredBin a) (toBinBiz n)))

ldiffSpec : (a, b, n : Biz) -> bizTestBit (bizDiff a b) n = bizTestBit a n && not (bizTestBit b n)
ldiffSpec a b    BizO    = ldiffSpecNonneg a b 0 uninhabited
ldiffSpec a b n@(BizP _) = ldiffSpecNonneg a b n uninhabited
ldiffSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  testbitNegR (bizDiff a b) n Refl

--lxor_spec

xor0R : (n : Biz) -> bizXor n BizO = n
xor0R  BizO    = Refl
xor0R (BizP _) = Refl
xor0R (BizM _) = Refl

lxorSpecNonneg : (a, b, n : Biz) -> 0 `Le` n -> bizTestBit (bizXor a b) n = (bizTestBit a n) `xor` (bizTestBit b n)
lxorSpecNonneg  BizO     b       n _    = rewrite testbit0L n in
                                          sym $ xorFalse (bizTestBit b n)
lxorSpecNonneg  a        BizO    n _    =
  rewrite testbit0L n in
  rewrite xor0R a in
  rewrite xorComm (bizTestBit a n) False in
  sym $ xorFalse (bizTestBit a n)
lxorSpecNonneg (BizP a) (BizP b) n zlen =
  rewrite testbitOfN1 (bipXor a b) n zlen in
  rewrite lxorSpec (BinP a) (BinP b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZpos b n zlen in
  Refl
lxorSpecNonneg (BizP a) (BizM b) n zlen =
  rewrite testbitZneg (binSuccBip (binXor (BinP a) (bipPredBin b))) n zlen in
  rewrite posPredSucc (binXor (BinP a) (bipPredBin b)) in
  rewrite lxorSpec (BinP a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZpos a n zlen in
  rewrite testbitZneg b n zlen in
  notXorR (bipTestBit a (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))
lxorSpecNonneg (BizM a) (BizP b) n zlen =
  rewrite testbitZneg (binSuccBip (binXor (bipPredBin a) (BinP b))) n zlen in
  rewrite posPredSucc (binXor (bipPredBin a) (BinP b)) in
  rewrite lxorSpec (bipPredBin a) (BinP b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZpos b n zlen in
  notXorL (binTestBit (bipPredBin a) (toBinBiz n)) (bipTestBit b (toBinBiz n))
lxorSpecNonneg (BizM a) (BizM b) n zlen =
  rewrite testbitOfN1 (binXor (bipPredBin a) (bipPredBin b)) n zlen in
  rewrite lxorSpec (bipPredBin a) (bipPredBin b) (toBinBiz n) in
  rewrite testbitZneg a n zlen in
  rewrite testbitZneg b n zlen in
  notXor2 (binTestBit (bipPredBin a) (toBinBiz n)) (binTestBit (bipPredBin b) (toBinBiz n))

lxorSpec : (a, b, n : Biz) -> bizTestBit (bizXor a b) n = (bizTestBit a n) `xor` (bizTestBit b n)
lxorSpec a b    BizO    = lxorSpecNonneg a b 0 uninhabited
lxorSpec a b n@(BizP _) = lxorSpecNonneg a b n uninhabited
lxorSpec a b n@(BizM _) =
  rewrite testbitNegR a n Refl in
  rewrite testbitNegR b n Refl in
  testbitNegR (bizXor a b) n Refl

-- TODO boolean comparisons ?

bizShiftinSpec : (b : Bool) -> (x : Biz) -> bizShiftin b x = 2 * x + (if b then 1 else 0)
bizShiftinSpec False x = rewrite add0R (2*x) in
                         doubleSpec x
bizShiftinSpec True x = succDoubleSpec x

bizShiftinInj : (b1, b2 : Bool) -> (x1, x2 : Biz) -> bizShiftin b1 x1 = bizShiftin b2 x2 -> (b1 = b2, x1 = x2)
bizShiftinInj True  True  x1 x2 prf = (Refl,    prf
                                           |> replace {P = \z => z = bizDPO x2} (succDoubleSpec x1)
                                           |> replace {P = \z => 2*x1 + 1 = z} (succDoubleSpec x2)
                                           |> addRegR 1 (2*x1) (2*x2)
                                           |> mulRegL x1 x2 2 uninhabited)
bizShiftinInj True  False x1 x2 prf = absurd $ notDDPO x2 x1 (sym prf)
bizShiftinInj False True  x1 x2 prf = absurd $ notDDPO x1 x2 prf
bizShiftinInj False False x1 x2 prf = (Refl,    prf
                                           |> replace {P = \z => z = bizD x2} (doubleSpec x1)
                                           |> replace {P = \z => 2*x1 = z} (doubleSpec x2)
                                           |> mulRegL x1 x2 2 uninhabited)

bizShiftinInd : (P : Biz -> Type) -> (f0 : P 0)
           -> ((b : Bool) -> (x : Biz) -> 0 `Le` x -> P x -> P (bizShiftin b x))
           -> (x : Biz) -> 0 `Le` x -> P x
bizShiftinInd _ f0 _  BizO    _    = f0
bizShiftinInd P f0 f (BizP a) _    = aux a
  where
  -- a workaround to convince totality checker that `BizP (O/I a) -> BizP a` is decreasing
  aux : (p : Bip) -> P (BizP p)
  aux  U    = f True 0 uninhabited f0
  aux (O a) = f False (BizP a) uninhabited $ aux a
  aux (I a) = f True (BizP a) uninhabited $ aux a
bizShiftinInd _ _  _ (BizM _) zlex = absurd $ zlex Refl

bizShiftinPosInd : (P : Biz -> Type) -> (f1 : P 1)
              -> ((b : Bool) -> (x : Biz) -> 0 `Lt` x -> P x -> P (bizShiftin b x))
              -> (x : Biz) -> 0 `Lt` x -> P x
bizShiftinPosInd _ _  _  BizO    zltx = absurd zltx
bizShiftinPosInd P f1 f (BizP a) _    = aux a
  where
  -- a workaround to convince totality checker that `BizP (O/I a) -> BizP a` is decreasing
  aux : (p : Bip) -> P (BizP p)
  aux  U    = f1
  aux (O a) = f False (BizP a) Refl $ aux a
  aux (I a) = f True (BizP a) Refl $ aux a
bizShiftinPosInd _ _  _ (BizM _) zltx = absurd zltx

zDecomp : (x : Biz) -> x = bizShiftin (bizOdd x) (bizDivTwo x)
zDecomp  BizO        = Refl
zDecomp (BizP  U)    = Refl
zDecomp (BizP (O _)) = Refl
zDecomp (BizP (I _)) = Refl
zDecomp (BizM  U)    = Refl
zDecomp (BizM (O _)) = Refl
zDecomp (BizM (I a)) = cong $ sym $ predDoubleSucc a

zTestbitShiftin : (b : Bool) -> (x, n : Biz) -> 0 `Le` n
               -> bizTestBit (bizShiftin b x) n = if n == 0 then b else bizTestBit x (bizPred n)
zTestbitShiftin b x n zlen with (n==0) proof nz
  zTestbitShiftin False x n zlen | False =
      testbitEvenSucc x (bizPred n) (ltPredRTo 0 n $ leNeqLt n 0 zlen $ neqbNeqTo n 0 (sym nz))
   |> replace {P = \z => bizTestBit (bizD x) z = bizTestBit x (bizPred n)} (sym $ addAssoc n (-1) 1)
   |> replace {P = \z => bizTestBit (bizD x) z = bizTestBit x (bizPred n)} (add0R n)
  zTestbitShiftin True  x n zlen | False =
      testbitOddSucc x (bizPred n) (ltPredRTo 0 n $ leNeqLt n 0 zlen $ neqbNeqTo n 0 (sym nz))
   |> replace {P = \z => bizTestBit (bizDPO x) z = bizTestBit x (bizPred n)} (sym $ addAssoc n (-1) 1)
   |> replace {P = \z => bizTestBit (bizDPO x) z = bizTestBit x (bizPred n)} (add0R n)
  zTestbitShiftin False x n zlen | True  = rewrite eqbEqTo n 0 (sym nz) in
                                           testbitEven0 x
  zTestbitShiftin True  x n zlen | True  = rewrite eqbEqTo n 0 (sym nz) in
                                           testbitOdd0 x

zTestbitShiftinBase : (b : Bool) -> (x : Biz) -> bizTestBit (bizShiftin b x) 0 = b
zTestbitShiftinBase b x =
  rewrite zTestbitShiftin b x 0 uninhabited in
  Refl

zTestbitShiftinSucc : (b : Bool) -> (x, n : Biz) -> 0 `Le` n -> bizTestBit (bizShiftin b x) (bizSucc n) = bizTestBit x n
zTestbitShiftinSucc b x n zlen =
  rewrite zTestbitShiftin b x (bizSucc n) $ ltLeIncl 0 (n+1) $ ltSuccRFro 0 n zlen in
  rewrite neqbNeqFro (n+1) 0 $ ltNotEq (n+1) 0 $ ltSuccRFro 0 n zlen in
  rewrite sym $ addAssoc n 1 (-1) in
  rewrite add0R n in
  Refl

zTestbitEq : (x, n : Biz) -> 0 `Le` n -> bizTestBit x n = if n == 0 then bizOdd x else bizTestBit (bizDivTwo x) (bizPred n)
zTestbitEq x n zlen =
  rewrite sym $ zTestbitShiftin (bizOdd x) (bizDivTwo x) n zlen in
  rewrite sym $ zDecomp x in
  Refl

-- zTestbitBase is trivial

zTestbitSucc : (a, n : Biz) -> 0 `Le` n -> bizTestBit a (bizSucc n) = bizTestBit (bizDivTwo a) n
zTestbitSucc a n zlen =
  case evenOrOdd a of
    Left  (b**eprf) =>
      rewrite sym $ testbitEvenSucc (bizDivTwo a) n zlen in
      rewrite eprf in
      rewrite sym $ doubleSpec b in
      rewrite div2D b in
      Refl
    Right (b**oprf) =>
      rewrite sym $ testbitOddSucc (bizDivTwo a) n zlen in
      rewrite oprf in
      rewrite sym $ succDoubleSpec b in
      rewrite div2DPO b in
      Refl

zOneComplement : (i, x : Biz) -> 0 `Le` i -> bizTestBit (-x-1) i = not (bizTestBit x i)
zOneComplement i x zlei =
  natlikeInd
    (\j => (y : Biz) -> bizTestBit (-y-1) j = not (bizTestBit y j))
    base
    (\j, zlej, pyj, y =>
        let zltj1 = ltSuccRFro 0 j zlej
            zlej1 = ltLeIncl 0 (j+1) zltj1 in
        rewrite zDecomp y in
        rewrite aux (bizOdd y) (bizDivTwo y) in
        rewrite zTestbitShiftin (not (bizOdd y)) (-bizDivTwo y - 1) (j+1) zlej1 in
        rewrite zTestbitShiftin (bizOdd y) (bizDivTwo y) (j+1) zlej1 in
        rewrite neqbNeqFro (j+1) 0 $ ltNotEq (j+1) 0 zltj1 in
        rewrite sym $ addAssoc j 1 (-1) in
        rewrite add0R j in
        pyj (bizDivTwo y))
    i zlei x
  where
  base : (x : Biz) -> bizOdd (-x-1) = not (bizOdd x)
  base  BizO        = Refl
  base (BizP  U)    = Refl
  base (BizP (O _)) = Refl
  base (BizP (I _)) = Refl
  base (BizM  U)    = Refl
  base (BizM (O a)) =
    case succPredOr a of
      Left au  => rewrite au in
                  Refl
      Right as => rewrite sym as in
                  rewrite predDoubleSucc (bipPred a) in
                  Refl
  base (BizM (I _)) = Refl

  aux : (b : Bool) -> (x : Biz) -> -(bizShiftin b x)-1 = bizShiftin (not b) (-x-1)
  aux False  BizO        = Refl
  aux False (BizP  a)    = rewrite add1R a in
                           cong $ sym $ predDoubleSucc a
  aux False (BizM  U)    = Refl
  aux False (BizM (O _)) = Refl
  aux False (BizM (I _)) = Refl
  aux True   BizO        = Refl
  aux True  (BizP  a)    = cong {f = BizM . O} $ sym $ add1R a
  aux True  (BizM  U)    = Refl
  aux True  (BizM (O _)) = Refl
  aux True  (BizM (I _)) = Refl

zAddIsOr : (x, y, i : Biz) -> 0 `Le` i -> ((j : Biz) -> 0 `Le` j -> j `Le` i -> bizTestBit x j && bizTestBit y j = False)
       -> bizTestBit (x + y) i = bizTestBit x i || bizTestBit y i
zAddIsOr x y i zlei f =
  natlikeInd
    (\k => (a, b : Biz) -> ((j : Biz) -> 0 `Le` j -> j `Le` k -> bizTestBit a j && bizTestBit b j = False) ->
           bizTestBit (a + b) k = bizTestBit a k || bizTestBit b k)
    (\a,b,g => base a b $ g 0 uninhabited uninhabited)
    (\k, zlek, ihk, a, b, g =>
      rewrite zDecomp a in
      rewrite zDecomp b in
      trans {b = bizTestBit (bizShiftin (bizOdd a || bizOdd b) (bizDivTwo a + bizDivTwo b)) (k+1)}
        (rewrite bizShiftinSpec (bizOdd a) (bizDivTwo a) in
         rewrite bizShiftinSpec (bizOdd b) (bizDivTwo b) in
         rewrite bizShiftinSpec (bizOdd a || bizOdd b) (bizDivTwo a + bizDivTwo b) in
         rewrite addAssoc (2*(bizDivTwo a)+(ifThenElse (bizOdd a) (Delay 1) (Delay 0))) (2*(bizDivTwo b)) (ifThenElse (bizOdd b) (Delay 1) (Delay 0)) in
         rewrite sym $ addAssoc (2*(bizDivTwo a)) (ifThenElse (bizOdd a) (Delay 1) (Delay 0)) (2*(bizDivTwo b)) in
         rewrite addComm (ifThenElse (bizOdd a) (Delay 1) (Delay 0)) (2*(bizDivTwo b)) in
         rewrite addAssoc (2*(bizDivTwo a)) (2*(bizDivTwo b)) (ifThenElse (bizOdd a) (Delay 1) (Delay 0)) in
         rewrite sym $ mulAddDistrL 2 (bizDivTwo a) (bizDivTwo b) in
         rewrite sym $ addAssoc (2*(bizDivTwo a + bizDivTwo b)) (ifThenElse (bizOdd a) (Delay 1) (Delay 0)) (ifThenElse (bizOdd b) (Delay 1) (Delay 0)) in
         rewrite aux (bizOdd a) (bizOdd b) (g 0 uninhabited $ leSuccR 0 k zlek) in
         Refl)
        (rewrite zTestbitShiftinSucc (bizOdd a || bizOdd b) (bizDivTwo a + bizDivTwo b) k zlek in
         rewrite zTestbitShiftinSucc (bizOdd a) (bizDivTwo a) k zlek in
         rewrite zTestbitShiftinSucc (bizOdd b) (bizDivTwo b) k zlek in
         ihk (bizDivTwo a) (bizDivTwo b) $
         \t, zlet, tlek =>
          rewrite sym $ zTestbitSucc a t zlet in
          rewrite sym $ zTestbitSucc b t zlet in
          g (t+1) (leSuccR 0 t zlet) (rewrite addCompareMonoR t k 1 in tlek)
        )
    )
    i zlei
    x y f
    where
    base : (x, y : Biz) -> bizOdd x && bizOdd y = False -> bizOdd (x + y) = bizOdd x || bizOdd y
    base x y prf with (bizOdd x) proof ox
      base x y prf | True with (bizOdd y) proof oy
        base x y prf | True | True = absurd prf
        base x y prf | True | False =
          let (a**prfa) = oddSpecTo x (sym ox)
              (b**prfb) = evenSpecTo y $ trans (sym $ notNot (bizEven y))
                                               (cong {f=not} $ trans (sym $ oddNotEven y) (sym oy))
          in
          oddSpecFro (x+y) $
          (a+b ** rewrite prfa in
                  rewrite prfb in
                  rewrite sym $ addAssoc (2*a) 1 (2*b) in
                  rewrite addComm 1 (2*b) in
                  rewrite addAssoc (2*a) (2*b) 1 in
                  rewrite mulAddDistrL 2 a b in
                  Refl)
      base x y prf | False with (bizOdd y) proof oy
        base x y prf | False | True =
          let (a**prfa) = evenSpecTo x $ trans (sym $ notNot (bizEven x))
                                               (cong {f=not} $ trans (sym $ oddNotEven x) (sym ox))
              (b**prfb) = oddSpecTo y (sym oy)
          in
          oddSpecFro (x+y) $
          (a+b ** rewrite prfa in
                  rewrite prfb in
                  rewrite addAssoc (2*a) (2*b) 1 in
                  rewrite mulAddDistrL 2 a b in
                  Refl)
        base x y prf | False | False =
          let (a**prfa) = evenSpecTo x $ trans (sym $ notNot (bizEven x))
                                               (cong {f=not} $ trans (sym $ oddNotEven x) (sym ox))
              (b**prfb) = evenSpecTo y $ trans (sym $ notNot (bizEven y))
                                               (cong {f=not} $ trans (sym $ oddNotEven y) (sym oy))
          in
          rewrite oddNotEven (x+y) in
          cong {f=not} {a=bizEven (x+y)} {b=True} $
          evenSpecFro (x+y) $
          (a+b ** rewrite prfa in
                  rewrite prfb in
                  sym $ mulAddDistrL 2 a b)
    aux : (b1, b2: Bool) -> b1 && b2 = False -> (if b1 then BizP U else BizO) + (if b2 then BizP U else BizO) = if b1 || b2 then BizP U else BizO
    aux True  True  prf = absurd prf
    aux True  False _   = Refl
    aux False True  _   = Refl
    aux False False _   = Refl

zShiftlMulBizPow2 : (x, n : Biz) -> 0 `Le` n -> bizShiftL x n = x * bizPow2 n
zShiftlMulBizPow2 x  BizO    _    = sym $ mul1R x
zShiftlMulBizPow2 x (BizP p) zlen =
  peanoRect
    (\z => bipIter (2*) x z = x*(BizP (bipIter O U z)))
    (mulComm 2 x)
    (\z, prf =>
     rewrite iterSucc (2*) x z in
     rewrite iterSucc O U z in
     rewrite mulAssoc x 2 (BizP (bipIter O U z)) in
     rewrite mulComm x 2 in
     rewrite sym $ mulAssoc 2 x (BizP (bipIter O U z)) in
     cong {f = (2*)} prf
    )
    p
zShiftlMulBizPow2 _ (BizM _) zlen = absurd $ zlen Refl

zZeroExtSpec : (n, x, i : Biz) -> 0 `Le` i -> bizTestBit (bizZeroExt n x) i = if i < n then bizTestBit x i else False
zZeroExtSpec n x i zlei =
  natlikeIndM
    (\m => (y, j : Biz) -> 0 `Le` j -> bizTestBit (bizZeroExt m y) j = if j < m then bizTestBit y j else False)
    (\y, j, zlej =>
     rewrite nltbLeFro 0 j zlej in
     testbit0L j)
    (\m, mle0, y, j, zlej =>
      rewrite iterBaseZ (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) m (\_ => BizO) mle0 in
      rewrite nltbLeFro m j (leTrans m 0 j mle0 zlej) in
      testbit0L j)
    (\m, zlem, prf, y, j, zlej =>
      rewrite iterSuccZ (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) m (\_ => BizO) zlem in
      rewrite zTestbitShiftin (bizOdd y) (bizIter (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) m (\_ => BizO) (bizDivTwo y)) j zlej in
      rewrite zTestbitEq y j zlej in
      case decEq j 0 of
        Yes j0 =>
          rewrite eqbEqFro j 0 j0 in
          rewrite j0 in
          rewrite ltbLtFro 0 (m+1) (leLtTrans 0 m (m+1) zlem (ltSucc m)) in
          Refl
        No jnz =>
          rewrite neqbNeqFro j 0 jnz in
          rewrite prf (bizDivTwo y) (j-1) (ltPredRTo 0 j $ leNeqLt j 0 zlej jnz) in
-- TODO bug : as in zTestbitModBizPow2, uncommenting both branches freezes the checker
          really_believe_me j
       --  case ltLeTotal j (m+1) of
       --    Left jltm1 =>
       --      rewrite ltbLtFro j (m+1) jltm1 in
       --      rewrite ltbLtFro (j-1) m $
       --              rewrite addComm j (-1) in
       --              rewrite sym $ addCompareTransferL j 1 m in
       --              rewrite addComm 1 m in
       --              jltm1
       --             in
       --      Refl
       --    Right m1lej =>
       --      rewrite nltbLeFro (m+1) j m1lej in
       --      rewrite nltbLeFro m (j-1) $
       --              rewrite addComm j (-1) in
       --              rewrite addCompareTransferL m (-1) j in
       --              rewrite addComm 1 m in
       --              m1lej
       --             in
       --      Refl
            )
    n x i zlei

zSignExtSpec : (n, x, i : Biz) -> 0 `Le` i -> 0 `Lt` n -> bizTestBit (bizSignExt n x) i = bizTestBit x (if i < n then i else n - 1)
zSignExtSpec n x i zlei zltn =
  let aux = natlikeInd
             (\m => (y, j : Biz) -> 0 `Le` j -> bizTestBit (bizSignExt (m+1) y) j = bizTestBit y (if j < m+1 then j else m))
             (\y,j,zlej =>
                case ltLeTotal j 1 of
                  Left jlt1 =>
                    rewrite ltbLtFro j 1 jlt1 in
                    rewrite leAntisym j 0 (ltPredRTo j 1 jlt1) zlej in
                    case trueOrFalse (bizOdd y) of
                      Left ey => rewrite ey in
                                 Refl
                      Right oy => rewrite oy in
                                  Refl
                  Right olej =>
                    rewrite nltbLeFro 1 j olej in
                    case trueOrFalse (bizOdd y) of
                      Left ey => rewrite ey in
                                 testbit0L j
                      Right oy => rewrite oy in
                                  testbitM1L j zlej
             )
             (\m,zlem,prf,y,j,zlej =>
                rewrite addComm (m+1+1) (-1) in
                rewrite addAssoc (-1) (m+1) 1 in
                rewrite addComm (-1) (m+1) in
                rewrite iterSuccZ (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) (m+1-1) (\x => ifThenElse (bizOdd x) (Delay (-1)) (Delay 0)) $
                        rewrite sym $ addAssoc m 1 (-1) in
                        rewrite add0R m in
                        zlem
                       in
                rewrite zTestbitShiftin (bizOdd y) (bizIter (\rec, x => bizShiftin (bizOdd x) (rec (bizDivTwo x))) (m+1-1) (\x => ifThenElse (bizOdd x) (Delay (-1)) (Delay 0)) (bizDivTwo y)) j zlej in
                case decEq j 0 of
                  Yes j0 =>
                    rewrite eqbEqFro j 0 j0 in
                    rewrite j0 in
                    rewrite ltbLtFro 0 (m+1+1) $
                            leLtTrans 0 m (m+1+1) zlem $
                            rewrite sym $ addAssoc m 1 1 in
                            rewrite addComm m 2 in
                            rewrite addCompareMonoR 0 2 m in
                            Refl
                           in
                    Refl
                  No jnz =>
                    rewrite neqbNeqFro j 0 jnz in
                    rewrite prf (bizDivTwo y) (j-1) (ltPredRTo 0 j $ leNeqLt j 0 zlej jnz) in
-- TODO bug : nested cases again
                    really_believe_me j
                   -- case ltLeTotal (j-1) (m+1) of
                   --   Left j1ltm1 =>
                   --      rewrite ltbLtFro (j-1) (m+1) j1ltm1 in
                   --      rewrite ltbLtFro j (m+1+1) $
                   --              rewrite addComm (m+1) 1 in
                   --              rewrite addCompareTransferL j 1 (m+1) in
                   --              rewrite addComm (-1) j in
                   --              j1ltm1
                   --             in
                   --      rewrite sym $ zTestbitSucc y (j-1) $
                   --              ltPredRTo 0 j $
                   --              leNeqLt j 0 zlej jnz
                   --             in
                   --      rewrite sym $ addAssoc j (-1) 1 in
                   --      rewrite add0R j in
                   --      Refl
                   --   Right m1lej1 =>
                   --     rewrite nltbLeFro (m+1) (j-1) m1lej1 in
                   --     rewrite nltbLeFro (m+1+1) j $
                   --             rewrite addComm (m+1) 1 in
                   --             rewrite sym $ addCompareTransferL (m+1) (-1) j in
                   --             rewrite addComm (-1) j in
                   --             m1lej1
                   --            in
                   --     sym $ zTestbitSucc y m zlem
             )
             (n-1) (ltPredRTo 0 n zltn) x i zlei
     in
  rewrite sym $ add0R n in
  rewrite addAssoc n (-1) 1 in
  rewrite aux in
  rewrite sym $ addAssoc n (-1) 1 in
  rewrite add0R n in
  Refl

bizDigitsNonneg : (x : Biz) -> 0 `Le` bizDigits x
bizDigitsNonneg  BizO    = uninhabited
bizDigitsNonneg (BizP _) = uninhabited
bizDigitsNonneg (BizM _) = uninhabited

bizDigitsPos : (x : Biz) -> 0 `Lt` x -> 0 `Lt` bizDigits x
bizDigitsPos  BizO    zltx = absurd zltx
bizDigitsPos (BizP _) _    = Refl
bizDigitsPos (BizM _) zltx = absurd zltx

bizDigitsShiftin : (b : Bool) -> (x : Biz) -> 0 `Lt` x -> bizDigits (bizShiftin b x) = bizSucc (bizDigits x)
bizDigitsShiftin _      BizO    zltx = absurd zltx
bizDigitsShiftin True  (BizP p) _    = cong $ sym $ add1R (bipDigits p)
bizDigitsShiftin False (BizP p) _    = cong $ sym $ add1R (bipDigits p)
bizDigitsShiftin _     (BizM _) zltx = absurd zltx

bizTestbitDigits1 : (x : Biz) -> 0 `Lt` x -> bizTestBit x (bizPred (bizDigits x)) = True
bizTestbitDigits1 x zltx =
  bizShiftinPosInd
    (\y => bizTestBit y (bizPred (bizDigits y)) = True)
    Refl
    (\b, y, zlty, prf =>
      rewrite bizDigitsShiftin b y zlty in
      rewrite sym $ addAssoc (bizDigits y) 1 (-1) in
      rewrite addAssoc (bizDigits y) (-1) 1 in
      rewrite zTestbitShiftinSucc b y (bizDigits y - 1) (ltPredRTo 0 (bizDigits y) $ bizDigitsPos y zlty) in
      prf)
    x zltx

bizTestbitDigits2 : (x, i : Biz) -> 0 `Le` x -> bizDigits x `Le` i -> bizTestBit x i = False
bizTestbitDigits2 x i zlex dxlei =
  case leLtOrEq 0 x zlex of
    Left zltx =>
      bizShiftinPosInd
        (\y => (j : Biz) -> bizDigits y `Le` j -> bizTestBit y j = False)
        (\j, ulej =>
          rewrite testbit1L j in
          neqbNeqFro j 0 $
          ltNotEq j 0 $
          leSuccLTo 0 j ulej)
        (\b, y, zlty, prf, j =>
          rewrite bizDigitsShiftin b y zlty in
          \dy1lei =>
          let zltj = ltLeTrans 0 (bizDigits y + 1) j
                       (ltSuccRFro 0 (bizDigits y) (bizDigitsNonneg y))
                       dy1lei
             in
          rewrite zTestbitShiftin b y j (ltLeIncl 0 j zltj) in
          rewrite neqbNeqFro j 0 $ ltNotEq j 0 zltj in
          prf (j-1) $
          rewrite addComm j (-1) in
          rewrite addCompareTransferL (bizDigits y) (-1) j in
          rewrite addComm 1 (bizDigits y) in
          dy1lei)
        x zltx i dxlei
    Right zeqx =>
      rewrite sym zeqx in
      testbit0L i