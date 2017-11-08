module Data.Biz.Bitwise

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
%access public export

Even : Biz -> Type
Even a = (b ** a = 2*b)

Odd : Biz -> Type
Odd a = (b ** a = 2*b+1)

-- Specification of parity functions

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

minusBiz : (p, q : Bip) -> bimToBin $ bimMinus p q = toBinBiz $ bipMinusBiz p q
minusBiz p q = case ltTotal p q of
  Left $ Left pq  =>
    rewrite subMaskNeg p q pq in
    rewrite posSubLt p q pq in
    Refl
  Right eq        =>
    rewrite eq in
    rewrite subMaskDiag q in
    rewrite posSubDiag q in
    Refl
  Left $ Right qp =>
    let (_**prf) = subMaskPos p q qp in
    rewrite prf in
    rewrite posSubGt p q qp in
    cong {f = BinP . bipMinusHelp} $ sym prf

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
         sym $ testbitNegR a (m-(BizP b)) $
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

