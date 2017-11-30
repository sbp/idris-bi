module Data.BizMod2.Bitwise.ZSExt

import Data.Util

import Data.Bip.AddMul
import Data.Bip.Iter

import Data.Biz
import Data.Biz.Ord
import Data.Biz.Bitwise

import Data.BizMod2

%access export
%default total

-- Properties of integer zero extension and sign extension.

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