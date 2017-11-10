module Data.BizMod2.AddSubMul

import Data.Biz
import Data.Biz.AddSubMul
import Data.Biz.Ord
import Data.Biz.DivMod

import Data.BizMod2
import Data.BizMod2.Core

%access export
%default total

-- Properties of addition

-- addUnsigned is trivial

addSigned : (x, y : BizMod2 n) -> x + y = repr (signed x + signed y) n
addSigned {n} x y =
  eqmSamerepr (unsigned x + unsigned y) (signed x + signed y) n $
  eqmodAdd (unsigned x) (signed x) (unsigned y) (signed y) (modulus n)
    (eqmUnsignedSigned x)
    (eqmUnsignedSigned y)

addComm : (x, y : BizMod2 n) -> x + y = y + x
addComm x y = rewrite addComm (unsigned x) (unsigned y) in
              Refl

add0R : (x : BizMod2 n) -> x + 0 = x
add0R {n} x = rewrite unsignedZero n in
              rewrite add0R (unsigned x) in
              reprUnsigned x

add0L : (x : BizMod2 n) -> 0 + x = x
add0L x = rewrite addComm 0 x in
          add0R x

eqmUnsignedAdd : (x, y : BizMod2 n) -> eqm (unsigned x + unsigned y) (unsigned (x + y)) n
eqmUnsignedAdd {n=Z}   x y =
  rewrite bizMod2P0 x in
  rewrite bizMod2P0 y in
  (0 ** Refl)
eqmUnsignedAdd {n=S n} x y =
  rewrite bizMod2Eq (unsigned x + unsigned y) (S n) in
  eqmodMod (unsigned x + unsigned y) (modulus (S n)) uninhabited

addAssoc : (x, y, z : BizMod2 n) -> x + (y + z) = x + y + z
addAssoc {n} x y z =
  eqmSamerepr ((unsigned x) + unsigned (y + z)) (unsigned (x + y) + unsigned z) n $
  eqmodTrans ((unsigned x) + unsigned (y + z)) (unsigned x + unsigned y + unsigned z) (unsigned (x + y) + unsigned z) (modulus n)
    (rewrite sym $ addAssoc (unsigned x) (unsigned y) (unsigned z) in
     eqmodAdd (unsigned x) (unsigned x) (unsigned (y + z)) (unsigned y + unsigned z) (modulus n)
       (eqmodRefl (unsigned x) (modulus n))
       (eqmodSym (unsigned y + unsigned z) (unsigned (y + z)) (modulus n) $
        eqmUnsignedAdd y z)
    )
    (eqmodAdd (unsigned x + unsigned y) (unsigned (x+y)) (unsigned z) (unsigned z) (modulus n)
       (eqmUnsignedAdd x y)
       (eqmodRefl (unsigned z) (modulus n))
    )

addPermut : (x, y, z : BizMod2 n) -> x + (y + z) = y + (x + z)
addPermut x y z =
  rewrite addComm y z in
  rewrite addAssoc x z y in
  addComm (x + z) y

addNegZero : (x : BizMod2 n) -> x+(-x) = 0
addNegZero {n} x =
  eqmSamerepr (unsigned x + (unsigned $ repr (-unsigned x) n)) 0 n $
  rewrite unsignedReprEq (-unsigned x) n in
  rewrite sym $ addOppDiagR (unsigned x) in
  eqmodAdd (unsigned x) (unsigned x) (-unsigned x `bizMod` modulus n) (-unsigned x) (modulus n)
    (eqmodRefl (unsigned x) (modulus n))
    (eqmodSym (-unsigned x) (-unsigned x `bizMod` modulus n) (modulus n) $
     eqmodMod (-unsigned x) (modulus n) uninhabited)

unsignedAddCarry : (x, y : BizMod2 n) -> unsigned (x + y) = unsigned x + unsigned y - unsigned (addCarry x y 0) * (modulus n)
unsignedAddCarry {n} x y =
  rewrite unsignedZero n in
  rewrite add0R (unsigned x + unsigned y) in
  rewrite unsignedReprEq (unsigned x + unsigned y) n in
  aux n x y
  where
  aux : (n : Nat) -> (x, y : BizMod2 n) -> (unsigned x + unsigned y) `bizMod` (modulus n) = unsigned x + unsigned y - (unsigned $ if unsigned x + unsigned y < modulus n then (repr 0 n) else (repr 1 n)) * (modulus n)
  aux  Z    x y =
    -- TODO after 2 `bizMod2P0`s this becomes `0 mod 1 = 0` but there's apparently a bug preventing those rewrites
    -- TODO try `decEq n 0` instread of splitting
    -- rewrite bizMod2P0 x in
    -- rewrite bizMod2P0 y in
    really_believe_me Z
  aux (S n) x y with ((unsigned x + unsigned y) < (modulus (S n))) proof xym
    | False = sym $ snd $ divModPos (unsigned x + unsigned y) (modulus (S n)) 1 (unsigned x + unsigned y - modulus (S n))
                (rewrite sym $ compareSubR (modulus (S n)) (unsigned x + unsigned y) in
                 nltbLeTo (modulus (S n)) (unsigned x + unsigned y) (sym xym))
                (rewrite addComm (unsigned x + unsigned y) (-modulus (S n)) in
                 rewrite sym $ addCompareTransferL (unsigned x + unsigned y) (modulus (S n)) (modulus (S n)) in
                 addLtMono (unsigned x) (modulus (S n)) (unsigned y)  (modulus (S n)) (snd $ unsignedRange x) (snd $ unsignedRange y))
                (rewrite addComm (unsigned x + unsigned y) (-modulus (S n)) in
                 rewrite addAssoc (modulus (S n)) (-modulus (S n)) (unsigned x + unsigned y) in
                 rewrite posSubDiag (bipPow2 n) in
                 Refl)
    | True = rewrite add0R (unsigned x + unsigned y) in
             snd $ divModSmall (unsigned x + unsigned y) (modulus (S n))
               (addLeMono 0 (unsigned x) 0 (unsigned y) (fst $ unsignedRange x) (fst $ unsignedRange y))
               (ltbLtTo (unsigned x + unsigned y) (modulus (S n)) (sym xym))

unsignedAddEither : (x, y : BizMod2 n) -> Either (unsigned (x + y) = unsigned x + unsigned y)
                                                 (unsigned (x + y) = unsigned x + unsigned y - modulus n)
unsignedAddEither {n} x y =
  rewrite unsignedAddCarry x y in
  rewrite unsignedZero n in
  rewrite add0R (unsigned x + unsigned y) in
  aux n x y
  where
  aux : (n : Nat) -> (x, y : BizMod2 n) -> let m = (unsigned $ if unsigned x + unsigned y < modulus n then repr 0 n else repr 1 n)*(modulus n) in
                                           Either (unsigned x + unsigned y - m = unsigned x + unsigned y)
                                                  (unsigned x + unsigned y - m = unsigned x + unsigned y - modulus n)
  aux  Z    x y =
    -- TODO same bug as above
    -- rewrite bizMod2P0 x in
    -- rewrite bizMod2P0 y in
      really_believe_me Z
  aux (S n) x y with ((unsigned x + unsigned y) < (modulus (S n)))
    | False = Right Refl
    | True  = rewrite add0R (unsigned x + unsigned y) in
              Left Refl

-- Properties of negation

negRepr : (z : Biz) -> (n : Nat) -> -repr z n = repr (-z) n
negRepr z n =
  sym $
  eqmSamerepr (-z) (-(unsigned $ repr z n)) n $
  eqmodNeg z (unsigned $ repr z n) (modulus n) $
  eqmUnsignedRepr z n

negZero : (n : Nat) -> -repr 0 n = repr 0 n
negZero n = rewrite unsignedZero n in
            Refl

negInvolutive : (x : BizMod2 n) -> -(-x) = x
negInvolutive {n} x =
  eqmReprEq (-(unsigned $ repr (-unsigned x) n)) x $
  eqmodTrans (-(unsigned $ repr (-unsigned x) n)) (-(-unsigned x)) (unsigned x) (modulus n)
    (eqmodNeg (unsigned $ repr (-unsigned x) n) (-unsigned x) (modulus n) $
     eqmUnsignedReprL (-unsigned x) (-unsigned x) n $
     eqmodRefl (-unsigned x) (modulus n))
    (eqmodRefl2 (-(-unsigned x)) (unsigned x) (modulus n) $
     oppInvolutive (unsigned x))

negAddDistr : (x, y : BizMod2 n) -> -(x + y) = (-x) + (-y)
negAddDistr x y =
  eqmSamerepr (-(unsigned $ repr (unsigned x + unsigned y) n)) ((unsigned $ repr (-unsigned x) n)+(unsigned $ repr (-unsigned y) n)) n $
  eqmodTrans (-(unsigned $ repr (unsigned x + unsigned y) n)) (-(unsigned x + unsigned y)) ((unsigned $ repr (-unsigned x) n)+(unsigned $ repr (-unsigned y) n)) (modulus n)
    (eqmodNeg (unsigned $ repr (unsigned x + unsigned y) n) (unsigned x + unsigned y) (modulus n) $
     eqmUnsignedRepr' (unsigned x + unsigned y) n)
    (rewrite oppAddDistr (unsigned x) (unsigned y) in
     eqmodAdd (-unsigned x) (unsigned $ repr (-unsigned x) n) (-unsigned y) (unsigned $ repr (-unsigned y) n) (modulus n)
       (eqmUnsignedRepr (-unsigned x) n)
       (eqmUnsignedRepr (-unsigned y) n))

-- Properties of subtraction

sub0L : (x : BizMod2 n) -> x - 0 = x
sub0L {n} x =
  rewrite unsignedZero n in
  rewrite add0R (unsigned x) in
  reprUnsigned x

sub0R : (x : BizMod2 n) -> 0 - x = -x
sub0R {n} x =
  rewrite unsignedZero n in
  Refl

subAddNeg : (x, y : BizMod2 n) -> x - y = x + (-y)
subAddNeg {n} x y =
  eqmSamerepr (unsigned x - unsigned y) ((unsigned x)+(unsigned $ repr (-unsigned y) n)) n $
  eqmodAdd (unsigned x) (unsigned x) (-unsigned y) (unsigned $ repr (-unsigned y) n) (modulus n)
    (eqmodRefl (unsigned x) (modulus n))
    (eqmUnsignedRepr (-unsigned y) n)

subIdem : (x : BizMod2 n) -> x - x = 0
subIdem x =
  rewrite addOppDiagR (unsigned x) in
  Refl

subAddL : (x, y, z : BizMod2 n) -> (x + y) - z = (x - z) + y
subAddL x y z =
  rewrite subAddNeg (x+y) z in
  rewrite subAddNeg x z in
  rewrite sym $ addAssoc x y (-z) in
  rewrite sym $ addAssoc x (-z) y in
  rewrite addComm y (-z) in
  Refl

subAddR : (x, y, z : BizMod2 n) -> x - (y + z) = (x - z) + (-y)
subAddR x y z =
  rewrite subAddNeg x (y+z) in
  rewrite subAddNeg x z in
  rewrite negAddDistr y z in
  rewrite addComm (-y) (-z) in
  addAssoc x (-z) (-y)

subShifted : (x, y, z : BizMod2 n) -> (x + z) - (y + z) = x - y
subShifted x y z =
  rewrite subAddNeg (x+z) (y+z) in
  rewrite negAddDistr y z in
  rewrite addComm (-y) (-z) in
  rewrite sym $ addAssoc x z ((-z)+(-y)) in
  rewrite addAssoc z (-z) (-y) in
  rewrite addNegZero z in
  rewrite add0L (-y) in
  rewrite subAddNeg x y in
  Refl

subSigned : (x, y : BizMod2 n) -> x - y = repr (signed x - signed y) n
subSigned {n} x y =
  eqmSamerepr (unsigned x - unsigned y) (signed x - signed y) n $
  eqmodSub (unsigned x) (signed x) (unsigned y) (signed y) (modulus n)
    (eqmUnsignedSigned x) (eqmUnsignedSigned y)

unsignedSubBorrow : (x, y : BizMod2 n) -> unsigned (x - y) = unsigned x - unsigned y + (unsigned $ subBorrow x y 0) * (modulus n)
unsignedSubBorrow {n} x y =
  rewrite unsignedZero n in
  rewrite add0R (unsigned x - unsigned y) in
  rewrite unsignedReprEq (unsigned x - unsigned y) n in
  aux n x y
  where
  aux : (n : Nat) -> (x, y : BizMod2 n)
     -> (unsigned x - unsigned y) `bizMod` (modulus n) = unsigned x - unsigned y + (unsigned $ if unsigned x - unsigned y < 0 then repr 1 n else repr 0 n) * (modulus n)
  aux  Z    x y =
    -- TODO same bug as in `unsignedAddCarry`
    -- rewrite bizMod2P0 x in
    -- rewrite bizMod2P0 y in
      really_believe_me Z
  aux (S n) x y with (unsigned x - unsigned y < 0) proof xy
    | False = rewrite add0R (unsigned x - unsigned y) in
              snd $ divModSmall (unsigned x - unsigned y) (modulus (S n))
                (nltbLeTo 0 (unsigned x - unsigned y) (sym xy))
                (addLtLeMono (unsigned x) (modulus (S n)) (-unsigned y) 0
                            (snd $ unsignedRange x)
                            (rewrite sym $ compareOpp 0 (unsigned y) in
                             fst $ unsignedRange y))
    | True = sym $ snd $ divModPos (unsigned x - unsigned y) (modulus (S n)) (-1) (unsigned x - unsigned y + modulus (S n))
                (rewrite addComm (unsigned x - unsigned y) (modulus (S n)) in
                 rewrite addCompareTransferL 0 (modulus (S n)) (unsigned x - unsigned y) in
                 ltLeIncl (-modulus (S n)) (unsigned x - unsigned y) $
                 addLeLtMono 0 (unsigned x) (-modulus (S n)) (-unsigned y)
                   (fst $ unsignedRange x)
                   (rewrite sym $ compareOpp (unsigned y) (modulus (S n)) in
                    snd $ unsignedRange y))
                (rewrite addCompareMonoR (unsigned x - unsigned y) 0 (modulus (S n)) in
                 ltbLtTo (unsigned x - unsigned y) 0 (sym xy))
                (rewrite addComm (unsigned x - unsigned y) (modulus (S n)) in
                 rewrite addAssoc (-modulus (S n)) (modulus (S n)) (unsigned x - unsigned y) in
                 rewrite addOppDiagL (modulus (S n)) in
                 Refl)

addTransferL : (x, y, z : BizMod2 n) -> x = y+z -> z = x-y
addTransferL x y z prf =
  rewrite prf in
  rewrite subAddL y z y in
  rewrite subIdem y in
  sym $ add0L z

-- Properties of multiplication

mulComm : (x, y : BizMod2 n) -> x * y = y * x
mulComm x y = rewrite mulComm (unsigned x) (unsigned y) in
              Refl

mul0R : (x : BizMod2 n) -> x * 0 = 0
mul0R {n} x = rewrite unsignedZero n in
              rewrite mul0R (unsigned x) in
              Refl

mul1R : (x : BizMod2 n) -> x * 1 = x
mul1R {n = Z}   x = sym $ bizMod2P0 x
mul1R {n = S _} x = rewrite mul1R (unsigned x) in
                    reprUnsigned x

mulM1R : (x : BizMod2 n) -> x * (-1) = -x
mulM1R {n} x =
  rewrite unsignedMone n in
  eqmSamerepr ((unsigned x)*((modulus n)-1)) (-unsigned x) n $
  rewrite mulAddDistrL (unsigned x) (modulus n) (-1) in
  rewrite sym $ oppEqMulM1 (unsigned x) in
  eqmodSub ((unsigned x)*(modulus n)) 0 (unsigned x) (unsigned x) (modulus n)
    (unsigned x ** sym $ add0R ((unsigned x)*(modulus n)))
    (eqmodRefl (unsigned x) (modulus n))

mulAssoc : (x, y, z : BizMod2 n) -> x * (y * z) = x * y * z
mulAssoc {n} x y z =
  let ux = unsigned x
      uy = unsigned y
      uz = unsigned z in
  eqmSamerepr (ux*(unsigned $ repr (uy*uz) n)) ((unsigned $ repr (ux*uy) n)*uz) n $
  eqmodTrans (ux*(unsigned $ repr (uy*uz) n)) (ux*(uy*uz)) ((unsigned $ repr (ux*uy) n)*uz) (modulus n)
    (eqmodMult ux ux (unsigned $ repr (uy*uz) n) (uy*uz) (modulus n)
       (eqmodRefl ux (modulus n))
       (eqmUnsignedRepr' (uy*uz) n))
    (rewrite mulAssoc ux uy uz in
     eqmodMult (ux*uy) (unsigned $ repr (ux*uy) n) uz uz (modulus n)
       (eqmUnsignedRepr (ux*uy) n)
       (eqmodRefl uz (modulus n)))

mulAddDistrL : (x, y, z : BizMod2 n) -> x * (y + z) = x * y + x * z
mulAddDistrL x y z =
  let ux = unsigned x
      uy = unsigned y
      uz = unsigned z in
  eqmSamerepr (ux*(unsigned $ repr (uy+uz) n)) ((unsigned $ repr (ux*uy) n)+(unsigned $ repr (ux*uz) n)) n $
  eqmodTrans (ux*(unsigned $ repr (uy+uz) n)) (ux*(uy+uz)) ((unsigned $ repr (ux*uy) n)+(unsigned $ repr (ux*uz) n)) (modulus n)
    (eqmodMult ux ux (unsigned $ repr (uy+uz) n) (uy+uz) (modulus n)
      (eqmodRefl ux (modulus n))
      (eqmUnsignedRepr' (uy+uz) n))
    (rewrite mulAddDistrL ux uy uz in
     eqmodAdd (ux*uy) (unsigned $ repr (ux*uy) n) (ux*uz) (unsigned $ repr (ux*uz) n) (modulus n)
      (eqmUnsignedRepr (ux*uy) n)
      (eqmUnsignedRepr (ux*uz) n))

mulAddDistrR : (x, y, z : BizMod2 n) -> (x + y) * z = x * z + y * z
mulAddDistrR x y z =
  rewrite mulComm (x+y) z in
  rewrite mulComm x z in
  rewrite mulComm y z in
  mulAddDistrL z x y

mulNegL : (x, y : BizMod2 n) -> (-x) * y = -(x * y)
mulNegL {n} x y =
  let ux = unsigned x
      uy = unsigned y in
  eqmSamerepr ((unsigned $ repr (-ux) n)*uy) (-(unsigned $ repr (ux*uy) n)) n $
  eqmodTrans ((unsigned $ repr (-ux) n)*uy) (-(ux*uy)) (-(unsigned $ repr (ux*uy) n)) (modulus n)
    (rewrite sym $ mulOppL ux uy in
     eqmodMult (unsigned $ repr (-ux) n) (-ux) uy uy (modulus n)
       (eqmUnsignedRepr' (-ux) n)
       (eqmodRefl uy (modulus n)))
    (eqmodNeg (ux*uy) (unsigned $ repr (ux*uy) n) (modulus n) $
     eqmUnsignedRepr (ux*uy) n)

mulNegR : (x, y : BizMod2 n) -> x * (-y) = -(x * y)
mulNegR x y =
  rewrite mulComm x (-y) in
  rewrite mulComm x y in
  mulNegL y x

mulSigned : (x, y : BizMod2 n) -> x * y = repr (signed x * signed y) n
mulSigned {n} x y =
  eqmSamerepr (unsigned x * unsigned y) (signed x * signed y) n $
  eqmodMult (unsigned x) (signed x) (unsigned y) (signed y) (modulus n)
    (eqmUnsignedSigned x)
    (eqmUnsignedSigned y)
