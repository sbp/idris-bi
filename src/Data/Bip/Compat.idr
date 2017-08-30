module Data.Bin.Nat

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.OrdSub

%access public export
%default total

-- "Compatibility facts", how useful are these in practice?

-- Pminus_mask_Gt 

subMaskGt : (p, q : Bip) -> p `Gt` q -> (r ** ( bimMinus p q = BimP r
                                              , q + r = p
                                              , Either (r = U) (bimMinusCarry p q = BimP $ bipPred r)
                                              ))
subMaskGt p q pgtq = 
  let (r**(prfm,prfp)) = subMaskPos' p q $ gtLt p q pgtq 
  in 
    (r**( prfm
        , prfp
        , rewrite subMaskCarrySpec p q in 
          rewrite prfm in 
          aux
        ))
  where
  aux : Either (r = U) (bimPred $ BimP r = BimP $ bipPred r)
  aux {r=U  } = Left Refl
  aux {r=O a} = Right Refl
  aux {r=I a} = Right Refl

-- Pplus_minus 

addMinus : (p, q : Bip) -> p `Gt` q -> q+(p-q) = p
addMinus p q pgtq = rewrite addComm q (p-q) in 
                    subAdd p q $ gtLt p q pgtq
