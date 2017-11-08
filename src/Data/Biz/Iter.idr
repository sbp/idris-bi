module Data.Biz.Iter

import Data.Bip.AddMul
import Data.Bip.Iter

import Data.Biz
import Data.Biz.AddSubMul

%default total
%access public export

-- peano_ind
-- TODO rename all versions to peanoInd ?
peanoRect : (P : Biz -> Type) -> (f0 : P BizO)
         -> (fs : (x : Biz) -> P x -> P (bizSucc x))
         -> (fp : (x : Biz) -> P x -> P (bizPred x))
         -> (z : Biz) -> P z
peanoRect _ f0 _  _   BizO    = f0
peanoRect P f0 fs _  (BizP a) =
  peanoRect (P . BizP) (fs BizO f0) (\p => rewrite sym $ add1R p in
                                           fs $ BizP p) a
peanoRect P f0 _  fp (BizM a) =
  peanoRect (P . BizM) (fp BizO f0) (\p => rewrite sym $ add1R p in
                                           fp $ BizM p) a

-- bi_induction

biInduction : (P : Biz -> Type) -> (f0 : P BizO)
           -> (fto  : (x : Biz) -> P x -> P (bizSucc x))
           -> (ffro : (x : Biz) -> P (bizSucc x) -> P x)
           -> (z : Biz) -> P z
biInduction P f0 fto ffro z =
  Iter.peanoRect P f0 fto (\x, psx =>
    ffro (x-1) $
      rewrite sym $ addAssoc x (-1) 1 in
      rewrite add0R x in
      psx) z
