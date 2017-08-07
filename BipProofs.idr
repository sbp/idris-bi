import Bip

import Language.Reflection
import Pruviloj.Core
import Pruviloj.Induction

%default total

-- Following PArith/BinPos.v

-- Coq xI_succ_xO

iSuccORefl : (p: Bip) -> (I p) = bipSucc (O p)
iSuccORefl _ = Refl

iSuccO : (p: Bip) -> (I p) = bipSucc (O p)
iSuccO = %runElab
  (do intro'
      reflexivity)
