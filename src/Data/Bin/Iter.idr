module Data.Bin.Iter

import Data.Bin
import Data.Bip.Iter

%access public export
%default total

-- Peano induction

-- peano_rect

peanoRect : (P : Bin -> Type) -> (f0 : P BinO) ->
            (f: (n : Bin) -> P n -> P (binSucc n)) ->
            (n : Bin) -> P n
peanoRect _ f0 _  BinO    = f0
peanoRect P f0 f (BinP a) = peanoRect (P . BinP) (f BinO f0) (\p => f $ BinP p) a

-- peano_rect_base is trivial

-- peano_rect_succ
-- peano_rec_base
-- peano_rec_succ
-- TODO

-- Generic induction / recursion

-- bi_induction
-- TODO without setoids this is essentially `peanoRect` with an additional
-- constraint `(n : Bin) -> A (binSucc n) -> A n`, so I'm not sure how useful
-- it is here

binRecursion : a -> (Bin -> a -> a) -> Bin -> a
binRecursion {a} = peanoRect (\_ => a)

-- recursion_wd
-- TODO

-- recursion_0 is trivial

-- recursion_succ
-- TODO
