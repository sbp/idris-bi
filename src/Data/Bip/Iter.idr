module Data.Bip.Iter

import Data.Bip
import Data.Bip.AddMul

%default total

-- peano_rect

mutual
  export
  peanoRect : (0 t : Bip -> Type) -> (a : t U) ->
              (f : (p : Bip) -> t p -> t (bipSucc p)) ->
              (p : Bip) -> t p
  peanoRect _ a _  U    = a
  peanoRect t a f (O q) = peanoAux t a f q
  peanoRect t a f (I q) = f _ (peanoAux t a f q)

  peanoAux : (0 t : Bip -> Type) -> (a : t U) ->
             (f : (p : Bip) -> t p -> t (bipSucc p)) ->
             (p : Bip) -> t (O p)
  peanoAux t a f p = peanoRect (t . O) (f _ a) (\_ => f _ . f _) p

-- TODO rest of Peano?

-- iter_swap_gen

iterSwapGen : (f : a -> b) -> (g : a -> a) -> (h : b -> b) ->
              ((x : a) -> f (g x) = h (f x)) ->
              (x : a) -> (p : Bip) -> f (bipIter g x p) = bipIter h (f x) p
iterSwapGen _ _ _ fx x  U     = fx x
iterSwapGen f g h fx x (O b)  =
  rewrite sym $ iterSwapGen f g h fx x b in
  rewrite iterSwapGen f g h fx (bipIter g x b) b in
  Refl
iterSwapGen f g h fx x (I b) =
  rewrite sym $ iterSwapGen f g h fx x b in
  rewrite fx (bipIter g (bipIter g x b) b) in
  rewrite iterSwapGen f g h fx (bipIter g x b) b in
  Refl

-- iter_swap

iterSwap : (f : a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f (f x) p = f (bipIter f x p)
iterSwap f x p = sym $ iterSwapGen f f f (\_ => Refl) x p

-- iter_succ

iterSucc : (f : a -> a) -> (x : a) -> (p : Bip) ->
           bipIter f x (bipSucc p) = f (bipIter f x p)
iterSucc _ _  U    = Refl
iterSucc _ _ (O _) = Refl
iterSucc f x (I a) =
  rewrite iterSucc f x a in
  rewrite iterSwap f (bipIter f x a) (bipSucc a) in
  rewrite iterSucc f (bipIter f x a) a in
  Refl

-- iter_add

iterAdd : (f : a -> a) -> (x: a) -> (p,q : Bip) ->
           bipIter f x (p+q) = bipIter f (bipIter f x q) p
iterAdd f x  U    q = rewrite add1L q in
                      iterSucc f x q
iterAdd f x (O a) q =
  rewrite sym $ iterAdd f x a q in
  rewrite sym $ iterAdd f x a (a+q) in
  rewrite addAssoc a a q in
  rewrite addDiag a in
  Refl
iterAdd f x (I a) q =
  rewrite sym $ iterAdd f x a q in
  rewrite sym $ iterAdd f x a (a+q) in
  rewrite sym $ iterSucc f x (a+(a+q)) in
  rewrite addAssoc a a q in
  rewrite addDiag a in
  rewrite sym $ addSuccL (O a) q in
  Refl

-- iter_invariant

iterInvariant : (f : a -> a) -> (inv : a -> Type) -> (p : Bip) ->
                ((x : a) -> inv x -> inv (f x)) ->
                (x : a) -> inv x -> inv (bipIter f x p)
iterInvariant f inv  U    g x ix = g x ix
iterInvariant f inv (O b) g x ix =
  let ih = iterInvariant f inv b g x ix in
    iterInvariant f inv b g (bipIter f x b) ih
iterInvariant f inv (I b) g x ix =
  let ih = iterInvariant f inv b g x ix
      ih2 = iterInvariant f inv b g (bipIter f x b) ih in
    g (bipIter f (bipIter f x b) b) ih2

-- TODO reformulate iter_op_succ so that it describes toNatBip/bipMultNat