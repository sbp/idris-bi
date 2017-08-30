module Data.Bin.Nat

import Data.Bip
import Data.Bip.AddMul
import Data.Bip.IterPow

%access public export
%default total

-- TODO move to other toBipNat proofs lower

-- of_nat_succ

ofNatSucc : (n : Nat) -> toBipNatSucc n = toBipNat (S n)
ofNatSucc  Z    = Refl
ofNatSucc (S k) = cong $ ofNatSucc k

--- pred_of_succ_nat

predOfSuccNat : (n : Nat) -> bipPred (toBipNatSucc n) = toBipNat n
predOfSuccNat Z = Refl
predOfSuccNat (S k) = rewrite predSucc (toBipNatSucc k) in
                      ofNatSucc k

-- succ_of_nat

succOfNat : (n : Nat) -> Not (n=Z) -> bipSucc (toBipNat n) = toBipNatSucc n
succOfNat  Z    contra = absurd $ contra Refl
succOfNat (S k) _      = cong $ sym $ ofNatSucc k


-- Properties of the injection from binary positive numbers to Peano natural
-- numbers

-- inj_succ  

injSucc : (p : Bip) -> toNatBip (bipSucc p) = S (toNatBip p)
injSucc p = aux p 1
  where
  aux : (p : Bip) -> (n : Nat) -> bipMultNat (bipSucc p) n = n + bipMultNat p n
  aux  U    _ = Refl
  aux (O _) _ = Refl
  aux (I a) n = rewrite plusAssociative n n (bipMultNat a (n+n)) in
                        aux a (n+n) 
    
-- inj_add 

injAdd : (p, q : Bip) -> toNatBip (p+q) = toNatBip p + toNatBip q
injAdd p q = 
  peanoRect 
  (\x => toNatBip (x+q) = toNatBip x + toNatBip q)
  (rewrite add1L q in 
   injSucc q)
  (\p', prf => 
    rewrite addSuccL p' q in 
    rewrite injSucc (p'+q) in 
    rewrite injSucc p' in 
    cong prf
  )
  p

-- inj_mul 

injMul : (p, q : Bip) -> toNatBip (p*q) = toNatBip p * toNatBip q
injMul p q = 
  peanoRect 
    (\x => toNatBip (x*q) = toNatBip x * toNatBip q)
    (rewrite plusZeroRightNeutral $ toNatBip q in 
     Refl)
    (\p',prf => 
      rewrite mulSuccL p' q in 
      rewrite injSucc p' in 
      rewrite injAdd q (p'*q) in 
      cong {f=plus (toNatBip q)} prf
    )
    p

-- inj_1 is trivial

-- inj_xO 

injXO : (p : Bip) -> toNatBip (O p) = 2 * toNatBip p
injXO p = rewrite plusZeroRightNeutral $ toNatBip p in 
          rewrite sym $ injAdd p p in 
          rewrite addDiag p in 
          Refl

-- inj_xI 

injXI : (p : Bip) -> toNatBip (I p) = S (2 * toNatBip p)
injXI p = cong $ injXO p

-- is_succ 

isSucc : (p : Bip) -> (n ** toNatBip p = S n)
isSucc = 
  peanoRect
    (\x => (n ** toNatBip x = S n))
    (Z ** Refl)
    (\p, (n**prf) => 
      rewrite injSucc p in 
      (S n ** cong prf)
    )

-- is_pos 
-- TODO can't use Nat.LT here, it clashes

isPos : (p : Bip) -> 1 `LTE` (toNatBip p)
isPos p = rewrite snd $ isSucc p in 
          LTESucc LTEZero

-- id 

toNatBipId : (p : Bip) -> toBipNat $ toNatBip p = p
toNatBipId p = 
  peanoRect 
    (\x => toBipNat $ toNatBip x = x)
    Refl
    (\p',prf => 
      rewrite injSucc p' in 
      let (_**prfn) = isSucc p' in 
      rewrite prfn in 
      rewrite sym prfn in 
      cong prf
    )
    p

-- inj 

toNatBipInj : (p, q : Bip) -> toNatBip p = toNatBip q -> p = q
toNatBipInj p q prf = 
  rewrite sym $ toNatBipId p in 
  rewrite sym $ toNatBipId q in 
  rewrite prf in 
  Refl

-- inj_iff: `fro` is just `cong`
