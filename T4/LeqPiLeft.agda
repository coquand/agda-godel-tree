{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.LeqPiLeft -- the Cantor FIRST-coordinate bound  leq A (pi A B) .
--
-- T4.LeqMono ships  leq_sigma_left/right ,  leq_pi_right : leq B (pi A B) ,
-- and  leq_trans .  The internal CR endpoint maps (T4.ParEnds) need, for the
-- BINARY certificate nodes (cAd / cRS, payload  pi d1 d2 ), the LEFT child
-- bound  leq d1 (pi d1 d2)  -- which is NOT one of the easy projections
-- (Cantor  Fst  is not even a non-strict sigma-component of  pi A B =
-- sigma (tau (sigma A B)) B ).  It is the genuine Cantor inequality
-- A <= <A,B> , provable via the TRIANGULAR lower bound  n <= tau n :
--
--   A  <=  sigma A B            [leq_sigma_left]
--      <=  tau (sigma A B)      [leq_tau, the triangular bound]
--      <=  sigma (tau (sigma A B)) B  =  pi A B   [leq_sigma_left + T114].
--
-- The triangular bound  leq n (tau n)  is a one-line  ruleIndNat  whose
-- STEP does not even use the IH: at  s n ,  tau (s n) = sigma (s n) (tau n)
-- (T91), so  s n <= tau (s n)  is just  leq_sigma_left (s n) (tau n) .

module T4.LeqPiLeft where

open import T4.Base
open import T4.LeqMono using ( leq_sigma_left ; leq_trans ; T114_at )

open import BRA3.Church    using ( pi ; sigma ; tau ; sub ; T90 ; T91 )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )

------------------------------------------------------------------------
-- The triangular lower bound  leq n (tau n) , by ruleIndNat on n.

private
  Pform : Formula
  Pform = leq (var 0) (ap1 tau (var 0))

  -- Base:  leq O (tau O) .   tau O = O (T90) ; sub O O = O (sub_self).
  leq_tau_base : Deriv (eqF (ap2 sub O (ap1 tau O)) O)
  leq_tau_base = ruleTrans (congR sub O T90) (sub_self O)

  -- Step conclusion  Q = leq (s n) (tau (s n))  is provable outright:
  --   tau (s n) = sigma (s n) (tau n)  (T91) , then leq_sigma_left.
  leq_tau_stepQ :
    Deriv (eqF (ap2 sub (ap1 s (var 0)) (ap1 tau (ap1 s (var 0)))) O)
  leq_tau_stepQ =
    ruleTrans (congR sub (ap1 s (var 0)) (T91 (var 0)))
              (leq_sigma_left (ap1 s (var 0)) (ap1 tau (var 0)))

  leq_tau_step :
    Deriv (imp Pform (substF 0 (ap1 s (var 0)) Pform))
  leq_tau_step =
    mp (axK (leq (ap1 s (var 0)) (ap1 tau (ap1 s (var 0)))) Pform) leq_tau_stepQ

  leq_tau_univ : Deriv Pform
  leq_tau_univ = ruleIndNat 0 {P = Pform} leq_tau_base leq_tau_step

leq_tau : (n : Term) -> Deriv (leq n (ap1 tau n))
leq_tau n = ruleInst 0 n leq_tau_univ

------------------------------------------------------------------------
-- leq_pi_left :  leq A (pi A B) .

leq_pi_left : (A B : Term) -> Deriv (leq A (ap2 pi A B))
leq_pi_left A B =
  let X : Term
      X = ap1 tau (ap2 sigma A B)

      l1 : Deriv (leq A (ap2 sigma A B))
      l1 = leq_sigma_left A B

      l2 : Deriv (leq (ap2 sigma A B) X)
      l2 = leq_tau (ap2 sigma A B)

      -- A <= tau (sigma A B) = X .
      l12 : Deriv (leq A X)
      l12 = leq_trans A (ap2 sigma A B) X l1 l2

      -- X <= sigma X B = pi A B (via T114).
      eqPi : Deriv (eqF (ap2 pi A B) (ap2 sigma X B))
      eqPi = T114_at A B

      l3' : Deriv (leq X (ap2 sigma X B))
      l3' = leq_sigma_left X B

      l3 : Deriv (leq X (ap2 pi A B))
      l3 = ruleTrans (congR sub X eqPi) l3'
  in leq_trans A X (ap2 pi A B) l12 l3
