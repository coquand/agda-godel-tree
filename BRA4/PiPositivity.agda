{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.PiPositivity -- universal-in-Term lemmas asserting that
--  ap2 pi (ap1 s A) B  has  s-shape  (= positive).
--
-- Used by S4 to rewrite the sbt input  pi (natCode tag) X = pi (s ...) X
-- into  ap1 s P_outer  so  cov_spec_step_univ  can fire.
--
-- The Cantor formula T114 says
--   pi v0 v1 = sigma (tau (sigma v0 v1)) v1 .
-- For  v0 = s A , the chain via T35 + T91 + T35 again gives the s-shape.

module BRA4.PiPositivity where

open import BRA4.Base

open import BRA3.Church       using ( pi ; sigma ; tau ; T34 ; T35 ; T91 ; T114 )
open import BRA3.RuleInst2    using ( ruleInst2 )

------------------------------------------------------------------------
-- Building blocks specialised to our universal-in-Term form.

-- T35 at  (var 0 := A, var 1 := B):
--   sigma (s A) B = s (sigma A B) .

T35_at : (A B : Term) ->
  Deriv (eqF (ap2 sigma (ap1 s A) B) (ap1 s (ap2 sigma A B)))
T35_at A B = ruleInst2 0 A 1 B refl T35

-- T91 at  n := Y  for an arbitrary Y:
--   tau (s Y) = sigma (s Y) (tau Y) .
--
-- T91 is stated in BRA3.Church as
--   T91 : Deriv (eqF (ap1 tau (ap1 s (var 0)))
--                     (ap2 sigma (ap1 s (var 0)) (ap1 tau (var 0))))

T91_at : (Y : Term) ->
  Deriv (eqF (ap1 tau (ap1 s Y)) (ap2 sigma (ap1 s Y) (ap1 tau Y)))
T91_at Y = T91 Y

-- T114 at  (var 0 := A, var 1 := B):
--   pi A B = sigma (tau (sigma A B)) B .

T114_at : (A B : Term) ->
  Deriv (eqF (ap2 pi A B) (ap2 sigma (ap1 tau (ap2 sigma A B)) B))
T114_at A B = ruleInst2 0 A 1 B refl T114

------------------------------------------------------------------------
-- pi_succ_outer : a universal Term that is the predecessor of
--   ap2 pi (ap1 s A) B  via the Cantor formula.
--
-- Concretely:
--   pi_succ_outer A B =
--     sigma (sigma (sigma A B) (tau (sigma A B))) B

pi_succ_outer : Term -> Term -> Term
pi_succ_outer A B =
  ap2 sigma (ap2 sigma (ap2 sigma A B) (ap1 tau (ap2 sigma A B))) B

------------------------------------------------------------------------
-- pi_at_succ :  pi (s A) B = s (pi_succ_outer A B) .
--
-- Universal-in-Term.  Derivation chain:
--
--   pi (s A) B
--     = sigma (tau (sigma (s A) B)) B               by T114
--     = sigma (tau (s (sigma A B))) B               by T35 at (A, B), under tau, sigma
--     = sigma (sigma (s (sigma A B)) (tau (sigma A B))) B
--                                                   by T91 at (sigma A B), under sigma
--     = s (sigma (sigma (sigma A B) (tau (sigma A B))) B)
--                                                   by T35 at appropriate args.

pi_at_succ :
  (A B : Term) ->
  Deriv (eqF (ap2 pi (ap1 s A) B) (ap1 s (pi_succ_outer A B)))
pi_at_succ A B =
  let -- Step 1: T114 at (s A, B).
      e1 :
        Deriv (eqF (ap2 pi (ap1 s A) B)
                    (ap2 sigma (ap1 tau (ap2 sigma (ap1 s A) B)) B))
      e1 = T114_at (ap1 s A) B

      -- Step 2: sigma (s A) B = s (sigma A B).
      e_s35 :
        Deriv (eqF (ap2 sigma (ap1 s A) B) (ap1 s (ap2 sigma A B)))
      e_s35 = T35_at A B

      -- Lift under tau: tau (sigma (s A) B) = tau (s (sigma A B)).
      e2 :
        Deriv (eqF (ap1 tau (ap2 sigma (ap1 s A) B))
                    (ap1 tau (ap1 s (ap2 sigma A B))))
      e2 = cong1 tau e_s35

      -- Lift under sigma _ B.
      e2_lift :
        Deriv (eqF (ap2 sigma (ap1 tau (ap2 sigma (ap1 s A) B)) B)
                    (ap2 sigma (ap1 tau (ap1 s (ap2 sigma A B))) B))
      e2_lift = congL sigma B e2

      -- Step 3: T91 at  Y := sigma A B:
      --   tau (s (sigma A B)) = sigma (s (sigma A B)) (tau (sigma A B)).
      e3 :
        Deriv (eqF (ap1 tau (ap1 s (ap2 sigma A B)))
                    (ap2 sigma (ap1 s (ap2 sigma A B)) (ap1 tau (ap2 sigma A B))))
      e3 = T91_at (ap2 sigma A B)

      -- Lift under sigma _ B.
      e3_lift :
        Deriv (eqF (ap2 sigma (ap1 tau (ap1 s (ap2 sigma A B))) B)
                    (ap2 sigma (ap2 sigma (ap1 s (ap2 sigma A B))
                                             (ap1 tau (ap2 sigma A B))) B))
      e3_lift = congL sigma B e3

      -- Step 4: rewrite the inner  sigma (s (sigma A B)) (tau (sigma A B))
      --   to  s (sigma (sigma A B) (tau (sigma A B)))  by T35 at (sigma A B, tau (sigma A B)).
      e_inner_T35 :
        Deriv (eqF (ap2 sigma (ap1 s (ap2 sigma A B)) (ap1 tau (ap2 sigma A B)))
                    (ap1 s (ap2 sigma (ap2 sigma A B) (ap1 tau (ap2 sigma A B)))))
      e_inner_T35 = T35_at (ap2 sigma A B) (ap1 tau (ap2 sigma A B))

      -- Lift under sigma _ B.
      e_inner_T35_lift :
        Deriv (eqF (ap2 sigma (ap2 sigma (ap1 s (ap2 sigma A B))
                                             (ap1 tau (ap2 sigma A B))) B)
                    (ap2 sigma (ap1 s (ap2 sigma (ap2 sigma A B)
                                                    (ap1 tau (ap2 sigma A B)))) B))
      e_inner_T35_lift =
        congL sigma B e_inner_T35

      -- Step 5: outer T35 at (sigma (sigma A B) (tau (sigma A B)), B):
      --   sigma (s X) B = s (sigma X B)  where X = sigma (sigma A B) (tau (sigma A B)).
      e_outer_T35 :
        Deriv (eqF (ap2 sigma (ap1 s (ap2 sigma (ap2 sigma A B)
                                                     (ap1 tau (ap2 sigma A B)))) B)
                    (ap1 s (ap2 sigma (ap2 sigma (ap2 sigma A B)
                                                    (ap1 tau (ap2 sigma A B))) B)))
      e_outer_T35 =
        T35_at (ap2 sigma (ap2 sigma A B) (ap1 tau (ap2 sigma A B))) B
  in ruleTrans e1
       (ruleTrans e2_lift
         (ruleTrans e3_lift
           (ruleTrans e_inner_T35_lift e_outer_T35)))
