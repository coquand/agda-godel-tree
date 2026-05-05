{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14Step2
--
-- Guard's Theorem 14 step 2 (guard15.pdf p.17 line 2):
--
--   th(Dsub(i,i)) = "sub(i,i) = j"  ,   by Theorem 13.
--
-- In our codebase's numeral-only, doubly-encoded formulation this is:
--
--   thmT (reify Dsub_jj_tree)
--     = reify (codeFormula (atomic (eqn (ap2 sub i i) cG)))
--
-- where:
--   * i  = reify j  (Guard's "i" = our diagonal-prefix Goedel number,
--                    j : Tree  from BRA.Thm11Diagonal.Diagonal),
--   * cG = reify (codeFormula G) (Guard's "j" = our diagonal-sentence
--                                                   Goedel number).
-- The BRA-Deriv that  sub(i,i) = cG  (Guard's meta-fact "sub(i,i) = j")
-- is already proved as  subIIeqcG  in BRA.Thm14Abstract.Thm14
-- (re-exported via BRA.GoedelII).
--
-- Theorem 14 step 2 in our codebase:  apply  encode  to  subIIeqcG .
-- This is the canonical-input / "prove once, use once" reading of
-- Guard's schematic-x Theorem 13 instance.
--
-- No postulates, no holes.

module BRA.Th14Step2 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Sub using (sub)
open import BRA.Thm.ThmT using (thmT)
open BRA.Thm.ThmT.WithDispatch using (encode)
open import BRA.GoedelII using (i ; cG ; subIIeqcG)

------------------------------------------------------------------------
-- Theorem 14 step 2 in numeral-only form.

Th14_step2 :
  Sigma Term (\ Df ->
    Deriv (atomic (eqn (ap1 thmT Df)
                       (reify (codeFormula
                         (atomic (eqn (ap2 sub i i) cG)))))))
Th14_step2 =
  let
    P : Formula
    P = atomic (eqn (ap2 sub i i) cG)

    r : Sigma Tree (\ y ->
          Deriv (atomic (eqn (ap1 thmT (reify y)) (reify (codeFormula P)))))
    r = encode P subIIeqcG

  in mkSigma (reify (fst r)) (snd r)
