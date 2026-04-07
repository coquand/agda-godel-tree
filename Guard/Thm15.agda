{-# OPTIONS --safe --without-K --exact-split #-}

-- Rose Theorems 14-15 (pp.133-134).
--
-- Theorem 14: "If A |- B in system T, then th(y) + [B] |- th(y) + [A]"
-- Theorem 15: "If A = B then th(y) + [A = 0] |- th(y) + [B = 0]"
--             (immediate consequence of Theorem 14)
--
-- In our system: given Deriv hyp eq, there exists an encoding tree enc
-- such that the system proves thFunTFor(reify enc) = reify(codeEqn eq).
--
-- The proof is by induction on Deriv (all 26 cases). The combined
-- induction is thm14E; we extract the encoding and correctness Deriv.

module Guard.Thm15 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.Thm14E using (ProofE ; thm14E)
open import Guard.ProofEAny using (mkProofEAny)

------------------------------------------------------------------------
-- Thm14Result: the encoding tree and its correctness proof.
-- enc = nd pa pb is the proof tree encoding.
-- The Deriv proves: thFunTFor(reify enc) = reify(codeEqn eq).

Thm14Result : Equation -> Set
Thm14Result eq = Sigma Tree (\enc ->
  {hyp : Equation} -> Deriv hyp (eqn (ap1 thFunTFor (reify enc))
                                      (reify (codeEqn eq))))

------------------------------------------------------------------------
-- Extract Thm14Result from ProofE.

fromProofE : {eq : Equation} -> ProofE eq -> Thm14Result eq
fromProofE pe =
  mkSigma (nd (fst pe) (fst (snd pe)))
          (fst (snd (snd (snd pe))))

------------------------------------------------------------------------
-- Rose Theorem 14/15: combined induction on Deriv.
--
-- Given Deriv hyp eq and Thm14Result for the hypothesis,
-- produce Thm14Result for the derived equation.
--
-- Uses mkProofEAny to construct ProofE hyp (needed for thm14E's
-- ruleHyp case), then extracts the result.

thm15 : {hyp eq : Equation} -> Deriv hyp eq ->
         Thm14Result hyp -> Thm14Result eq
thm15 {eqn l r} d _ = fromProofE (thm14E d (mkProofEAny l r))
