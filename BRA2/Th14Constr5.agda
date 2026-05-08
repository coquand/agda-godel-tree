{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th14Constr5
--
-- Carneiro-lifted Theorem 14 chain (Guard 1963 p.16-17): builds
-- constr5 + step5 from r12_th, r12_sub.  Plugs into BRA2.GoedelII.Compose
-- to produce
--
--   godelII : Deriv Con -> Deriv bot
--
-- parametric in r12_th, r12_sub (Thm 12 results for thmT and sub --
-- the only remaining gap; see BRA/THM14-CARNEIRO-STEP0-BLOCKER.md).
--
-- Architecture (per NEXT-SESSION-THM14-CARNEIRO.md):
--   * Each Guard step lifted under hypothesis  P = PrAtX x  via
--     liftAxiom / liftedRuleTrans / liftedCong1 / B_combinator.
--   * t_term = encoding of axEqTrans-shape closed tautology
--     "(x_0 = x_2) ⊃ (x_1 = x_2) ⊃ (x_0 = x_1)" .
--   * t'_term = encoding of axNeg-shape closed tautology
--     "(x_0 = x_1) ⊃ ((x_0 ≠ x_1) ⊃ '0 = 1')" .
--   * constr5 : Fun1 = mp_enc (mp_enc (K_part) (...)) ...  encoded Hilbert
--     proof tree, x-parametric via cor at f_part / g_part / K_part / h_part
--     leaf positions.
--   * step5 = the lifted chain producing the internal implication.
--
-- Status: file builds the helper layer + axImpRefl + liftThm13_F1.
-- The full constr5 / step5 construction is the substantial body work
-- (~800-1000 LoC) following the steps in
-- NEXT-SESSION-THM14-CARNEIRO.md sections "Building constr5" /
-- "Carneiro lifting -- the chain in full".
--
-- No postulates, no holes, no with-abstractions, no dot patterns.

module BRA2.Th14Constr5 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor      using (cor)
open import BRA2.Sub      using (sub)

open import BRA2.Thm.ThmT using (thmT)
open BRA2.Thm.ThmT.WithDispatch using (encode)

open import BRA2.Thm12
  using (Thm12_F1_Result ; Thm12_F2_Result ; codeFTeq1 ; codeFTeq2)
open import BRA2.Thm13
  using (codeFTeq1Hyp ; codeFTeq2Hyp ; thm13_F1 ; thm13_F2)

open import BRA2.Thm.EvalHelpers
  using (liftAxiom ; B_combinator
       ; liftedAxEqTrans ; liftedRuleSym ; liftedRuleTrans
       ; liftedCong1 ; liftedCongL ; liftedCongR)

open import BRA2.GoedelII
  using (i ; cG ; PrAtX ; Con ; bot ; subIIeqcG)
import BRA2.GoedelII

----------------------------------------------------------------------
-- Helpers (singly-lifted Carneiro deduction-theorem combinators).

-- axImpRefl P : Deriv (P imp P).  Standard SK derivation:
--   P imp P  =  mp (mp axS axK_a) axK_b
-- where axK_a : P imp ((P imp P) imp P) and axK_b : P imp (P imp P).

axImpRefl : (P : Formula) -> Deriv (P imp P)
axImpRefl P =
  mp (mp (axS P (P imp P) P)
         (axK P (P imp P)))
     (axK P P)

----------------------------------------------------------------------
-- Carneiro-lifted Theorem 13 for singular functors.
--
-- Mirrors thm13_F1 (BRA2.Thm13) but lifted under an arbitrary
-- antecedent P : Formula.  Each step in thm13_F1's body --
--   bridge = congR Pair lhs_part (cong1 cor hyp)
--   ruleTrans (Thm12_F1_Result.proof r12 x) bridge
-- becomes a singly-lifted version under P, with the hyp-using leaf
-- consuming a lifted hypothesis  Deriv (P imp atomic (eqn (ap1 f x) y)) .

module _
  (f : Fun1)
  (r12 : Thm12_F1_Result f)
  (x y : Term)
  (P : Formula)
  where

  private
    Df : Fun1
    Df = Thm12_F1_Result.Df r12

    lhs_part : Term
    lhs_part = ap2 Pair (reify tagAp1)
                        (ap2 Pair (reify (codeF1 f)) (ap1 cor x))

  liftThm13_F1 :
    Deriv (P imp atomic (eqn (ap1 f x) y)) ->
    Deriv (P imp atomic (eqn (ap1 thmT (ap1 Df x))
                              (codeFTeq1Hyp f x y)))
  liftThm13_F1 lifted_hyp =
    let
        cor_lifted :
          Deriv (P imp atomic (eqn (ap1 cor (ap1 f x)) (ap1 cor y)))
        cor_lifted = liftedCong1 P cor (ap1 f x) y lifted_hyp

        bridge_lifted :
          Deriv (P imp atomic (eqn (codeFTeq1 f x) (codeFTeq1Hyp f x y)))
        bridge_lifted =
          liftedCongR P Pair (ap1 cor (ap1 f x)) (ap1 cor y)
            lhs_part cor_lifted

        proof_lifted :
          Deriv (P imp atomic (eqn (ap1 thmT (ap1 Df x)) (codeFTeq1 f x)))
        proof_lifted = liftAxiom P (Thm12_F1_Result.proof r12 x)

    in liftedRuleTrans P
         (ap1 thmT (ap1 Df x))
         (codeFTeq1 f x)
         (codeFTeq1Hyp f x y)
         proof_lifted bridge_lifted

----------------------------------------------------------------------
-- The Th14Constr5 module proper.

module Th14Constr5
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  --------------------------------------------------------------------
  -- Convenient projections.

  D_thmT : Fun1
  D_thmT = Thm12_F1_Result.Df r12_th

  D_sub : Fun2
  D_sub = Thm12_F2_Result.Dg r12_sub

  --------------------------------------------------------------------
  -- Step 1 of Guard, lifted under  P = PrAtX x = thmT(x) = cG .
  --
  -- liftThm13_F1 with hypothesis  axImpRefl P  -- the antecedent proves
  -- itself, exactly the meta-arrow (H -> ...) shape of step 1 in
  -- Carneiro form.

  step1_l : (x : Term) ->
    Deriv (PrAtX x imp
            atomic (eqn (ap1 thmT (ap1 D_thmT x))
                        (codeFTeq1Hyp thmT x cG)))
  step1_l x =
    liftThm13_F1 thmT r12_th x cG (PrAtX x) (axImpRefl (PrAtX x))

  --------------------------------------------------------------------
  -- Step 2 of Guard, lifted (closed in x; just liftAxiom).

  step2_l : (x : Term) ->
    Deriv (PrAtX x imp
            atomic (eqn (ap1 thmT (ap2 D_sub i i))
                        (codeFTeq2Hyp sub i i cG)))
  step2_l x = liftAxiom (PrAtX x)
                (thm13_F2 sub r12_sub i i cG subIIeqcG)

  --------------------------------------------------------------------
  -- TODO (next session work): the full constr5 + step5 chain.
  --
  -- The remaining steps follow NEXT-SESSION-THM14-CARNEIRO.md's
  -- "Carneiro lifting -- the chain in full":
  --
  --   * t_term, t_witness via encode of axEqTrans-shape tautology.
  --   * t'_term, t'_witness via encode of axNeg-shape tautology.
  --   * f_part : Fun1   such that  ap1 f_part x = encoded sb-chain on t.
  --   * g_part : Fun1   = mp_enc f_part (D_thmT x) (D_sub i i)  builder.
  --   * K_part : Fun1   = sb-step on the diagonal Tree j.
  --   * h_part : Fun1   = sb-chain on t' for the negation step.
  --   * constr5 : Fun1  = mp_enc (mp_enc K_part) (mp_enc g_part h_part).
  --   * step5_l x : the meta-Pi lifted chain producing the internal
  --     implication form Thm14Abstract.GodelII demands.
  --
  -- Once  constr5  and  step5  are built, the closure is one line via
  -- BRA2.GoedelII.Compose:
  --
  --   module Final = BRA2.GoedelII.Compose constr5 step5
  --   godelII : Deriv Con -> Deriv bot
  --   godelII = Final.godelII
  --
  -- The CARNEIRO LIFTING for each step is mechanical given step1_l,
  -- step2_l above and the singly-lifted helpers in
  -- BRA2.Thm.EvalHelpers.  The constr5 BUILDER is mechanical given the
  -- BRA-level Pair/Lift/KT/Comp combinators.  The substantive
  -- VERIFICATIONS are the thmTDispMp_param / thmTDispRuleInst_param /
  -- thmTDispAxEqTrans / thmTDispAxNeg shape-obligations at each chain
  -- node.
