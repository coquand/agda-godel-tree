{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.RuleInst : Term-level wrapper for the substitution
-- (ruleInst) dispatch.  Given a proof-code Tree y_h whose thmT-image is
-- the encoded formula P, parEncRuleInst encodes the application of
-- substF x t to that proof; parDispRuleInst gives the corresponding
-- thmT-image, namely the encoded substituted formula  substF x t P .
--
-- This is the formal bridge corresponding to Guard's
--   th(Sub(p, t)) = code(substituted theorem)
-- (guard15.pdf p.16).  The substitution is performed at the proof-code
-- level by  body_ruleInst  inside  BRA2.Thm.ThmT , using the  subT
-- combinator (BRA2.SubT).  No Hilbert-level deduction theorem required.
--
-- Used by Theorem 12's Rec/RecP/TreeEq successor cases:  the Pair
-- branch of  D_X  applies  parEncRuleInst  to a universal axiom proof
-- code (e.g. axRecNd at fresh vars x_0, x_1) plus runtime-specific
-- substitution terms, producing the encoded specialization at runtime
-- args.

module BRA2.Thm12.Param.RuleInst where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_ruleInst ; thmTDispRuleInst )
open import BRA2.Thm.Parts.RuleInst public
  using ( encRuleInst ; outRuleInst )

------------------------------------------------------------------------
-- Term-level encoder.
--
-- parEncRuleInst xT yT tT = ap2 Pair tagCode_ruleInst
--                              (ap2 Pair (ap2 Pair xT tT) yT)
--
-- (refactor 2026-05-02: closed (xT, tT) pair at inner Fst,
-- OPEN proof yT at outer Snd; matches encRuleInst.)
--
-- xT  encodes  reify (code (var x))  -- the variable being substituted.
-- yT  encodes the proof of P (typically reify y_h for a Tree y_h).
-- tT  encodes  reify (code t)  -- the substitute term.

parEncRuleInst : Term -> Term -> Term -> Term
parEncRuleInst xT yT tT =
  ap2 Pair tagCode_ruleInst (ap2 Pair (ap2 Pair xT tT) yT)

------------------------------------------------------------------------
-- Encoded conclusion: the encoded substituted formula.

parOutRuleInst : Nat -> Term -> Formula -> Term
parOutRuleInst x t P = reify (outRuleInst x t P)

------------------------------------------------------------------------
-- Parametric dispatch.  Given a Tree y_h with shape lemma + correctness,
-- gives the thmT-image of  parEncRuleInst (reify (code (var x))) (reify y_h) (reify (code t)) .
--
-- This is the canonical  th(Sub(p, t)) = code(substituted theorem)
-- equation, in BRA's tree-based notation.

parDispRuleInst : (x : Nat) (t : Term) (P : Formula) (y_h : Tree) (y_h' : Term) ->
  Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
  Deriv (atomic (eqn (ap1 thmT (reify y_h)) (reify (codeFormula P)))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncRuleInst (reify (code (var x))) (reify y_h) (reify (code t))))
                     (parOutRuleInst x t P)))
parDispRuleInst x t P y_h y_h' shape_h d_h =
  thmTDispRuleInst x t P y_h y_h' shape_h d_h
