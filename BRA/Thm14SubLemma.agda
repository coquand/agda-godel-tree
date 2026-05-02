{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14SubLemma
--
-- Definition 12 line 2 stated as a parametric lemma:
--
--   given  Deriv (thmT y = codeP)  and a Fst-shape proof on y,
--   derive  Deriv (thmT (sb-encoded-tree-with-proof-index-y) =
--                  subT (Pair (reify (code (var n))) tT) codeP).
--
-- Built on top of  BRA.Thm.ThmT.thmTDispRuleInst_param  by
-- transitively rewriting the result's  ap1 thmT y  to  codeP  via the
-- supplied hypothesis.  No new axioms; no body_ruleInst surgery.
--
-- Required xShape on y is supplied at the call site (e.g., in Phase C
-- when constructing K_part / h_part chains, the proof-index for the
-- sb-encoded numerals is wrapped in a Fun1 whose output has derivable
-- Pair-shape — see BRA/Thm14Constr5Final.agda).

module BRA.Thm14SubLemma where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

open import BRA.SubT using (subT)

open import BRA.Thm.ThmT
  using ( thmT
        ; thmTDispRuleInst_param
        ; tagCode_ruleInst )

----------------------------------------------------------------------
-- thmTSubLemma : the parametric Def 12 line 2 (sb-clause) for thmT.
--
-- Inputs:
--   * n      : Nat       -- the variable index being substituted.
--   * tT     : Term      -- the substituent (a Term, may be open).
--   * y      : Term      -- the proof-index Term (may be open;
--                          xShape supplies its Fst-shape).
--   * codeP  : Term      -- the closed encoded conclusion of the
--                          proof referenced by y (under hypothesis).
--   * d_h    : Deriv (thmT y = codeP)   -- the hypothesis.
--   * xShape : Sigma proof of  Fst y = Pair x' y' .
--
-- Output:
--   thmT (Pair tagCode_ruleInst (Pair varCode (Pair y tT)))
--     = subT (Pair varCode tT) codeP
--
-- Construction:
--   step1 = thmTDispRuleInst_param n tT y xShape
--          -- gives: thmT (sb-encoded) = subT (Pair varCode tT) (thmT y)
--   step2 = congR subT _ d_h
--          -- gives: subT (Pair varCode tT) (thmT y) = subT (Pair varCode tT) codeP
--   result = ruleTrans step1 step2

thmTSubLemma :
  (n : Nat) (tT y codeP : Term) ->
  (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
     Deriv (atomic (eqn (ap1 Fst y) (ap2 Pair x' y')))))) ->
  Deriv (atomic (eqn (ap1 thmT y) codeP)) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair tagCode_ruleInst
                (ap2 Pair (reify (code (var n))) (ap2 Pair y tT))))
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
thmTSubLemma n tT y codeP xShape d_h =
  let
      varCodeT : Term
      varCodeT = reify (code (var n))

      -- Step 1: dispatch via thmTDispRuleInst_param.
      -- Result has  ap1 thmT y  on the RHS (not yet codeP).
      step1 :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 Pair tagCode_ruleInst
                      (ap2 Pair varCodeT (ap2 Pair y tT))))
          (ap2 subT (ap2 Pair varCodeT tT) (ap1 thmT y))))
      step1 = thmTDispRuleInst_param n tT y xShape

      -- Step 2: rewrite  ap1 thmT y  to  codeP  via the hypothesis d_h .
      step2 :
        Deriv (atomic (eqn
          (ap2 subT (ap2 Pair varCodeT tT) (ap1 thmT y))
          (ap2 subT (ap2 Pair varCodeT tT) codeP)))
      step2 = congR subT (ap2 Pair varCodeT tT) d_h

  in ruleTrans step1 step2
