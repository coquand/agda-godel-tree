{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.AlternativeStep1Experiment
--
-- Feasibility check for the user's proposal: replace the parametric
-- Theorem 12 / 13 machinery used in Step 1 of Theorem 14 with a direct
-- operator E satisfying
--
--    E : (f : Fun1) (x k : Term) ->
--        Deriv (atomic (eqn (ap1 f x) k)) ->
--        Sigma Tree (\ y ->
--          Deriv (atomic (eqn (ap1 thmT (reify y))
--                             (reify (codeFormula
--                                      (atomic (eqn (ap1 f (ap1 cor x)) k)))))))
--
-- i.e. given a BRA-internal proof that  f x = k , produce an encoded
-- proof tree whose  thmT -evaluation is the code of  "f(x_) = k" .
--
-- The proposal aims to bypass Theorem 12's 15-case parametric  D_f
-- construction.  This file probes how far the proposal goes for the
-- specific case  f := thmT  used in Step 1 of Theorem 14.
--
-- KEY CONSTRUCTION (when f and k are "closed enough"):
--
--   Step a:  Apply ruleInst n (ap1 cor (var n)) to pf, where x = var n.
--            This substitutes  ap1 cor (var n)  for  var n  inside the
--            formula  (atomic (eqn (ap1 f (var n)) k)) .
--   Step b:  Reduce/transport the result using
--              substF1 n (ap1 cor (var n)) f = f      (closure of f), and
--              subst n (ap1 cor (var n)) k   = k      (k closed at n)
--            to land at  Deriv (atomic (eqn (ap1 f (ap1 cor (var n))) k)) .
--   Step c:  Apply  encode  to that derivation.
--
-- For  f := thmT :  thClosed gives Step b automatically (`refl` inside
-- ThmT's abstract block, propositional outside).  For  k := cG : closed
-- term, Step b for the right-hand side is also automatic.
--
-- So E_thmT exists and is short.  The interesting question is whether
-- it suffices for Step 1 of Theorem 14 in a way that downstream
-- (Step 4, Step 5, constr5_final) can compose with.
--
-- See the trailing comment for the assessment of trade-offs.

module BRA.AlternativeStep1Experiment where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Thm.ThmT using (thmT ; thClosed)
open import BRA.MaxVar   using (natEq_refl)

-- encode is defined inside ThmT's WithDispatch (parametric over the
-- 30 deferred dispatchers).  For this isolated experiment, we
-- parametrise over its signature; substitute the concrete instance
-- when integrating downstream.

module Experiment
  (encode : (P : Formula) -> Deriv P ->
            Sigma Tree (\ y ->
              Deriv (atomic (eqn (ap1 thmT (reify y))
                                 (reify (codeFormula P))))))
  where

----------------------------------------------------------------------
-- Step (a): ruleInst-based bridge.
--
-- Inputs:
--   n  : the index of the free variable inside the hypothesis pf.
--   k  : a Term, assumed closed at index n.
--   k_closed_n : witness that  subst n (ap1 cor (var n)) k = k .
--   f  : a Fun1, assumed closed.
--   f_closed_n : witness that  substF1 n (ap1 cor (var n)) f = f .
--   pf : Deriv of  ap1 f (var n) = k .
--
-- Output:
--   Deriv of  ap1 f (ap1 cor (var n)) = k .

  bridge_ruleInst :
    (n : Nat) (k : Term) (f : Fun1) ->
    Eq (subst n (ap1 cor (var n)) k) k ->
    Eq (substF1 n (ap1 cor (var n)) f) f ->
    Deriv (atomic (eqn (ap1 f (var n)) k)) ->
    Deriv (atomic (eqn (ap1 f (ap1 cor (var n))) k))
  bridge_ruleInst n k f k_closed f_closed pf =
    let
      raw : Deriv (substF n (ap1 cor (var n))
                    (atomic (eqn (ap1 f (var n)) k)))
      raw = ruleInst n (ap1 cor (var n)) pf
      -- substF reduces to atomic (eqn lhs0 rhs0) where
      --   lhs0 = ap1 (substF1 n t f) (boolCase (natEq n n) t (var n))
      --   rhs0 = subst n t k
      -- We need to reduce  natEq n n = true  to get the var slot to t,
      -- then apply f_closed and k_closed to land at  ap1 f t = k .
      n_refl : Eq (natEq n n) true
      n_refl = natEq_refl n

      -- Step 1: reduce the var-slot via n_refl.
      step1 : Eq (boolCase (natEq n n) (ap1 cor (var n)) (var n))
                 (ap1 cor (var n))
      step1 = eqCong (\ b -> boolCase b (ap1 cor (var n)) (var n)) n_refl

      raw1 : Deriv (atomic (eqn (ap1 (substF1 n (ap1 cor (var n)) f) (ap1 cor (var n)))
                                 (subst n (ap1 cor (var n)) k)))
      raw1 = eqSubst (\ vSlot -> Deriv (atomic (eqn
                                          (ap1 (substF1 n (ap1 cor (var n)) f) vSlot)
                                          (subst n (ap1 cor (var n)) k))))
                    step1 raw

      -- Step 2: apply f_closed.
      e_lhs : Eq (ap1 (substF1 n (ap1 cor (var n)) f) (ap1 cor (var n)))
                (ap1 f (ap1 cor (var n)))
      e_lhs = eqCong (\ g -> ap1 g (ap1 cor (var n))) f_closed

      raw2 : Deriv (atomic (eqn (ap1 f (ap1 cor (var n)))
                                 (subst n (ap1 cor (var n)) k)))
      raw2 = eqSubst (\ lhs -> Deriv (atomic (eqn lhs (subst n (ap1 cor (var n)) k))))
                    e_lhs raw1

      -- Step 3: apply k_closed.
    in
      eqSubst (\ rhs -> Deriv (atomic (eqn (ap1 f (ap1 cor (var n))) rhs)))
              k_closed raw2

  --------------------------------------------------------------------
  -- The user's E for the special case  f := thmT , k closed at n.
  --
  -- thmT is closed at every n via thClosed (= refl inside ThmT's
  -- abstract block).  So bridge_ruleInst applies with thClosed.

  E_thmT :
    (n : Nat) (k : Term) ->
    Eq (subst n (ap1 cor (var n)) k) k ->
    Deriv (atomic (eqn (ap1 thmT (var n)) k)) ->
    Sigma Tree (\ y ->
      Deriv (atomic (eqn (ap1 thmT (reify y))
                         (reify (codeFormula
                                   (atomic (eqn (ap1 thmT (ap1 cor (var n))) k)))))))
  E_thmT n k k_closed pf =
    let
      bridged : Deriv (atomic (eqn (ap1 thmT (ap1 cor (var n))) k))
      bridged = bridge_ruleInst n k thmT k_closed (thClosed n (ap1 cor (var n))) pf
    in
      encode _ bridged

----------------------------------------------------------------------
-- Assessment / trade-offs:
--
-- (1) E_thmT typechecks (modulo verifying the eqSubst chain in
--     bridge_ruleInst -- the substT-of-var-at-the-binding-index
--     definitional reduction).  So the user's E exists for f := thmT.
--
-- (2) Trade-off vs Theorem 12 + 13 + Step 1:
--
--   * Theorem 12's  D_f : Fun1  is a primitive-recursive Fun1 functor.
--     For any (closed) Term x, the encoded form is  ap1 D_f x  -- a
--     Fun1 application.  This makes  D_thmT  composable with other
--     Fun1's in the constr5 chain (constr5 itself is Fun1).
--
--   * E_thmT's output Tree  y  is a CLOSED tree depending on the
--     hypothesis Deriv  pf .  It is NOT of the form  ap1 (some Fun1) (var n) .
--     Instead, the tree is built by  encode  walking the hypothesis +
--     ruleInst chain and emitting the encoded proof tree.
--
-- (3) Why this matters for downstream Theorem 14:
--
--   The closure step (BRA/Thm14Abstract.agda) builds  constr5 : Fun1
--   from D_thmT, D_sub via Fun1/Fun2 composition (Comp, Comp2, Pair,
--   Lift, Post, Fan).  Step 5's parametric internal-implication
--   shape  thmT(constr5(x)) = code bot  is achievable because
--   constr5(x) reduces uniformly in x via  ap1 .
--
--   With E_thmT producing a Tree (not a Fun1 application of x), we
--   would need to redesign  constr5  as a meta-level Tree-valued
--   function -- breaking the Fun1-uniformity.  In particular,
--   ruleInst applications inside  constr5  (currently used to
--   instantiate the encoded tautologies tterm and t'term) would need
--   to interleave with E_thmT-style calls.
--
-- (4) Where it MIGHT still work:
--
--   The closure could be redesigned around a NEW primitive  constr5*
--   that takes the hypothesis  pf : Deriv (PrAtX x)  as an argument
--   rather than being a fixed Fun1.  Then  step5*  would have shape
--      step5* : (x : Term) -> Deriv (PrAtX x) ->
--               Deriv (atomic (eqn (ap1 thmT (constr5* pf)) (cor bot)))
--   This is a DIFFERENT kind of step5 than the current one (where
--   constr5 doesn't take pf).  The downstream closure would need to
--   match this shape.
--
--   Whether this is simpler than the current Theorem 12 chain is the
--   real question.  My initial assessment: probably similar
--   complexity, just shifted.  The 15-case Thm 12 D_f construction
--   gets replaced by an analogous case analysis inside the redesigned
--   constr5*; the ruleInst transports become explicit at the closure
--   level rather than absorbed into D_f.
--
-- (5) The Step 2 simplification stands:
--
--   For Step 2 (sub(i,i) = j is closed), there's no free variable to
--   ruleInst over.  The closed Deriv  subIIeqcG : Deriv (sub(i,i) = j)
--   directly yields, via  encode , a Tree  E_sub  such that
--      thmT(E_sub) = code "sub(i,i) = j"
--   No Theorem 12 for sub needed.  This part of the user's
--   observation is correct and would simplify  Th14Step2Step / Step3
--   substantially -- replacing the current Thm12 + Thm13 invocations
--   on sub with direct  encode  calls on the closed hypothesis.
--
-- CONCLUSION:
--
--   * For Step 2: the user's observation is correct.  Theorem 12 for
--     sub is unnecessary -- direct  encode  of  subIIeqcG  suffices.
--     Eliminating this would save the  thm12_F2  invocation and the
--     Thm 12 Fun2 cases (Pair, Lift, Post, Fan, Comp2, IfLf, TreeEq,
--     treeRec) for the Fun2 functor case.
--
--   * For Step 1: the user's E_thmT is short and works, but its
--     output is a closed Tree dependent on  pf , not a Fun1
--     application.  This breaks composition with the existing
--     Fun1-based constr5.  Replacing Step 1's Thm 12 + 13 use with E
--     requires redesigning constr5 as a Tree-valued meta-function
--     parameterised on the closure hypothesis.  Doable but a
--     different architecture; whether simpler than current is unclear.
