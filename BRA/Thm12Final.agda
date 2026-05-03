{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12Final
--
-- Closes Theorem 12 for TreeEq via the new universal Th12_F2_TreeEq
-- (BRA/Th12TreeEqClose.agda).  This file delivers the TreeEq side of
-- the FromBridges integration plus the easy IfLf and z_corLemma
-- pieces (Stage 1 of NEXT-SESSION-THM12FINAL.md):
--
--   TreeEq side (4 of 14 FromBridges params):
--     * D_TreeEq_NN_fun         -- chain-Df Fun2 (BRA/Th12TreeEqNNFun.agda).
--     * D_TreeEq_NN_closed      -- substF2 closure (refl).
--     * D_correct2_TreeEq_NN_pt_C   p q a b (with 4 closure args).
--     * D_correct2_TreeEq_univ_C    x v (with 4 closure args).
--
--   Stage 1 additions (2 more params):
--     * D_correct2_IfLf_univ_C  x v (with 4 closure args)  -- P1.
--     * z_corLemma_for_O        : (t : Tree) -> ...        -- P2.
--
-- Each "with closure args" entry takes the four Eq-closure proofs
-- required to handle substitution distributivity across cor / Df / Pair.
-- At closed (numeral or var-NOT-in-{0,1}) inputs all closure args
-- reduce to refl.
--
-- The remaining 8 FromBridges parameters (Rec/RecP NN bundles, the two
-- universal Rec/RecP closure proofs, the two shape lemmas) hit a real
-- architectural issue: see "Architectural finding" below.
--
-- Architectural finding (2026-04-30)
-- ----------------------------------
-- The FromBridges parameter D_correct_Rec_univ requires the universal
-- proof of Th12 for the Parts.Rec.Construction.D_Rec_zs Fun1 -- which
-- can be derived via ruleIndBT atop the existing pointwise lemmas
-- D_correct_Rec_zs_O and D_correct_Rec_zs_Nd, BUT only after committing
-- to closure proofs of D_Rec_zs and codeFTeq1_Rec_zs over var-zero
-- substitution.  The corresponding Th12RecUniv.WithClosure.ih_s_bra
-- parameter (BRA-Deriv form Theorem 12 for the recursion's stepper s)
-- is the SAME thing that FromBridges itself is constructing: this is
-- a true mutual-recursion circularity, not a missing-lemma gap.
--
-- The cleanest fix is to refactor the FromBridges interface so that
-- D_correct_Rec_univ takes ih_s_bra as an explicit predecessor input
-- (forwarded from the recursion's IH) -- structurally analogous to how
-- D_correct (Comp f g) gets D_correct f and D_correct g as inputs in
-- the dispatch.  At the architectural level this is a ~50 LoC change
-- to BRA.Thm12.FromBridges' signature; in this file it then becomes a
-- ~80-LoC universal-proof builder for Rec, mirroring this file's
-- D_correct2_TreeEq_univ_C (TreeEq's analog).  Same for RecP.
--
-- Until that refactor lands, P3-P10 are deferred.  See
-- BRA/NEXT-SESSION-THM12-CIRCULARITY.md for the proposed interface.
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.Thm12Final where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.ThmT using (thmT ; thClosed)

open import BRA.Th12TreeEqNNFun public
  using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed)
open import BRA.Th12TreeEqClose public using (Th12_F2_TreeEq)

import BRA.Thm12.Parts.TreeEq
module CB = BRA.Thm12.Parts.TreeEq.ConstructionBase
              D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB using (D_TreeEq ; D_TreeEq_closed ; D_TreeEq_reduce_NN)
open BRA.Thm12.Parts.TreeEq using (codeFTeq2_TreeEq) public

open import BRA.Th12TreeEqBaseLN using (P_Th12_TreeEq)

-- IfLf universal correctness (P1): re-export the closure-arg-parametric
-- form D_correct2_IfLf from Parts/IfLf.  At closed inputs the four
-- closure equalities reduce to refl.
open import BRA.Thm12.Parts.IfLf public
  using (D_IfLf ; codeFTeq2_IfLf ; D_correct2_IfLf)

-- corOfReify : the universal cor-on-reified-Tree lemma.
open import BRA.Cor public using (corOfReify)

------------------------------------------------------------------------
-- D_correct2_TreeEq_univ_C: universal correctness for D_TreeEq
-- at any (x, v), parametric on the four substitution-closure equalities.
--
-- Closure args (refl when x, v are vars not = var 0/1, or are O):
--   xeq0 : subst zero x x = x          (x has no var 0 to be replaced)
--   veq0 : subst zero x v = v
--   veq1 : subst (suc zero) v v = v
--   xeq1 : subst (suc zero) v x = x
--
-- This matches the signature of the existing
-- BRA.Thm12.Parts.TreeEq.Construction.D_correct2_TreeEq.

D_correct2_TreeEq_univ_C :
  (x v : Term)
  (xeq0 : Eq (subst zero x x) x)
  (veq0 : Eq (subst zero x v) v)
  (veq1 : Eq (subst (suc zero) v v) v)
  (xeq1 : Eq (subst (suc zero) v x) x) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq x v))
                     (codeFTeq2_TreeEq x v)))
D_correct2_TreeEq_univ_C x v xeq0 veq0 veq1 xeq1 =
  let
    s1 : Deriv (substF zero x P_Th12_TreeEq)
    s1 = ruleInst zero x Th12_F2_TreeEq

    s2 : Deriv (substF (suc zero) v (substF zero x P_Th12_TreeEq))
    s2 = ruleInst (suc zero) v s1

  in eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap2 D_TreeEq x v))
                                          (codeFTeq2_TreeEq x v))))
       (thClosed (suc zero) v)
       (eqSubst (\ fT -> Deriv (atomic (eqn (ap1 (substF1 (suc zero) v fT)
                                                 (ap2 D_TreeEq x v))
                                             (codeFTeq2_TreeEq x v))))
         (thClosed zero x)
         (eqSubst (\ xT -> Deriv (atomic (eqn (ap1 (substF1 (suc zero) v
                                                            (substF1 zero x thmT))
                                                   (ap2 D_TreeEq xT v))
                                               (codeFTeq2_TreeEq xT v))))
           xeq1
           s2))

------------------------------------------------------------------------
-- D_correct2_TreeEq_NN_pt_C: pointwise NN correctness at
-- (Pair p q, Pair a b), parametric on the four closure args (which
-- reduce to refl when p, q, a, b are closed or vars not in {0, 1}).

D_correct2_TreeEq_NN_pt_C :
  (p q a b : Term)
  (xeq0 : Eq (subst zero (ap2 Pair p q) (ap2 Pair p q)) (ap2 Pair p q))
  (veq0 : Eq (subst zero (ap2 Pair p q) (ap2 Pair a b)) (ap2 Pair a b))
  (veq1 : Eq (subst (suc zero) (ap2 Pair a b) (ap2 Pair a b)) (ap2 Pair a b))
  (xeq1 : Eq (subst (suc zero) (ap2 Pair a b) (ap2 Pair p q)) (ap2 Pair p q)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq_NN_fun (ap2 Pair p q)(ap2 Pair a b)))
                     (codeFTeq2_TreeEq (ap2 Pair p q)(ap2 Pair a b))))
D_correct2_TreeEq_NN_pt_C p q a b xeq0 veq0 veq1 xeq1 =
  let
    pairPQ : Term
    pairPQ = ap2 Pair p q

    pairAB : Term
    pairAB = ap2 Pair a b

    -- Universal proof at (Pair p q, Pair a b).
    univ : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq pairPQ pairAB))
                               (codeFTeq2_TreeEq pairPQ pairAB)))
    univ = D_correct2_TreeEq_univ_C pairPQ pairAB xeq0 veq0 veq1 xeq1

    -- Bridge: D_TreeEq dispatches at NN to D_TreeEq_NN_fun.
    s_reduce : Deriv (atomic (eqn (ap2 D_TreeEq pairPQ pairAB)
                                   (ap2 D_TreeEq_NN_fun pairPQ pairAB)))
    s_reduce = D_TreeEq_reduce_NN p q a b

    s_thmT_reduce : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq pairPQ pairAB))
                                        (ap1 thmT (ap2 D_TreeEq_NN_fun pairPQ pairAB))))
    s_thmT_reduce = cong1 thmT s_reduce

  in ruleTrans (ruleSym s_thmT_reduce) univ

------------------------------------------------------------------------
-- P1: D_correct2_IfLf_univ_C -- IfLf universal correctness, now closure-
-- free thanks to D_correct2_IfLf delivering the truly universal form
-- via the pickFresh trick.  The legacy xeq1 parameter is silently
-- discarded so existing TreeEq-side callers (which pass refl) still
-- compile.

D_correct2_IfLf_univ_C :
  (x v : Term)
  (xeq1 : Eq (subst (suc zero) v x) x) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf x v))
                     (codeFTeq2_IfLf x v)))
D_correct2_IfLf_univ_C x v _ = D_correct2_IfLf x v

------------------------------------------------------------------------
-- P2: z_corLemma_for_O -- closed-Tree restriction of z_corLemma.
--
-- For closed Tree z = reify t, ap1 cor (reify t) BRA-equals reify (code (reify t)).
-- This is the universal Cor lemma used by Parts/Rec.Construction at
-- the leaf input.  At t = lf, this is axRecLf O stepCor (= Deriv (eqn (cor O) O));
-- at t = nd a b it unfolds via axRecNd + structural induction (provided
-- by BRA.Cor.corOfReify).
--
-- Consumers (the Goedel II glue) instantiate FromBridges' z_corLemma_for
-- only at z = reify t for closed Trees t; this is the witness.

z_corLemma_for_O : (t : Tree) ->
  Deriv (atomic (eqn (ap1 cor (reify t)) (reify (code (reify t)))))
z_corLemma_for_O = corOfReify
