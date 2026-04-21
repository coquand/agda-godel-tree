{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.StrongPhiCorrAnalysis — feasibility of approach (C).
--
-- Goal: prove or refute the tractability of  strongPhiCorr  via direct
-- equational reasoning (no axiom-encoder build-out), trying minimal Phi
-- candidates  Phi = I  and  Phi = KT C  and  Phi = Comp I I .
--
-- Outcome: every minimal Phi reduces  strongPhiCorr  to a single
-- "missing fact" that is FALSE (or itself reduces to gsCR, which would
-- be circular).  We isolate the missing fact precisely with conditional
-- lemmas — each one PROVED — that take the false fact as a hypothesis
-- and derive  strongPhiCorr  for that Phi.
--
-- This file therefore documents WHY approach (C) is intractable:
-- the equation  reify cGSCR = codeBotT  is between two distinct closed
-- terms (cGSCR is the code of the Gödel sentence; codeBotT is the code
-- of the trivial inequation  trueT = falseT).  No Schema-F or
-- congruence chain can bridge them without a separate, non-derivable
-- lemma.  Hence Phi must genuinely DEPEND on v0 in a "diagonal-aware"
-- manner — i.e. approach (A).
--
-- No postulates, no holes.

module Guard.StrongPhiCorrAnalysis where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical using (Triv ; trivCT ; cGSCR)
open import Guard.ProvV3 using (codeBotT)

------------------------------------------------------------------------
-- The strong phiCorr equation, parameterised by Phi.

StrongPhiCorr : Fun1 -> Set
StrongPhiCorr Phi =
  (v0 : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR))
                 (ap2 TreeEq (ap1 (thmT trivCT) (ap1 Phi v0)) codeBotT))

------------------------------------------------------------------------
-- Trial 1:  Phi = I .
--
-- The RHS becomes  TreeEq (thmT trivCT (ap1 I v0)) codeBotT .  After
-- axI v0, this is  TreeEq (thmT trivCT v0) codeBotT .  Now LHS and RHS
-- agree on the "first slot" of TreeEq (both are  thmT trivCT v0 ).  We
-- need only equate the "second slots":  reify cGSCR = codeBotT .
--
-- BUT: reify cGSCR  and  codeBotT  are distinct closed reified trees:
--   * reify cGSCR  = reify (codeEqn gsCR)            -- code of gsCR
--   * codeBotT     = reify (codeEqn (eqn O (Pair O O)))  -- code of ⊥
-- gsCR is the (substantive) Gödel sentence; ⊥ is the trivial atomic
-- inequation.  These are unequal as Agda terms.
--
-- The lemma below shows that IF we had a Deriv proof of the missing
-- equation, strongPhiCorr for Phi = I would follow immediately.  This
-- isolates the obstruction.

MissingFactCgsBot : Set
MissingFactCgsBot =
  (hyp : Equation) -> Deriv hyp (eqn (reify cGSCR) codeBotT)

-- Conditional: given the missing fact, strongPhiCorr for Phi = I.
phiCorrIFromMissingFact : MissingFactCgsBot -> StrongPhiCorr I
phiCorrIFromMissingFact pfFact v0 {hyp} = ruleTrans step1 step2
  where
  step1 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR))
                         (ap2 TreeEq (ap1 (thmT trivCT) v0) codeBotT))
  step1 = congR TreeEq (ap1 (thmT trivCT) v0) (pfFact hyp)

  step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) codeBotT)
                         (ap2 TreeEq (ap1 (thmT trivCT) (ap1 I v0)) codeBotT))
  step2 = congL TreeEq codeBotT
            (cong1 (thmT trivCT) (ruleSym (axI v0)))

------------------------------------------------------------------------
-- Trial 2:  Phi = KT C  for any closed C.
--
-- Now  ap1 Phi v0 = ap1 (KT C) v0 = C  (via axKT).  So RHS becomes
--   TreeEq (thmT trivCT C) codeBotT
-- which is a fixed term not depending on v0.  But LHS DOES depend on
-- v0 (through  ap1 (thmT trivCT) v0 ).  So strongPhiCorr would force
-- LHS to equal a constant — only possible if  ap1 (thmT trivCT) v0  is
-- itself constant in v0, which it is not (it stays stuck on free v0).
--
-- Concretely: the missing fact for Phi = KT C is now
--   forall v0,  TreeEq (thmT trivCT v0) (reify cGSCR)
--             = TreeEq (thmT trivCT C) codeBotT
-- and the RHS is the same for every v0.  The lemma below is the
-- conditional form: given this universal equation as a Deriv, Phi = KT C
-- works.  But the universal equation itself cannot be proved without
-- knowing thmT-on-v0 reduces uniformly, which it doesn't.

MissingFactConst : Term -> Set
MissingFactConst C =
  (v0 : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR))
                 (ap2 TreeEq (ap1 (thmT trivCT) C) codeBotT))

phiCorrKTFromMissingFact :
  (C : Term) -> MissingFactConst C -> StrongPhiCorr (KT C)
phiCorrKTFromMissingFact C pfFact v0 {hyp} = ruleTrans (pfFact v0) reshape
  where
  reshape : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) C) codeBotT)
                           (ap2 TreeEq (ap1 (thmT trivCT) (ap1 (KT C) v0)) codeBotT))
  reshape = congL TreeEq codeBotT
              (cong1 (thmT trivCT) (ruleSym (axKT C v0)))

------------------------------------------------------------------------
-- Trial 3:  Phi = Comp I I .
--
-- Here  ap1 (Comp I I) v0 = ap1 I (ap1 I v0)  via axComp; further
-- axI x2 yields  v0 .  So this is operationally equivalent to Phi = I,
-- inheriting Trial 1's obstruction.

phiCorrCompIIFromMissingFact : MissingFactCgsBot -> StrongPhiCorr (Comp I I)
phiCorrCompIIFromMissingFact pfFact v0 {hyp} = ruleTrans step1 step2
  where
  step1 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR))
                         (ap2 TreeEq (ap1 (thmT trivCT) v0) codeBotT))
  step1 = congR TreeEq (ap1 (thmT trivCT) v0) (pfFact hyp)

  -- ap1 (Comp I I) v0 = ap1 I (ap1 I v0) = ap1 I v0 = v0.
  reduceCompII : Deriv hyp (eqn (ap1 (Comp I I) v0) v0)
  reduceCompII =
    ruleTrans (axComp I I v0)
    (ruleTrans (axI (ap1 I v0))
               (axI v0))

  step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) codeBotT)
                         (ap2 TreeEq (ap1 (thmT trivCT) (ap1 (Comp I I) v0)) codeBotT))
  step2 = congL TreeEq codeBotT
            (cong1 (thmT trivCT) (ruleSym reduceCompII))

------------------------------------------------------------------------
-- Schema-F (ruleF) feasibility check.
--
-- One might hope that  ruleF  could prove  thmT trivCT v0 = X  for
-- some clever X derived from Phi.  But ruleF requires both functors to
-- satisfy the SAME recursive scheme on (Pair var0 var1).  The step
-- function for  thmT  is  thmTStep , which depends on hCode in a
-- non-trivial way.  For ruleF to bridge LHS and RHS, we'd need:
--
--   F(v0) := TreeEq (thmT trivCT v0) (reify cGSCR)
--   G(v0) := TreeEq (thmT trivCT (ap1 Phi v0)) codeBotT
--
-- both expressible as  ap1 _ v0  for some Fun1, AND both satisfying
-- the same Rec(z, s) scheme.  But:
--   * F(O) = TreeEq O (reify cGSCR) reduces to  poo  (sentinel).
--   * G(O) = TreeEq (thmT trivCT (Phi O)) codeBotT — for  Phi = I, KT O,
--     or any Phi with  Phi O = O , also reduces to  poo .
-- So the BASE matches.
--
-- However, the STEP requires recovering  thmT trivCT var_i  from
-- F(var_i) = TreeEq (thmT trivCT var_i) (reify cGSCR) , which is
-- non-invertible (TreeEq erases the original argument).  Concretely:
-- the Fun2 step  s  must produce  TreeEq (thmTStep ...) (reify cGSCR)
-- from arguments  (Pair var0 var1)  and  (Pair F(var0) F(var1)) .  The
-- second component carries TreeEq-results, not raw thmT-results.
--
-- Therefore Schema F cannot bridge the two TreeEq applications in a
-- single step, regardless of Phi.  The full diagonal encoder (approach
-- A) is required.
--
-- We document this as an Agda comment rather than a Set-level negation
-- because formalising "Schema F cannot prove X" is a meta-statement
-- about provability, not a Deriv equation.

------------------------------------------------------------------------
-- Summary
--
-- For every minimal Phi (I, KT C, Comp I I, ...), strongPhiCorr
-- reduces to either:
--   (1) the false equation  reify cGSCR = codeBotT  (trials I, Comp I I),
--   (2) a v0-dependent equation that cannot hold for constant Phi v0
--       (trial KT C),
-- or (3) a Schema-F application that fails because TreeEq is not
--       invertible (trials with ruleF).
--
-- Conclusion: approach (C) is intractable.  Phi must depend on v0 in
-- a way that mirrors the diagonal proof transformation, which is the
-- ~1000-line axiom-encoder build-out of approach (A).  The skeleton
-- in  Guard.GodelIIClassicalSkel  remains valid; only the construction
-- of Phi must follow approach (A).
