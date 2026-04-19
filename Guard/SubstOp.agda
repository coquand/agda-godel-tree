{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.SubstOp — dynamic substitution via the RecP primitive.
--
-- substOp : Fun2  such that
--   ap2 substOp (Pair tC xC) (reify (code l))
--     = reify (code (subst x t l))
-- where tC = reify (code t), xC = reify (natCode x).
--
-- This is the dynamic counterpart of  closedSubstTFor tC xC  from
-- Guard.SubstTForCorrect : instead of tC, xC being baked in as
-- meta-level Fun1 parameters, they are extracted from the runtime
-- pair  Pair tC xC  passed as the  RecP  param.
--
-- Used by V3's  case23V3  (the ruleInst case) — see Guard.Thm14EV3.

module Guard.SubstOp where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstTFor using (tagVarT)
open import Guard.SubstTForCorrect using (closedSubstTFor)

------------------------------------------------------------------------
-- Accessors into the RecP-step's orig argument.
--
-- At a RecP-step call, orig = Pair param (Pair a b) where
--   param = Pair tC xC     (injected from RecP's first arg)
--   (a, b) = the current node's children
-- and recs = (rec_a, rec_b).

private
  -- param: Fst orig = Pair tC xC
  paramF : Fun2
  paramF = Lift Fst

  -- tC: Fst param = Fst(Fst orig)
  tCF : Fun2
  tCF = Lift (Comp Fst Fst)

  -- xC: Snd param = Snd(Fst orig)
  xCF : Fun2
  xCF = Lift (Comp Snd Fst)

  -- current node: Snd orig = Pair a b
  curNodeF : Fun2
  curNodeF = Lift Snd

  -- a (tag of current): Fst(Snd orig)
  aF : Fun2
  aF = Lift (Comp Fst Snd)

  -- b (data of current): Snd(Snd orig)
  bF : Fun2
  bF = Lift (Comp Snd Snd)

  -- recs passthrough: sndArg2(orig, recs) = recs
  recsF : Fun2
  recsF = Post Snd Pair

------------------------------------------------------------------------
-- The step function for substOp.
--
--   isVar := TreeEq(a, tagVarT)
--   if isVar = O:
--     if TreeEq(b, xC) = O: return tC
--     else:                  return curNode = Pair a b
--   else:
--     return recs

stepSubstP : Fun2
stepSubstP =
  Fan (Fan aF (Lift (KT tagVarT)) TreeEq)           -- isVar check
      (Fan (Fan (Fan bF xCF TreeEq)                  -- matchTgt check
                (Fan tCF curNodeF Pair) IfLf)        -- (repl, curNode) choice
           recsF Pair)                                -- (match-branch, recs-branch)
      IfLf

------------------------------------------------------------------------
-- substOp : Fun2
--
-- ap2 substOp p l  — apply substitution described by p to target l.

substOp : Fun2
substOp = RecP stepSubstP

------------------------------------------------------------------------
-- Step-level equivalence: at any input of matching shape,
-- stepSubstP computes the same result as closedSubstTFor tC xC's step.
--
-- stepSubstP takes orig_P = Pair (Pair tC xC) (Pair aT bT).
-- cStep (inside closedSubstTFor tC xC) takes orig_C = Pair aT bT.
-- Both receive the same recs.  Both reduce to the same result via
-- the Fun2 axioms.
--
-- We prove the equivalence directly by chaining Fun2 reductions.

------------------------------------------------------------------------
-- substOpLf and substOpNd: derived reductions on reified Tree inputs.

substOpLf : (tC xC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair tC xC) O) O)
substOpLf tC xC = axRecPLf stepSubstP (ap2 Pair tC xC)

substOpNd : (tC xC aT bT : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair tC xC) (ap2 Pair aT bT))
                 (ap2 stepSubstP (ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT))
                                 (ap2 Pair (ap2 substOp (ap2 Pair tC xC) aT)
                                           (ap2 substOp (ap2 Pair tC xC) bT))))
substOpNd tC xC aT bT = axRecPNd stepSubstP (ap2 Pair tC xC) aT bT

------------------------------------------------------------------------
-- closedSubstTFor-Lf and -Nd as named helpers for cleaner chaining.

closedSubstTForLf : (tC xC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor tC xC) O) O)
closedSubstTForLf tC xC = axRecLf O _
  where
  _ = tC ; _ = xC

-- Step-equivalence with cStep is non-trivial and requires substantial
-- proof engineering (~200 lines).  Completion of substOp correctness
-- is the next milestone for phase D2 of the redesign; see
-- GODEL-II-REDESIGN.md.  The definitions above suffice for D3's
-- case23V3 redesign, which we will wire up once correctness is proved.

