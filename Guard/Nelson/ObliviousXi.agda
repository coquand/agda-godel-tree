{-# OPTIONS --safe --without-K --exact-split #-}

-- ObliviousXi.agda
-- Experiment: which (program, xi) pairs pass checkProof2?
--
-- checkProof2 for Schema F evaluates h = Comp2 TreeEq p (KT (reify xi))
-- and g = KT poo on the stuck variable (tagVar). If geval(h(var0C)) =
-- geval(g(var0C)), it returns true.
--
-- IMPORTANT: checkProof2 = true is NECESSARY but NOT SUFFICIENT for the
-- Schema F proof to be valid. It only checks the conclusion on one point
-- (the stuck variable), not the full base/step cases.
-- However, if it returns false, the proof definitely fails.

module Guard.Nelson.ObliviousXi where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun
open import Guard.Nelson.Machine
open import Guard.Nelson.GroundEval

private
  poo : Term ; poo = ap2 Pair O O
  dSP : Tree ; dSP = encRefl (code O)

mkTestXi : Fun1 -> Tree -> Tree
mkTestXi p xiTree =
  let xiTerm = reify xiTree
      h = Comp2 TreeEq p (KT xiTerm)
      g = KT poo
      sF = Lift (KT poo)
  in encF (codeF1 h) (codeF1 g) (code poo) (codeF2 sF) dSP dSP dSP dSP

------------------------------------------------------------------------
-- Candidate xi values

xi1 : Tree ; xi1 = nd (nd lf lf) lf                              -- Pair(Pair(O,O), O)
xi2 : Tree ; xi2 = nd lf (nd lf lf)                              -- Pair(O, Pair(O,O))
xi3 : Tree ; xi3 = nd (nd lf lf) (nd lf lf)                     -- Pair(Pair(O,O), Pair(O,O))
xi4 : Tree ; xi4 = nd (nd (nd lf lf) lf) (nd lf lf)             -- Pair(Pair(Pair(O,O),O), Pair(O,O))
xi5 : Tree ; xi5 = nd (nd lf (nd lf lf)) (nd (nd lf lf) lf)    -- asymmetric

------------------------------------------------------------------------
-- Programs

p1 : Fun1 ; p1 = iterate prepend0 O               -- natCodeIter
p2 : Fun1 ; p2 = iterate prepend1 O               -- 1-bit prepend
p3 : Fun1 ; p3 = iterate (Comp2 Pair I I) O       -- doubler
p4 : Fun1 ; p4 = iterate (Comp2 Pair Snd Fst) O   -- swap
p5 : Fun1 ; p5 = I                                -- identity
p6 : Fun1 ; p6 = KT O                             -- constant O
p7 : Fun1 ; p7 = Fst                              -- left projection
p8 : Fun1 ; p8 = Snd                              -- right projection
p9 : Fun1 ; p9 = Comp2 Pair (KT poo) I            -- prepend Pair(O,O)

------------------------------------------------------------------------
-- Test xi1 = Pair(Pair(O,O), O) against all programs

t1_xi1 : Eq (checkProof2 (mkTestXi p1 xi1)) true ; t1_xi1 = refl
-- p2 vs xi1: p2 outputs xi1 at clock 1 (prepend1(O) = Pair(Pair(O,O), O) = xi1)
-- Does checkProof2 catch this?
t2_xi1 : Eq (checkProof2 (mkTestXi p2 xi1)) false ; t2_xi1 = refl  -- YES, caught!
t3_xi1 : Eq (checkProof2 (mkTestXi p3 xi1)) true ; t3_xi1 = refl
t4_xi1 : Eq (checkProof2 (mkTestXi p4 xi1)) true ; t4_xi1 = refl
t5_xi1 : Eq (checkProof2 (mkTestXi p5 xi1)) true ; t5_xi1 = refl
t6_xi1 : Eq (checkProof2 (mkTestXi p6 xi1)) true ; t6_xi1 = refl
t7_xi1 : Eq (checkProof2 (mkTestXi p7 xi1)) true ; t7_xi1 = refl
t8_xi1 : Eq (checkProof2 (mkTestXi p8 xi1)) true ; t8_xi1 = refl
t9_xi1 : Eq (checkProof2 (mkTestXi p9 xi1)) true ; t9_xi1 = refl

-- Result for xi1: 8/9 pass, p2 fails.

------------------------------------------------------------------------
-- Test xi2 = Pair(O, Pair(O,O)) against all programs
-- Note: p1 outputs xi2 at clock 2, but checkProof2 may still pass.

t1_xi2 : Eq (checkProof2 (mkTestXi p1 xi2)) true ; t1_xi2 = refl   -- passes despite outputting xi2!
t2_xi2 : Eq (checkProof2 (mkTestXi p2 xi2)) true ; t2_xi2 = refl
t3_xi2 : Eq (checkProof2 (mkTestXi p3 xi2)) true ; t3_xi2 = refl
t4_xi2 : Eq (checkProof2 (mkTestXi p4 xi2)) true ; t4_xi2 = refl
t5_xi2 : Eq (checkProof2 (mkTestXi p5 xi2)) true ; t5_xi2 = refl
t6_xi2 : Eq (checkProof2 (mkTestXi p6 xi2)) true ; t6_xi2 = refl
t7_xi2 : Eq (checkProof2 (mkTestXi p7 xi2)) true ; t7_xi2 = refl
t8_xi2 : Eq (checkProof2 (mkTestXi p8 xi2)) true ; t8_xi2 = refl
t9_xi2 : Eq (checkProof2 (mkTestXi p9 xi2)) true ; t9_xi2 = refl

-- Result for xi2: 9/9 pass! (but checkProof2 is unsound here — p1 does output xi2)

------------------------------------------------------------------------
-- Test xi3 = Pair(Pair(O,O), Pair(O,O))

t1_xi3 : Eq (checkProof2 (mkTestXi p1 xi3)) true ; t1_xi3 = refl
t2_xi3 : Eq (checkProof2 (mkTestXi p2 xi3)) true ; t2_xi3 = refl
t3_xi3 : Eq (checkProof2 (mkTestXi p3 xi3)) true ; t3_xi3 = refl  -- doubler outputs xi3 at clock 2!
t4_xi3 : Eq (checkProof2 (mkTestXi p4 xi3)) true ; t4_xi3 = refl
t5_xi3 : Eq (checkProof2 (mkTestXi p5 xi3)) true ; t5_xi3 = refl
t6_xi3 : Eq (checkProof2 (mkTestXi p6 xi3)) true ; t6_xi3 = refl
t7_xi3 : Eq (checkProof2 (mkTestXi p7 xi3)) true ; t7_xi3 = refl
t8_xi3 : Eq (checkProof2 (mkTestXi p8 xi3)) true ; t8_xi3 = refl
t9_xi3 : Eq (checkProof2 (mkTestXi p9 xi3)) true ; t9_xi3 = refl

-- Result for xi3: 9/9 pass (but some are unsound — p3 outputs xi3)

------------------------------------------------------------------------
-- Test xi4 = Pair(Pair(Pair(O,O),O), Pair(O,O))

t1_xi4 : Eq (checkProof2 (mkTestXi p1 xi4)) true ; t1_xi4 = refl
t2_xi4 : Eq (checkProof2 (mkTestXi p2 xi4)) true ; t2_xi4 = refl
t3_xi4 : Eq (checkProof2 (mkTestXi p3 xi4)) true ; t3_xi4 = refl
t4_xi4 : Eq (checkProof2 (mkTestXi p4 xi4)) true ; t4_xi4 = refl
t5_xi4 : Eq (checkProof2 (mkTestXi p5 xi4)) true ; t5_xi4 = refl
t6_xi4 : Eq (checkProof2 (mkTestXi p6 xi4)) true ; t6_xi4 = refl
t7_xi4 : Eq (checkProof2 (mkTestXi p7 xi4)) true ; t7_xi4 = refl
t8_xi4 : Eq (checkProof2 (mkTestXi p8 xi4)) true ; t8_xi4 = refl
t9_xi4 : Eq (checkProof2 (mkTestXi p9 xi4)) true ; t9_xi4 = refl

------------------------------------------------------------------------
-- Test xi5 = Pair(Pair(O, Pair(O,O)), Pair(Pair(O,O), O))

t1_xi5 : Eq (checkProof2 (mkTestXi p1 xi5)) true ; t1_xi5 = refl
t2_xi5 : Eq (checkProof2 (mkTestXi p2 xi5)) true ; t2_xi5 = refl
t3_xi5 : Eq (checkProof2 (mkTestXi p3 xi5)) true ; t3_xi5 = refl
t4_xi5 : Eq (checkProof2 (mkTestXi p4 xi5)) true ; t4_xi5 = refl
t5_xi5 : Eq (checkProof2 (mkTestXi p5 xi5)) true ; t5_xi5 = refl
t6_xi5 : Eq (checkProof2 (mkTestXi p6 xi5)) true ; t6_xi5 = refl
t7_xi5 : Eq (checkProof2 (mkTestXi p7 xi5)) true ; t7_xi5 = refl
t8_xi5 : Eq (checkProof2 (mkTestXi p8 xi5)) true ; t8_xi5 = refl
t9_xi5 : Eq (checkProof2 (mkTestXi p9 xi5)) true ; t9_xi5 = refl

------------------------------------------------------------------------
-- Now add the acid tests: programs that ALWAYS output their xi

-- KT(reify xi) = constant xi function
pConst1 : Fun1 ; pConst1 = KT (reify xi1)
pConst2 : Fun1 ; pConst2 = KT (reify xi2)
pConst3 : Fun1 ; pConst3 = KT (reify xi3)
pConst4 : Fun1 ; pConst4 = KT (reify xi4)
pConst5 : Fun1 ; pConst5 = KT (reify xi5)

-- Constant functions that ALWAYS output xi should FAIL checkProof2:
tConst1 : Eq (checkProof2 (mkTestXi pConst1 xi1)) false ; tConst1 = refl
tConst2 : Eq (checkProof2 (mkTestXi pConst2 xi2)) false ; tConst2 = refl
tConst3 : Eq (checkProof2 (mkTestXi pConst3 xi3)) false ; tConst3 = refl
tConst4 : Eq (checkProof2 (mkTestXi pConst4 xi4)) false ; tConst4 = refl
tConst5 : Eq (checkProof2 (mkTestXi pConst5 xi5)) false ; tConst5 = refl

------------------------------------------------------------------------
-- CRITICAL FINDING:
--
-- checkProof2 can return TRUE even when a program DOES output xi!
-- Example: p1 (natCodeIter) outputs xi2 = Pair(O, Pair(O,O)) at clock 2,
-- but checkProof2(mkTestXi p1 xi2) = true.
--
-- WHY: checkProof2 only evaluates on the stuck variable tagVar.
-- geval(h(var0C)) computes TreeEq(natCodeIter(tagVar), reify(xi2)).
-- natCodeIter on tagVar does Rec, recursing into tagVar's nd-children.
-- The resulting tree HAPPENS to differ from xi2. But on natCode 2 (a
-- different tree), natCodeIter produces exactly xi2.
--
-- CONSEQUENCE: checkProof2 is NOT a sound verifier for "p never outputs xi."
-- It IS sound for KT (constant functions) — those always produce the same
-- output regardless of input, so the stuck-var test catches them.
-- For Rec-based programs, the stuck-var test is INCOMPLETE: it evaluates
-- on ONE specific input (tagVar), not on all inputs.
--
-- WHAT THIS MEANS FOR NELSON:
-- The oblivious invariant detected by checkProof2 is weaker than we thought.
-- It confirms: "geval on tagVar agrees." This is useful as a FILTER
-- (it correctly rejects KT(xi)), but it OVER-ACCEPTS iterate programs.
--
-- The FULL Schema F proof (with base case and step case verification)
-- is needed for soundness. checkProof2 only checks the conclusion.
-- The step case for natCodeIter vs xi2 would FAIL (because prepend0's
-- structural invariant doesn't separate from xi2 — the left component
-- is O in both natCodeIter's output and xi2's left component for depth > 0).
--
-- TRUE oblivious invariant = checkProof2 passes AND the step case is
-- actually derivable. This requires that the TreeEq short-circuits
-- at a GROUND comparison that holds universally.
--
-- For natCodeIter: the short-circuit is at Fst (O vs Pair(O,O) for xi1). ✓
-- For natCodeIter vs xi2: both have Fst = O. No short-circuit at Fst.
-- The comparison falls through to Snd, which depends on the clock. ✗
