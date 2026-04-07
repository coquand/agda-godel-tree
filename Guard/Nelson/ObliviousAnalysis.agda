{-# OPTIONS --safe --without-K --exact-split #-}

-- ObliviousAnalysis.agda
-- Investigating WHAT geval computes on stuck variables.
--
-- For each program p, geval(mkAp1(codeF1 p, var0C)) computes a specific
-- tree — the program's "stuck-var output." Two programs have the same
-- oblivious behavior iff their stuck-var outputs agree.
--
-- This analysis reveals the semantic content of checkProof2:
-- it checks whether geval(stuck-var output of p) and geval(reify xi)
-- produce the same tree under TreeEq comparison.

module Guard.Nelson.ObliviousAnalysis where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun
open import Guard.Nelson.Machine
open import Guard.Nelson.GroundEval

private
  poo : Term ; poo = ap2 Pair O O
  var0C : Tree ; var0C = nd tagVar lf

------------------------------------------------------------------------
-- Compute the stuck-var output for a program
stuckOutput : Fun1 -> Tree
stuckOutput p = geval fuel (mkAp1 (codeF1 p) var0C)

------------------------------------------------------------------------
-- What does geval produce for each program on var0C?

-- I(var0C) = var0C = nd(tagVar, lf)
stuckI : Eq (stuckOutput I) (nd tagVar lf)
stuckI = refl

-- KT O (var0C) = geval(code O) = lf
stuckKT : Eq (stuckOutput (KT O)) lf
stuckKT = refl

-- Fst(var0C) = leftT(nd(tagVar, lf)) = tagVar
stuckFst : Eq (stuckOutput Fst) tagVar
stuckFst = refl

-- Snd(var0C) = rightT(nd(tagVar, lf)) = lf
stuckSnd : Eq (stuckOutput Snd) lf
stuckSnd = refl

------------------------------------------------------------------------
-- Iterate programs: geval recurses on tagVar's tree structure
-- tagVar = nd(nd(nd lf lf) lf) lf
-- This has 3 nd-nodes, so Rec iterates 3 times.

-- natCodeIter = iterate prepend0 O
-- Rec on tagVar:
--   tagVar = nd(nd(nd lf lf) lf)(lf)
--   left child = nd(nd lf lf) lf, right child = lf
--   rec(lf) = O = lf (base case)
--   rec(nd(nd lf lf) lf):
--     left = nd lf lf, right = lf
--     rec(lf) = lf
--     rec(nd lf lf):
--       left = lf, right = lf
--       rec(lf) = lf, rec(lf) = lf
--       step(nd lf lf, Pair(lf, lf)) = prepend0(Snd(Pair(lf, lf))) = prepend0(lf)
--         = Pair(O, O) at semantic level = nd(lf, lf)
--     step(nd(nd lf lf) lf, Pair(nd(lf,lf), lf)) = prepend0(Snd(Pair(nd(lf,lf), lf)))
--       = prepend0(lf) = nd(lf, lf)
--   step(tagVar, Pair(nd(lf,lf), lf)) = prepend0(Snd(Pair(nd(lf,lf), lf)))
--     = prepend0(lf) = nd(lf, lf)
--
-- So stuckOutput(natCodeIter) should be nd(lf, lf)

-- Let's check:
stuckNCI : Tree
stuckNCI = stuckOutput (iterate prepend0 O)

-- Expected: nd(lf, lf) = reified Pair(O, O)
-- Actually let me just compute it:
stuckNCIcheck : Eq stuckNCI (nd lf lf)
stuckNCIcheck = refl

-- So natCodeIter on stuck var = nd(lf, lf) = Pair(O, O) semantically.
-- TreeEq(Pair(O,O), xi1) where xi1 = Pair(Pair(O,O), O):
-- Compare Fst: O vs Pair(O,O) → unequal. Short-circuits! ✓

-- natCodeIter vs xi2 where xi2 = Pair(O, Pair(O,O)):
-- TreeEq(nd(lf,lf), nd(lf, nd(lf,lf)))
-- = IfLf(TreeEq(lf, lf), Pair(TreeEq(lf, nd(lf,lf)), Pair(lf,lf)))
-- = IfLf(lf, Pair(nd(lf,lf), nd(lf,lf)))
-- = first of Pair = nd(lf,lf)   [wait: IfLf(lf, Pair(a,b)) = a]
-- Hmm, nd(lf,lf) = Pair(O,O) = poo at tree level.
-- And geval(g(var0C)) where g = KT poo:
-- geval(mkAp1(codeKT(code poo), var0C)) = geval(code poo) = nd(lf,lf)
-- So: both sides = nd(lf,lf). checkProof2 = true. ✓
-- But this is a coincidence! The TreeEq comparison happens to give Pair(O,O)
-- because Fst matches but Snd doesn't, and the IfLf dispatches to give Pair(O,O).

-- Wait, let me re-examine. treeEqSem(nd lf lf, nd lf (nd lf lf)):
-- = boolCase(treeEq(treeEqSem lf lf) lf) (treeEqSem lf (nd lf lf)) (nd lf lf)
-- treeEqSem lf lf = lf. treeEq lf lf = true.
-- boolCase true (treeEqSem lf (nd lf lf)) (nd lf lf) = treeEqSem lf (nd lf lf) = nd lf lf
-- So treeEqSem gives nd lf lf = "unequal". ✓

-- So for the stuck-var test: TreeEq(output, xi2) = nd lf lf = Pair(O,O).
-- And KT(Pair(O,O)) on stuck var = nd lf lf.
-- Both = nd lf lf. checkProof2 = true.

-- BUT: the program DOES output xi2 at clock 2!
-- The Schema F step case would fail because Snd(prepend0(x)) = x varies.
-- checkProof2 doesn't check the step case. It only checks the conclusion
-- on one specific input.

------------------------------------------------------------------------
-- Doubler: iterate (Comp2 Pair I I) O

stuckDoubler : Tree
stuckDoubler = stuckOutput (iterate (Comp2 Pair I I) O)

-- tagVar = nd(nd(nd lf lf) lf) lf
-- Rec for doubler:
--   base: lf
--   step(orig, Pair(recL, recR)): doubler(recR) = Pair(recR, recR) = nd(recR, recR)
--   rec(lf) = lf
--   rec(nd lf lf):
--     recL = rec(lf) = lf
--     recR = rec(lf) = lf
--     step: Pair(lf, lf) = nd(lf, lf)
--   rec(nd(nd lf lf) lf):
--     recL = rec(nd lf lf) = nd(lf, lf)
--     recR = rec(lf) = lf
--     step: Pair(lf, lf) = nd(lf, lf)   [applies doubler to recR = lf: Pair(lf,lf)]
--     wait: step = iterStep doubler. iterStep f (orig, pair) = f(Snd(pair))
--     Snd(Pair(nd(lf,lf), lf)) = lf. doubler(lf) = Pair(lf, lf) = nd(lf,lf).
--   rec(tagVar = nd(nd(nd lf lf) lf) lf):
--     recL = rec(nd(nd lf lf) lf) = nd(lf, lf)
--     recR = rec(lf) = lf
--     step: doubler(Snd(Pair(nd(lf,lf), lf))) = doubler(lf) = nd(lf, lf)

stuckDoublerCheck : Eq stuckDoubler (nd lf lf)
stuckDoublerCheck = refl

-- Same stuck output as natCodeIter! Both give nd(lf,lf) on tagVar.
-- This makes sense: tagVar has right child = lf (base case).
-- So iterStep always sees recR = lf, and applies the step function to lf.
-- prepend0(lf) = nd(lf, lf). doubler(lf) = nd(lf, lf). Same!

------------------------------------------------------------------------
-- Swap: iterate (Comp2 Pair Snd Fst) O

stuckSwap : Tree
stuckSwap = stuckOutput (iterate (Comp2 Pair Snd Fst) O)

stuckSwapCheck : Eq stuckSwap (nd lf lf)
stuckSwapCheck = refl

-- Also nd(lf,lf)! Same reason: right child of tagVar is lf,
-- so the step function operates on lf.
-- swap(lf) = Pair(Snd(lf), Fst(lf)) = Pair(lf, lf) = nd(lf, lf).

------------------------------------------------------------------------
-- prepend1: iterate prepend1 O

stuckPrep1 : Tree
stuckPrep1 = stuckOutput (iterate prepend1 O)

-- prepend1(lf) = Pair(Pair(O,O), lf) = nd(nd(lf,lf), lf)
-- On stuck var (right child = lf), step gives prepend1(lf) = nd(nd(lf,lf), lf)

stuckPrep1Check : Eq stuckPrep1 (nd (nd lf lf) lf)
stuckPrep1Check = refl

-- nd(nd lf lf) lf = xi1 exactly!
-- So: stuckOutput(iterate prepend1 O) = xi1.
-- TreeEq(xi1, xi1) = O (equal), not Pair(O,O) (unequal).
-- But KT poo on stuck var = Pair(O,O) = nd(lf,lf).
-- O ≠ nd(lf,lf). So checkProof2 = false. ✓

-- This explains why p2 vs xi1 fails: the stuck-var output IS xi1.

------------------------------------------------------------------------
-- prepend Pair(O,O): Comp2 Pair (KT poo) I
-- Applied to lf: Pair(nd(lf,lf), lf) = nd(nd(lf,lf), lf) = xi1!

stuckPrep9 : Tree
stuckPrep9 = stuckOutput (Comp2 Pair (KT poo) I)

stuckPrep9Check : Eq stuckPrep9 (nd (nd lf lf) (nd tagVar lf))
stuckPrep9Check = refl

-- Not iterated, so not Rec. Direct: Pair(KT poo var0C, I var0C) = Pair(nd(lf,lf), nd(tagVar, lf))
-- = nd(nd(lf,lf), nd(tagVar, lf))
-- This is NOT equal to any small xi, so it passes against all tested xi values.

------------------------------------------------------------------------
-- KEY INSIGHT: Why iterate programs on tagVar all give similar results
--
-- tagVar = nd(nd(nd lf lf) lf)(lf).  Right child = lf.
--
-- For iterate f init: the Rec on tagVar does:
--   rec(tagVar) = step(tagVar, Pair(rec(left child), rec(right child)))
--   rec(right child) = rec(lf) = init (base case)
--   iterStep: takes Snd of the Pair, which is rec(right child) = init.
--   Then applies f to init.
--
-- So: stuckOutput(iterate f init) = f(init)  (modulo deeper recursion on left child)
--
-- Wait, the iterStep is: iterStep f (orig, pair) = f(Snd(pair)).
-- At the top level: pair = Pair(rec(left), rec(right)).
-- Snd(pair) = rec(right) = rec(lf) = init = O.
-- So iterStep gives f(O) regardless of left child recursion!
--
-- But that's only at the TOP level. The deeper recursion matters for
-- the left child. However, the final step just applies f to the
-- result of rec(right child of tagVar) = rec(lf) = O.
--
-- All iterate programs: stuckOutput = f(O).
-- prepend0: f(O) = Pair(O, O) = nd(lf, lf). ✓
-- prepend1: f(O) = Pair(Pair(O,O), O) = nd(nd lf lf, lf) = xi1. ✓
-- doubler: f(O) = Pair(O, O) = nd(lf, lf). ✓
-- swap: f(O) = Pair(Snd(O), Fst(O)) = Pair(lf, lf) = nd(lf, lf). ✓
--
-- So the stuck-var test for iterate programs reduces to:
--   TreeEq(f(O), reify(xi)) = Pair(O,O)?
--
-- This is a CONCRETE, DECIDABLE test: does f(O) differ from xi?
-- If f(O) = xi, the test fails.
-- If f(O) ≠ xi, the test passes.
--
-- For the KR argument: we need xi such that f(O) ≠ xi for ALL
-- step functions f of bounded code-size. Since f(O) is a specific
-- tree determined by f, and there are only finitely many f of
-- bounded size, we need xi ∉ {f(O) | codeSize(f) ≤ l}.
-- This is a FINITE exclusion set. Any xi outside it works.

------------------------------------------------------------------------
-- STRONGER TEST: Can we also verify the step case?
--
-- The step case of Schema F requires:
--   h(Pair(v0,v1)) = s(Pair(v0,v1), Pair(h(v0), h(v1)))
--
-- For the oblivious invariant with constant s:
--   h(Pair(v0,v1)) = Pair(O,O) for all v0, v1.
--
-- This means: TreeEq(p(Pair(v0,v1)), reify(xi)) = Pair(O,O).
-- For iterate f init:
--   p(Pair(v0,v1)) = f(p(v1))    by iterNd
--
-- The step case holds iff:
--   TreeEq(f(p(v1)), reify(xi)) = Pair(O,O)
-- for ALL v1, assuming h(v1) = Pair(O,O) (i.e., p(v1) ≠ xi).
--
-- This is where the oblivious invariant matters:
-- If TreeEq(f(x), xi) short-circuits at a GROUND position
-- (a comparison that doesn't depend on x), then the step case holds.
-- This is the "oblivious" property: the proof doesn't need to know x.
--
-- For natCodeIter vs xi1: f = prepend0, prepend0(x) = Pair(O, x).
-- TreeEq(Pair(O, x), Pair(Pair(O,O), O)):
-- First compare O vs Pair(O,O) → unequal → Pair(O,O). ✓
-- Short-circuits before examining x. OBLIVIOUS.
--
-- For natCodeIter vs xi2: f = prepend0, prepend0(x) = Pair(O, x).
-- TreeEq(Pair(O, x), Pair(O, Pair(O,O))):
-- First compare O vs O → equal.
-- Then compare x vs Pair(O,O). DEPENDS ON x. NOT OBLIVIOUS.
-- So the step case fails for some x values.
