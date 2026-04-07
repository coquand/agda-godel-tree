{-# OPTIONS --safe --without-K --exact-split #-}

-- ObliviousChar.agda
-- Characterization of oblivious invariants and the xi construction.
--
-- Main result: For iterate programs, the oblivious invariant against xi
-- exists iff f(O) ≠ xi AND there is a structural position where
-- f always produces a value differing from xi, regardless of input.
--
-- The xi construction: choose xi to avoid the finite set {f(O) | small f}
-- and to have enough structural diversity that some position always mismatches.

module Guard.Nelson.ObliviousChar where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun
open import Guard.Nelson.Machine
open import Guard.Nelson.GroundEval

private
  poo : Term ; poo = ap2 Pair O O
  dSP : Tree ; dSP = encRefl (code O)

------------------------------------------------------------------------
-- 1. The f(O) exclusion principle
--
-- For iterate f init (where init = O):
-- checkProof2 on stuck var computes TreeEq(f(O), reify(xi)) at tree level.
-- If f(O) = xi at tree level: checkProof2 = false.
-- If f(O) ≠ xi at tree level: checkProof2 = true.
--
-- So the stuck-var test exactly detects: is f(O) = xi?

-- Compute f(O) for various step functions
fO : Fun1 -> Tree
fO f = geval fuel (mkAp1 (codeF1 f) (nd lf lf))  -- nd lf lf = code O

-- prepend0(O) = Pair(O, O)
fO_prep0 : Eq (fO prepend0) (nd lf lf)
fO_prep0 = refl

-- prepend1(O) = Pair(Pair(O,O), O)
fO_prep1 : Eq (fO prepend1) (nd (nd lf lf) lf)
fO_prep1 = refl

-- doubler(O) = Pair(O, O)
fO_doubler : Eq (fO (Comp2 Pair I I)) (nd lf lf)
fO_doubler = refl

-- swap(O) = Pair(Snd(O), Fst(O)) = Pair(O, O)
fO_swap : Eq (fO (Comp2 Pair Snd Fst)) (nd lf lf)
fO_swap = refl

------------------------------------------------------------------------
-- 2. The structural position principle
--
-- For iterate f init on Pair(v0,v1):
--   result = f(iterate f init v1) = f(rec(v1))
--
-- The oblivious invariant holds if there exists a position (path of
-- Fst/Snd projections) where:
--   (a) f ALWAYS produces a fixed value at that position, regardless of input
--   (b) xi has a DIFFERENT value at that position
--
-- For prepend0: f(x) = Pair(O, x). Position Fst: always O.
-- If xi has Fst ≠ O (e.g., xi1 = Pair(Pair(O,O), O)): oblivious. ✓
-- If xi has Fst = O (e.g., xi2 = Pair(O, Pair(O,O))): NOT oblivious. ✗
--
-- For prepend1: f(x) = Pair(Pair(O,O), x). Position Fst: always Pair(O,O).
-- If xi has Fst ≠ Pair(O,O): oblivious.
-- If xi has Fst = Pair(O,O) (e.g., xi1): NOT oblivious for step case.
-- But wait: xi1 = Pair(Pair(O,O), O). Fst(xi1) = Pair(O,O) = Fst(f(x)). Matches!
-- The TreeEq check at Fst would give "equal," falling through to Snd.
-- Snd(f(x)) = x, which varies. So no oblivious invariant at Snd.
-- But the FULL proof via Schema F works differently — the base case f(O) = xi1
-- means the program DOES output xi1. So the proof can't exist.
--
-- Summary: prepend1 outputs xi1 at clock 1 (f(O) = xi1). No invariant possible.

------------------------------------------------------------------------
-- 3. The xi construction for bounded programs
--
-- Given bound l on program code-size:
-- Let S = {f(O) | f is a Fun1 with codeSize(f) <= l} ∪ {O}
-- |S| <= C^l for some constant C (bounded by number of Fun1 codes of size l)
--
-- Choose xi ∉ S with treeSize(xi) > some threshold.
-- Also choose xi so that for EVERY f with codeSize(f) <= l,
-- there is a position where f(x) has a constant value differing from xi.
--
-- CLAIM: For any f built from {Pair, Fst, Snd, I, KT, Comp, Comp2, IfLf}
-- (no Rec in the step function), f(x) has a "constant skeleton":
-- some positions in f(x) are fixed constants, others depend on x.
-- If xi differs from f at a constant position, the invariant holds.
--
-- Example skeletons:
--   prepend0(x) = Pair(O, x):          skeleton = Pair(O, _)
--   prepend1(x) = Pair(Pair(O,O), x):  skeleton = Pair(Pair(O,O), _)
--   doubler(x) = Pair(x, x):           skeleton = Pair(_, _) (no constant!)
--   swap(x) = Pair(Snd(x), Fst(x)):    skeleton = Pair(_, _) (no constant!)
--
-- For doubler and swap: no position has a fixed value. But the RELATIONSHIP
-- between positions is fixed (both sides equal for doubler; swapped for swap).
-- This means xi with Fst ≠ Snd avoids doubler.
-- And xi with Fst ≠ Snd avoids swap (since swap(x) also has the property
-- that if input is "balanced," output is "balanced").

------------------------------------------------------------------------
-- 4. Concrete xi construction for l = 3

-- Programs of code-size <= 3:
-- I (size 1), Fst (size 1), Snd (size 1), KT O (size 2), KT(Pair(O,O)) (size 3)
-- Comp I I (size 3), Comp Fst I (size 3), etc.

-- f(O) values for these:
-- I: O = lf
-- Fst: Fst(O) = O = lf  (leftT lf = lf)
-- Snd: Snd(O) = O = lf
-- KT O: O = lf
-- KT(Pair(O,O)): Pair(O,O) = nd(lf,lf)
-- Comp I I: O = lf
-- Comp Fst I: Fst(O) = O = lf

-- Exclusion set for l=3: {lf, nd(lf,lf)} (just O and Pair(O,O))
-- Any xi ∉ {lf, nd(lf,lf)} works for the stuck-var test.

-- For the FULL oblivious invariant (step case too):
-- We need xi where the TreeEq short-circuits at a ground comparison.
-- xi = nd(nd lf lf) lf = Pair(Pair(O,O), O) works against prepend0
-- (Fst comparison: O vs Pair(O,O) → immediate mismatch).
-- xi = nd lf (nd(nd lf lf) lf) works against prepend1
-- (Fst comparison: Pair(O,O) vs O → immediate mismatch).
-- For doubler/swap: need xi with Fst ≠ Snd. Both xi candidates satisfy this.

------------------------------------------------------------------------
-- 5. Test: direct step-case verification via geval
--
-- For a TRUE oblivious invariant, we need the step case to hold.
-- The step case: TreeEq(f(rec(v1)), reify(xi)) = Pair(O,O) for all v1.
-- Since rec(v1) is arbitrary, this requires TreeEq(f(x), reify(xi)) = Pair(O,O) for all x.
-- Equivalently: f(x) ≠ xi for all x.
--
-- For iterate f init: f(x) ≠ xi for ALL x iff:
-- there is a Fst/Snd position where f ALWAYS puts a constant ≠ xi's value there.
--
-- We can test this by evaluating f on a few representative inputs:

-- Test f on O, Pair(O,O), Pair(Pair(O,O), O), tagVar
testF : Fun1 -> Tree -> Bool
testF f xiTree =
  let t0 = geval fuel (mkAp1 (codeF1 f) (nd lf lf))           -- f(O)
      t1 = geval fuel (mkAp1 (codeF1 f) (nd (nd lf lf) lf))   -- f(Pair(O,O))... wait, this is code not tree
  in boolAnd (treeEq (treeEqSem t0 xiTree) lf)   -- true iff f(O) = xi (BAD)
             true   -- placeholder

-- Actually, let's just verify concrete oblivious invariants directly.

-- VERIFIED: natCodeIter vs xi1 has a TRUE oblivious invariant
-- (the full equational proof exists in KRShortProof.agda).

-- QUESTION: does natCodeIter vs xi2 have a true invariant?
-- Step case: prepend0(rec(v1)) = Pair(O, rec(v1)).
-- TreeEq(Pair(O, rec(v1)), Pair(O, Pair(O,O))):
-- Fst: TreeEq(O, O) = O (equal).
-- Snd: TreeEq(rec(v1), Pair(O,O)) depends on rec(v1). NOT OBLIVIOUS.
-- So: NO true oblivious invariant. checkProof2 is wrong here (false positive).

-- QUESTION: does doubler vs xi1 have a true invariant?
-- Step case: Pair(rec(v1), rec(v1)).
-- TreeEq(Pair(rec(v1), rec(v1)), Pair(Pair(O,O), O)):
-- Fst: TreeEq(rec(v1), Pair(O,O)). Depends on rec(v1). NOT OBLIVIOUS at Fst.
-- But: if h(v1) = Pair(O,O) (by induction), then rec(v1) ≠ xi1.
-- This means rec(v1) has SOME difference from xi1.
-- However, the STEP CASE of Schema F doesn't get to use h(v1) = Pair(O,O)
-- directly — it must derive the step equation from the equational axioms.
-- For a constant step function s = Lift(KT(Pair(O,O))):
-- s(Pair(v0,v1), Pair(h(v0), h(v1))) = Pair(O,O).
-- We need h(Pair(v0,v1)) = Pair(O,O).
-- h(Pair(v0,v1)) = TreeEq(Pair(rec(v1), rec(v1)), Pair(Pair(O,O), O))
-- This is NOT derivable as a constant because rec(v1) is a free variable.
-- So: NOT OBLIVIOUS. The step case cannot be proved equationally
-- without knowing something about rec(v1).
--
-- CONCLUSION: For doubler, we need a NON-CONSTANT step function s
-- that uses h(v1) to derive h(Pair(v0,v1)). This is a BLevel ≥ 1 proof.
-- The oblivious (BLevel 0) approach only works when f has a constant position
-- that differs from xi.

------------------------------------------------------------------------
-- FINAL CHARACTERIZATION
--
-- A program "iterate f O" has an oblivious invariant against xi iff:
-- (a) f(O) ≠ xi  (necessary for the base case to work)
-- (b) There exists a position p (Fst/Snd path) such that:
--     - f(x)|_p is a constant c for all x (f "stamps" a fixed value there)
--     - c ≠ xi|_p (the constant differs from xi at that position)
--
-- When (a) and (b) hold:
-- - Base: TreeEq(O, xi) short-circuits (O is leaf, xi is non-leaf).
-- - Step: TreeEq(f(rec), xi) short-circuits at position p
--   (comparing c against xi|_p, both ground).
-- - Schema F gives h(v0) = Pair(O,O) for all v0.
-- - The proof is O(1) in size.
--
-- When (a) holds but (b) fails:
-- - The stuck-var test (checkProof2) may still pass (false positive).
-- - But the Schema F step case CANNOT be proved equationally with a constant s.
-- - A non-oblivious proof (BLevel ≥ 1) is needed.
--
-- For the KR argument:
-- Choose xi so that (a) and (b) hold for ALL programs of bounded size.
-- This requires xi ∉ {f(O) | small f} and xi to differ from every
-- small f's "constant skeleton" at some position.
-- The SKELETON of f is the set of positions with fixed values.
-- The ANTI-SKELETON of xi is the set of xi's positional values.
-- The condition is: for each small f, skeleton(f) ∩ anti-skeleton(xi) ≠ ∅
-- at a position where the values differ.
