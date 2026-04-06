{-# OPTIONS --safe --without-K --exact-split #-}

-- KR.agda
-- Kritchman-Raz approach to Godel II via the tree system.
--
-- Structure:
-- 1. Programs as Fun1 terms (iterate step init)
-- 2. "Program p outputs x at clock c" as equational derivability
-- 3. Kolmogorov complexity K(x) as infimum of program code sizes
-- 4. Tree counting (pigeonhole source)
-- 5. The KR argument: consistency -> exists uncomputably complex string
-- 6. Analysis: where the obstruction lives (contrast with diagonal)

module Guard.KR where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.Machine

------------------------------------------------------------------------
-- 1. "Program p outputs x at clock c" (object-level)
--
-- OutputsAt p c x means: there is a derivation of
--   ap1 p (reify(natCode c)) = reify(x)
-- in the equational system.

OutputsAt : Fun1 -> Nat -> Tree -> Equation -> Set
OutputsAt p c x hyp =
  Deriv hyp (eqn (ap1 p (reify (natCode c))) (reify x))

-- "Program p outputs x" = exists a clock c such that OutputsAt p c x
OutputsEv : Fun1 -> Tree -> Equation -> Set
OutputsEv p x hyp = Sigma Nat (\c -> OutputsAt p c x hyp)

-- "No program of size <= n outputs x" (for all programs and clocks)
-- This is the negation of: exists p with progSize p <= n, exists c, OutputsAt p c x
-- We express it as: for any f with small enough code, any clock fails.
NoSmallProg : Nat -> Tree -> Equation -> Set
NoSmallProg n x hyp =
  (p : Fun1) -> Leq (progSize p) n ->
  (c : Nat) -> Deriv hyp (eqn (ap1 p (reify (natCode c))) (reify x)) -> Empty

------------------------------------------------------------------------
-- 2. Kolmogorov complexity: K(x) > n means NoSmallProg n x

-- K(x) > n is precisely NoSmallProg n x
-- K is not computable, but "K(x) > n" is Pi-1:
--   for all p, for all c, if progSize(p) <= n then ap1 p (natCode c) =/= reify(x)

------------------------------------------------------------------------
-- 3. The incompressible string lemma (pigeonhole)
--
-- For the counting argument, we need:
--   numTrees(n) = number of distinct trees of treeSize exactly n
--
-- Binary trees with n nodes: Catalan number C_n ~ 4^n / n^{3/2}
-- Programs of code-size n: also trees, but a SUBSET of all trees
--   (only those parseable as valid codeF1 / iterate structures)
--
-- The key combinatorial fact:
--   For each n, there are at least 2^n trees of size <= 2n
--   But there are at most 2^n trees of size <= n
--   So some tree of size <= 2n cannot be output by any program of size <= n
--   (because programs of size <= n are trees of size <= n, so there are <= 2^n of them,
--    but they would need to cover all 2^{2n} possible outputs)
--
-- Actually the clean version: there are 2^{n+1} - 1 trees of size <= n
-- (binary trees), but this overcounts. The exact number doesn't matter;
-- what matters is that outputs can be any tree while programs are constrained.

-- Decidable propositions
data Dec (P : Set) : Set where
  yes : P -> Dec P
  no  : (P -> Empty) -> Dec P

-- Decidable equality on trees
ndInjL : {a1 a2 b1 b2 : Tree} -> Eq (nd a1 a2) (nd b1 b2) -> Eq a1 b1
ndInjL refl = refl

ndInjR : {a1 a2 b1 b2 : Tree} -> Eq (nd a1 a2) (nd b1 b2) -> Eq a2 b2
ndInjR refl = refl

treeEqDec : (a b : Tree) -> Dec (Eq a b)
treeEqDec lf lf = yes refl
treeEqDec lf (nd _ _) = no (\())
treeEqDec (nd _ _) lf = no (\())
treeEqDec (nd a1 a2) (nd b1 b2) = helper (treeEqDec a1 b1) (treeEqDec a2 b2)
  where
  helper : Dec (Eq a1 b1) -> Dec (Eq a2 b2) -> Dec (Eq (nd a1 a2) (nd b1 b2))
  helper (yes p1) (yes p2) = yes (eqCong2 nd p1 p2)
  helper (yes _)  (no q2)  = no (\e -> q2 (ndInjR e))
  helper (no q1)  _        = no (\e -> q1 (ndInjL e))

------------------------------------------------------------------------
-- 4. The Chaitin search program
--
-- For the KR argument, we construct a program C_l that:
--   (a) Enumerates proof-encoding trees t by size
--   (b) Runs thFun on each t to check if it encodes a valid proof
--   (c) Checks if the proved equation has the form "K(xi) > l"
--   (d) If found, outputs xi
--
-- The key observation (Leivant connection):
-- Step (b) is a BOUNDED computation — thFun is a tree recursion,
-- so running it on a tree of size s takes O(s) steps.
-- Step (c) is a tree comparison (finite, decidable).
-- The iteration (a) is: Rec over the enumeration clock.
--
-- C_l is itself a Fun1 (iterate searchStep searchInit).
-- Its code-size is FIXED (independent of l for l encoded as data, not code).
--
-- This is where the KR argument diverges from diagonal:
-- - Diagonal: needs evalCode (universal evaluator for ALL coded terms)
-- - KR: needs only thFun/thFunTFor (proof checker) + bounded search

------------------------------------------------------------------------
-- 5. What the system must prove internally
--
-- For the KR argument to work, the system must prove:
--
-- (A) Pigeonhole: "for each l, there exists xi with K(xi) > l"
--     This requires the system to count trees and programs.
--     In our system: this is a theorem about natCode/treeSize,
--     provable by induction on l.
--
-- (B) If consistent, the Chaitin search terminates:
--     "If Consistent(hyp), then for all l, exists c, C_l(c) = xi
--      where xi satisfies K(xi) > l"
--     This requires:
--     (i)  The system can verify its own proofs (thFunTFor correctness)
--     (ii) The system can verify that thFun correctly checks proofs
--     (iii) The system can internalize the pigeonhole argument
--
-- (C) C_l outputs xi, but |C_l| is fixed, contradicting K(xi) > l.

------------------------------------------------------------------------
-- 6. The obstruction (the sharp question from NEXT-SESSION-PROMPT)
--
-- In the diagonal proof (GodelII.agda), the obstruction is:
--   EvalOK — the side condition for evalCode correctness.
--   evalCode can only evaluate GROUND terms (no variables).
--   When ruleInst introduces variables, evalCode fails.
--   This manifests as: axFst/axSnd/axConst are excluded from WC0.
--
-- In the KR proof, the obstruction is DIFFERENT:
--
-- OBSTRUCTION 1: Computation bounds
--   The Chaitin search C_l must enumerate proofs up to some size bound.
--   "If consistent, the search terminates" requires:
--   For each l, there exists a SPECIFIC size bound B(l) such that
--   if a proof of "K(xi) > l" exists, one exists of size <= B(l).
--   This is the COMPUTATION BOUND side condition.
--   It replaces EvalOK.
--
-- OBSTRUCTION 2: Internalization of pigeonhole
--   The system must prove its own counting argument.
--   This requires internalizing treeSize, natCode enumeration,
--   and the pigeonhole principle as equational derivations.
--   The pigeonhole principle is: if f : {0,...,n} -> {0,...,m} with n > m,
--   then f is not injective.
--   In the tree system, this becomes a statement about Fun1 terms
--   applied to natCode values.
--
-- OBSTRUCTION 3: Fixed-point free
--   The key advantage of KR over diagonal: NO fixed point / diagonal lemma.
--   The self-reference in the diagonal proof (G says "I am not provable")
--   is replaced by the Chaitin machine (C_l says "find me an incompressible string").
--   This means substTFor and the variable-capture issues DON'T APPEAR.
--   The KR obstruction is purely about COMPUTATION BOUNDS.
--
-- Connection to BLevel:
--   In the WC hierarchy, BLevel counts the backtracking depth.
--   BLevel 0 = no ruleInst = no variables = ground computation only.
--   The diagonal proof needs BLevel >= 1 (for ruleInst in the Godel sentence).
--   The KR proof also needs BLevel >= 1, but for a different reason:
--   the pigeonhole argument uses induction (ruleF / Schema F),
--   which introduces variables.
--   The KR parameter delta (the incompressibility threshold) corresponds to
--   the proof-size bound B(l), which in turn bounds the BLevel.
--
-- Connection to Aschieri:
--   Aschieri's backtracking level counts how many times a realizer
--   "changes its mind" during proof normalization.
--   In the KR setting: the Chaitin search C_l "changes its mind"
--   each time it finds a candidate xi and then discovers a smaller program.
--   The backtracking level is bounded by the number of programs of size <= l,
--   which is finite. This gives a CONCRETE bound on the backtracking,
--   unlike the diagonal case where backtracking depends on proof structure.
--
-- CONCLUSION:
--   The Nelson-WC boundary looks DIFFERENT for KR than for diagonal.
--   - Diagonal: obstruction = evalCode (tag dispatch for variable-containing terms)
--   - KR: obstruction = computation bound (proof-size bound for pigeonhole)
--   - The KR obstruction is MORE NATURAL from a complexity perspective:
--     it's about "how long do you need to search?" rather than
--     "can you evaluate terms with free variables?"

------------------------------------------------------------------------
-- 7. Concrete ingredients for KR in the tree system
--
-- What would need to be built:

-- (a) natLeq as a Fun1: compare two natCode values
-- natLeq(natCode m, natCode n) = O if m <= n, Pair(O,O) otherwise
-- This is definable by Rec on the first argument.

natLeqStep : Fun2
natLeqStep = Fan
  (Lift (Comp Fst Snd))    -- extract (recL, recR) -> recL = result for m-1
  (Post Snd sndArg)         -- extract recs -> Snd(recs) = result for right subtree
  -- Actually: we compare by simultaneous recursion on both args.
  -- For natCode, simpler: natLeq = Rec (KT O) checkStep
  -- where checkStep looks at the second arg.
  Pair                       -- placeholder

-- For now, a metalevel version:
natLeqB : Nat -> Nat -> Bool
natLeqB zero    _ = true
natLeqB (suc _) zero = false
natLeqB (suc m) (suc n) = natLeqB m n

-- (b) Proof enumeration: enumerate all trees up to size n
-- This is tree recursion on the size bound.
-- Not built here — the point is that it's DEFINABLE.

-- (c) thFun check: given a tree, run thFun to check if it's a valid proof encoding
-- thFun is already defined in ThFun.agda as a metalevel function.
-- thFunTFor is the object-level version.
-- For KR we need: the system can prove "thFunTFor(t) = reify(codeEqn eq)"
-- This is exactly what ProofE / thm14E provides.

-- (d) Equation parsing: given the output of thFunTFor, check if it encodes "K(xi) > l"
-- This is a tree comparison: check if the equation has a specific form.
-- Definable by TreeEq + IfLf.

------------------------------------------------------------------------
-- 8. The key theorem (to be formalized)
--
-- KR-Godel-II: If the system proves its own consistency AND can internalize
-- the pigeonhole argument AND has computation bounds, then contradiction.
--
-- The computation-bound condition is:
--   CompBound : Nat -> Nat -> Set
--   CompBound l b = for all proofs d of size <= b,
--     if thFun(d) = codeEqn(eq) and eq has the form "K(xi) > l",
--     then C_l terminates within b steps and outputs xi.
--
-- This replaces the diagonal proof's condition:
--   ProofE : for each derivation, the proof encoding is well-formed.
--
-- The advantage: CompBound is about CONCRETE computation, not about
-- the algebraic structure of encoded proofs. This makes it potentially
-- easier to verify in bounded arithmetic.

-- Sketch of the formalized KR argument:
-- (Stated as a type; proof would be substantial)

KRGodelII : Set
KRGodelII =
  (hyp : Equation) ->
  -- System proves consistency
  Deriv hyp (eqn (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O)) ->
  -- System can count trees (pigeonhole)
  ((l : Nat) -> Sigma Tree (\xi -> NoSmallProg l xi hyp)) ->
  -- Chaitin machine terminates if consistent
  ((l : Nat) (xi : Tree) -> NoSmallProg l xi hyp ->
    Sigma Nat (\c -> Deriv hyp (eqn (ap1 (chaitinMachine l) (reify (natCode c))) (reify xi)))) ->
  -- Contradiction: chaitinMachine has fixed size, but outputs incompressible xi
  Empty
  where
  -- Placeholder: the actual Chaitin machine definition
  chaitinMachine : Nat -> Fun1
  chaitinMachine l = iterate I O   -- placeholder
