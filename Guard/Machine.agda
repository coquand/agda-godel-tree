{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Machine where

open import Guard.Base
open import Guard.Term
open import Guard.Step

------------------------------------------------------------------------
-- Leivant register machines in the tree system
--
-- Binary strings:  lf = empty,  nd b rest  where b in {lf, nd lf lf}
-- Registers: tuple of trees (nested pairs)
-- One-step function: Fun1 built from Pair/Fst/Snd/IfLf/KT/Comp/Comp2
--   (NO Rec -- this is the key Leivant property)
-- Multi-step: Rec applied to one-step via natCode clock
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Binary string constants

bit0 : Tree
bit0 = lf

bit1 : Tree
bit1 = nd lf lf

-- Bit terms
tBit0 : Term
tBit0 = O

tBit1 : Term
tBit1 = ap2 Pair O O

------------------------------------------------------------------------
-- 2. String operations as Fun1 (Rec-free)

-- prepend0 x = nd(lf, x) = Pair(O, x)
prepend0 : Fun1
prepend0 = Comp2 Pair (KT O) I

-- prepend1 x = nd(nd(lf,lf), x) = Pair(Pair(O,O), x)
prepend1 : Fun1
prepend1 = Comp2 Pair (KT (ap2 Pair O O)) I

-- tail (predecessor): nd(b, rest) -> rest, lf -> lf
-- tail = Snd (works on nd nodes; on lf, Snd(lf) = lf by rightT)
-- But in the equational system, Snd is only defined on Pair terms.
-- For the equational system: we use IfLf to handle the lf case.
-- tailSafe x = IfLf(x, Pair(Snd(x), O))
--   if x = lf: returns lf (first branch)
--   if x = nd(a,b): returns Snd(Pair(Snd(x), O)) = O ... no.
-- Actually: IfLf(x, Pair(anything, Snd(x)))
--   if x = O: returns first of pair = anything
--   if x = Pair(a,b): returns second = Snd(x)
-- We want: if x = O then O else Snd(x)
-- tailSafe = Comp2 IfLf I (Comp2 Pair (KT O) Snd)
--   IfLf(I(x), Pair(KT(O)(x), Snd(x)))
--   = IfLf(x, Pair(O, Snd(x)))
--   if x = O: returns O (first element)
--   if x = Pair(a,b): returns Snd(x) = b  (second element)

tailSafe : Fun1
tailSafe = Comp2 IfLf I (Comp2 Pair (KT O) Snd)

-- head: nd(b, rest) -> b, lf -> lf
-- headSafe = Comp2 IfLf I (Comp2 Pair (KT O) Fst)
--   if x = O: returns O
--   if x = Pair(a,b): returns Fst(x) = a

headSafe : Fun1
headSafe = Comp2 IfLf I (Comp2 Pair (KT O) Fst)

------------------------------------------------------------------------
-- 3. Correctness of string operations (equational proofs)

-- prepend0 reduces correctly
prep0Red : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 prepend0 t) (ap2 Pair O t))
prep0Red t =
  ruleTrans (axComp2 Pair (KT O) I t)
    (ruleTrans (congL Pair (ap1 I t) (axKT O t))
      (congR Pair O (axI t)))

-- prepend1 reduces correctly
prep1Red : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 prepend1 t) (ap2 Pair (ap2 Pair O O) t))
prep1Red t =
  ruleTrans (axComp2 Pair (KT (ap2 Pair O O)) I t)
    (ruleTrans (congL Pair (ap1 I t) (axKT (ap2 Pair O O) t))
      (congR Pair (ap2 Pair O O) (axI t)))

-- tailSafe on O
tailLf : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 tailSafe O) O)
tailLf =
  ruleTrans (axComp2 IfLf I (Comp2 Pair (KT O) Snd) O)
    (ruleTrans
      (congL IfLf
        (ap1 (Comp2 Pair (KT O) Snd) O) (axI O))
      (ruleTrans
        (congR IfLf O (axComp2 Pair (KT O) Snd O))
        (ruleTrans
          (congR IfLf O (congL Pair (ap1 Snd O) (axKT O O)))
          (axIfLfL O (ap1 Snd O)))))

-- tailSafe on Pair(a, b)
tailNd : {hyp : Equation} (a b : Term) ->
  Deriv hyp (eqn (ap1 tailSafe (ap2 Pair a b)) b)
tailNd a b =
  ruleTrans (axComp2 IfLf I (Comp2 Pair (KT O) Snd) (ap2 Pair a b))
    (ruleTrans
      (congL IfLf
        (ap1 (Comp2 Pair (KT O) Snd) (ap2 Pair a b))
        (axI (ap2 Pair a b)))
      (ruleTrans
        (congR IfLf (ap2 Pair a b)
          (axComp2 Pair (KT O) Snd (ap2 Pair a b)))
        (ruleTrans
          (congR IfLf (ap2 Pair a b)
            (congL Pair (ap1 Snd (ap2 Pair a b)) (axKT O (ap2 Pair a b))))
          (ruleTrans
            (congR IfLf (ap2 Pair a b)
              (congR Pair O (axSnd a b)))
            (axIfLfN a b O b)))))

-- headSafe on O
headLf : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 headSafe O) O)
headLf =
  ruleTrans (axComp2 IfLf I (Comp2 Pair (KT O) Fst) O)
    (ruleTrans
      (congL IfLf
        (ap1 (Comp2 Pair (KT O) Fst) O) (axI O))
      (ruleTrans
        (congR IfLf O (axComp2 Pair (KT O) Fst O))
        (ruleTrans
          (congR IfLf O (congL Pair (ap1 Fst O) (axKT O O)))
          (axIfLfL O (ap1 Fst O)))))

-- headSafe on Pair(a, b)
headNd : {hyp : Equation} (a b : Term) ->
  Deriv hyp (eqn (ap1 headSafe (ap2 Pair a b)) a)
headNd a b =
  ruleTrans (axComp2 IfLf I (Comp2 Pair (KT O) Fst) (ap2 Pair a b))
    (ruleTrans
      (congL IfLf
        (ap1 (Comp2 Pair (KT O) Fst) (ap2 Pair a b))
        (axI (ap2 Pair a b)))
      (ruleTrans
        (congR IfLf (ap2 Pair a b)
          (axComp2 Pair (KT O) Fst (ap2 Pair a b)))
        (ruleTrans
          (congR IfLf (ap2 Pair a b)
            (congL Pair (ap1 Fst (ap2 Pair a b)) (axKT O (ap2 Pair a b))))
          (ruleTrans
            (congR IfLf (ap2 Pair a b)
              (congR Pair O (axFst a b)))
            (axIfLfN a b O a)))))

------------------------------------------------------------------------
-- 4. Iteration combinator
--
-- iterate f init n  =  f^n(init)
--
-- Key idea: Rec on natCode n iterates.
--   natCode 0 = lf
--   natCode (suc n) = nd lf (natCode n)
--
-- Rec init step (natCode 0) = init
-- Rec init step (natCode (suc n))
--   = step (nd lf (natCode n)) (Pair (Rec init step lf) (Rec init step (natCode n)))
--   = step (nd lf (natCode n)) (Pair init (f^n(init)))
--
-- We want step to extract Snd of the pair (= previous result) and apply f.
-- sndArg(a, b) = b  is  Post Snd Pair
-- So: step = Post f (Post Snd Pair)

-- Extract second argument of a Fun2: (a, b) -> b
sndArg : Fun2
sndArg = Post Snd Pair

-- Iteration step: ignores orig, applies f to Snd of recursive-results pair
-- The Rec step receives (orig, Pair(recL, recR)).
-- We want f(recR) = f(Snd(sndArg(orig, pair))).
iterStep : Fun1 -> Fun2
iterStep f = Post f (Post Snd sndArg)

-- The iteration functor: ap1 (iterate f init) (natCode n) = f^n(init)
iterate : Fun1 -> Term -> Fun1
iterate f init = Rec init (iterStep f)

------------------------------------------------------------------------
-- 5. Iteration correctness

-- Base case: iterate f init on O = init
iterBase : {hyp : Equation} (f : Fun1) (init : Term) ->
  Deriv hyp (eqn (ap1 (iterate f init) O) init)
iterBase f init = axRecLf init (iterStep f)

-- sndArg reduces: sndArg(a, Pair(b, c)) = Pair(b, c)
-- Actually: sndArg(a, x) = x  for any x
-- Post Snd Pair (a, x) = Snd(Pair(a, x)) = x
sndArgRed : {hyp : Equation} (a x : Term) ->
  Deriv hyp (eqn (ap2 sndArg a x) x)
sndArgRed a x =
  ruleTrans (axPost Snd Pair a x)
    (axSnd a x)

-- iterStep reduces: iterStep f (a, x) = f(Snd(x))
-- Post f (Post Snd sndArg) (a, x)
--   = f(Post Snd sndArg (a, x))   by axPost
--   = f(Snd(sndArg(a, x)))        by axPost
--   = f(Snd(x))                   by sndArgRed
iterStepRed : {hyp : Equation} (f : Fun1) (a x : Term) ->
  Deriv hyp (eqn (ap2 (iterStep f) a x) (ap1 f (ap1 Snd x)))
iterStepRed f a x =
  ruleTrans (axPost f (Post Snd sndArg) a x)
    (cong1 f (ruleTrans (axPost Snd sndArg a x)
      (cong1 Snd (sndArgRed a x))))

-- Step case: iterate f init on Pair(a, b) applies step to recursive results
-- iterate f init (Pair(a,b))
--   = iterStep f (Pair(a,b)) (Pair(rec(a), rec(b)))
--   = f(Snd(Pair(rec(a), rec(b))))
--   = f(rec(b))
iterNd : {hyp : Equation} (f : Fun1) (init : Term) (a b : Term) ->
  Deriv hyp (eqn (ap1 (iterate f init) (ap2 Pair a b))
                 (ap1 f (ap1 (iterate f init) b)))
iterNd f init a b =
  ruleTrans (axRecNd init (iterStep f) a b)
    (ruleTrans
      (iterStepRed f (ap2 Pair a b)
        (ap2 Pair (ap1 (iterate f init) a) (ap1 (iterate f init) b)))
      (cong1 f (axSnd (ap1 (iterate f init) a) (ap1 (iterate f init) b))))

-- Corollary for natCode: iterate on natCode (suc n)
-- natCode (suc n) = nd lf (natCode n) = Pair(O, natCode_n)
-- So iterate f init (natCode(suc n)) = f(iterate f init (natCode n))
iterSuc : {hyp : Equation} (f : Fun1) (init : Term) (n : Nat) ->
  Deriv hyp (eqn (ap1 (iterate f init) (reify (natCode (suc n))))
                 (ap1 f (ap1 (iterate f init) (reify (natCode n)))))
iterSuc f init n =
  iterNd f init (reify (natCode zero)) (reify (natCode n))

------------------------------------------------------------------------
-- 6. Program model
--
-- A "program" is a Fun1 of the form:  iterate stepFun init
-- where stepFun is Rec-free (uses only Pair, Fst, Snd, IfLf, KT, Comp, Comp2, Fan, etc.)
--
-- The program's output on clock c is:  ap1 prog (reify (natCode c))
-- The program's code-size is:  treeSize (codeF1 prog)

-- Addition on Nat
natAdd : Nat -> Nat -> Nat
natAdd zero    m = m
natAdd (suc n) m = suc (natAdd n m)

-- Tree size (number of nd nodes)
treeSize : Tree -> Nat
treeSize lf       = zero
treeSize (nd a b) = suc (natAdd (treeSize a) (treeSize b))

-- Program size = code size
progSize : Fun1 -> Nat
progSize f = treeSize (codeF1 f)

-- "Program f outputs x at clock c" (metalevel)
Outputs : Fun1 -> Nat -> Tree -> Set
Outputs f c x = Eq (treeSize (codeF1 f)) (treeSize (codeF1 f))
-- placeholder; the real notion is equational derivability

------------------------------------------------------------------------
-- 7. Counting: number of trees of bounded size
--
-- For Kolmogorov complexity / pigeonhole, we need:
--   numTrees(n) = number of distinct trees of size <= n
--   numProgs(n) = number of distinct trees (codes) of size <= n
-- Both are bounded by 2^(2n+1) (Catalan-like), but we only need:
--   numProgs(n) < numTrees(2n) for large enough n
-- (there are more possible outputs than programs of a given size)

-- List of all trees of exactly size n (metalevel)
data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

listLen : {A : Set} -> List A -> Nat
listLen nil        = zero
listLen (cons _ t) = suc (listLen t)

append : {A : Set} -> List A -> List A -> List A
append nil        ys = ys
append (cons x t) ys = cons x (append t ys)

-- All trees of size exactly n
treesOfSize : Nat -> List Tree
treesOfSize zero = cons lf nil
treesOfSize (suc n) = treesOfSizeAux n n
  where
  -- Pair all trees of size i with trees of size (n - i)
  -- treesOfSizeAux i j generates nd nodes where left has size i, right has size j
  -- (simplified: just the structure, actual enumeration would be more involved)
  treesOfSizeAux : Nat -> Nat -> List Tree
  treesOfSizeAux zero    j = nil
  treesOfSizeAux (suc i) j = treesOfSizeAux i j

------------------------------------------------------------------------
-- 8. Kolmogorov complexity (metalevel definition)
--
-- K(x) = min { progSize(f) | exists c. ap1 f (reify(natCode c)) evaluates to reify(x) }
--
-- The key property: K is NOT computable, but for each specific x,
-- the fact "K(x) > n" is expressible (as: no program of size <= n outputs x).

-- "No program of code-size <= n outputs x" is a Pi-1 statement:
--   forall f. progSize(f) <= n -> forall c. ap1 f (natCode c) =/= reify(x)
-- This is expressible because progSize is decidable and inequality is decidable.

------------------------------------------------------------------------
-- 9. The KR argument structure (informal, to be formalized)
--
-- Theorem (Kritchman-Raz, via Leivant machines):
--   If the system is consistent, then for each l there exists x with K(x) > l.
--
-- Proof sketch:
-- (a) There are >= 2^l distinct trees of size <= l  (pigeonhole source)
-- (b) There are < 2^l programs of code-size <= l    (pigeonhole target)
-- (c) By pigeonhole: some tree of size <= l is not output by any program of size <= l
-- (d) Call this tree xi. Then K(xi) > l.
-- (e) The search for xi is itself a program (the "Chaitin machine")
-- (f) If the system proves its own consistency, the Chaitin machine terminates
-- (g) But then K(xi) <= size of Chaitin machine, contradiction for large l
--
-- The obstruction: step (f) requires that "consistency implies termination"
-- is provable WITHIN the system. This is where the new side condition appears.

------------------------------------------------------------------------
-- 10. Example: a concrete Leivant machine
--
-- Copy machine: given input in register 1, copies it to register 2
-- State = Pair(r1, r2)
-- Step:
--   if r1 = O then halt (identity)
--   if head(r1) = O then (tail(r1), prepend0(r2))
--   if head(r1) = 1 then (tail(r1), prepend1(r2))

-- Extract register 1 from state Pair(r1, r2)
getReg1 : Fun1
getReg1 = Fst

-- Extract register 2 from state Pair(r1, r2)
getReg2 : Fun1
getReg2 = Snd

-- Update register 1: state -> Pair(new_r1, r2)
setReg1 : Fun1 -> Fun1
setReg1 f = Comp2 Pair f Snd

-- Update register 2: state -> Pair(r1, new_r2)
setReg2 : Fun1 -> Fun1
setReg2 f = Comp2 Pair Fst f

-- The copy step function (Rec-free!)
-- copyStep(state) =
--   IfLf(Fst(state),                     -- is r1 empty?
--     Pair(O,                             -- if empty: halt, return (O, r2)
--       IfLf(Fst(Fst(state)),             -- head of r1 = O?
--         Pair(Snd(Fst(state)),           -- yes: (tail(r1), prepend0(r2))
--              Pair(O, Snd(state))),
--         Pair(Snd(Fst(state)),           -- no: (tail(r1), prepend1(r2))
--              Pair(Pair(O,O), Snd(state))))))

-- Simplified version using our combinators:
-- First: isEmptyR1 = Comp2 IfLf Fst (...)

-- Identity on state (halt)
haltF : Fun1
haltF = I

-- For the non-empty case: dispatch on head bit
-- We use nested IfLf. The outer IfLf checks if r1 is empty.
-- The inner IfLf checks the head bit.

-- copyStepInner: when r1 = Pair(bit, rest)
-- result = Pair(rest, Pair(bit, r2))
-- This prepends the head of r1 to r2 and advances r1
-- = Pair(Snd(Fst(state)), Pair(Fst(Fst(state)), Snd(state)))

-- copyStepInner = Comp2 Pair (Comp Snd Fst) (Comp2 Pair (Comp Fst Fst) Snd)

copyStepInner : Fun1
copyStepInner = Comp2 Pair (Comp Snd Fst) (Comp2 Pair (Comp Fst Fst) Snd)

-- copyStep: dispatch on whether r1 is empty
-- copyStep(state) = IfLf(Fst(state), Pair(state, copyStepInner(state)))
--   if Fst(state) = O: return first element = state (halt)
--   if Fst(state) = Pair(a,b): return second = copyStepInner(state)

copyStep : Fun1
copyStep = Comp2 IfLf Fst (Comp2 Pair I copyStepInner)

-- The copy program: iterate copyStep, initial state = Pair(input, O)
-- To make it a Fun1 from input to output:
-- copyProg(clock)(input) isn't quite right -- we need to fix input first.
-- A program takes a clock and produces output.
-- For a specific input x: copyProgX = iterate copyStep (Pair(reify x, O))
-- Output = Snd of final state

------------------------------------------------------------------------
-- 11. Correctness of copyStep

-- When r1 is empty: copyStep(Pair(O, r2)) = Pair(O, r2)
copyStepHalt : {hyp : Equation} (r2 : Term) ->
  Deriv hyp (eqn (ap1 copyStep (ap2 Pair O r2)) (ap2 Pair O r2))
copyStepHalt r2 =
  ruleTrans (axComp2 IfLf Fst (Comp2 Pair I copyStepInner) (ap2 Pair O r2))
    (ruleTrans
      (congL IfLf
        (ap1 (Comp2 Pair I copyStepInner) (ap2 Pair O r2))
        (axFst O r2))
      (ruleTrans
        (congR IfLf O
          (axComp2 Pair I copyStepInner (ap2 Pair O r2)))
        (ruleTrans
          (congR IfLf O
            (congL Pair
              (ap1 copyStepInner (ap2 Pair O r2))
              (axI (ap2 Pair O r2))))
          (axIfLfL (ap2 Pair O r2)
            (ap1 copyStepInner (ap2 Pair O r2))))))

-- When r1 = Pair(bit, rest):
-- copyStep(Pair(Pair(bit, rest), r2)) = copyStepInner(Pair(Pair(bit,rest), r2))
-- = Pair(Snd(Fst(state)), Pair(Fst(Fst(state)), Snd(state)))
-- = Pair(rest, Pair(bit, r2))

copyStepInnerRed : {hyp : Equation} (bit rest r2 : Term) ->
  Deriv hyp (eqn (ap1 copyStepInner (ap2 Pair (ap2 Pair bit rest) r2))
                 (ap2 Pair rest (ap2 Pair bit r2)))
copyStepInnerRed bit rest r2 =
  ruleTrans
    (axComp2 Pair (Comp Snd Fst) (Comp2 Pair (Comp Fst Fst) Snd)
      (ap2 Pair (ap2 Pair bit rest) r2))
    (ruleTrans
      (congL Pair
        (ap1 (Comp2 Pair (Comp Fst Fst) Snd) (ap2 Pair (ap2 Pair bit rest) r2))
        (ruleTrans (axComp Snd Fst (ap2 Pair (ap2 Pair bit rest) r2))
          (cong1 Snd (axFst (ap2 Pair bit rest) r2))))
      (ruleTrans
        (congL Pair
          (ap1 (Comp2 Pair (Comp Fst Fst) Snd) (ap2 Pair (ap2 Pair bit rest) r2))
          (axSnd bit rest))
        (congR Pair rest
          (ruleTrans
            (axComp2 Pair (Comp Fst Fst) Snd (ap2 Pair (ap2 Pair bit rest) r2))
            (ruleTrans
              (congL Pair
                (ap1 Snd (ap2 Pair (ap2 Pair bit rest) r2))
                (ruleTrans (axComp Fst Fst (ap2 Pair (ap2 Pair bit rest) r2))
                  (cong1 Fst (axFst (ap2 Pair bit rest) r2))))
              (ruleTrans
                (congL Pair
                  (ap1 Snd (ap2 Pair (ap2 Pair bit rest) r2))
                  (axFst bit rest))
                (congR Pair bit (axSnd (ap2 Pair bit rest) r2))))))))

copyStepAdvance : {hyp : Equation} (bit rest r2 : Term) ->
  Deriv hyp (eqn (ap1 copyStep (ap2 Pair (ap2 Pair bit rest) r2))
                 (ap2 Pair rest (ap2 Pair bit r2)))
copyStepAdvance bit rest r2 =
  ruleTrans (axComp2 IfLf Fst (Comp2 Pair I copyStepInner)
    (ap2 Pair (ap2 Pair bit rest) r2))
    (ruleTrans
      (congL IfLf
        (ap1 (Comp2 Pair I copyStepInner) (ap2 Pair (ap2 Pair bit rest) r2))
        (axFst (ap2 Pair bit rest) r2))
      (ruleTrans
        (congR IfLf (ap2 Pair bit rest)
          (axComp2 Pair I copyStepInner (ap2 Pair (ap2 Pair bit rest) r2)))
        (ruleTrans
          (congR IfLf (ap2 Pair bit rest)
            (congL Pair
              (ap1 copyStepInner (ap2 Pair (ap2 Pair bit rest) r2))
              (axI (ap2 Pair (ap2 Pair bit rest) r2))))
          (ruleTrans
            (axIfLfN bit rest
              (ap2 Pair (ap2 Pair bit rest) r2)
              (ap1 copyStepInner (ap2 Pair (ap2 Pair bit rest) r2)))
            (copyStepInnerRed bit rest r2)))))

------------------------------------------------------------------------
-- 12. Tree size in the system
--
-- treeSize as a Fun1 using Rec:
--   treeSize(lf) = O
--   treeSize(nd a b) = Pair(O, Pair(treeSize a, treeSize b))
-- Wait -- we need addition. natCode uses lf/nd lf encoding.
-- treeSize : Tree -> Nat-as-Tree
--
-- Actually simpler: count = Rec O (Post (Comp prepend0 I) sndArg)
-- No, let's use natAdd:
--   natAdd = Rec I (Lift prepend0)
--   natAdd(O, n) = n
--   natAdd(Pair(a,b), n) = prepend0(natAdd(a, n)) ... no this doesn't add.
--
-- For the counting argument, we work at the metalevel (Agda Nat).
-- The object-level formalization of "size" can come later.

------------------------------------------------------------------------
-- 13. Comparison: Less-than on Nat

data Leq : Nat -> Nat -> Set where
  leqZ : (n : Nat) -> Leq zero n
  leqS : {m n : Nat} -> Leq m n -> Leq (suc m) (suc n)

data Lt : Nat -> Nat -> Set where
  ltBase : (n : Nat) -> Lt n (suc n)
  ltStep : {m n : Nat} -> Lt m n -> Lt m (suc n)

------------------------------------------------------------------------
-- 14. Pigeonhole (metalevel)
--
-- For the KR argument we need:
--   "There exist more trees of size <= n than Fun1 codes of size <= n
--    for large enough n"
--
-- This is a counting argument. The number of binary trees with n nodes
-- is the Catalan number C_n. Programs are ALSO trees (their codes),
-- but with additional structure (they must be valid codeF1 trees).
-- So the set of programs of size <= n is a SUBSET of all trees of size <= n.
-- But program OUTPUTS can be ANY tree. So for large n:
--   #{outputs} > #{programs of size <= n}
--
-- The pigeonhole principle:
--   If f : A -> B is injective and |A| > |B|, then f is not surjective.
--   Equivalently: if |A| > |B|, there exists a in A not in image(f).

------------------------------------------------------------------------
-- 15. The Chaitin machine (sketch)
--
-- ChaitinMachine(l) does:
--   For each proof d in the system (enumerated by size):
--     Check if d proves "K(xi) > l" for some xi
--     If so: find the program p of size <= l that outputs xi (must exist
--            if the system is consistent -- wait, this is backwards)
--
-- Actually the KR argument is:
--   ChaitinMachine(l) searches for a PROOF of "there exists xi with K(xi) > l"
--   Once found, it extracts xi from the proof
--   Then xi is a specific tree, and ChaitinMachine(l) outputs xi
--   But ChaitinMachine itself has fixed code-size (independent of l for large l)
--   So for large enough l, progSize(ChaitinMachine) < l
--   Then K(xi) <= progSize(ChaitinMachine) < l, contradicting K(xi) > l
--
-- The issue: the search terminates only if the system can PROVE "exists xi. K(xi) > l"
-- This requires:
--   (a) The system can formalize the pigeonhole argument (counting)
--   (b) The system can verify that specific programs don't output specific trees
--       (this requires BOUNDED computation -- running programs for all clocks up to
--        some bound, or proving non-termination)
--
-- THIS is where the new obstruction lives:
-- The diagonal proof needs evalCode (universal evaluation).
-- The KR proof needs BOUNDED computation verification:
--   "program p with clock c does not output x"
-- This is a DECIDABLE statement (just run the computation).
-- But proving it IN THE SYSTEM requires the system to internalize
-- bounded computation -- which is exactly what iterStep + Rec gives us!
-- The side condition is now about COMPUTATION BOUNDS rather than tag dispatch.
