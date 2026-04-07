{-# OPTIONS --safe --without-K --exact-split #-}

-- ObliviousTest.agda
-- Testing oblivious invariants for various program types.
--
-- For each program p, we check whether
--   h = Comp2 TreeEq p (KT xiT)
-- with g = KT poo gives checkProof2(encF(codeF1 h, codeF1 g, ...)) = true.
--
-- If true: geval confirms h(stuck_var) = g(stuck_var) = Pair(O,O),
-- meaning p(t) /= xi for ALL trees t. This is the oblivious invariant.

module Guard.Nelson.ObliviousTest where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun
open import Guard.Nelson.Machine
open import Guard.Nelson.GroundEval

private
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero

------------------------------------------------------------------------
-- Target: xi = nd(nd lf lf) lf = Pair(Pair(O,O), O)
xi : Tree
xi = nd (nd lf lf) lf

xiT : Term
xiT = ap2 Pair poo O

------------------------------------------------------------------------
-- Dummy sub-proofs for Schema F encoding (checkProof2 ignores them)
dSP : Tree
dSP = encRefl (code O)

------------------------------------------------------------------------
-- Helper: build the Schema F test for a program p against xi
-- h = Comp2 TreeEq p (KT xiT), g = KT poo
-- Returns the encoded Schema F proof tree.

mkTest : Fun1 -> Tree
mkTest p =
  let h = Comp2 TreeEq p (KT xiT)
      g = KT poo
      sF = Lift (KT poo)
  in encF (codeF1 h) (codeF1 g) (code poo) (codeF2 sF) dSP dSP dSP dSP

------------------------------------------------------------------------
-- 1. natCodeIter (already proved in KRShortProof, verify here)

prog1 : Fun1
prog1 = iterate prepend0 O

test1 : Eq (checkProof2 (mkTest prog1)) true
test1 = refl

------------------------------------------------------------------------
-- 2. Constant function: KT O
-- Output is always O. TreeEq(O, xi) = Pair(O,O). Trivially oblivious.

prog2 : Fun1
prog2 = KT O

test2 : Eq (checkProof2 (mkTest prog2)) true
test2 = refl

------------------------------------------------------------------------
-- 3. Identity: I
-- I(t) = t. On stuck var: geval returns nd(tagVar, lf).
-- TreeEq(nd(tagVar, lf), xi)?
-- geval dispatches: both are nd nodes.
-- TreeEq(tagVar, Pair(O,O)) then TreeEq(lf, O).
-- tagVar = nd(nd(nd lf lf) lf) lf, Pair(O,O) = nd(nd lf lf)(nd lf lf)
-- These differ at first component: nd(nd lf lf) lf vs nd lf lf.
-- So TreeEq short-circuits. Oblivious.

prog3 : Fun1
prog3 = I

test3 : Eq (checkProof2 (mkTest prog3)) true
test3 = refl

------------------------------------------------------------------------
-- 4. Comp Fst I = Fst
-- Fst on stuck var: leftT(nd(tagVar, lf)) = tagVar.
-- Then code result is... geval on mkAp1(codeFst, var0C):
-- gevalAp1 with Fst tag: leftT(geval(var0C)) = leftT(nd(tagVar, lf)) = tagVar
-- So result = tagVar = nd(nd(nd lf lf) lf) lf.
-- TreeEq(tagVar, xi) = TreeEq(nd(nd(nd lf lf) lf) lf, nd(nd lf lf) lf)
-- First: TreeEq(nd(nd lf lf) lf, nd lf lf):
--   TreeEq(nd lf lf, lf) = Pair(O,O). So IfLf(Pair(O,O), ...) = second of pair = Pair(O,O).
-- Short-circuits at depth 2.

prog4 : Fun1
prog4 = Fst

test4 : Eq (checkProof2 (mkTest prog4)) true
test4 = refl

------------------------------------------------------------------------
-- 5. Comp-based: Comp Fst (Comp2 Pair I I)
-- This is Fst(Pair(x, x)) = x (on Pair inputs; identity).
-- But as a standalone Fun1 applied to stuck var:
-- Comp2 Pair I I (var0C) = Pair(var0C, var0C) ... but geval:
-- gevalAp1 with Comp2 tag: evaluates I(var0C) twice = nd(tagVar,lf) twice
-- Then Pair(nd(tagVar,lf), nd(tagVar,lf)) = nd(nd(tagVar,lf), nd(tagVar,lf))
-- Then Fst of that = nd(tagVar, lf). Same as I.
-- So TreeEq result same as test3.

prog5 : Fun1
prog5 = Comp Fst (Comp2 Pair I I)

test5 : Eq (checkProof2 (mkTest prog5)) true
test5 = refl

------------------------------------------------------------------------
-- 6. Doubler: iterate (Comp2 Pair I I) O
-- doubler^n(O): 0->O, 1->Pair(O,O), 2->Pair(Pair(O,O),Pair(O,O)), ...
-- On stuck var (geval recurses on tagVar structure):
-- tagVar = nd(nd(nd lf lf) lf) lf has depth 3.
-- Rec on this applies the step 3 times (3 nd nodes).

prog6 : Fun1
prog6 = iterate (Comp2 Pair I I) O

test6 : Eq (checkProof2 (mkTest prog6)) true
test6 = refl

------------------------------------------------------------------------
-- 7. Comp2-based: Comp2 Pair Snd Fst (swap)
-- iterate swap O:
-- On stuck var: Rec on tagVar structure.
-- swap(O) = Pair(Snd(O), Fst(O)) = Pair(lf, lf) = nd(lf, lf) = Pair(O,O)
-- In code: swap on lf gives nd(lf,lf).
-- swap(nd(a,b)) = nd(b, a). So it flips.
-- After recursion on tagVar: complex tree, but should differ from xi.

prog7 : Fun1
prog7 = iterate (Comp2 Pair Snd Fst) O

test7 : Eq (checkProof2 (mkTest prog7)) true
test7 = refl

------------------------------------------------------------------------
-- 8. Rec-based (non-iterate): direct Rec with custom step
-- treeFlip: swap every pair's children
-- treeFlip(O) = O
-- treeFlip(Pair(a,b)) = Pair(treeFlip(b), treeFlip(a))
-- Step: s(orig, Pair(recL, recR)) = Pair(recR, recL)
-- s = Fan Const (Lift Snd) Pair ... no.
-- s(x, y) where x = orig, y = Pair(recL, recR)
-- We want Pair(Snd(y), Fst(y)) = Pair(recR, recL)
-- s = Comp2 Pair (Lift Snd) (Lift Fst)
--   Lift Snd (x, y) = Snd(x). No, Lift f (x, y) = f(x).
-- We want f(x, y) = Pair(Snd(y), Fst(y)).
-- Post (Comp2 Pair Snd Fst) Pair ... no.
-- Fan takes (h1 h2 h)(x, y) = h(h1(x,y), h2(x,y)).
-- We want Pair(Snd(y), Fst(y)).
-- Post Snd Pair (x, y) = Snd(Pair(x, y)) = y. So Post Snd Pair = sndArg.
-- Lift Snd (x, y) = Snd(x).
-- Lift Fst (x, y) = Fst(x).
-- Post Snd sndArg (x, y) = Snd(sndArg(x, y)) = Snd(y).
-- Post Fst sndArg (x, y) = Fst(sndArg(x, y)) = Fst(y).
-- Fan (Post Snd sndArg) (Post Fst sndArg) Pair (x, y)
--   = Pair(Snd(y), Fst(y)). Yes!

treeFlipStep : Fun2
treeFlipStep = Fan (Post Snd sndArg) (Post Fst sndArg) Pair

treeFlip : Fun1
treeFlip = Rec O treeFlipStep

prog8 : Fun1
prog8 = treeFlip

test8 : Eq (checkProof2 (mkTest prog8)) true
test8 = refl

------------------------------------------------------------------------
-- 9. Iterate prepend1 O (codes with 1-bits)
-- prepend1 x = Pair(Pair(O,O), x)
-- Output on natCode n: 0->O, 1->Pair(Pair(O,O), O), 2->Pair(Pair(O,O), Pair(Pair(O,O), O)), ...
-- Note: output at n=1 IS xi = Pair(Pair(O,O), O)!
-- So this program DOES output xi. The oblivious invariant should FAIL.

prog9 : Fun1
prog9 = iterate prepend1 O

-- This should be false (program outputs xi at n=1).
-- Let's check what happens:
-- geval on h(var0C) where h = Comp2 TreeEq (iterate prepend1 O) (KT xiT)
-- geval recurses on tagVar structure with iterate prepend1 O
-- The output may or may not equal geval on g(var0C) = Pair(O,O)

-- test9 : Eq (checkProof2 (mkTest prog9)) true
-- test9 = refl    -- EXPECTED TO FAIL if geval correctly identifies the issue

-- Let's check if it's false:
test9f : Eq (checkProof2 (mkTest prog9)) false
test9f = refl

------------------------------------------------------------------------
-- 10. Constant function: KT xi (always outputs xi)
-- Obviously should fail the invariant.

prog10 : Fun1
prog10 = KT (reify xi)

test10f : Eq (checkProof2 (mkTest prog10)) false
test10f = refl

------------------------------------------------------------------------
-- SUMMARY (to be verified by Agda)
--
-- Programs with oblivious invariant against xi:
--   1. natCodeIter (iterate prepend0 O)     -- prepend0 puts O on left, xi has Pair(O,O) on left
--   2. KT O (constant O)                     -- trivially different
--   3. I (identity)                           -- stuck var structure differs from xi
--   4. Fst                                    -- extracts left child, differs
--   5. Comp Fst (Comp2 Pair I I)             -- reduces to identity
--   6. iterate doubler O                      -- doubler produces symmetric trees
--   7. iterate swap O                         -- swap produces permuted trees
--   8. treeFlip (Rec-based, non-iterate)     -- flip produces reversed trees
--
-- Programs WITHOUT oblivious invariant against xi:
--   9. iterate prepend1 O                    -- OUTPUTS xi at clock 1!
--  10. KT xi (constant xi)                   -- always outputs xi
--
-- Key observation: programs that CAN output xi fail (as they should).
-- Programs that CANNOT output xi pass. The oblivious invariant detects
-- this because geval on the stuck variable produces a specific tree
-- that happens to disagree with xi.
--
-- The deeper question: can we CHOOSE xi so that ALL programs of
-- bounded size have an oblivious invariant against xi?
-- Program 9 shows that xi must not be in the image of any program.
-- But iterate prepend1 O outputs nd(nd lf lf) lf at clock 1.
-- So if we want to exclude iterate prepend1: choose a different xi!
