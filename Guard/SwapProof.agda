{-# OPTIONS --safe --without-K --exact-split #-}

-- SwapProof.agda
-- Case 4 test: step function where g and h project DIFFERENTLY.
--
-- safeSwap(x) = IfLf(x, Pair(Snd(x), Fst(x)))
--   O           -> O  (first element of Pair(Snd(x), Fst(x)) when x = O: wait, axIfLfL)
--   Pair(a, b)  -> Pair(b, a)  (by axIfLfN)
--
-- iterate safeSwap O:
--   natCode 0 = O -> O
--   natCode 1 = Pair(O, O) -> safeSwap(O) = O (by iterNd: applies to rec(v1))
--   Wait: iterate safeSwap O (Pair(v0,v1)) = safeSwap(rec(v1)).
--   rec(lf) = O. safeSwap(O) = O.
--   So iterate safeSwap O on natCode n: always O for n >= 0.
--   Because rec(rightChild) = rec(lf) = O at every step, and safeSwap(O) = O.
--
-- That's trivial — output is always O. Let me make it more interesting.
--
-- Better: use a non-trivial initial value.
-- Or: compose swap with something that builds pairs.
--
-- Actually the interesting Case 4 is: step function = Comp2 Pair Snd Fst
-- applied directly (not iterated from O). Let me reconsider.
--
-- The REAL question: for iterate programs starting from O, the Rec
-- structure means rec(lf) = O at every base case. So the iterate
-- always produces step^n(O) on natCode n. For safeSwap: step^n(O) cycles:
-- 0 -> O, 1 -> safeSwap(O) = O, so it's stuck at O.
--
-- For UNsafe swap (Comp2 Pair Snd Fst): step^n(O) is equationally stuck
-- at n=1 because Snd(O) and Fst(O) are undefined.
--
-- So swap-iterate is not a good test case. Let me find a REAL Case 4:
-- a step function where both Fst and Snd of the output depend on the input
-- in DIFFERENT ways, and the iterate produces non-trivial outputs.
--
-- Example: rotate(x) = Pair(Snd(x), Pair(O, Fst(x)))
-- rotate(Pair(a,b)) = Pair(b, Pair(O, a))
-- Pushes Fst to deep right, brings Snd to top.
-- rotate(O) is stuck. Use safe version:
-- safeRotate(x) = IfLf(x, Pair(Snd(x), Pair(O, Fst(x))))
-- safeRotate(O) = O.
-- safeRotate(Pair(a,b)) = Pair(b, Pair(O, a)).
--
-- iterate safeRotate O: always O (same issue — starts at O, stays at O).
--
-- The core issue: iterate f O always gives f^n(O), and if f(O) = O then
-- it's stuck at O forever. For non-trivial output, f(O) must be non-O.
--
-- So Case 4 really means: f(O) = Pair(c, d) where c and d are ground,
-- and the iterate builds from there.
--
-- Example: f(x) = Pair(Snd(x), Pair(O, Fst(x)))  (rotate)
-- With safe wrapping: safeRotate(x) = IfLf(x, Pair(O, Pair(Snd(x), Pair(O, Fst(x)))))
--   O -> O
--   Pair(a,b) -> Pair(Snd(Pair(a,b)), Pair(O, Fst(Pair(a,b)))) = Pair(b, Pair(O, a))
--
-- iterate safeRotate (Pair(O, O)):  — start from non-O initial value!
-- Wait, iterate always starts from the init parameter.
-- iterate f init (natCode n) = f^n(init).
-- If init = Pair(O, O):
--   n=0: Pair(O, O)
--   n=1: rotate(Pair(O,O)) = Pair(O, Pair(O, O))
--   n=2: rotate(Pair(O, Pair(O,O))) = Pair(Pair(O,O), Pair(O, O))
--   n=3: rotate(Pair(Pair(O,O), Pair(O,O))) = Pair(Pair(O,O), Pair(O, Pair(O,O)))
--
-- Output Fst cycles: O, O, Pair(O,O), Pair(O,O), ...
-- Output Snd grows: O, Pair(O,O), Pair(O,O), Pair(O, Pair(O,O)), ...
--
-- xi = Pair(Pair(O,O), O): is this ever output?
-- n=2 output = Pair(Pair(O,O), Pair(O, O)). Snd = Pair(O,O) ≠ O. No.
-- Actually the Snd is always Pair(O, something), never just O.
-- So Snd is always non-O for n >= 1. TreeEq(Snd, O) = Pair(O,O). ✓
-- An oblivious invariant at Snd! But wait...
--
-- At n=0: Pair(O,O). Snd = O. TreeEq(Pair(O,O), xi) = TreeEq(Pair(O,O), Pair(Pair(O,O), O)):
--   Fst: TreeEq(O, Pair(O,O)) = Pair(O,O). Short-circuits. ✓
--
-- Hmm, this is getting complicated. Let me instead focus on what's
-- STRUCTURALLY interesting: a step function f where f(x) = Pair(g(x), h(x))
-- and g, h are genuinely different projections, AND the iterate produces
-- non-trivial outputs against a specific xi.
--
-- SIMPLEST CASE 4: f(x) = Pair(Pair(O, Fst(x)), Snd(x))
-- f inserts O at the left of the first component.
-- f(Pair(a,b)) = Pair(Pair(O, a), b)
-- iterate f O:
--   n=0: O
--   n=1: f(O) = Pair(Pair(O, Fst(O)), Snd(O)). Stuck.
--
-- Same problem. Safe version:
-- safef(x) = IfLf(x, Pair(Pair(O, Fst(x)), Snd(x)))
-- safef(O) = O. iterate safef O: always O.
--
-- I think the fundamental point is:
-- ALL iterate-from-O programs that produce non-trivial outputs
-- must have f(O) ≠ O. The only way f(O) ≠ O is if f stamps a non-O
-- constant somewhere (Case 1/2/3) or if f is a composition
-- that produces a Pair from O.
--
-- f(O) can be Pair(g(O), h(O)). For g(O) and h(O) to be non-stuck,
-- g and h must handle O inputs. This means g and h either:
-- (a) are constant (KT c) — giving Case 1
-- (b) are I — giving g(O) = O, h(O) = O, so f(O) = Pair(O,O)
-- (c) are guarded (IfLf-based) — giving a ground value
--
-- For (b): f = Comp2 Pair I I = doubler. Already proved.
-- For (c): the IfLf guard makes f(O) = some ground constant.
-- The output of iterate f O is determined by the sequence f^n(O).
-- Each value is ground. The equational proof just needs TreeEq
-- against xi at each step.
--
-- CONCLUSION: Case 4 (different projections) only arises for
-- step functions that TAKE APART their input. But taking apart O
-- is stuck in the equational system. So either:
-- (a) Use IfLf-guarding, making f(O) = ground constant (Case 1/2)
-- (b) Use Comp2 Pair with two I-like functions (Case 3)
-- (c) Have a stuck f(O), making the iterate trivially O.
--
-- The "different projections" case essentially reduces to earlier cases!
-- Fst and Snd only produce meaningful outputs on Pair inputs.
-- On Pair inputs, the step function's projections are
-- sub-expressions of the PREVIOUS iterate output, which is determined
-- by the iterate structure. The proof handles this via the Rec
-- unwinding in Schema F.

module Guard.SwapProof where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.Machine
open import Guard.GroundEval

private
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero
  v1 : Term ; v1 = var (suc zero)
  pair01 : Term ; pair01 = ap2 Pair v0 v1
  gKT : Fun1 ; gKT = KT poo
  sConst : Fun2 ; sConst = Lift (KT poo)
  sConstRed : {hyp : Equation} (a b : Term) -> Deriv hyp (eqn (ap2 sConst a b) poo)
  sConstRed a b = ruleTrans (axLift (KT poo) a b) (axKT poo a)
  gStepS : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 gKT pair01)
                   (ap2 sConst pair01 (ap2 Pair (ap1 gKT v0) (ap1 gKT v1))))
  gStepS = ruleTrans (axKT poo pair01)
           (ruleSym (sConstRed pair01 (ap2 Pair (ap1 gKT v0) (ap1 gKT v1))))
  dSP : Tree ; dSP = encRefl (code O)

------------------------------------------------------------------------
-- R lemma (from GeneralQ)
rFun : Fun1
rFun = Comp2 IfLf I (KT (ap2 Pair poo poo))

rFunRed : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 rFun t) (ap2 IfLf t (ap2 Pair poo poo)))
rFunRed t =
  ruleTrans (axComp2 IfLf I (KT (ap2 Pair poo poo)) t)
  (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair poo poo)) t) (axI t))
    (congR IfLf t (axKT (ap2 Pair poo poo) t)))

rBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 rFun O) poo)
rBase = ruleTrans (rFunRed O) (axIfLfL poo poo)

rStepS : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 rFun pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 rFun v0) (ap1 rFun v1))))
rStepS = ruleTrans (ruleTrans (rFunRed pair01) (axIfLfN v0 v1 poo poo))
         (ruleSym (sConstRed pair01 (ap2 Pair (ap1 rFun v0) (ap1 rFun v1))))

rIsConst : {hyp : Equation} -> Deriv hyp (eqn (ap1 rFun v0) (ap1 gKT v0))
rIsConst = ruleF rFun gKT poo sConst rBase rStepS (axKT poo O) gStepS

rInst : {hyp : Equation} (t : Term) -> Deriv hyp (eqn (ap1 rFun t) poo)
rInst t = ruleTrans (ruleInst zero t rIsConst) (axKT poo t)

ifLfCollapse : {hyp : Equation} (x : Term) ->
  Deriv hyp (eqn (ap2 IfLf x (ap2 Pair poo poo)) poo)
ifLfCollapse x = ruleTrans (ruleSym (rFunRed x)) (rInst x)

------------------------------------------------------------------------
-- ACTUAL Case 4 test: a step function with different projections
-- that produces non-trivial outputs.
--
-- Strategy: use a step function that BUILDS structure with a constant
-- AND rearranges via projections.
--
-- f(x) = Pair(Pair(O, Fst(x)), Pair(Snd(x), O))
-- = Comp2 Pair (Comp2 Pair (KT O) Fst) (Comp2 Pair Snd (KT O))
--
-- f(Pair(a,b)) = Pair(Pair(O, a), Pair(b, O))
-- f(O) = Pair(Pair(O, Fst(O)), Pair(Snd(O), O)). Fst(O) and Snd(O) stuck.
-- Need safe version:
-- safef(x) = IfLf(x, Pair(Pair(O, Fst(x)), Pair(Snd(x), O)))
-- safef(O) = O.
-- safef(Pair(a,b)) = Pair(Pair(O, a), Pair(b, O)).
--
-- But iterate safef O: rec(lf) = O, safef(O) = O. Always O.
--
-- Need non-O init. Use init = Pair(O, O):
-- n=0: Pair(O, O)
-- n=1: f(Pair(O,O)) = Pair(Pair(O, O), Pair(O, O)) = Pair(poo, poo)
-- n=2: f(Pair(poo, poo)) = Pair(Pair(O, poo), Pair(poo, O))
-- n=3: f(Pair(Pair(O,poo), Pair(poo,O)))
--     = Pair(Pair(O, Pair(O,poo)), Pair(Pair(poo,O), O))
--
-- The Fst of output is always Pair(O, prev_Fst). So Fst always starts with O.
-- xi = Pair(Pair(O,O), O): Fst(xi) = Pair(O,O). Fst(output) = Pair(O, prev_Fst).
-- At n=0: Fst = O ≠ Pair(O,O). At n=1: Fst = Pair(O,O) = Fst(xi). Matches!
-- But Snd at n=1: Pair(O,O) ≠ O = Snd(xi). So overall ≠ xi. ✓
-- At n=2: Fst = Pair(O, Pair(O,O)). Fst(Fst) = O ≠ O. Wait, Fst(Pair(O, Pair(O,O))) = O.
-- Hmm, Fst(xi) = Pair(O,O). Fst of output at n=2 = Pair(O, Pair(O,O)) ≠ Pair(O,O). ✓
--
-- The step case:
-- f(rec) = Pair(Pair(O, Fst(rec)), Pair(Snd(rec), O))
-- TreeEq(Pair(Pair(O, Fst(rec)), Pair(Snd(rec), O)), Pair(Pair(O,O), O))
-- = IfLf(TreeEq(Pair(O, Fst(rec)), Pair(O,O)),
--        Pair(TreeEq(Pair(Snd(rec), O), O), Pair(O,O)))
--
-- Second arg: TreeEq(Pair(Snd(rec), O), O) = Pair(O,O) by axTreeEqNL. ✓
-- So second arg = Pair(Pair(O,O), Pair(O,O)).
-- By R (ifLfCollapse): result = Pair(O,O) regardless of first arg. ✓
--
-- This is Case 2! The Snd comparison short-circuits (Pair vs O),
-- making the second IfLf argument Pair(poo, poo), and R collapses it.
--
-- The "different projections" DON'T create a new case after all —
-- one of the comparisons always hits a Pair-vs-O or constant mismatch.

-- Let me just BUILD this proof to verify.

-- The safe step function (IfLf-guarded)
-- IfLf(x, Pair(O, Pair(Pair(O, Fst(x)), Pair(Snd(x), O))))
--   x = O: axIfLfL → first element = O
--   x = Pair(a,b): axIfLfN → second element = Pair(Pair(O,a), Pair(b,O))

private
  innerRot : Fun1
  innerRot = Comp2 Pair (Comp2 Pair (KT O) Fst) (Comp2 Pair Snd (KT O))

rotStep : Fun1
rotStep = Comp2 IfLf I (Comp2 Pair (KT O) innerRot)

-- innerRot(Pair(a,b)) = Pair(Pair(O, a), Pair(b, O))
innerRotPair : {hyp : Equation} (a b : Term) ->
  Deriv hyp (eqn (ap1 innerRot (ap2 Pair a b))
                 (ap2 Pair (ap2 Pair O a) (ap2 Pair b O)))
innerRotPair a b =
  ruleTrans (axComp2 Pair (Comp2 Pair (KT O) Fst) (Comp2 Pair Snd (KT O)) (ap2 Pair a b))
  (ruleTrans
    (congL Pair (ap1 (Comp2 Pair Snd (KT O)) (ap2 Pair a b))
      (ruleTrans (axComp2 Pair (KT O) Fst (ap2 Pair a b))
        (ruleTrans (congL Pair (ap1 Fst (ap2 Pair a b)) (axKT O (ap2 Pair a b)))
          (congR Pair O (axFst a b)))))
    (congR Pair (ap2 Pair O a)
      (ruleTrans (axComp2 Pair Snd (KT O) (ap2 Pair a b))
        (ruleTrans (congL Pair (ap1 (KT O) (ap2 Pair a b)) (axSnd a b))
          (congR Pair b (axKT O (ap2 Pair a b)))))))

-- rotStep reduction on O: rotStep(O) = O
rotStepO : {hyp : Equation} -> Deriv hyp (eqn (ap1 rotStep O) O)
rotStepO =
  ruleTrans (axComp2 IfLf I (Comp2 Pair (KT O) innerRot) O)
  (ruleTrans (congL IfLf (ap1 (Comp2 Pair (KT O) innerRot) O) (axI O))
  (ruleTrans (congR IfLf O (axComp2 Pair (KT O) innerRot O))
  (ruleTrans (congR IfLf O (congL Pair (ap1 innerRot O) (axKT O O)))
  (axIfLfL O (ap1 innerRot O)))))

-- rotStep reduction on Pair(a, b)
rotStepPair : {hyp : Equation} (a b : Term) ->
  Deriv hyp (eqn (ap1 rotStep (ap2 Pair a b))
                 (ap2 Pair (ap2 Pair O a) (ap2 Pair b O)))
rotStepPair a b =
  ruleTrans (axComp2 IfLf I (Comp2 Pair (KT O) innerRot) (ap2 Pair a b))
  (ruleTrans (congL IfLf (ap1 (Comp2 Pair (KT O) innerRot) (ap2 Pair a b))
    (axI (ap2 Pair a b)))
  (ruleTrans (congR IfLf (ap2 Pair a b)
    (axComp2 Pair (KT O) innerRot (ap2 Pair a b)))
  (ruleTrans (congR IfLf (ap2 Pair a b)
    (congL Pair (ap1 innerRot (ap2 Pair a b)) (axKT O (ap2 Pair a b))))
  (ruleTrans (congR IfLf (ap2 Pair a b)
    (congR Pair O (innerRotPair a b)))
  (axIfLfN a b O (ap2 Pair (ap2 Pair O a) (ap2 Pair b O)))))))

------------------------------------------------------------------------
-- The iterate program with init = Pair(O, O)
rotIter : Fun1
rotIter = iterate rotStep poo

xi : Tree ; xi = nd (nd lf lf) lf
xiT : Term ; xiT = ap2 Pair poo O

hRot : Fun1
hRot = Comp2 TreeEq rotIter (KT xiT)

private
  rec1 : Term ; rec1 = ap1 rotIter v1

-- Base: rotIter(O) = poo
-- h(O) = TreeEq(poo, xi)
-- TreeEq(Pair(O,O), Pair(Pair(O,O), O))
-- = IfLf(TreeEq(O, Pair(O,O)), Pair(TreeEq(O, O), Pair(O,O)))
-- = IfLf(Pair(O,O), Pair(O, Pair(O,O)))
-- = Pair(O,O)   [axIfLfN: Snd of the pair]

-- Wait, axIfLfN says IfLf(Pair(x,y), Pair(a,b)) = b.
-- So IfLf(Pair(O,O), Pair(O, Pair(O,O))) = Pair(O,O). ✓

hRotBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 hRot O) poo)
hRotBase =
  ruleTrans (axComp2 TreeEq rotIter (KT xiT) O)
  (ruleTrans (congL TreeEq (ap1 (KT xiT) O) (iterBase rotStep poo))
  (ruleTrans (congR TreeEq poo (axKT xiT O))
  (ruleTrans (axTreeEqNN O O poo O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) (axTreeEqLN O O))
    (axIfLfN O O (ap2 TreeEq O O) poo)))))

-- Step: rotIter(Pair(v0,v1)) = rotStep(rec(v1))
-- Two cases for rec(v1): O or Pair(a,b).
-- But Schema F doesn't case-split — it uses the Rec structure.
-- rotIter(Pair(v0,v1)) = iterStep rotStep (Pair(v0,v1)) (Pair(rec(v0), rec(v1)))
--   = rotStep(Snd(Pair(rec(v0), rec(v1)))) = rotStep(rec(v1))
-- by iterNd.
--
-- Now: h(Pair(v0,v1)) = TreeEq(rotStep(rec(v1)), xiT)
--
-- rotStep(rec(v1)): we can't reduce this further because rec(v1) is a variable.
-- BUT: rotStep = IfLf-based. rotStep(x) = IfLf(x, inner(x)).
-- On ANY input x:
--   if x = O: O
--   if x = Pair(a,b): Pair(Pair(O,a), Pair(b,O))
--
-- For the Schema F proof: we need rotStep(rec(v1)) expressed via the Rec structure.
-- Since rec(v1) is the recursive result of rotIter on v1, and we're proving
-- h(v1) = poo (i.e., rec(v1) ≠ xi), we have this info in Schema F.
--
-- But actually: we can AVOID reducing rotStep entirely.
-- The trick: just show TreeEq(rotStep(rec(v1)), xiT) = poo.
--
-- Hmm, rotStep(rec(v1)) is either O or Pair(Pair(O, a), Pair(b, O)) for some a,b.
-- If O: TreeEq(O, xiT) = poo by axTreeEqLN. ✓
-- If Pair(Pair(O,a), Pair(b,O)): TreeEq(..., Pair(poo, O))
--   = IfLf(TreeEq(Pair(O,a), poo), Pair(TreeEq(Pair(b,O), O), poo))
--   TreeEq(Pair(b,O), O) = poo by axTreeEqNL.
--   So = IfLf(TreeEq(Pair(O,a), poo), Pair(poo, poo))
--   = poo by ifLfCollapse. ✓
--
-- Both branches give poo! So we need to express this via rotStep's IfLf.
-- rotStep(rec(v1)) = IfLf(rec(v1), inner(rec(v1)))
-- TreeEq(IfLf(rec(v1), inner(rec(v1))), xiT) = ?
--
-- We can't directly reason about TreeEq of IfLf results equationally
-- without knowing which branch was taken.
--
-- Alternative approach: use a HELPER function that combines rotStep and TreeEq.
-- h2(x) = TreeEq(rotStep(x), xiT) = Comp2 TreeEq rotStep (KT xiT)
-- h2 is a Fun1. We prove h2(v0) = poo by Schema F.
--
-- h2(O) = TreeEq(rotStep(O), xiT) = TreeEq(O, xiT) = poo. ✓
-- h2(Pair(v0,v1)) = TreeEq(rotStep(Pair(v0,v1)), xiT)
--   = TreeEq(Pair(Pair(O,v0), Pair(v1,O)), Pair(poo, O))
--   = IfLf(TreeEq(Pair(O,v0), poo), Pair(TreeEq(Pair(v1,O), O), poo))
--   TreeEq(Pair(v1,O), O) = poo by axTreeEqNL.
--   = IfLf(TreeEq(Pair(O,v0), poo), Pair(poo, poo))
--   = poo by ifLfCollapse. ✓
--
-- So h2(v0) = poo is provable by Schema F directly!
-- Then: h(Pair(v0,v1)) = TreeEq(rotStep(rec(v1)), xiT) = h2(rec(v1)).
-- And h2(rec(v1)) = poo by instantiating h2's Schema F result.
-- This gives h(Pair(v0,v1)) = poo. ✓

------------------------------------------------------------------------
-- h2 = Comp2 TreeEq rotStep (KT xiT)
-- h2(x) = TreeEq(rotStep(x), xi)

h2 : Fun1
h2 = Comp2 TreeEq rotStep (KT xiT)

h2Red : {hyp : Equation} (t : Term) ->
  Deriv hyp (eqn (ap1 h2 t) (ap2 TreeEq (ap1 rotStep t) xiT))
h2Red t =
  ruleTrans (axComp2 TreeEq rotStep (KT xiT) t)
    (congR TreeEq (ap1 rotStep t) (axKT xiT t))

-- h2 base: h2(O) = TreeEq(O, xiT) = poo
h2Base : {hyp : Equation} -> Deriv hyp (eqn (ap1 h2 O) poo)
h2Base =
  ruleTrans (h2Red O)
  (ruleTrans (congL TreeEq xiT rotStepO)
             (axTreeEqLN poo O))

-- h2 step: h2(Pair(v0,v1)) = poo
-- TreeEq(rotStep(Pair(v0,v1)), xiT)
-- = TreeEq(Pair(Pair(O,v0), Pair(v1,O)), Pair(poo, O))
-- = IfLf(TreeEq(Pair(O,v0), poo), Pair(TreeEq(Pair(v1,O), O), poo))
-- = IfLf(TreeEq(Pair(O,v0), poo), Pair(poo, poo))    [axTreeEqNL]
-- = poo                                                [ifLfCollapse]

h2Step : {hyp : Equation} -> Deriv hyp (eqn (ap1 h2 pair01) poo)
h2Step =
  ruleTrans (h2Red pair01)
  (ruleTrans (congL TreeEq xiT (rotStepPair v0 v1))
  (ruleTrans (axTreeEqNN (ap2 Pair O v0) (ap2 Pair v1 O) poo O)
  (ruleTrans (congR IfLf (ap2 TreeEq (ap2 Pair O v0) poo)
    (congL Pair poo (axTreeEqNL v1 O)))
  (ifLfCollapse (ap2 TreeEq (ap2 Pair O v0) poo)))))

-- Schema F for h2
h2StepS : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 h2 pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 h2 v0) (ap1 h2 v1))))
h2StepS = ruleTrans h2Step
          (ruleSym (sConstRed pair01 (ap2 Pair (ap1 h2 v0) (ap1 h2 v1))))

h2IsConst : {hyp : Equation} -> Deriv hyp (eqn (ap1 h2 v0) (ap1 gKT v0))
h2IsConst = ruleF h2 gKT poo sConst h2Base h2StepS (axKT poo O) gStepS

h2Inst : {hyp : Equation} (t : Term) -> Deriv hyp (eqn (ap1 h2 t) poo)
h2Inst t = ruleTrans (ruleInst zero t h2IsConst) (axKT poo t)

------------------------------------------------------------------------
-- Main theorem: rotIter(t) ≠ xi for all t.
-- h(Pair(v0,v1)) = TreeEq(rotStep(rec(v1)), xiT) = h2(rec(v1)) = poo.

hRotStepFull : {hyp : Equation} -> Deriv hyp (eqn (ap1 hRot pair01) poo)
hRotStepFull =
  -- h(Pair(v0,v1)) = TreeEq(rotIter(Pair(v0,v1)), xiT)
  ruleTrans (axComp2 TreeEq rotIter (KT xiT) pair01)
  (ruleTrans (congR TreeEq (ap1 rotIter pair01) (axKT xiT pair01))
  -- = TreeEq(rotStep(rec(v1)), xiT)    by iterNd
  (ruleTrans (congL TreeEq xiT (iterNd rotStep poo v0 v1))
  -- = h2(rec(v1))                      by h2Red inverse
  (ruleTrans (ruleSym (h2Red rec1))
  -- = poo                              by h2Inst
             (h2Inst rec1))))

hRotStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 hRot pair01)
                 (ap2 sConst pair01 (ap2 Pair (ap1 hRot v0) (ap1 hRot v1))))
hRotStep = ruleTrans hRotStepFull
           (ruleSym (sConstRed pair01 (ap2 Pair (ap1 hRot v0) (ap1 hRot v1))))

rotNeverXi : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 hRot v0) (ap1 gKT v0))
rotNeverXi = ruleF hRot gKT poo sConst hRotBase hRotStep (axKT poo O) gStepS

------------------------------------------------------------------------
-- Verify with checkProof2

private
  encRotSF : Tree
  encRotSF = encF (codeF1 hRot) (codeF1 gKT) (code poo) (codeF2 sConst) dSP dSP dSP dSP

  checkRot : Eq (checkProof2 encRotSF) true
  checkRot = refl

------------------------------------------------------------------------
-- RESULT
--
-- The rotate program (Case 4: Fst and Snd depend on input DIFFERENTLY)
-- has an O(1) Schema F proof at BLevel 0.
--
-- The key: the HELPER h2(x) = TreeEq(rotStep(x), xi) is proved constant
-- by its OWN Schema F (independent of the iterate). The step function's
-- IfLf structure gives:
--   h2(O) = TreeEq(O, xi) = poo         [rotStep(O) = O]
--   h2(Pair(v0,v1)) = ifLfCollapse(...)  [Pair-vs-O at Snd component]
--
-- Then the iterate proof just invokes h2Inst on rec(v1).
--
-- PATTERN: for any IfLf-guarded step function f:
--   1. Prove h_f(x) = TreeEq(f(x), xi) = poo by Schema F.
--      Base: f(O) = O by IfLf guard. TreeEq(O, xi) = poo.
--      Step: f(Pair(v0,v1)) reduces. TreeEq collapses via R/Q/NL.
--   2. Prove h(t) = TreeEq(iterate f init (t), xi) = poo by Schema F.
--      Base: TreeEq(init, xi). Need init ≠ xi.
--      Step: h(Pair(v0,v1)) = TreeEq(f(rec(v1)), xi) = h_f(rec(v1)) = poo.
--
-- This is MODULAR: the step function proof (h2) and the iterate proof (h)
-- are separate Schema F applications. The step function proof is O(1)
-- (depends on f's structure, not on any parameter). The iterate proof
-- is O(1) (just invokes h2Inst).
--
-- CASE 4 IS RESOLVED. Different projections don't create a new case
-- because one of the projections always hits a structural mismatch
-- (Pair vs O) that collapses via R. The IfLf guard ensures f(O) = O,
-- making the base case trivial.
