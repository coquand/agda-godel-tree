{-# OPTIONS --safe --without-K --exact-split #-}

-- KRInstance.agda
-- The minimal Kritchman-Raz experiment.
--
-- Target: ξ = nd(nd lf lf) lf — a tree not in the range of natCode
-- Programs: I, KT(O)
-- Question: can we prove "these programs don't output ξ" in the system,
--   and does the proof stay at BLevel 0?
--
-- GROUND INSTANCES (BLevel 0):
--   For each specific clock c, "program(natCode c) ≠ ξ" is decidable.
--
-- UNIVERSAL INSTANCE (the real test):
--   "For all c, I(natCode c) ≠ ξ" — where does BLevel climb?

module Guard.KRInstance where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.FindError

------------------------------------------------------------------------
-- Setup

private
  poo : Term ; poo = ap2 Pair O O

-- Target tree: ξ = nd(nd lf lf) lf
-- reify ξ = Pair(Pair(O,O), O) = Pair(poo, O)
xi : Tree
xi = nd (nd lf lf) lf

xiT : Term
xiT = ap2 Pair poo O

-- Key structural fact: reify ξ is a Pair (not O)
-- So TreeEq(O, reify ξ) = Pair(O,O) by axTreeEqLN

------------------------------------------------------------------------
-- Part 1: Ground instances (BLevel 0)
--
-- "I(O) ≠ ξ": prove TreeEq(ap1 I O, xiT) is nonzero.

-- Step 1: ap1 I O = O
-- Step 2: TreeEq(O, xiT) = Pair(O,O)
-- Step 3: TreeEq(ap1 I O, xiT) = Pair(O,O) by trans + cong

iDoesntOutputXiAt0 : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 I O) xiT) poo)
iDoesntOutputXiAt0 =
  ruleTrans (congL TreeEq xiT (axI O)) (axTreeEqLN poo O)

-- "KT(O)(O) ≠ ξ": same structure
ktDoesntOutputXiAt0 : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (KT O) O) xiT) poo)
ktDoesntOutputXiAt0 =
  ruleTrans (congL TreeEq xiT (axKT O O)) (axTreeEqLN poo O)

-- Clock 1: I(Pair(O,O)) = Pair(O,O) ≠ ξ = Pair(Pair(O,O), O)
-- TreeEq(Pair(O,O), Pair(Pair(O,O), O))
-- = IfLf(TreeEq(O, Pair(O,O)), Pair(TreeEq(O, O), Pair(O,O)))  [axTreeEqNN]
-- = IfLf(Pair(O,O), Pair(TreeEq(O,O), Pair(O,O)))               [axTreeEqLN]
-- = Pair(TreeEq(O,O), Pair(O,O))                                 [axIfLfN]
-- = Pair(O, Pair(O,O))                                           [axTreeEqLL]
-- This is nonzero (it's a Pair), so the trees differ.

-- iDoesntOutputXiAt1 omitted (complex TreeEq chain, not needed for experiment)

-- Clock 1 for KT(O):
ktDoesntOutputXiAt1 : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (KT O) (ap2 Pair O O)) xiT) poo)
ktDoesntOutputXiAt1 =
  ruleTrans (congL TreeEq xiT (axKT O poo)) (axTreeEqLN poo O)

------------------------------------------------------------------------
-- Part 2: Encode these proofs and run checkProof
--
-- Encode iDoesntOutputXiAt0 as a proof encoding tree and verify.

-- The proof is: congL TreeEq xiT (axI O) ; axTreeEqLN poo O
-- = trans(congL(TreeEq, xiT, axI(O)), axTreeEqLN(poo, O))

-- Encoding:
-- axI(O): encAxI(code O)
-- congL(TreeEq, xiT, axI(O)): encCongL(codeF2 TreeEq, code xiT, encAxI(code O))
-- axTreeEqLN(poo, O): encAxTreeEqLN(code poo, code O)
-- trans: encTrans(enc_congL, enc_treeEqLN)

private
  cO : Tree ; cO = code O
  cPoo : Tree ; cPoo = code poo
  cXi : Tree ; cXi = code xiT

  -- thFun check on the axI encoding
  encAI : Tree ; encAI = encAxI cO

  checkAI : Eq (checkProof encAI) true
  checkAI = refl

  -- The TreeEqLN axiom: tag 14
  encTELN : Tree ; encTELN = encAxTreeEqLN cPoo cO

  -- DISCOVERY: checkProof FAILS on TreeEqLN!
  -- eval only handles tagO (→ lf) and tagAp1 (→ strip). It doesn't
  -- evaluate TreeEq, Pair, Fst, or any other functor.
  -- So eval(code(TreeEq(O, Pair(a,b)))) ≠ eval(code(Pair(O,O))) —
  -- both just get passthrough treatment, producing different trees.
  checkTELN : Eq (checkProof encTELN) false
  checkTELN = refl

  -- This means checkProof works ONLY for:
  --   axRefl (both sides identical)
  --   axI (eval correctly strips ap1)
  --   structural rules (sym, trans, cong) preserving eval equality
  -- ALL other computation axioms (TreeEq, Fst, Snd, Rec, ...) FAIL.
  -- This IS the EvalOK obstruction, observed at the metalevel.

------------------------------------------------------------------------
-- Part 3: The universal — "I(c) ≠ ξ for all natCode c"
--
-- THIS is the critical experiment. We want to prove, in the system:
--   TreeEq(ap1 I (var 0), xiT) = Pair(O,O)     ... for all natCode values
--
-- But var 0 ranges over ALL trees, not just natCode values.
-- And TreeEq(ξ, ξ) = O, so the equation FAILS when var 0 = xiT.
--
-- Schema F proves equations for ALL trees. It cannot restrict to natCode.
--
-- APPROACH 1: Use Schema F on a different decomposition.
--   Define f(t) = TreeEq(t, xiT). We want f(natCode c) = nonzero for all c.
--   The natCode iteration is: natCode 0 = lf, natCode(suc n) = nd lf (natCode n).
--   So natCode values are RIGHT SPINES: lf, nd(lf,lf), nd(lf,nd(lf,lf)), ...
--   Their LEFT child is always lf.
--   While Fst(xiT) = Pair(O,O).
--   So TreeEq(Fst(natCode c), Fst(xiT)) = TreeEq(O, Pair(O,O)) = Pair(O,O) ≠ O.
--
--   Key: for ANY tree t with Fst(t) ≠ Fst(xiT), we have TreeEq(t, xiT) ≠ O.
--   The structural decomposition via axTreeEqNN gives:
--     TreeEq(Pair(a,b), Pair(Pair(O,O),O)) = IfLf(TreeEq(a, Pair(O,O)), ...)
--   When a ≠ Pair(O,O): TreeEq(a, Pair(O,O)) ≠ O (i.e., it's a Pair)
--     so IfLf(Pair(...), ...) returns second branch.
--   When a = O (which is the case for ALL natCode values with c ≥ 1):
--     TreeEq(O, Pair(O,O)) = Pair(O,O) by axTreeEqLN.
--     IfLf(Pair(O,O), Pair(TreeEq(b, O), Pair(O,O))) = Pair(TreeEq(b,O), Pair(O,O))
--     by axIfLfN. This is always a Pair, hence nonzero.
--
-- APPROACH 2: Use Schema F to show that
--   Comp Fst (Comp2 TreeEq I (KT xiT))
-- applied to any natCode value gives O.
--   i.e., the first component of TreeEq(natCode c, xiT) is always O.
--   For c=0: Fst(TreeEq(O, Pair(Pair(O,O),O))) = Fst(Pair(O,O)) = O.
--   For c≥1: Fst(TreeEq(Pair(O,X), Pair(Pair(O,O),O))) = ...
--     TreeEq(Pair(O,X), Pair(Pair(O,O),O)) = IfLf(TreeEq(O,Pair(O,O)), Pair(TreeEq(X,O), Pair(O,O)))
--     = IfLf(Pair(O,O), Pair(TreeEq(X,O), Pair(O,O))) = Pair(TreeEq(X,O), Pair(O,O)).
--     Fst = TreeEq(X,O). Where X = natCode(c-1).
--     Hmm, this doesn't simplify to O in general. TreeEq(natCode(c-1), O) = Pair(O,O)
--     for c≥2, and = O for c=1.
--
-- So the structure depends on the specific c. No uniform simplification.
--
-- APPROACH 3: Avoid the universal entirely.
--   The KR argument doesn't need to prove "I never outputs ξ" in the system.
--   It needs: "if the system is consistent, the Chaitin machine terminates."
--   The Chaitin machine searches for PROOFS, not for computation results.
--   So it searches for a proof tree t such that thFun(t) encodes "∃ξ. K(ξ) > l".
--   If the system can prove this (by pigeonhole), the machine finds the proof
--   and extracts ξ.
--
-- THE REAL QUESTION: Can the system prove "∃ξ. K(ξ) > l" staying in BLevel 0?
--
-- The proof of "∃ξ. K(ξ) > l" needs to EXHIBIT ξ and show K(ξ) > l.
-- Showing K(ξ) > l means: for each program p of size ≤ l, for each clock c,
-- p(c) ≠ ξ. This is the "for all clocks" problem.
--
-- For KT(O): KT(O)(c) = O for all c. O ≠ ξ because ξ is a Pair.
--   Can we prove KT(O)(var 0) = O universally? YES: axKT O (var 0) gives it!
--   Then TreeEq(O, xiT) = Pair(O,O) by axTreeEqLN. GROUND computation.
--   So "KT(O) never outputs ξ" IS provable at BLevel 0!
--   No ruleInst, no Schema F. Just axKT + axTreeEqLN.
--
-- For I: I(var 0) = var 0 by axI. But TreeEq(var 0, xiT) ≠ Pair(O,O) universally.
--   I CAN output ξ (when input = ξ). So "I never outputs ξ" is FALSE!
--   But "I never outputs ξ AT A NATCODE CLOCK" is true.
--   The system can't express "var 0 is restricted to natCode values."
--
-- DISCOVERY: The universal "for all clocks" splits into two cases:
--   (a) Constant programs (KT v): BLevel 0, universal by axKT.
--   (b) Non-constant programs: the system CANNOT prove "p(c) ≠ ξ for all c"
--       because var 0 ranges over all trees.
--       It can only prove this for SPECIFIC ground clocks.
--
-- For case (b), the system would need either:
--   - Schema F with some invariant (but the invariant doesn't hold for all trees)
--   - ruleInst to instantiate a Schema F result at specific natCode values
--   - Or: a reformulation that avoids the universal over clocks

-- Demonstrate case (a): KT(O) never outputs ξ, BLevel 0.

ktNeverOutputsXi : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (KT O) (var zero)) xiT) poo)
ktNeverOutputsXi =
  ruleTrans (congL TreeEq xiT (axKT O (var zero))) (axTreeEqLN poo O)

-- This is universal (free var 0) and BLevel 0!
-- Encode it and run checkProof.

private
  v0 : Nat ; v0 = zero
  cVar0 : Tree ; cVar0 = code (var v0)

  -- Encode: trans(congL(TreeEq, xiT, axKT(O, var 0)), axTreeEqLN(poo, O))
  -- axKT(O, var 0): encAxKT(code O, code(var 0))
  encKTstep : Tree
  encKTstep = encAxKT cO cVar0

  -- congL(TreeEq, xiT, encKTstep): encCongL(codeF2 TreeEq, code xiT, encKTstep)
  encCL : Tree
  encCL = encCongL (codeF2 TreeEq) cXi encKTstep

  -- axTreeEqLN(poo, O): encAxTreeEqLN(code poo, code O)
  encTE : Tree
  encTE = encAxTreeEqLN cPoo cO

  -- trans chain
  encFull : Tree
  encFull = encTrans encCL encTE

  -- DISCOVERY: checkProof also fails on axKT!
  -- eval can't evaluate KT(O)(var 0) → O. It just passthrough's.
  -- The only axiom that passes checkProof is axI and axRefl.
  checkKTstep : Eq (checkProof encKTstep) false
  checkKTstep = refl

  -- TreeEqLN step: checkProof FAILS (eval can't handle TreeEq)
  checkTE2 : Eq (checkProof encTE) false
  checkTE2 = refl

  -- The congL step: thFun will give us something involving codeF2 TreeEq.
  -- The question: does checkProof pass?
  -- thFun(encCongL(gC, xC, sp)) for tag 21:
  --   nd(mkAp2(leftT a, leftT rb, rightT a), mkAp2(leftT a, rightT rb, rightT a))
  --   where a = nd(gC, xC), b = sp
  -- eval on mkAp2: strips tagAp2, then passthrough for gC (functor code).
  -- The key: eval(mkAp2(gC, t1, t2)) = eval(nd tagAp2 (nd gC (nd t1 t2)))
  -- tagAp2 is not tagO, not tagAp1 → passthrough
  -- = nd(eval tagAp2, eval(nd gC (nd t1 t2)))
  -- So both sides of the equation get the same passthrough structure.
  -- If leftT rb = rightT rb (i.e., the sub-proof proves an equality where both
  -- sides are equal), then the congL result also has equal sides.
  -- But we need to CHECK: does checkProof actually pass?

  -- congL: checkProof may or may not pass depending on sub-proof structure
  -- Let Agda decide:
  -- checkCL : Eq (checkProof encCL) ?
  -- (omitted — depends on whether eval agrees on mkAp2 wrappers)

  -- THE FULL CHAIN: contains axTreeEqLN sub-proof which fails checkProof.
  -- So either the chain fails, or findError locates the TreeEqLN step.
  checkFull : Eq (checkProof encFull) false
  checkFull = refl

  -- findError locates the first failing sub-step.
  -- It may find encCL (the congL step) or encTE (TreeEqLN) depending
  -- on which child it checks first and which fails.
  findFullNotLf : Eq (findError encFull) lf -> Empty
  findFullNotLf ()

------------------------------------------------------------------------
-- Part 4: The non-constant case — I applied to var 0
--
-- I(var 0) = var 0 by axI.
-- TreeEq(var 0, xiT) is NOT provably nonzero (fails when var 0 = xiT).
--
-- For a SPECIFIC clock: I(natCode 0) = O, O ≠ ξ. Encoding:
-- trans(congL(TreeEq, xiT, axI(O)), axTreeEqLN(poo, O))

encIat0CL : Tree
encIat0CL = encCongL (codeF2 TreeEq) cXi (encAxI cO)

encIat0 : Tree
encIat0 = encTrans encIat0CL encTE

-- checkProof fails because the proof chain contains axTreeEqLN
checkIat0 : Eq (checkProof encIat0) false
checkIat0 = refl

-- For clock 1: I(natCode 1) = natCode 1 = Pair(O,O)
-- TreeEq(Pair(O,O), Pair(Pair(O,O), O)):
-- = IfLf(TreeEq(O, Pair(O,O)), Pair(TreeEq(O, O), Pair(O,O)))
-- = IfLf(Pair(O,O), Pair(O, Pair(O,O)))
-- = Pair(O, Pair(O,O))
-- This IS nonzero (a Pair), so the trees differ.
-- But the proof needs: axI, axTreeEqNN, axTreeEqLN, axIfLfN, axTreeEqLL
-- All ground, all BLevel 0.

-- Encode the clock-1 proof:
private
  cPooT : Tree ; cPooT = code poo

  -- axI applied to poo
  encAI1 : Tree ; encAI1 = encAxI cPooT

  checkAI1 : Eq (checkProof encAI1) true
  checkAI1 = refl

-- For the UNIVERSAL over clocks: we're stuck.
-- Schema F can't prove TreeEq(var 0, xiT) is universally nonzero.
-- ruleInst would be needed to extract specific instances from a universal.
--
-- FINDING: Even for the identity function, the universal
-- "I doesn't output ξ at any natCode clock" requires either:
--   (a) infinitely many ground proofs (one per clock), or
--   (b) some form of restricted quantification (which the system lacks), or
--   (c) ruleInst to instantiate a Schema-F result.
--
-- Options (a) and (c) are the only viable ones.
-- Option (a) avoids ruleInst but requires an external meta-argument.
-- Option (c) uses ruleInst = BLevel 1.
--
-- CONCLUSION (for this instance):
-- The KR proof for non-constant programs DOES require BLevel ≥ 1
-- (or infinitely many ground instances assembled externally).
-- Only constant programs (KT v) stay at BLevel 0.
--
-- This is Scenario B from the analysis: the obstacle is structural,
-- not specific to diagonalization. The universal over computation steps
-- forces BLevel ≥ 1 regardless of proof method.

------------------------------------------------------------------------
-- Part 5: But wait — there's a subtlety.
--
-- For ITERATE-based programs (the actual Leivant machines),
-- the output at clock c depends only on iterating the step function c times.
-- The iterate combinator gives:
--   iterate f init (natCode 0) = init
--   iterate f init (natCode (suc n)) = f(iterate f init (natCode n))
--
-- If the step function has a FIXED POINT (f(v) = v), and the iteration
-- reaches v by some clock T, then for all c ≥ T: iterate f init (natCode c) = v.
--
-- Schema F can prove: iterate f init (var 0) = KT v (var 0) = v
-- IF f(v) = v (fixed point) AND init = v (immediate fixed point).
-- Or more generally, if we can show both sides satisfy the same Rec.
--
-- For a machine that HALTS (reaches fixed point v after T steps):
--   1. Prove iterate f init (natCode T) = v  [ground, BLevel 0, T applications of iterNd]
--   2. Prove f(v) = v                        [ground, BLevel 0]
--   3. Use Schema F to show: iterate f v (var 0) = v for all trees
--      [This works if f(v)=v, because both Rec(v, step)(O)=v and step(x, Pair(v,v))=v]
--   4. Bridge: for c ≥ T, iterate f init (natCode c) = iterate f v (natCode(c-T))
--      [This step might need ruleInst to instantiate Schema F at specific clocks]
--
-- Step 4 is where ruleInst potentially enters.
-- Without ruleInst, we have ap1 (iterate f v) (var 0) = v (by Schema F),
-- which is universal and BLevel 0.
-- But linking iterate-from-init to iterate-from-v at specific clocks
-- requires instantiating var 0 at natCode(c-T)... which IS ruleInst.
--
-- UNLESS we restructure: define the WHOLE program as iterate-from-v
-- (pretending the machine starts at the fixed point).
-- Then the program trivially outputs v at all clocks.
-- But then it's just KT(v) in disguise — a constant program.
--
-- SUMMARY:
-- Non-constant output behavior always requires clock-specific reasoning.
-- Clock-specific reasoning requires ruleInst.
-- So BLevel 0 is limited to constant programs.
-- The KR argument for non-trivial programs inevitably hits BLevel ≥ 1.
