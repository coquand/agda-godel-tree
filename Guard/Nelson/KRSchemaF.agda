{-# OPTIONS --safe --without-K --exact-split #-}

-- KRSchemaF.agda
-- Step 4: Does Schema F pass checkProof2?
--
-- Schema F (ruleF, tag 24) proves: ap1 f (var 0) = ap1 g (var 0)
-- when f and g satisfy the same Rec equations.
--
-- thFun on encF produces: nd(mkAp1(fC, var0C), mkAp1(gC, var0C))
-- where fC = codeF1 f, gC = codeF1 g, var0C = nd tagVar lf
--
-- checkProof2: does geval(mkAp1(fC, var0C)) = geval(mkAp1(gC, var0C))?
-- This depends on what fC and gC are, and how geval evaluates them
-- applied to the stuck variable value.

module Guard.Nelson.KRSchemaF where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.Nelson.Machine
open import Guard.Nelson.GroundEval

------------------------------------------------------------------------
-- Test 1: Schema F with f = g (trivial case)
--
-- ruleF f f z s ... proves ap1 f (var 0) = ap1 f (var 0)
-- Both sides identical → checkProof2 passes trivially.

private
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero
  v1 : Term ; v1 = var (suc zero)

  -- Schema F comparing iterate I O with KT O:
  -- Both satisfy Rec O s for s = iterStep I:
  --   iterate I O (O) = O  [axRecLf]
  --   KT O (O) = O         [axKT]
  --   iterate I O (Pair(a,b)) = I(iterate I O b) = iterate I O b  [step]
  --   But KT O (Pair(a,b)) = O  [axKT]
  -- The step equations DIFFER: iterate I O unfolds to I(recR), while KT O gives O.
  -- So this Schema F instance doesn't apply directly.

  -- Simpler: Schema F comparing Rec O s with KT O, where s is chosen so
  -- the step equation trivially holds.
  -- Actually, the simplest Schema F instance is comparing a Rec with itself.

  -- The real use case from GodelII.agda: treeEqSelfAll
  -- f = Comp2 TreeEq I I (= teI), g = KT O
  -- Both satisfy: base = O, step = teSelf
  -- This proves: TreeEq(t,t) = O for all t.
  --
  -- thFun on encF: nd(mkAp1(codeF1 teI, var0C), mkAp1(codeF1 (KT O), var0C))
  -- geval on left: evaluates Comp2(TreeEq, I, I) applied to stuck var0C
  --   = TreeEq(I(var0C), I(var0C)) = TreeEq(stuck, stuck) = treeEqSem(stuck, stuck)
  --   = lf (equal! because stuck = stuck)
  -- geval on right: evaluates KT(O) applied to var0C = geval(code O) = lf
  -- Both = lf! checkProof2 should pass!

  teI : Fun1
  teI = Comp2 TreeEq I I

  -- The encoding for Schema F:
  -- encF(fC, gC, zC, sC, sp1, sp2, sp3, sp4)
  -- where sp1..sp4 are the four sub-proofs (base/step for f and g)

  -- For the treeEqSelf proof, the sub-proofs are complex.
  -- Let me just test directly: what does geval give on the Schema F output?

  -- thFun(encF ...) = nd(mkAp1(codeF1 teI, var0C), mkAp1(codeF1 (KT O), var0C))
  -- Let me compute the left and right sides directly.

  cTeI : Tree
  cTeI = codeF1 teI

  cKTO : Tree
  cKTO = codeF1 (KT O)

  var0C : Tree
  var0C = nd tagVar (natCode zero)

  -- mkAp1(cTeI, var0C) = nd tagAp1 (nd cTeI var0C)
  leftSide : Tree
  leftSide = nd tagAp1 (nd cTeI var0C)

  rightSide : Tree
  rightSide = nd tagAp1 (nd cKTO var0C)

  -- geval on leftSide:
  -- tagAp1 → dispatch on cTeI
  -- cTeI = codeF1(Comp2 TreeEq I I) = nd (natCode 30) (nd (codeF2 TreeEq) (nd (codeF1 I) (codeF1 I)))
  -- ftag = natCode 30 = ft4 → Comp2 case
  -- hC = codeF2 TreeEq, fC = codeF1 I, gC = codeF1 I
  -- fResult = gevalAp1(I, var0C) = geval(var0C) = nd tagVar (natCode 0) [stuck]
  -- gResult = gevalAp1(I, var0C) = same stuck value
  -- gevalAp2(TreeEq, reifyCode(stuck), reifyCode(stuck))
  -- v1 = geval(reifyCode(stuck)), v2 = geval(reifyCode(stuck))
  -- Both are stuck. treeEqSem(stuck, stuck) = ?
  -- stuck = nd tagVar (natCode 0)
  -- treeEqSem(nd tagVar (natCode 0), nd tagVar (natCode 0))
  --   = boolCase (treeEq (treeEqSem tagVar tagVar) lf)
  --              (treeEqSem (natCode 0) (natCode 0))
  --              (nd lf lf)
  --   tagVar = nd (nd (nd lf lf) lf) lf
  --   treeEqSem tagVar tagVar: both identical → lf
  --   boolCase (treeEq lf lf) (treeEqSem (natCode 0) (natCode 0)) (nd lf lf)
  --   = treeEqSem lf lf = lf
  -- So geval(leftSide) involves treeEqSem(stuck, stuck) = lf. Good.

  -- geval on rightSide:
  -- cKTO = codeF1(KT O) = nd (natCode 32) (code O)
  -- ftag = natCode 32 = ft6 → KT case
  -- return geval(code O) = geval(nd lf lf) = lf (tagO case)

  -- Both sides = lf! They agree!

  gevalLeft : Eq (geval fuel leftSide) lf
  gevalLeft = refl

  gevalRight : Eq (geval fuel rightSide) lf
  gevalRight = refl

  -- So checkProof2 on a Schema F encoding WOULD pass, because geval
  -- gives the same result on both sides.

------------------------------------------------------------------------
-- Now test with actual Schema F encoding.
-- The encoding is: encF(cTeI, cKTO, zCode, sCode, sp1, sp2, sp3, sp4)
-- The sub-proofs are complex, but thFun only looks at the tag and
-- the fC/gC codes. The sub-proofs go into the recursive structure
-- but don't affect the top-level output of thFun.

  -- thFun on tag 24 (n24):
  -- nd(mkAp1(leftT a, var0C), mkAp1(rightT a, var0C))
  -- where a = nd(fC, gC)

  -- Minimal encoding (sub-proofs can be anything, thFun ignores them
  -- for the output equation):
  dummySP : Tree
  dummySP = encRefl (code O)

  encSchemaF : Tree
  encSchemaF = encF cTeI cKTO (code O) (codeF2 (Fan (Post Fst (Post Snd Pair))
               (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair) IfLf))
               dummySP dummySP dummySP dummySP

  -- checkProof2: geval on both sides of the Schema F output
  check2SchemaF : Eq (checkProof2 encSchemaF) true
  check2SchemaF = refl

------------------------------------------------------------------------
-- KEY RESULT:
--
-- Schema F passes checkProof2!
--
-- Why: thFun produces nd(mkAp1(fC, var0C), mkAp1(gC, var0C)).
-- geval evaluates both:
--   - left: Comp2(TreeEq, I, I)(stuck) = TreeEq(stuck, stuck) = lf
--   - right: KT(O)(stuck) = O = lf
-- Both give lf. checkProof2 returns true.
--
-- The crucial insight: geval on a stuck variable gives a CONSISTENT
-- stuck value (nd tagVar (natCode 0)). When the SAME stuck value
-- appears in both arguments of TreeEq, treeEqSem returns lf (equal).
-- And KT ignores its argument entirely, always returning the constant.
--
-- So for this specific Schema F instance (TreeEq(t,t) = O):
--   Left side: TreeEq(var0, var0) → geval sees same stuck on both → lf
--   Right side: KT(O)(var0) → geval ignores var0 → lf
--   They agree!
--
-- This works because the EQUATION being proved is SEMANTICALLY TRUE
-- for all values of var 0, and geval's stuck-value treatment happens
-- to be consistent with this truth.

------------------------------------------------------------------------
-- Does this always work? Consider a DIFFERENT Schema F instance.
--
-- Schema F comparing Rec O s with Rec (Pair(O,O)) s':
-- If thFun gives nd(mkAp1(fC, var0C), mkAp1(gC, var0C)),
-- geval on left: Rec(O, s)(stuck). Since stuck = nd tagVar (natCode 0),
-- which is a non-lf tree, Rec unfolds into the step case.
-- The step gets: (stuck, Pair(Rec(tagVar), Rec(natCode 0))).
-- This recurses into the stuck value's children...
-- The recursion terminates because the children are smaller trees.
-- tagVar = nd(nd(nd lf lf) lf) lf, so Rec recurses into nd(nd lf lf) lf and lf.
-- Eventually bottoms out at lf → returns z.
-- So Rec treats the stuck variable as a SPECIFIC tree and evaluates accordingly.
--
-- This means geval gives a DEFINITE answer even for variable-containing terms.
-- The answer is correct for this specific stuck tree value, but may be wrong
-- for other values of var 0.
--
-- For Schema F to pass checkProof2: geval(f applied to stuck) must equal
-- geval(g applied to stuck). This happens when f and g agree on the specific
-- tree nd(tagVar, natCode 0). Since Schema F guarantees they agree on ALL trees,
-- they certainly agree on this one.
--
-- THEREFORE: Schema F ALWAYS passes checkProof2, because:
-- (1) Schema F proves f(var 0) = g(var 0) for ALL trees
-- (2) geval evaluates var 0 as the specific tree nd(tagVar, natCode 0)
-- (3) f and g agree on this tree (by (1))
-- (4) So geval(f(stuck)) = geval(g(stuck))
--
-- This is a GENERAL argument, not specific to this instance!

------------------------------------------------------------------------
-- Contrast: ruleInst can FAIL checkProof2 when the substituted equation
-- is not semantically true for the stuck variable value.
--
-- Example: ruleInst(0, O, proof_of "TreeEq(var 0, O) = O")
-- After substitution: TreeEq(O, O) = O. TRUE, and checkProof2 passes.
--
-- But: the INNER proof (before substitution) has TreeEq(var 0, O) = O.
-- This is true ONLY when var 0 = O. For the stuck value nd(tagVar, natCode 0):
-- TreeEq(stuck, O) = nd lf lf ≠ lf = O. So checkProof2 would FAIL on the
-- inner proof (if it were checked standalone).
--
-- With ruleInst, the outer (substituted) proof is checked — and it passes
-- because O is substituted for var 0. But the INNER proof's side conditions
-- depend on the variable's value.
--
-- So: ruleInst(0, ground_value, inner_proof) passes checkProof2 at the
-- OUTER level, but the inner proof may fail if checked in isolation.
-- The substitution "heals" the failure by fixing the variable.
--
-- This is why ruleInst with GROUND substitution worked in our earlier test.
