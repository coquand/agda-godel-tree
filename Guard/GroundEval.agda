{-# OPTIONS --safe --without-K --exact-split #-}

-- GroundEval.agda
-- A full ground-term evaluator for coded terms.
--
-- Unlike eval (= evalCode), which only handles tagO and strips tagAp1,
-- this evaluator dispatches on ALL functor codes:
--   Fun1: I, Fst, Snd, KT (Comp/Comp2/Rec handled by fuel)
--   Fun2: Pair, Const, IfLf, TreeEq (Lift/Post/Fan handled by fuel)
--
-- Key property: for GROUND coded terms (no tagVar), this evaluator
-- computes the correct semantic value. For terms WITH variables,
-- it returns a default (passthrough), which will cause checkProof2
-- to fail — exactly as it should.
--
-- This separates two concerns:
--   (1) Can the evaluator handle the functors? (YES for ground terms)
--   (2) Can the evaluator handle variables? (NO — this is the real obstacle)
--
-- Nelson's distinction: the KR proof uses only ground terms,
-- so (1) suffices. The diagonal proof introduces variables via ruleInst,
-- so it hits (2).

module Guard.GroundEval where

open import Guard.Base
open import Guard.Term
open import Guard.ThFun
open import Guard.FindError using (treeSize)

------------------------------------------------------------------------
-- Functor tag constants (offset 26)

private
  n26 : Nat
  n26 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))
  ft0 : Tree ; ft0 = natCode n26             -- 26: I / Pair
  ft1 : Tree ; ft1 = natCode (suc n26)       -- 27: Fst / Const
  ft2 : Tree ; ft2 = natCode (suc (suc n26)) -- 28: Snd / Lift
  ft3 : Tree ; ft3 = natCode (suc (suc (suc n26)))         -- 29: Comp / Post
  ft4 : Tree ; ft4 = natCode (suc (suc (suc (suc n26))))   -- 30: Comp2 / Fan
  ft5 : Tree ; ft5 = natCode (suc (suc (suc (suc (suc n26)))))  -- 31: Rec / IfLf
  ft6 : Tree ; ft6 = natCode (suc (suc (suc (suc (suc (suc n26))))))  -- 32: KT / TreeEq

------------------------------------------------------------------------
-- TreeEq semantics: returns lf (equal) or nd lf lf (unequal)
-- Matches the system's TreeEq axioms exactly.

treeEqSem : Tree -> Tree -> Tree
treeEqSem lf       lf       = lf
treeEqSem lf       (nd _ _) = nd lf lf
treeEqSem (nd _ _) lf       = nd lf lf
treeEqSem (nd a b) (nd c d) =
  boolCase (treeEq (treeEqSem a c) lf)
    (treeEqSem b d)
    (nd lf lf)

------------------------------------------------------------------------
-- IfLf semantics: if first arg = lf, return leftT(second); else rightT(second)

ifLfSem : Tree -> Tree -> Tree
ifLfSem lf       lf       = lf
ifLfSem lf       (nd a b) = a
ifLfSem (nd _ _) lf       = lf
ifLfSem (nd _ _) (nd a b) = b

------------------------------------------------------------------------
-- Full ground evaluator with fuel
--
-- Fuel prevents non-termination for Comp/Rec chains.
-- For the experiment, we pick fuel > depth of terms.
-- Returns lf on fuel exhaustion (safe default).

geval : Nat -> Tree -> Tree
gevalAp1 : Nat -> Tree -> Tree -> Tree
gevalAp2 : Nat -> Tree -> Tree -> Tree -> Tree

geval zero _ = lf
geval (suc n) lf = lf
geval (suc n) (nd a b) =
  boolCase (treeEq a lf)
    -- tagO: return lf
    lf
    (boolCase (treeEq a tagVar)
      -- tagVar: variable — return encoded form (stuck)
      (nd a b)
      (boolCase (treeEq a tagAp1)
        -- tagAp1: dispatch on functor code in leftT(b), eval argument in rightT(b)
        (gevalAp1 n (leftT b) (rightT b))
        (boolCase (treeEq a tagAp2)
          -- tagAp2: dispatch on functor code in leftT(b)
          (gevalAp2 n (leftT b) (leftT (rightT b)) (rightT (rightT b)))
          -- Unknown tag: passthrough
          (nd (geval n a) (geval n b)))))

-- Reify a tree value back to coded form for re-evaluation
-- reifyCode : Tree -> Tree matches code(reify(t))
reifyCode : Tree -> Tree
reifyCode lf = nd lf lf  -- code O = nd tagO lf; but we need nd(tagO, lf) as coded term
-- Actually: the semantic value lf represents O. code(O) = nd tagO lf = nd lf lf.
-- Semantic nd(a,b) represents Pair(reify a, reify b).
-- code(ap2 Pair (reify a) (reify b)) = nd tagAp2 (nd (codeF2 Pair) (nd (reifyCode a) (reifyCode b)))
reifyCode (nd a b) = nd tagAp2 (nd (codeF2 Pair) (nd (reifyCode a) (reifyCode b)))

-- Fun1 dispatch: fCode is the functor code tree, argCode is the argument code
gevalAp1 zero _ _ = lf
gevalAp1 (suc n) fCode argCode =
  let ftag = leftT fCode
      fdata = rightT fCode
  in
  boolCase (treeEq ftag ft0)
    -- I (tag 26): identity, return eval(arg)
    (geval n argCode)
    (boolCase (treeEq ftag ft1)
      -- Fst (tag 27): return leftT(eval(arg))
      (leftT (geval n argCode))
      (boolCase (treeEq ftag ft2)
        -- Snd (tag 28): return rightT(eval(arg))
        (rightT (geval n argCode))
        (boolCase (treeEq ftag ft6)
          -- KT (tag 32): return eval(payload), ignore arg
          (geval n fdata)
          (boolCase (treeEq ftag ft5)
            -- Rec (tag 31): tree recursion
            -- fdata = nd zCode sCode
            -- Rec z s applied to arg:
            --   if arg evaluates to lf: return eval(zCode)
            --   if arg evaluates to nd(a,b): return ap2 s (nd a b) (Pair(rec a, rec b))
            (let argVal = geval n argCode
                 zCode = leftT fdata
                 sCode = rightT fdata
             in boolCase (treeEq argVal lf)
                  (geval n zCode)
                  (let recL = gevalAp1 n fCode (reifyCode (leftT argVal))
                       recR = gevalAp1 n fCode (reifyCode (rightT argVal))
                   in gevalAp2 n sCode
                        (reifyCode argVal)
                        (reifyCode (nd recL recR))))
            (boolCase (treeEq ftag ft3)
              -- Comp (tag 29): Comp f g → f(g(arg))
              -- fdata = nd fC gC
              (let gResult = gevalAp1 n (rightT fdata) argCode
               in gevalAp1 n (leftT fdata) (reifyCode gResult))
              (boolCase (treeEq ftag ft4)
                -- Comp2 (tag 30): Comp2 h f g → h(f(arg), g(arg))
                -- fdata = nd hC (nd fC gC)
                (let hC = leftT fdata
                     fC = leftT (rightT fdata)
                     gC = rightT (rightT fdata)
                     fResult = gevalAp1 n fC argCode
                     gResult = gevalAp1 n gC argCode
                 in gevalAp2 n hC (reifyCode fResult) (reifyCode gResult))
                -- Unknown: passthrough
                (nd (geval n fCode) (geval n argCode))))))))

-- Fun2 dispatch
gevalAp2 zero _ _ _ = lf
gevalAp2 (suc n) gCode t1Code t2Code =
  let gtag = leftT gCode
      v1 = geval n t1Code
      v2 = geval n t2Code
  in
  boolCase (treeEq gtag ft0)
    (nd v1 v2)                       -- Pair (26): nd(eval t1, eval t2)
    (boolCase (treeEq gtag ft1)
      v1                             -- Const (27): eval t1
      (boolCase (treeEq gtag ft2)
        -- Lift (tag 28): Lift f (a, b) = f(a)
        (gevalAp1 n (rightT gCode) t1Code)
        (boolCase (treeEq gtag ft3)
          -- Post (tag 29): Post f h (a, b) = f(h(a, b))
          -- gCode data = nd fC hC
          (let fC = leftT (rightT gCode)
               hC = rightT (rightT gCode)
               hResult = gevalAp2 n hC t1Code t2Code
           in gevalAp1 n fC (reifyCode hResult))
          (boolCase (treeEq gtag ft4)
            -- Fan (tag 30): Fan h1 h2 h (a, b) = h(h1(a,b), h2(a,b))
            -- gCode data = nd h1C (nd h2C hC)
            (let h1C = leftT (rightT gCode)
                 h2C = leftT (rightT (rightT gCode))
                 hC = rightT (rightT (rightT gCode))
                 r1 = gevalAp2 n h1C t1Code t2Code
                 r2 = gevalAp2 n h2C t1Code t2Code
             in gevalAp2 n hC (reifyCode r1) (reifyCode r2))
            (boolCase (treeEq gtag ft5)
              (ifLfSem v1 v2)        -- IfLf (31)
              (boolCase (treeEq gtag ft6)
                (treeEqSem v1 v2)    -- TreeEq (32)
                (nd v1 v2)))))))

------------------------------------------------------------------------
-- checkProof2: like checkProof but using geval

fuel : Nat
fuel = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       zero)))))))))))))))))))))))))))))))))))))))))))))))))  -- 50

checkProof2 : Tree -> Bool
checkProof2 t = treeEq (geval fuel (leftT (thFun t)))
                       (geval fuel (rightT (thFun t)))

------------------------------------------------------------------------
-- Tests: ground axioms

private
  cO : Tree ; cO = code O
  cPoo : Tree ; cPoo = code (ap2 Pair O O)
  cXi : Tree ; cXi = code (ap2 Pair (ap2 Pair O O) O)
  poo : Term ; poo = ap2 Pair O O

  -- axI: checkProof2 passes (just like checkProof)
  check2AxI : Eq (checkProof2 (encAxI cO)) true
  check2AxI = refl

  -- axRefl: both sides identical
  check2Refl : Eq (checkProof2 (encRefl cO)) true
  check2Refl = refl

  -- axKT: geval handles KT!
  -- thFun(encAxKT(cO, cVar0)):
  --   nd(mkAp1(codeKT(cO), cVar0), cO)
  -- geval on mkAp1 with KT tag: returns geval(cO) = lf
  -- geval on cO = lf
  -- Match!
  check2AxKT : Eq (checkProof2 (encAxKT cO (code (var zero)))) true
  check2AxKT = refl

  -- axTreeEqLN: geval handles TreeEq!
  -- thFun(encAxTreeEqLN(cPoo, cO)):
  --   nd(mkAp2(treeeqC, oC, mkAp2(pairC, cPoo, cO)), oneC)
  -- geval on left: TreeEq(geval(oC), geval(mkAp2(pairC, cPoo, cO)))
  --   = TreeEq(lf, nd(geval cPoo, geval cO))
  --   = TreeEq(lf, nd(nd(lf, lf), lf))  -- poo evaluates to nd(lf,lf)
  --   = nd lf lf  (unequal)
  -- geval on right: oneC = mkAp2(pairC, oC, oC) → nd(lf, lf)
  -- Do they match? nd lf lf = nd lf lf? YES!
  check2TreeEqLN : Eq (checkProof2 (encAxTreeEqLN cPoo cO)) true
  check2TreeEqLN = refl

  -- axFst: geval handles Fst!
  -- thFun(encAxFst(cO, cPoo)):
  --   nd(mkAp1(codeFst, mkAp2(pairC, cO, cPoo)), cO)
  -- geval on left: Fst(Pair(geval cO, geval cPoo)) = Fst(nd(lf, nd(lf,lf))) = lf
  -- geval on right: geval cO = lf
  check2Fst : Eq (checkProof2 (encAxFst cO cPoo)) true
  check2Fst = refl

  -- axSnd: geval handles Snd!
  check2Snd : Eq (checkProof2 (encAxSnd cO cPoo)) true
  check2Snd = refl

------------------------------------------------------------------------
-- The KR proof: "KT(O) never outputs ξ"
--
-- Proof: trans(congL(TreeEq, xiT, axKT(O, var 0)), axTreeEqLN(poo, O))
-- Both sub-proofs now pass checkProof2!

  cVar0 : Tree ; cVar0 = code (var zero)

  encKTstep : Tree ; encKTstep = encAxKT cO cVar0
  encCL : Tree ; encCL = encCongL (codeF2 TreeEq) cXi encKTstep
  encTE : Tree ; encTE = encAxTreeEqLN cPoo cO
  encFull : Tree ; encFull = encTrans encCL encTE

  -- Individual steps pass
  check2KTstep : Eq (checkProof2 encKTstep) true
  check2KTstep = refl

  check2TE : Eq (checkProof2 encTE) true
  check2TE = refl

  -- Full chain passes!
  check2Full : Eq (checkProof2 encFull) true
  check2Full = refl

------------------------------------------------------------------------
-- The diagonal contrast: ruleInst introduces variables
--
-- ruleInst(x, t, sp) produces:
--   nd(codedSubst(leftT a, rightT a, leftT rb),
--      codedSubst(leftT a, rightT a, rightT rb))
-- where a = nd(tCode, xCode), rb = thFun(sp)
--
-- When tCode contains var codes: codedSubst may leave tagVar nodes.
-- geval on tagVar: returns nd(tagVar, natCode n) — a stuck term.
-- This means the two sides of the substituted equation may contain
-- different stuck terms, causing checkProof2 to return false.
--
-- Example: ruleInst(0, var 1, refl(var 0))
-- This substitutes var 1 for var 0 in the equation var 0 = var 0.
-- Result: var 1 = var 1. VALID equation, but geval can't check it
-- because var 1 is stuck.

  -- Encode ruleInst(0, var 1, refl(code(var 0)))
  cVar1 : Tree ; cVar1 = code (var (suc zero))
  cVar0code : Tree ; cVar0code = code (var zero)
  encRI : Tree
  encRI = encInst cVar1 (natCode zero) (encRefl cVar0code)

  -- checkProof2 on ruleInst with variables: PASSES!
  -- Because ruleInst on refl(var 0) gives var 1 = var 1 — both sides identical.
  -- codedSubst produces the SAME tree on both sides. geval agrees trivially.
  check2RI : Eq (checkProof2 encRI) true
  check2RI = refl

------------------------------------------------------------------------
-- The subtle case: ruleInst on axI PASSES geval
-- because geval correctly strips ap1(I, _) even with variables inside.
-- The real failure: when a VARIABLE'S VALUE matters for evaluation.
--
-- Example: Schema F produces ap1 f (var 0) = ap1 g (var 0).
-- After ruleInst(0, t): ap1 f t = ap1 g t. For ground t, geval works.
-- The issue only arises when the substituted value itself CONTAINS variables
-- passed through from a deeper ruleInst — which is the nested substitution
-- problem (BLevel ≥ 2).
--
-- For BLevel 1 (single ruleInst with ground substitution):
-- geval handles it correctly! The substituted ground value evaluates fine.

  -- ruleInst(0, O, axI(var 0)): substitutes O for var 0 in "I(var 0) = var 0"
  -- Result: I(O) = O. Both sides ground. geval handles it.
  encRI2 : Tree
  encRI2 = encInst cO (natCode zero) (encAxI cVar0code)

  check2RI2 : Eq (checkProof2 encRI2) true
  check2RI2 = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- checkProof  (eval, crude)   : passes axI, axRefl. Fails almost everything.
-- checkProof2 (geval, ground) : passes ALL ground axioms + ruleInst with
--                               ground substitution. Handles I, Fst, Snd,
--                               KT, Pair, Const, IfLf, TreeEq.
--
-- The KR proof "KT(O) never outputs ξ" passes checkProof2.
-- ruleInst with ground substitution also passes.
--
-- The distinction is NOT "variables present / absent" but
-- "can geval fully evaluate both sides to compare?"
-- For ground terms: YES. For terms where a variable's value matters
-- for a branching decision (IfLf, TreeEq on variable): geval gives
-- a fixed answer that may be wrong for some substitutions.
--
-- Nelson's point, refined: ground computation is feasible (checkProof2).
-- The question is whether the KR argument can be structured so that
-- ALL evaluation stays ground — meaning all branching decisions
-- are on known values, not on variables.
