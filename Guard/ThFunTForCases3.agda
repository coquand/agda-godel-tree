{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTForCases3 where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs

------------------------------------------------------------------------
-- Cases 17-25: axRefl, ruleSym, ruleTrans, cong1, congL, congR,
--              ruleInst, ruleF, axKT

private
  var0C : Term ; var0C = reify (nd (nd (nd lf lf) lf) lf)
  -- Actually var0C should be code of (var 0), which is nd tagVar (natCode 0)
  -- = nd (nd (nd (nd lf lf) lf) lf) lf
  -- reify = Pair(reify(nd(nd(nd lf lf) lf) lf), O) = Pair(tagVarT, O)

  n26 : Nat
  n26 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  n31 : Nat ; n31 = suc n30
  n32 : Nat ; n32 = suc n31

  codeKTTag : Term
  codeKTTag = reify (natCode n32)

-- Case 17: axRefl. a=tCode, b=lf.
-- thFun: nd(a, a)
case17 : Fun2
case17 = mkEqF origA origA

-- Case 18: ruleSym. a=lf, b=subproof.
-- recsB = thFunTFor(subproof) = Pair(L, R)
-- thFun: nd(R, L) = Pair(Snd(recsB), Fst(recsB))
case18 : Fun2
case18 = mkEqF recsBR recsBL

-- Case 19: ruleTrans. a=sp1, b=sp2.
-- recsA = thFunTFor(sp1) = Pair(L1, R1)
-- recsB = thFunTFor(sp2) = Pair(L2, R2)
-- thFun: nd(L1, R2) = Pair(Fst(recsA), Snd(recsB))
case19 : Fun2
case19 = mkEqF recsAL recsBR

-- Case 20: cong1. a=fCode, b=subproof.
-- recsB = thFunTFor(subproof) = Pair(L, R)
-- thFun: nd(mkAp1(f, L), mkAp1(f, R))
case20 : Fun2
case20 = mkEqF (mkAp1F origA recsBL) (mkAp1F origA recsBR)

-- Case 21: congL. a=nd(gCode, xCode), b=subproof.
-- recsB = thFunTFor(subproof) = Pair(L, R)
-- thFun: nd(mkAp2(g, L, x), mkAp2(g, R, x))
case21 : Fun2
case21 = mkEqF (mkAp2F origAL recsBL origAR) (mkAp2F origAL recsBR origAR)

-- Case 22: congR. a=nd(gCode, xCode), b=subproof.
-- recsB = thFunTFor(subproof) = Pair(L, R)
-- thFun: nd(mkAp2(g, x, L), mkAp2(g, x, R))
case22 : Fun2
case22 = mkEqF (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR)

-- Case 23: ruleInst. a=nd(xCode, tCode), b=subproof.
-- recsB = thFunTFor(subproof) = Pair(L, R)
-- thFun: nd(codedSubst(t, x, L), codedSubst(t, x, R))
-- codedSubst in the equational theory is ap1 substTFor with variables.
-- But at the Fun2 level, we use the ap1 substTFor combinator directly.
-- Actually, codedSubst here means: apply the object-level substTFor
-- to the coded subst arguments. We use Comp2 for this:
-- substResult(t, x, code) = ap1 (Rec O stepSubst) code
-- with var11=t, var12=x instantiated.
-- At the Fun2 level, this is complex. For now, use a simpler encoding:
-- The step function just pairs origAR (tCode) and origAL (xCode) with the result.
-- thFun dispatches codedSubst at the metalevel.
--
-- For the object-level Fun2, we need:
-- Fan (codedSubstF origAR origAL recsBL) (codedSubstF origAR origAL recsBR) Pair
-- where codedSubstF is substTFor applied at the Fun2 level.
--
-- This requires composing substTFor into the step function.
-- substTFor is a Fun1. We can use:
-- Post substTFor recsB  -- apply substTFor to recsBL? No...
--
-- Actually this is hard. The ruleInst case in thFun uses the metalevel
-- codedSubst. At the object level, we'd need to apply substTFor to the
-- equation parts with the right instantiation.
--
-- For now, define case23 using a placeholder that will be filled properly.
-- The key insight: substTFor is already a Fun1. We can Comp it:

-- Actually: codedSubst(tCode, xCode, eqPart) at the object level is
-- ap1 substTFor eqPart, then ruleInst to set var11=tCode, var12=xCode.
-- But we can't do ruleInst inside a Fun2 expression.
--
-- Alternative: define a 3-argument coded substitution combinator.
-- But we only have 1-ary and 2-ary functors.
--
-- The cleanest approach for the object-level:
-- thFunStep for case 23 constructs:
-- Pair(ap1 substTFor L, ap1 substTFor R) with appropriate var bindings.
-- But substTFor uses var 11 and var 12 which need to be origAR and origAL.
-- At the Fun2 level, these are runtime values, not static.
--
-- Since substTFor is a Rec that references var 11 and var 12,
-- and those get instantiated by ruleInst at use time,
-- the object-level step should just apply substTFor directly and
-- let ruleInst handle the variable binding.
--
-- Hmm, but substTFor is a CLOSED Fun1 (its Rec base is O, step is fixed).
-- The vars 11 and 12 appear inside the step function (via KT).
--
-- At the Fun2 level, applying substTFor gives:
-- ap1 substTFor eqPart = result with var11 and var12 free.
-- These free vars get bound by ruleInst at the DerivE level.
--
-- So case23 result = Pair(ap1 substTFor L, ap1 substTFor R)
-- But L and R are runtime values (from recsB).
-- In Fun2: Fan (Post substTFor recsBL) (Post substTFor recsBR) Pair
-- Wait: Post substTFor recsBL would be Post (Fun1) (Fun2).
-- Post : Fun1 -> Fun2 -> Fun2.
-- Post substTFor recsBL (orig, recs) = substTFor(recsBL(orig, recs)) -- WRONG type
-- Post f h (a, b) = ap1 f (ap2 h a b). So:
-- Post substTFor recsBL (orig, recs) = ap1 substTFor (ap2 recsBL orig recs)
-- But recsBL is a Fun2, so ap2 recsBL orig recs = Fst(Snd(recs)).
-- And ap1 substTFor (Fst(Snd(recs))) = substTFor applied to the left side.
-- But substTFor needs var11=tCode and var12=xCode...
--
-- Actually, I think the approach is wrong. The ruleInst case at the
-- object level should NOT use substTFor (which is for coded terms).
-- Instead, it should use a "substitution on coded equations" which
-- is just codedSubst applied to both sides.
--
-- For the step function, I'll define case23 to construct the codedSubst
-- application using the available primitives.
-- Actually, the simplest: case23 uses Comp2 to apply substTFor to each part.

-- Wait, let me reconsider. In the metalevel thFun, ruleInst case uses:
-- codedSubst (rightT a) (leftT a) (leftT rb)
-- where a = nd(xCode, tCode), rb = thFun(subproof) = nd(L, R).
--
-- At the object level, codedSubst IS substTFor (with appropriate var bindings).
-- The step function should construct terms that, when evaluated, give codedSubst.
--
-- In the equational theory, we build:
-- ap1 substTFor L  and  ap1 substTFor R
-- where substTFor has var 11 = tCode and var 12 = xCode.
-- These vars are bound by ruleInst at the Deriv level, not in the Fun2.
--
-- So case23 just applies substTFor to both sides:

case23 : Fun2
case23 = mkEqF (Post substTFor recsBL) (Post substTFor recsBR)
  where
  open import Guard.SubstTFor using (substTFor)
  -- Note: substTFor has free vars 11 and 12 inside its step function.
  -- At use time, ruleInst will bind these to origAR (tCode) and origAL (xCode).
  -- This means case23 doesn't reference origA at all in the Fun2!
  -- The connection happens at the Deriv level when we prove correctness.

-- Hmm, but this doesn't bind var 11 and var 12 to the right values.
-- substTFor's step function uses KT (var 11) and KT (var 12).
-- These will be FREE variables in the result.
-- At the Deriv level, ruleInst x t binds var x to t in the equation.
-- For ruleInst case, we need var 11 = tCode and var 12 = xCode.
-- But in the step function, origAR = tCode and origAL = xCode.
-- The connection: after applying ruleInst at the Deriv level,
-- var 11 in the substTFor output gets replaced by tCode.
--
-- But the step function doesn't DO the ruleInst — it just constructs
-- the ap1 substTFor term. The ruleInst happens in the correctness proof.
--
-- Actually, I think there's a deeper issue. substTFor uses var 11
-- and var 12 INSIDE its Rec step function (via KT). When substTFor
-- is used as part of thFunStep (inside thFunTFor's Rec), the vars 11
-- and 12 are STILL free. They DON'T get bound to origAR/origAL.
--
-- For the correctness proof, after unfolding thFunTFor at a ruleInst
-- encoding, we get: Pair(ap1 substTFor L, ap1 substTFor R).
-- Then we use ruleInst at the Deriv level to bind var 11 to tCode
-- and var 12 to xCode.
--
-- This is fine! The ruleInst case in the correctness proof does:
-- 1. Unfold thFunTFor to get Pair(ap1 substTFor L, ap1 substTFor R)
-- 2. Apply ruleInst 11 tCode and ruleInst 12 xCode
-- 3. Use substTFor correctness to simplify
--
-- So case23 IS just Post substTFor applied to each side. ✓

-- Case 24: ruleF. a=nd(fCode, gCode), b=nd(sp1, sp2).
-- thFun: nd(mkAp1(f, var0C), mkAp1(g, var0C))
-- where var0C = reify(code(var 0)) = nd tagVar lf at the tree level
-- Actually in thFun: nd(mkAp1(leftT a, var0C), mkAp1(rightT a, var0C))

private
  var0CodeT : Term
  var0CodeT = reify (nd (nd (nd (nd lf lf) lf) lf) lf)

case24 : Fun2
case24 = mkEqF (mkAp1F origAL (kF2 var0CodeT)) (mkAp1F origAR (kF2 var0CodeT))

-- Case 25: axKT. a=tCode, b=xCode.
-- thFun: nd(mkAp1(codeKT(a), b), a)
case25 : Fun2
case25 = mkEqF (mkAp1F (Fan (kF2 codeKTTag) origA Pair) origB) origA
