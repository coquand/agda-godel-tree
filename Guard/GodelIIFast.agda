{-# OPTIONS --safe --without-K --exact-split #-}

-- Fast variant of Guard.GodelII.
--
-- Differences from the original:
--   * Imports Guard.SubstTForPrecompFast and Guard.SubstTForPrecomp2Fast
--     (these omit the slow `instForm2 = refl`).
--   * The `godelIIFast` function uses the schematic Nelson helpers
--     (substReify / substTForClose / thFunTForSubstEq / instFormGen)
--     instead of the 108-second `instForm2`.
--
-- Mathematically the proof structure is unchanged.  The technical
-- shift is to apply ruleInst to the *open* template equation
-- (containing thFunTFor and substTFor) BEFORE chaining with cstf,
-- so the substituted-and-ruleInst'd type never has cstf in a
-- position that requires unfolding crTC.

module Guard.GodelIIFast where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect
open import Guard.SubstTFor using (substTFor ; stepSubst)
open import Guard.SubstTForCorrect
open import Guard.SubstTForPrecompFast
open import Guard.SubstTForPrecomp2Fast
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.Thm14E
open import Guard.Nelson.SubstReify using (substReify ; substClosedSTF)
open import Guard.Nelson.SubstTForClose using (substTForClose)
open import Guard.Nelson.ThFunTForSubst using (thFunTForClosed ; thFunTForSubstEq)
open import Guard.Nelson.InstForm using (instFormGen)

private
  poo : Term ; poo = ap2 Pair O O
  v1 : Nat ; v1 = suc zero
  v11 : Nat ; v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat ; v12 = suc v11
  tgtT : Term ; tgtT = reify (natCode v1)
  v0 : Term ; v0 = var zero
  v1T : Term ; v1T = var (suc zero)

------------------------------------------------------------------------
-- TreeEq(t,t) = O for all t, via Schema F.  (Same as Guard.GodelII.)

private
  teI : Fun1
  teI = Comp2 TreeEq I I

  teSelf : Fun2
  teSelf = Fan (Post Fst (Post Snd Pair))
               (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair)
               IfLf

  teIRed : (t : Term) -> {hyp : Equation} -> Deriv hyp (eqn (ap1 teI t) (ap2 TreeEq t t))
  teIRed t = ruleTrans (axComp2 TreeEq I I t)
             (ruleTrans (congL TreeEq (ap1 I t) (axI t)) (congR TreeEq t (axI t)))

  teSelfRed : (ab fa fb : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 teSelf ab (ap2 Pair fa fb)) (ap2 IfLf fa (ap2 Pair fb poo)))
  teSelfRed ab fa fb =
    let recs = ap2 Pair fa fb
    in ruleTrans (fanRed (Post Fst (Post Snd Pair)) (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair) IfLf ab recs)
       (ruleTrans (congL IfLf (ap2 (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair) ab recs)
         (ruleTrans (postRed Fst (Post Snd Pair) ab recs)
         (ruleTrans (cong1 Fst (postRed Snd Pair ab recs))
         (ruleTrans (cong1 Fst (axSnd ab recs)) (axFst fa fb)))))
       (congR IfLf fa
         (ruleTrans (fanRed (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair ab recs)
         (ruleTrans (congL Pair (ap2 (Lift (KT poo)) ab recs)
           (ruleTrans (postRed Snd (Post Snd Pair) ab recs)
           (ruleTrans (cong1 Snd (postRed Snd Pair ab recs))
           (ruleTrans (cong1 Snd (axSnd ab recs)) (axSnd fa fb)))))
         (congR Pair fb (ruleTrans (liftRed (KT poo) ab recs) (axKT poo ab)))))))

  fBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 teI O) O)
  fBase = ruleTrans (teIRed O) axTreeEqLL

  fStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 teI (ap2 Pair v0 v1T))
                   (ap2 teSelf (ap2 Pair v0 v1T) (ap2 Pair (ap1 teI v0) (ap1 teI v1T))))
  fStep =
    let ab = ap2 Pair v0 v1T ; fa = ap1 teI v0 ; fb = ap1 teI v1T
    in ruleTrans (ruleTrans (teIRed ab) (axTreeEqNN v0 v1T v0 v1T))
       (ruleSym (ruleTrans (teSelfRed ab fa fb)
                (ruleTrans (congL IfLf (ap2 Pair fb poo) (teIRed v0))
                (congR IfLf (ap2 TreeEq v0 v0) (congL Pair poo (teIRed v1T))))))

  gBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 (KT O) O) O)
  gBase = axKT O O

  gStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (KT O) (ap2 Pair v0 v1T))
                   (ap2 teSelf (ap2 Pair v0 v1T) (ap2 Pair (ap1 (KT O) v0) (ap1 (KT O) v1T))))
  gStep =
    let ab = ap2 Pair v0 v1T ; ga = ap1 (KT O) v0 ; gb = ap1 (KT O) v1T
    in ruleTrans (axKT O ab)
       (ruleSym (ruleTrans (teSelfRed ab ga gb)
                (ruleTrans (congL IfLf (ap2 Pair gb poo) (axKT O v0))
                (ruleTrans (axIfLfL gb poo) (axKT O v1T)))))

treeEqSelfAll : {hyp : Equation} -> Deriv hyp (eqn (ap1 teI v0) (ap1 (KT O) v0))
treeEqSelfAll = ruleF teI (KT O) O teSelf fBase fStep gBase gStep

treeEqSelf : (t : Term) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq t t) O)
treeEqSelf t = ruleTrans (ruleSym (teIRed t))
               (ruleTrans (ruleInst zero t treeEqSelfAll) (axKT O t))

------------------------------------------------------------------------
-- diagFTarget: cstf(reify TC) = reify(cGS).
-- Same proof as in Guard.GodelII; we just import the abstract pieces
-- from the *Fast variants of SubstTForPrecomp.

diagFTarget : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 cstf (reify templateCode)) (reify cGS))
diagFTarget {hyp} =
  let tgtN = natCode v1
      cstf' = closedSubstTFor (reify crTC) (reify tgtN)
      combined = closedSTFNd crTC tgtN codeLhsT codePoo
                   codeLhsTNeqTagVar codeLhsTNotVar
                   (lhsTSTF crTC) (pooSTF crTC)
      step1 = eqSubst (\tc -> Deriv hyp (eqn (ap1 cstf' (reify tc)) (reify (codedSubst crTC tgtN tc))))
                       (eqSym templateCodeForm) combined
      step2 = eqSubst (\f -> Deriv hyp (eqn (ap1 f (reify templateCode)) (reify (codedSubst crTC tgtN templateCode))))
                       (eqSym cstfDef) step1
      fp = eqTrans (codedSubstNd crTC tgtN codeLhsT codePoo codeLhsTNotVar) (eqSym cGSisCS)
      fp2 = eqTrans (eqSubst (\tc -> Eq (codedSubst crTC tgtN tc) (codedSubst crTC tgtN (nd codeLhsT codePoo))) (eqSym templateCodeForm) refl) fp
  in eqSubst (\v -> Deriv hyp (eqn (ap1 cstf (reify templateCode)) (reify v)))
             fp2 step2

------------------------------------------------------------------------
-- Helper: substitution is identity on cstf (using cstfDef + substClosedSTF).
-- This is the bridge that lets us swap subst's into cstf without unfolding crTC.

substCstf : (x : Nat) (r : Term) -> Eq (substF1 x r cstf) cstf
substCstf x r = eqTrans (eqCong (substF1 x r) cstfDef)
                (eqTrans (substClosedSTF x r crTC (natCode v1))
                         (eqSym cstfDef))

------------------------------------------------------------------------
-- godelIIFast: the Gödel I form (= Guard.GodelII.godelII), restructured
-- to avoid instForm2.
--
-- Strategy:
--   * instD as before — open form, no cstf in the type
--   * Apply ruleInst v12 then v11 on instD (open template equation),
--     producing instD2 via instFormGen + cstfDef bridge.
--   * Apply ruleInst v12 then v11 on chain (the open chain equation),
--     producing chainSubst via thFunTForSubstEq + substReify + substCstf.
--   * Combine chainSubst with instD2 to get TreeEq(cstf TC, cstf TC) = poo.
--   * Conclude with treeEqSelf.

godelIIFast : {hyp : Equation} -> ProofE hyp -> Consistent hyp ->
              Deriv hyp godelSentence -> Empty
godelIIFast {hyp} ph con dG = con botDeriv
  where
  pe : ProofE godelSentence ; pe = thm14E dG ph
  pa : Tree ; pa = fst pe
  pb : Tree ; pb = fst (snd pe)
  enc : Term ; enc = ap2 Pair (reify pa) (reify pb)

  -- corrPf: thFunTFor(enc) = reify(cGS)
  corrPf : Deriv hyp (eqn (ap1 thFunTFor enc) (reify cGS))
  corrPf = eqSubst (\t -> Deriv hyp (eqn (ap1 thFunTFor enc) (reify t)))
                    (eqSym cGSdef)
                    (fst (snd (snd (snd pe))) {hyp})

  -- chain: thFunTFor(enc) = cstf(reify TC)
  chain : Deriv hyp (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))
  chain = ruleTrans corrPf (ruleSym diagFTarget)

  -- instD: TreeEq(thFunTFor(enc), substTFor(reify TC)) = poo
  instD : Deriv hyp (eqn (ap2 TreeEq (ap1 thFunTFor enc) (ap1 substTFor (reify templateCode))) poo)
  instD = eqSubst (\eq -> Deriv hyp eq) (substGodelSentence enc) (ruleInst zero enc dG)

  -- instD2pre: result of ruleInst v12 then v11 on instD, with type
  -- massaged via instFormGen.
  instD2pre : Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                          (ap1 (closedSubstTFor (reify crTC) (reify (natCode v1))) (reify templateCode)))
                              poo)
  instD2pre = eqSubst (\eq -> Deriv hyp eq)
                       (instFormGen crTC (natCode v1) pa pb templateCode)
                       (ruleInst v11 (reify crTC) (ruleInst v12 (reify (natCode v1)) instD))

  -- instD2: same as instD2pre but with `cstf` in place of the explicit closedSubstTFor.
  instD2 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                       (ap1 cstf (reify templateCode)))
                           poo)
  instD2 = eqSubst (\f -> Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                                      (ap1 f (reify templateCode)))
                                          poo))
                    (eqSym cstfDef) instD2pre

  -- chainBridge: the equation showing that double-substituted chain has the desired form.
  chainBridge :
    Eq (substEq v11 (reify crTC) (substEq v12 (reify (natCode v1))
         (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))))
       (eqn (ap1 (thFunTForClosed crTC (natCode v1)) enc) (ap1 cstf (reify templateCode)))
  chainBridge =
    eqCong2 eqn
      -- LHS: subst v11 (subst v12 (ap1 thFunTFor enc)) → ap1 (thFunTForClosed ...) enc
      (eqCong2 ap1
        (thFunTForSubstEq crTC (natCode v1))
        (eqTrans
          (eqCong (subst v11 (reify crTC))
            (eqCong2 (ap2 Pair)
              (substReify v12 (reify (natCode v1)) pa)
              (substReify v12 (reify (natCode v1)) pb)))
          (eqCong2 (ap2 Pair)
            (substReify v11 (reify crTC) pa)
            (substReify v11 (reify crTC) pb))))
      -- RHS: subst v11 (subst v12 (ap1 cstf (reify TC))) → ap1 cstf (reify TC)
      (eqCong2 ap1
        (eqTrans (eqCong (substF1 v11 (reify crTC)) (substCstf v12 (reify (natCode v1))))
                 (substCstf v11 (reify crTC)))
        (eqTrans
          (eqCong (subst v11 (reify crTC)) (substReify v12 (reify (natCode v1)) templateCode))
          (substReify v11 (reify crTC) templateCode)))

  chainSubst : Deriv hyp (eqn (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                              (ap1 cstf (reify templateCode)))
  chainSubst = eqSubst (\eq -> Deriv hyp eq) chainBridge
                       (ruleInst v11 (reify crTC) (ruleInst v12 (reify (natCode v1)) chain))

  -- step2: TreeEq(cstf(reify TC), cstf(reify TC)) = poo
  -- Replace thFunTForClosed(enc) with cstf(reify TC) in instD2 using chainSubst.
  step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) poo)
  step2 = ruleTrans (ruleSym (congL TreeEq (ap1 cstf (reify templateCode)) chainSubst)) instD2

  -- TreeEq(X, X) = O for X = cstf(reify TC)
  selfEq : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) O)
  selfEq = treeEqSelf (ap1 cstf (reify templateCode))

  botDeriv : Deriv hyp (eqn O poo)
  botDeriv = ruleTrans (ruleSym selfEq) step2
