{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.GodelII where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstTForCorrect
open import Guard.SubstTForPrecomp
open import Guard.SubstTForPrecomp2
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.Thm14E

private
  poo : Term ; poo = ap2 Pair O O
  v1 : Nat ; v1 = suc zero
  v11 : Nat ; v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat ; v12 = suc v11
  tgtT : Term ; tgtT = reify (natCode v1)
  v0 : Term ; v0 = var zero
  v1T : Term ; v1T = var (suc zero)

------------------------------------------------------------------------
-- TreeEq(t,t) = O for all t, via Schema F.

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
-- diagFTarget: cstf(reify TC) = reify(cGS)

private
  tgtN : Tree ; tgtN = natCode v1

  diagFTarget : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 cstf (reify templateCode)) (reify cGS))
  diagFTarget {hyp} =
    let cstf' = closedSubstTFor (reify crTC) (reify tgtN)
        combined = closedSTFNd crTC tgtN codeLhsT codePoo
                     codeLhsTNeqTagVar codeLhsTNotVar
                     (lhsTSTF crTC) (pooSTF crTC)
        -- combined type has Pair(reify codeLhsT, reify codePoo), need reify templateCode
        step1 = eqSubst (\tc -> Deriv hyp (eqn (ap1 cstf' (reify tc)) (reify (codedSubst crTC tgtN tc))))
                         (eqSym templateCodeForm) combined
        -- Bridge cstf' to cstf
        step2 = eqSubst (\f -> Deriv hyp (eqn (ap1 f (reify templateCode)) (reify (codedSubst crTC tgtN templateCode))))
                         (eqSym cstfDef) step1
        -- Bridge codedSubst crTC tgtN templateCode to cGS
        fp = eqTrans (codedSubstNd crTC tgtN codeLhsT codePoo codeLhsTNotVar) (eqSym cGSisCS)
        -- But codedSubst crTC tgtN templateCode is stuck (templateCode abstract).
        -- Use templateCodeForm to bridge: codedSubst crTC tgtN templateCode
        --   = codedSubst crTC tgtN (nd codeLhsT codePoo) [by templateCodeForm]
        --   = nd(codedSubst...)(codedSubst...) [by codedSubstNd]
        --   = cGS [by cGSisCS]
        fp2 = eqTrans (eqSubst (\tc -> Eq (codedSubst crTC tgtN tc) (codedSubst crTC tgtN (nd codeLhsT codePoo))) (eqSym templateCodeForm) refl) fp
    in eqSubst (\v -> Deriv hyp (eqn (ap1 cstf (reify templateCode)) (reify v)))
               fp2 step2

------------------------------------------------------------------------
-- Godel II
--
-- Key: reify(cGS) NEVER appears in an equation that gets ruleInst'd.
-- It only appears as the middle term of ruleTrans chains.

godelII : {hyp : Equation} -> ProofE hyp -> Consistent hyp ->
          Deriv hyp godelSentence -> Empty
godelII {hyp} ph con dG = con botDeriv
  where
  pe : ProofE godelSentence ; pe = thm14E dG ph
  enc : Term ; enc = ap2 Pair (reify (fst pe)) (reify (fst (snd pe)))

  -- corrPf: thFunTFor(enc) = reify(cGS)  [v11/v12 free, reify(cGS) is abstract]
  corrPf : Deriv hyp (eqn (ap1 thFunTFor enc) (reify cGS))
  corrPf = eqSubst (\t -> Deriv hyp (eqn (ap1 thFunTFor enc) (reify t)))
                    (eqSym cGSdef)
                    (fst (snd (snd (snd pe))) {hyp})

  -- Chain corrPf with diagFTarget: thFunTFor(enc) = cstf(reify TC)
  -- reify(cGS) is the MIDDLE term — not in the result type.
  chain : Deriv hyp (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))
  chain = ruleTrans corrPf (ruleSym diagFTarget)

  -- Instantiate G with enc: TreeEq(thFunTFor(enc), substTFor(reify TC)) = poo
  instD : Deriv hyp (eqn (ap2 TreeEq (ap1 thFunTFor enc) (ap1 substTFor (reify templateCode))) poo)
  instD = eqSubst (\eq -> Deriv hyp eq) (substGodelSentence enc) (ruleInst zero enc dG)

  -- Replace thFunTFor(enc) with cstf(reify TC) using chain:
  -- TreeEq(cstf(reify TC), substTFor(reify TC)) = poo  [v11/v12 free in substTFor only]
  step1 : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 substTFor (reify templateCode))) poo)
  step1 = ruleTrans (ruleSym (congL TreeEq (ap1 substTFor (reify templateCode)) chain)) instD

  -- ruleInst v11/v12: substTFor becomes cstf. cstf(reify TC) is closed — no traversal issue.
  -- NO reify(cGS) in this equation!
  step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) poo)
  step2 = eqSubst (\eq -> Deriv hyp eq) instForm2
                   (ruleInst v12 tgtT (ruleInst v11 (reify crTC) step1))

  -- TreeEq(X, X) = O for X = cstf(reify TC)
  selfEq : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) O)
  selfEq = treeEqSelf (ap1 cstf (reify templateCode))

  botDeriv : Deriv hyp (eqn O poo)
  botDeriv = ruleTrans (ruleSym selfEq) step2
