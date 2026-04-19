{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.SubstOp -- dynamic substitution via the RecP primitive.
--
-- substOp : Fun2  such that for every Term t and Nat x
--   ap2 substOp (ap2 Pair (reify (code t)) (reify (natCode x))) (reify (code l))
--     = reify (code (subst x t l))
--
-- This is the dynamic counterpart of  closedSubstTFor tC xC  from
-- Guard.SubstTForCorrect : instead of tC, xC being baked in as
-- meta-level Term parameters, they are extracted from the runtime
-- pair  Pair tC xC  passed as the  RecP  param.
--
-- Used by V3's  case23V3  (the ruleInst case) -- see Guard.Thm14EV3.

module Guard.SubstOp where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstTFor using (tagVarT)
open import Guard.SubstTForCorrect using (closedSubstTFor ; closedSTFCode)
open import Guard.SubstCorrect using (csCorrect)

------------------------------------------------------------------------
-- Accessors into the RecP-step's orig argument.
--
-- At a RecP-step call, orig = Pair param (Pair a b) where
--   param = Pair tC xC     (injected from RecP's first arg)
--   (a, b) = the current node's children
-- and recs = (rec_a, rec_b).

private
  tCF : Fun2
  tCF = Lift (Comp Fst Fst)       -- Fst(Fst orig) = tC

  xCF : Fun2
  xCF = Lift (Comp Snd Fst)       -- Snd(Fst orig) = xC

  curNodeF : Fun2
  curNodeF = Lift Snd              -- Snd orig = Pair a b

  aF : Fun2
  aF = Lift (Comp Fst Snd)         -- Fst(Snd orig) = a

  bF : Fun2
  bF = Lift (Comp Snd Snd)         -- Snd(Snd orig) = b

  recsF : Fun2
  recsF = Post Snd Pair            -- Snd(Pair orig recs) = recs

  -- Named sub-Fun2s of stepSubstP, so we can apply congruence/axFan
  -- at each layer without having to expand the whole nest.

  isVarFP : Fun2
  isVarFP = Fan aF (Lift (KT tagVarT)) TreeEq

  matchFP : Fun2
  matchFP = Fan bF xCF TreeEq

  replOrigFP : Fun2
  replOrigFP = Fan tCF curNodeF Pair

  innerFP : Fun2
  innerFP = Fan matchFP replOrigFP IfLf

  outerFP : Fun2
  outerFP = Fan innerFP recsF Pair

------------------------------------------------------------------------
-- The step function for substOp.
--
--   isVar := TreeEq(a, tagVarT)
--   if isVar = O:
--     if TreeEq(b, xC) = O: return tC
--     else:                  return curNode = Pair a b
--   else:
--     return recs

stepSubstP : Fun2
stepSubstP = Fan isVarFP outerFP IfLf

------------------------------------------------------------------------
-- substOp : Fun2
--
-- ap2 substOp p l -- apply substitution described by p to target l.

substOp : Fun2
substOp = RecP stepSubstP

------------------------------------------------------------------------
-- Derived Lf and Nd reductions on reified Tree inputs.

substOpLf : (tC xC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair tC xC) O) O)
substOpLf tC xC = axRecPLf stepSubstP (ap2 Pair tC xC)

substOpNd : (tC xC aT bT : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair tC xC) (ap2 Pair aT bT))
                 (ap2 stepSubstP (ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT))
                                 (ap2 Pair (ap2 substOp (ap2 Pair tC xC) aT)
                                           (ap2 substOp (ap2 Pair tC xC) bT))))
substOpNd tC xC aT bT = axRecPNd stepSubstP (ap2 Pair tC xC) aT bT

------------------------------------------------------------------------
-- closedSubstTFor Lf reduction.

closedSubstTForLf : (tC xC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor tC xC) O) O)
closedSubstTForLf tC xC = axRecLf O _

------------------------------------------------------------------------
-- Shadow replica of the cStep that lives inside  closedSubstTFor tC xC .
-- This Fun2 is *definitionally equal* to the private cStep there, so
-- recNdRed can unfold Rec to it directly.

private
  cStepOf : Term -> Term -> Fun2
  cStepOf tC xC =
    Fan (Fan (Lift Fst) (Lift (KT tagVarT)) TreeEq)
        (Fan (Fan (Fan (Lift Snd) (Lift (KT xC)) TreeEq)
                  (Fan (Lift (KT tC)) Const Pair) IfLf)
             (Post Snd Pair) Pair) IfLf

------------------------------------------------------------------------
-- Canonical form that both stepSubstP (with the parameterised orig)
-- and cStepOf (with the closed orig) reduce to.

private
  canonForm : (tC xC aT bT recs : Term) -> Term
  canonForm tC xC aT bT recs =
    ap2 IfLf (ap2 TreeEq aT tagVarT)
        (ap2 Pair (ap2 IfLf (ap2 TreeEq bT xC)
                            (ap2 Pair tC (ap2 Pair aT bT)))
                  recs)

------------------------------------------------------------------------
-- Accessor reductions for stepSubstP's orig = Pair (Pair tC xC) (Pair aT bT).

private
  aFRed : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    Deriv hyp (eqn (ap2 aF origP recs) aT)
  aFRed tC xC aT bT recs =
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    ruleTrans (liftRed (Comp Fst Snd) origP recs)
    (ruleTrans (axComp Fst Snd origP)
    (ruleTrans (cong1 Fst (axSnd (ap2 Pair tC xC) (ap2 Pair aT bT)))
               (axFst aT bT)))

  bFRed : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    Deriv hyp (eqn (ap2 bF origP recs) bT)
  bFRed tC xC aT bT recs =
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    ruleTrans (liftRed (Comp Snd Snd) origP recs)
    (ruleTrans (axComp Snd Snd origP)
    (ruleTrans (cong1 Snd (axSnd (ap2 Pair tC xC) (ap2 Pair aT bT)))
               (axSnd aT bT)))

  tCFRed : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    Deriv hyp (eqn (ap2 tCF origP recs) tC)
  tCFRed tC xC aT bT recs =
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    ruleTrans (liftRed (Comp Fst Fst) origP recs)
    (ruleTrans (axComp Fst Fst origP)
    (ruleTrans (cong1 Fst (axFst (ap2 Pair tC xC) (ap2 Pair aT bT)))
               (axFst tC xC)))

  xCFRed : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    Deriv hyp (eqn (ap2 xCF origP recs) xC)
  xCFRed tC xC aT bT recs =
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    ruleTrans (liftRed (Comp Snd Fst) origP recs)
    (ruleTrans (axComp Snd Fst origP)
    (ruleTrans (cong1 Snd (axFst (ap2 Pair tC xC) (ap2 Pair aT bT)))
               (axSnd tC xC)))

  curNodeFRed : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    Deriv hyp (eqn (ap2 curNodeF origP recs) (ap2 Pair aT bT))
  curNodeFRed tC xC aT bT recs =
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    ruleTrans (liftRed Snd origP recs)
              (axSnd (ap2 Pair tC xC) (ap2 Pair aT bT))

  recsFRed : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    Deriv hyp (eqn (ap2 recsF origP recs) recs)
  recsFRed tC xC aT bT recs =
    let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT) in
    ruleTrans (postRed Snd Pair origP recs) (axSnd origP recs)

------------------------------------------------------------------------
-- Step-equivalence at the parameterised orig:
--   stepSubstP (Pair (Pair tC xC) (Pair aT bT)) recs  ==  canonForm ...

stepSubstPAtPair : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 stepSubstP (ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT)) recs)
                 (canonForm tC xC aT bT recs))
stepSubstPAtPair tC xC aT bT recs {hyp} =
  let origP = ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT)
      -- sub-targets at each layer
      tgtIsVar    = ap2 TreeEq aT tagVarT
      tgtMatch    = ap2 TreeEq bT xC
      tgtReplOrig = ap2 Pair tC (ap2 Pair aT bT)
      tgtInner    = ap2 IfLf tgtMatch tgtReplOrig
      tgtOuter    = ap2 Pair tgtInner recs
      -- isVarFP: ap2 isVarFP origP recs == TreeEq aT tagVarT
      isVarEval : Deriv hyp (eqn (ap2 isVarFP origP recs) tgtIsVar)
      isVarEval =
        ruleTrans (fanRed aF (Lift (KT tagVarT)) TreeEq origP recs)
        (ruleTrans (congL TreeEq (ap2 (Lift (KT tagVarT)) origP recs)
                          (aFRed tC xC aT bT recs))
                   (congR TreeEq aT (constF2Red tagVarT origP recs)))
      -- matchFP: ap2 matchFP origP recs == TreeEq bT xC
      matchEval : Deriv hyp (eqn (ap2 matchFP origP recs) tgtMatch)
      matchEval =
        ruleTrans (fanRed bF xCF TreeEq origP recs)
        (ruleTrans (congL TreeEq (ap2 xCF origP recs) (bFRed tC xC aT bT recs))
                   (congR TreeEq bT (xCFRed tC xC aT bT recs)))
      -- replOrigFP: ap2 replOrigFP origP recs == Pair tC (Pair aT bT)
      replOrigEval : Deriv hyp (eqn (ap2 replOrigFP origP recs) tgtReplOrig)
      replOrigEval =
        ruleTrans (fanRed tCF curNodeF Pair origP recs)
        (ruleTrans (congL Pair (ap2 curNodeF origP recs) (tCFRed tC xC aT bT recs))
                   (congR Pair tC (curNodeFRed tC xC aT bT recs)))
      -- innerFP: ap2 innerFP origP recs == IfLf tgtMatch tgtReplOrig
      innerEval : Deriv hyp (eqn (ap2 innerFP origP recs) tgtInner)
      innerEval =
        ruleTrans (fanRed matchFP replOrigFP IfLf origP recs)
        (ruleTrans (congL IfLf (ap2 replOrigFP origP recs) matchEval)
                   (congR IfLf tgtMatch replOrigEval))
      -- outerFP: ap2 outerFP origP recs == Pair tgtInner recs
      outerEval : Deriv hyp (eqn (ap2 outerFP origP recs) tgtOuter)
      outerEval =
        ruleTrans (fanRed innerFP recsF Pair origP recs)
        (ruleTrans (congL Pair (ap2 recsF origP recs) innerEval)
                   (congR Pair tgtInner (recsFRed tC xC aT bT recs)))
  in ruleTrans (fanRed isVarFP outerFP IfLf origP recs)
     (ruleTrans (congL IfLf (ap2 outerFP origP recs) isVarEval)
                (congR IfLf tgtIsVar outerEval))

------------------------------------------------------------------------
-- Accessor reductions for cStepOf's orig = Pair aT bT.

private
  cAFRed : (aT bT recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (Lift Fst) (ap2 Pair aT bT) recs) aT)
  cAFRed aT bT recs =
    ruleTrans (liftRed Fst (ap2 Pair aT bT) recs) (axFst aT bT)

  cBFRed : (aT bT recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (Lift Snd) (ap2 Pair aT bT) recs) bT)
  cBFRed aT bT recs =
    ruleTrans (liftRed Snd (ap2 Pair aT bT) recs) (axSnd aT bT)

  cRecsFRed : (aT bT recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (Post Snd Pair) (ap2 Pair aT bT) recs) recs)
  cRecsFRed aT bT recs =
    ruleTrans (postRed Snd Pair (ap2 Pair aT bT) recs)
              (axSnd (ap2 Pair aT bT) recs)

------------------------------------------------------------------------
-- Step-equivalence at the closed orig:
--   cStepOf tC xC (Pair aT bT) recs  ==  canonForm ...

cStepOfAtPair : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (cStepOf tC xC) (ap2 Pair aT bT) recs)
                 (canonForm tC xC aT bT recs))
cStepOfAtPair tC xC aT bT recs {hyp} =
  let origC = ap2 Pair aT bT
      isVarFC    = Fan (Lift Fst) (Lift (KT tagVarT)) TreeEq
      matchFC    = Fan (Lift Snd) (Lift (KT xC)) TreeEq
      replOrigFC = Fan (Lift (KT tC)) Const Pair
      innerFC    = Fan matchFC replOrigFC IfLf
      outerFC    = Fan innerFC (Post Snd Pair) Pair
      tgtIsVar    = ap2 TreeEq aT tagVarT
      tgtMatch    = ap2 TreeEq bT xC
      tgtReplOrig = ap2 Pair tC origC
      tgtInner    = ap2 IfLf tgtMatch tgtReplOrig
      tgtOuter    = ap2 Pair tgtInner recs
      -- isVarFC eval
      isVarEval : Deriv hyp (eqn (ap2 isVarFC origC recs) tgtIsVar)
      isVarEval =
        ruleTrans (fanRed (Lift Fst) (Lift (KT tagVarT)) TreeEq origC recs)
        (ruleTrans (congL TreeEq (ap2 (Lift (KT tagVarT)) origC recs)
                          (cAFRed aT bT recs))
                   (congR TreeEq aT (constF2Red tagVarT origC recs)))
      -- matchFC eval
      matchEval : Deriv hyp (eqn (ap2 matchFC origC recs) tgtMatch)
      matchEval =
        ruleTrans (fanRed (Lift Snd) (Lift (KT xC)) TreeEq origC recs)
        (ruleTrans (congL TreeEq (ap2 (Lift (KT xC)) origC recs)
                          (cBFRed aT bT recs))
                   (congR TreeEq bT (constF2Red xC origC recs)))
      -- replOrigFC eval
      replOrigEval : Deriv hyp (eqn (ap2 replOrigFC origC recs) tgtReplOrig)
      replOrigEval =
        ruleTrans (fanRed (Lift (KT tC)) Const Pair origC recs)
        (ruleTrans (congL Pair (ap2 Const origC recs) (constF2Red tC origC recs))
                   (congR Pair tC (axConst origC recs)))
      -- innerFC eval
      innerEval : Deriv hyp (eqn (ap2 innerFC origC recs) tgtInner)
      innerEval =
        ruleTrans (fanRed matchFC replOrigFC IfLf origC recs)
        (ruleTrans (congL IfLf (ap2 replOrigFC origC recs) matchEval)
                   (congR IfLf tgtMatch replOrigEval))
      -- outerFC eval
      outerEval : Deriv hyp (eqn (ap2 outerFC origC recs) tgtOuter)
      outerEval =
        ruleTrans (fanRed innerFC (Post Snd Pair) Pair origC recs)
        (ruleTrans (congL Pair (ap2 (Post Snd Pair) origC recs) innerEval)
                   (congR Pair tgtInner (cRecsFRed aT bT recs)))
  in ruleTrans (fanRed isVarFC outerFC IfLf origC recs)
     (ruleTrans (congL IfLf (ap2 outerFC origC recs) isVarEval)
                (congR IfLf tgtIsVar outerEval))

------------------------------------------------------------------------
-- closedSubstTFor at a Pair input: unfold Rec to cStepOf, then reduce
-- to canonForm with the right recs.

closedSTFAtPair : (tC xC aT bT : Term) -> {hyp : Equation} ->
  let cstf = closedSubstTFor tC xC
      recs = ap2 Pair (ap1 cstf aT) (ap1 cstf bT)
  in Deriv hyp (eqn (ap1 cstf (ap2 Pair aT bT))
                    (canonForm tC xC aT bT recs))
closedSTFAtPair tC xC aT bT =
  ruleTrans (recNdRed O (cStepOf tC xC) aT bT)
            (cStepOfAtPair tC xC aT bT _)

------------------------------------------------------------------------
-- Main equivalence: substOp == closedSubstTFor on reified trees.

substOpEquiv : (tC xC : Term) (c : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair tC xC) (reify c))
                 (ap1 (closedSubstTFor tC xC) (reify c)))
substOpEquiv tC xC lf =
  ruleTrans (substOpLf tC xC) (ruleSym (closedSubstTForLf tC xC))
substOpEquiv tC xC (nd a b) {hyp} =
  let cstf     = closedSubstTFor tC xC
      A        = reify a
      B        = reify b
      paramT   = ap2 Pair tC xC
      origP    = ap2 Pair paramT (ap2 Pair A B)
      subA     = ap2 substOp paramT A
      subB     = ap2 substOp paramT B
      cstfA    = ap1 cstf A
      cstfB    = ap1 cstf B
      recSubst = ap2 Pair subA subB
      recCstf  = ap2 Pair cstfA cstfB
      ihA      = substOpEquiv tC xC a
      ihB      = substOpEquiv tC xC b
      -- Combine IHs into one equation on the recs pair.
      ihPair : Deriv hyp (eqn recSubst recCstf)
      ihPair = ruleTrans (congL Pair subB ihA)
                         (congR Pair cstfA ihB)
      -- LHS chain: substOp -> stepSubstP -> canonForm
      s1 : Deriv hyp (eqn (ap2 substOp paramT (ap2 Pair A B))
                          (ap2 stepSubstP origP recSubst))
      s1 = substOpNd tC xC A B
      s2 : Deriv hyp (eqn (ap2 stepSubstP origP recSubst)
                          (ap2 stepSubstP origP recCstf))
      s2 = congR stepSubstP origP ihPair
      s3 : Deriv hyp (eqn (ap2 stepSubstP origP recCstf)
                          (canonForm tC xC A B recCstf))
      s3 = stepSubstPAtPair tC xC A B recCstf
      -- RHS chain: closedSubstTFor -> canonForm (via cStepOf)
      s4 : Deriv hyp (eqn (ap1 cstf (ap2 Pair A B))
                          (canonForm tC xC A B recCstf))
      s4 = closedSTFAtPair tC xC A B
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 (ruleSym s4)))

------------------------------------------------------------------------
-- Final correctness: substOp computes the reified code of subst.

substOpCorrect : (t : Term) (x : Nat) (l : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify (code t)) (reify (natCode x)))
                              (reify (code l)))
                 (reify (code (subst x t l))))
substOpCorrect t x l {hyp} =
  let tC       = reify (code t)
      xC       = reify (natCode x)
      cstf     = closedSubstTFor tC xC
      stepEq   = substOpEquiv tC xC (code l)
      -- closedSTFCode : cstf (reify (code l)) == reify (codedSubst (code t) (natCode x) (code l))
      codedEq  = closedSTFCode (code t) (natCode x) l
      -- csCorrect : codedSubst (code t) (natCode x) (code l) == code (subst x t l)
      metaEq   = csCorrect t x l
      -- Transport codedEq's RHS via the metalevel equation metaEq.
      rhsEq : Deriv hyp (eqn (ap1 cstf (reify (code l))) (reify (code (subst x t l))))
      rhsEq = eqSubst (\c' -> Deriv hyp (eqn (ap1 cstf (reify (code l))) (reify c')))
                      metaEq codedEq
  in ruleTrans stepEq rhsEq
