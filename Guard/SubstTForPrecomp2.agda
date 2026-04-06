{-# OPTIONS --safe --without-K --exact-split #-}

-- Level 2: assembles lhsT-level closedSTFCode from opaque Level 1 pieces.
-- No normalization of codeF1 thFunTFor — uses abstract thfCode/stfCode/thfSTF/stfSTF.

module Guard.SubstTForPrecomp2 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstCorrect using (codeF2NotVar)
open import Guard.SubstTForCorrect
open import Guard.SubstTForPrecomp

private
  v1 : Nat ; v1 = suc zero
  tgtT : Tree ; tgtT = natCode v1

abstract
  lhsTSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codeLhsT))
                   (reify (codedSubst replT tgtT codeLhsT)))
  lhsTSTF replT {hyp} =
    let poo' = ap2 Pair O O
        cVar0 = nd tagVar lf
        cVarV1 = nd tagVar (natCode v1)
        cThF = nd tagAp1 (nd thfCode cVar0)
        cStF = nd tagAp1 (nd stfCode cVarV1)
        -- cThF ≠ tagVar: reify cThF = Pair(Pair(O, Pair(O,O)), ...) — f1f2NeqTagVar pattern
        cThFNeq : {h : Equation} -> Deriv h (eqn (ap2 TreeEq (reify cThF) (reify tagVar)) poo')
        cThFNeq = f1f2NeqTagVar (ap2 Pair O O) (ap2 Pair (reify thfCode) (reify cVar0))
        cThFNV : Eq (treeEq cThF tagVar) false
        cThFNV = refl
        -- cStF ≠ tagVar: same pattern
        cStFNeq : {h : Equation} -> Deriv h (eqn (ap2 TreeEq (reify cStF) (reify tagVar)) poo')
        cStFNeq = f1f2NeqTagVar (ap2 Pair O O) (ap2 Pair (reify stfCode) (reify cVarV1))
        cStFNV : Eq (treeEq cStF tagVar) false
        cStFNV = refl
        ihVar0 = closedSTFCode replT tgtT (var zero)
        ihVarV1 = closedSTFCode replT tgtT (var v1)
        ihTeq = closedSTFF2 replT tgtT TreeEq
        ihThFVar = closedSTFNd replT tgtT thfCode cVar0 thfCodeNeqTagVar thfCodeNotVar (thfSTF replT) ihVar0
        ihAp1ThF = closedSTFNd replT tgtT tagAp1 (nd thfCode cVar0) tagAp1NeqTagVar refl
                     (closedSTFTagAp1 replT tgtT) ihThFVar
        ihStFVar = closedSTFNd replT tgtT stfCode cVarV1 stfCodeNeqTagVar stfCodeNotVar (stfSTF replT) ihVarV1
        ihAp1StF = closedSTFNd replT tgtT tagAp1 (nd stfCode cVarV1) tagAp1NeqTagVar refl
                     (closedSTFTagAp1 replT tgtT) ihStFVar
        ihInner = closedSTFNd replT tgtT cThF cStF cThFNeq cThFNV ihAp1ThF ihAp1StF
        assembled = closedSTFNd replT tgtT tagAp2 (nd (codeF2 TreeEq) (nd cThF cStF)) tagAp2NeqTagVar refl
                      (closedSTFTagAp2 replT tgtT)
                      (closedSTFNd replT tgtT (codeF2 TreeEq) (nd cThF cStF) (codeF2NeqTagVar TreeEq) (codeF2NotVar TreeEq)
                        ihTeq ihInner)
    in eqSubst {Tree} (\c -> Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify c)) (reify (codedSubst replT tgtT c))))
               (eqSym codeLhsTForm) assembled
