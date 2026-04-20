{-# OPTIONS --safe --without-K --exact-split #-}

-- V3 analog of Guard.SubstTForPrecompFast.
--
-- Heavy tree traversals (code of  thmT (var v2) , reify of templateCodeV3,
-- etc.) are cached behind an  abstract  block.  This file carefully
-- mirrors the V2 Fast variant — every definition that forces a big
-- traversal is wrapped once here and treated opaquely by downstream
-- files.  diagFTargetV3 itself lives in a separate file (GodelIV3)
-- so that it uses these cached opaque values without re-triggering
-- the traversals.
--
-- Differences from V2:
--   * thFunTFor (closed Fun1) replaced by  thmT (var v2)  — hypothesis
--     placeholder handled via  var v2  so ruleInst binds it at use-time.
--   * substTFor (with internal var 11 / var 12) replaced by
--      ap2 substOp (ap2 Pair (var v11') (var v12')) (var v1) .

module Guard.SubstTForPrecompV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstCorrect
open import Guard.SubstTForCorrect
open import Guard.SubstOp using (substOp)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)

private
  v1 : Nat ; v1 = suc zero
  v2 : Nat ; v2 = suc v1
  tgtT : Tree ; tgtT = natCode v1
  poo : Term ; poo = ap2 Pair O O
  v11' : Nat ; v11' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12' : Nat ; v12' = suc v11'

abstract
  -- The template LHS Term: TreeEq(thmT(var v2)(var 0),
  --                                substOp(Pair(var v11')(var v12'))(var v1))
  lhsTermV3 : Term
  lhsTermV3 = ap2 TreeEq (ap1 (thmT (var v2)) (var zero))
                         (ap2 substOp (ap2 Pair (var v11') (var v12')) (var v1))

  codeLhsTV3 : Tree
  codeLhsTV3 = code lhsTermV3

  codePoo : Tree
  codePoo = code poo

  codeLhsTV3NeqTagVar : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq (reify codeLhsTV3) (reify tagVar)) poo)
  codeLhsTV3NeqTagVar = codeNeqTagVarGen lhsTermV3

  codeLhsTV3NotVar : Eq (treeEq codeLhsTV3 tagVar) false
  codeLhsTV3NotVar = codeNotVar lhsTermV3

  pooSTF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codePoo))
                   (reify (codedSubst replT tgtT codePoo)))
  pooSTF replT = closedSTFCode replT tgtT poo

  csLhsTV3 : (r : Term) ->
    Eq (codedSubst (code r) tgtT codeLhsTV3) (code (subst v1 r lhsTermV3))
  csLhsTV3 r = csCorrect r v1 lhsTermV3

  csPoo : (r : Term) ->
    Eq (codedSubst (code r) tgtT codePoo) (code (subst v1 r poo))
  csPoo r = csCorrect r v1 poo

  lhsTV3STF : (replT : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify codeLhsTV3))
                   (reify (codedSubst replT tgtT codeLhsTV3)))
  lhsTV3STF replT = closedSTFCode replT tgtT lhsTermV3

  templateCodeV3 : Tree
  templateCodeV3 = nd codeLhsTV3 codePoo

  templateCodeV3Form : Eq templateCodeV3 (nd codeLhsTV3 codePoo)
  templateCodeV3Form = refl

  crTCV3 : Tree
  crTCV3 = code (reify templateCodeV3)

  templateV3 : Equation
  templateV3 = eqn lhsTermV3 poo

  godelSentenceV3 : Equation
  godelSentenceV3 = substEq v1 (reify templateCodeV3) templateV3

  cGSV3 : Tree
  cGSV3 = codeEqn godelSentenceV3

  -- Fixed-point identity: cGSV3 = codeEqn of the substituted template.
  cGSisCSV3 : Eq cGSV3 (nd (codedSubst crTCV3 tgtT codeLhsTV3)
                           (codedSubst crTCV3 tgtT codePoo))
  cGSisCSV3 = eqSym
    (eqTrans (eqCong2 nd (csLhsTV3 (reify templateCodeV3))
                         (csPoo (reify templateCodeV3)))
             (eqSym (codedSubstNd crTCV3 tgtT codeLhsTV3 codePoo codeLhsTV3NotVar)))

  cGSdefV3 : Eq cGSV3 (codeEqn godelSentenceV3)
  cGSdefV3 = refl

  cstfV3 : Fun1
  cstfV3 = closedSubstTFor (reify crTCV3) (reify (natCode v1))

  cstfV3Def : Eq cstfV3 (closedSubstTFor (reify crTCV3) (reify (natCode v1)))
  cstfV3Def = refl

  -- Equivalence between godelSentenceV3 and its expanded form (gsForm
  -- below).  The  substEq v1 (reify templateCodeV3)  inside the
  -- definition reduces via subst traversal through the small lhsTermV3
  -- structure — fast inside the abstract block.

  godelSentenceV3Form : Eq godelSentenceV3
    (eqn (ap2 TreeEq (ap1 (thmT (var v2)) (var zero))
                     (ap2 substOp (ap2 Pair (var v11') (var v12'))
                                  (reify templateCodeV3)))
         poo)
  godelSentenceV3Form = refl

  -- Schematic substF propagation lemmas.  Universally quantified — Y
  -- stays opaque under reduction, so the proof doesn't re-traverse
  -- any large sub-term.  Inside abstract, thmT/substOp unfold once;
  -- the resulting  refl  proof is cached and used as a black box.

  substThmT : (x : Nat) (r Y : Term) ->
    Eq (substF1 x r (thmT Y)) (thmT (subst x r Y))
  substThmT x r Y = refl

  substSubstOpClosed : (x : Nat) (r : Term) ->
    Eq (substF2 x r substOp) substOp
  substSubstOpClosed x r = refl

  -- substEq v2 on godelSentenceV3.  Since var v2 appears only inside
  -- thmT's hCode, the substitution propagates via substThmT.
  -- Single fused substEq lemma capturing the entire ruleInst chain.
  -- All intermediate substitutions push through the Gödel sentence in
  -- one reduction step; universally quantified args keep Agda from
  -- materializing any concrete term.

  fullyInstGS : (X0 X2 X11 X12 : Term) ->
    Eq (substEq zero X0
         (substEq v12' X12
           (substEq v11' X11
             (substEq v2 X2 godelSentenceV3))))
       (eqn (ap2 TreeEq (ap1 (thmT (subst zero X0 (subst v12' X12 (subst v11' X11 X2)))) X0)
                        (ap2 substOp
                             (ap2 Pair (subst zero X0 (subst v12' X12 X11))
                                       (subst zero X0 X12))
                             (reify templateCodeV3)))
            poo)
  fullyInstGS X0 X2 X11 X12 = refl
