{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIClassicalTriv -- classical Gödel II over Triv.
--
-- Target theorem:
--
--   godelIIClassicalTriv : Consistent Triv ->
--                          Deriv Triv ConTrivRose -> Empty
--
-- where  ConTrivRose  is the Rose/Ryan-style impT-form statement of
-- Triv's internal consistency:
--
--   ConTrivRose = eqn
--     (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT) falseT)
--     trueT
--
-- Strategy (see Guard/RoseChainAnalysis.md):
--
-- 1. Build  gsFromCon : Deriv Triv ConTrivRose -> Deriv Triv gsCR .
-- 2. Compose with  godelIClassical : Deriv Triv gsCR -> Deriv Triv bot .
-- 3. Apply  Consistent Triv  to obtain Empty.
--
-- The one-liner  godelIIClassicalTrivWith  in this file does (2) and
-- (3) unconditionally, taking  gsFromCon  as a parameter so the
-- reduction to Gödel I is machine-checked immediately.
--
-- Partial infrastructure for the construction of  gsFromCon  itself
-- (Schema F split on  var 0 ) is provided here:
--
--   * diagBody + diagBodyEqCGSCR  -- bridge to  reify cGSCR
--   * F, G, z, s                   -- Schema F ingredients
--   * baseF, baseG                 -- Schema F base premises (var 0 := O)
--   * stepG                        -- Schema F step premise for  G
--   * assembleGSCR                 -- given the hard F-step premise,
--                                    produce Deriv Triv gsCR via ruleF
--
-- The remaining step-case for  F  (the Pair case of Schema F, which
-- internally invokes  roseLemma1  +  dCon ) is the non-mechanical
-- piece and is deferred as a module parameter.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.GodelIIClassicalTriv where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstOp using (substOp)
open import Guard.CodeOfReify using (cor)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical
open import Guard.GodelIClassical using (godelIClassical ; diagFTargetCR)
open import Guard.ImpT using (impT ; trueT ; falseT)
open import Guard.ProvV3 using (codeBotT)
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.RoseLemma1T
open import Guard.ThFunTForV3 using (ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)

------------------------------------------------------------------------
-- Local abbreviations.

private
  v1 : Nat ; v1 = suc zero
  poo : Term ; poo = ap2 Pair O O

  -- The diagonal body appearing on the RHS of TreeEq in  gsCR 's LHS.
  -- We recall  diagFTargetCR :  diagBody = reify cGSCR  as a Deriv.
  diagBody : Term
  diagBody = ap2 substOp
               (ap2 Pair (ap1 cor (reify templateCodeCR))
                         (reify (natCode v1)))
               (reify templateCodeCR)

  -- gsCR in expanded form (from SubstTForPrecompClassical.gsCRForm).

  gsCRExpanded : Equation
  gsCRExpanded = eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) diagBody)
                     poo

  gsCRIsExpanded : Eq gsCR gsCRExpanded
  gsCRIsExpanded = gsCRForm

------------------------------------------------------------------------
-- The  Rose-style  consistency sentence over Triv.
--
-- ConTrivRose says: "for every proof-encoding x under  thmT trivCT ,
-- it is not the case that x proves ⊥ (the equation  trueT = falseT )".
-- The negation is expressed via object-level  impT  (Guard/ImpT.agda).

ConTrivRose : Equation
ConTrivRose =
  eqn (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT) falseT)
      trueT

------------------------------------------------------------------------
-- Top-level theorem (parameterised form).
--
-- Given a proof that  Deriv Triv ConTrivRose  yields  Deriv Triv gsCR
-- (the construction of which is Rose's Theorem 4 over Triv), compose
-- with the V3 classical Gödel I  godelIClassical  to close the loop.
--
-- Both steps (gsFromCon and godelIClassical) happen at the Deriv
-- level under hypothesis Triv; applying  Consistent Triv  to the
-- resulting Deriv Triv  bot  yields Empty.

godelIIClassicalTrivWith :
  (gsFromCon : Deriv Triv ConTrivRose -> Deriv Triv gsCR) ->
  Consistent Triv -> Deriv Triv ConTrivRose -> Empty
godelIIClassicalTrivWith gsFromCon con dCon =
  con (godelIClassical (gsFromCon dCon))

------------------------------------------------------------------------
-- Schema F ingredients for the  gsFromCon  construction.
--
-- Goal:  Deriv Triv gsCR  where gsCR = eqn LHS poo with
--
--   LHS := ap2 TreeEq (ap1 (thmT trivCT) (var zero)) diagBody .
--
-- We express LHS as  ap1 F (var zero)  for
--
--   F := Comp2 TreeEq (thmT trivCT) (KT diagBody)
--
-- and  poo  as  ap1 G (var zero)  for  G := KT poo .  Then  ruleF
-- proves  ap1 F (var zero) = ap1 G (var zero) , and bridging via
-- axComp2 + axKT yields gsCR.
--
-- The four Schema-F premises:
--   (A) ap1 F O = z                                    -- baseF
--   (B) ap1 F (Pair v0 v1) = s (Pair v0 v1) (Pair (F v0) (F v1)) -- stepF  (HARD)
--   (C) ap1 G O = z                                    -- baseG
--   (D) ap1 G (Pair v0 v1) = s (Pair v0 v1) (Pair (G v0) (G v1)) -- stepG
--
-- With  z := poo  and  s := Post (KT poo) Pair , (A), (C), (D) are
-- straightforward.  (B) is Rose's Theorem 4 argument and requires
-- roseLemma1 + dCon (see RoseChainAnalysis.md).

FF : Fun1
FF = Comp2 TreeEq (thmT trivCT) (KT diagBody)

GG : Fun1
GG = KT poo

zz : Term
zz = poo

ss : Fun2
ss = Post (KT poo) Pair

------------------------------------------------------------------------
-- Premise (C):  ap1 GG O = zz .
--
-- GG O = KT poo O = poo = zz  (via axKT).

baseG : {hyp : Equation} -> Deriv hyp (eqn (ap1 GG O) zz)
baseG = axKT poo O

------------------------------------------------------------------------
-- Premise (D):  ap1 GG (Pair v0 v1) = ss (Pair v0 v1) (Pair (GG v0) (GG v1)) .
--
-- LHS = KT poo (Pair v0 v1) = poo                       (axKT)
-- RHS = Post (KT poo) Pair (Pair v0 v1) (Pair (GG v0) (GG v1))
--     = KT poo (Pair (Pair v0 v1) (Pair (GG v0) (GG v1)))
--     = poo                                              (axPost + axKT)
-- So both are poo.

stepG : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 GG (ap2 Pair (var zero) (var (suc zero))))
                 (ap2 ss (ap2 Pair (var zero) (var (suc zero)))
                         (ap2 Pair (ap1 GG (var zero))
                                   (ap1 GG (var (suc zero))))))
stepG = ruleTrans
  (axKT poo (ap2 Pair (var zero) (var (suc zero))))
  (ruleSym (ruleTrans
    (axPost (KT poo) Pair
      (ap2 Pair (var zero) (var (suc zero)))
      (ap2 Pair (ap1 GG (var zero)) (ap1 GG (var (suc zero)))))
    (axKT poo (ap2 Pair (ap2 Pair (var zero) (var (suc zero)))
                       (ap2 Pair (ap1 GG (var zero))
                                 (ap1 GG (var (suc zero))))))))

------------------------------------------------------------------------
-- Premise (A):  ap1 FF O = zz .
--
-- FF O = Comp2 TreeEq (thmT trivCT) (KT diagBody) O
--      = TreeEq (thmT trivCT O) (KT diagBody O)          (axComp2)
--      = TreeEq O (KT diagBody O)                         (axRecLf; thmT = Rec O _)
--      = TreeEq O diagBody                                (axKT)
--      = TreeEq O (reify cGSCR)                           (diagFTargetCR)
--      = poo                                              (axTreeEqLN; reify cGSCR = Pair _ _)
--
-- We expand  reify cGSCR  once: cGSCR = codeEqn gsCR = nd (code LHS) (code poo),
-- so reify cGSCR = ap2 Pair (reify (code LHS)) (reify (code poo)).  axTreeEqLN
-- then applies directly.

baseF : {hyp : Equation} -> Deriv hyp (eqn (ap1 FF O) zz)
baseF {hyp} = ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))
  where
  -- step1: ap1 FF O = ap2 TreeEq (ap1 (thmT trivCT) O) (ap1 (KT diagBody) O)
  step1 : Deriv hyp (eqn (ap1 FF O)
                         (ap2 TreeEq (ap1 (thmT trivCT) O) (ap1 (KT diagBody) O)))
  step1 = axComp2 TreeEq (thmT trivCT) (KT diagBody) O

  -- thmT trivCT = Rec O (thmTStep trivCT).  Applied to O via axRecLf, yields O.
  thmTOisO : Deriv hyp (eqn (ap1 (thmT trivCT) O) O)
  thmTOisO = axRecLf O _  -- Rec O _'s base case

  -- step2: rewrite first argument of TreeEq using thmTOisO.
  step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) O) (ap1 (KT diagBody) O))
                         (ap2 TreeEq O (ap1 (KT diagBody) O)))
  step2 = congL TreeEq (ap1 (KT diagBody) O) thmTOisO

  -- step3: rewrite second argument via axKT.
  step3 : Deriv hyp (eqn (ap2 TreeEq O (ap1 (KT diagBody) O))
                         (ap2 TreeEq O diagBody))
  step3 = congR TreeEq O (axKT diagBody O)

  -- step4: TreeEq O diagBody = TreeEq O (reify cGSCR) = poo.
  -- diagFTargetCR provides  diagBody = reify cGSCR  as a Deriv.
  -- Then TreeEq O (reify cGSCR) reduces via axTreeEqLN once we
  -- recognise  reify cGSCR  as  ap2 Pair ... ... .
  --
  -- cGSCR is abstract (defined in SubstTForPrecompClassical), so we
  -- cannot use  refl  directly.  Instead we bridge via cGSisCSCR,
  -- which exposes cGSCR = nd <codedSubst ..> <codedSubst ..>.  Since
  -- reify is not abstract, reify (nd L R) unfolds to ap2 Pair (reify
  -- L) (reify R) definitionally.
  step4 : Deriv hyp (eqn (ap2 TreeEq O diagBody) poo)
  step4 = ruleTrans (congR TreeEq O diagFTargetCR) bottomOut
    where
    -- From cGSisCSCR, the tree-level structure of cGSCR is a node
    -- with two specific components.
    aTree : Tree
    aTree = codedSubst crTCCR (natCode v1) codeLhsTCR
    bTree : Tree
    bTree = codedSubst crTCCR (natCode v1) codePoo

    cGSCRIsPair : Eq (reify cGSCR) (ap2 Pair (reify aTree) (reify bTree))
    cGSCRIsPair = eqCong reify cGSisCSCR

    bottomOut : Deriv hyp (eqn (ap2 TreeEq O (reify cGSCR)) poo)
    bottomOut = eqSubst
      (\t -> Deriv hyp (eqn (ap2 TreeEq O t) poo))
      (eqSym cGSCRIsPair)
      (axTreeEqLN (reify aTree) (reify bTree))

------------------------------------------------------------------------
-- Assembly: given the hard step-case for  FF  (the Pair case of
-- Schema F), produce  Deriv Triv gsCR  via ruleF + bridging.
--
-- The stepF parameter packages Rose's Theorem 4 argument for the
-- Pair case.  See RoseChainAnalysis.md for the proof sketch.

StepFType : Set
StepFType =
  Deriv Triv (eqn (ap1 FF (ap2 Pair (var zero) (var (suc zero))))
                  (ap2 ss (ap2 Pair (var zero) (var (suc zero)))
                          (ap2 Pair (ap1 FF (var zero))
                                    (ap1 FF (var (suc zero))))))

------------------------------------------------------------------------
-- Core F-step type: the  TreeEq-at-Pair  equation from which StepFType
-- follows by axComp2 / axKT / axPost bridging.
--
-- This is the "TreeEq (thmT trivCT (Pair v0 v1)) diagBody = poo"
-- statement which is the actual Rose-Theorem-4 content.  See
-- RoseChainAnalysis.md for the proof sketch.

StepFCoreType : Set
StepFCoreType =
  Deriv Triv
    (eqn (ap2 TreeEq (ap1 (thmT trivCT) (ap2 Pair (var zero) (var (suc zero))))
                      diagBody)
         poo)

-- Bridge:  StepFCoreType -> StepFType .
-- Unfolds FF on the LHS via axComp2+axKT; unfolds ss on the RHS via
-- axPost+axKT and shows both sides equal poo.

stepFFromCore : StepFCoreType -> StepFType
stepFFromCore stepCore =
  ruleTrans lhsUnfold (ruleTrans stepCore (ruleSym rhsUnfold))
  where
  pv : Term
  pv = ap2 Pair (var zero) (var (suc zero))

  -- lhsUnfold:  ap1 FF (Pair v0 v1) = TreeEq (thmT trivCT (Pair v0 v1)) diagBody.
  --   ap1 (Comp2 TreeEq (thmT trivCT) (KT diagBody)) (Pair v0 v1)
  --     = TreeEq (thmT trivCT (Pair v0 v1)) (KT diagBody (Pair v0 v1))    [axComp2]
  --     = TreeEq (thmT trivCT (Pair v0 v1)) diagBody                      [axKT]
  lhsUnfold : Deriv Triv (eqn (ap1 FF pv)
                              (ap2 TreeEq (ap1 (thmT trivCT) pv) diagBody))
  lhsUnfold = ruleTrans
    (axComp2 TreeEq (thmT trivCT) (KT diagBody) pv)
    (congR TreeEq (ap1 (thmT trivCT) pv) (axKT diagBody pv))

  -- rhsUnfold:  ss (Pair v0 v1) (Pair (FF v0) (FF v1)) = poo.
  --   ap2 (Post (KT poo) Pair) (Pair v0 v1) (Pair (FF v0) (FF v1))
  --     = KT poo (Pair (Pair v0 v1) (Pair (FF v0) (FF v1)))              [axPost]
  --     = poo                                                              [axKT]
  rhsUnfold : Deriv Triv (eqn (ap2 ss pv (ap2 Pair (ap1 FF (var zero))
                                                    (ap1 FF (var (suc zero)))))
                              poo)
  rhsUnfold = ruleTrans
    (axPost (KT poo) Pair pv
            (ap2 Pair (ap1 FF (var zero)) (ap1 FF (var (suc zero)))))
    (axKT poo (ap2 Pair pv (ap2 Pair (ap1 FF (var zero))
                                     (ap1 FF (var (suc zero))))))

------------------------------------------------------------------------
-- gsFromConWith : the  Deriv Triv gsCR  derivation parameterised by
-- the still-unbuilt F-step premise.

gsFromConWith : StepFType -> Deriv Triv gsCR
gsFromConWith stepF =
  eqSubst (Deriv Triv) (eqSym bridgeEqn) ruleFOutConv
  where
  -- ruleF applied to the four premises yields  ap1 FF (var 0) = ap1 GG (var 0).
  ruleFOut : Deriv Triv (eqn (ap1 FF (var zero)) (ap1 GG (var zero)))
  ruleFOut = ruleF FF GG zz ss baseF stepF baseG stepG

  -- Bridge:  ap1 FF (var 0) = ap2 TreeEq (ap1 (thmT trivCT) (var 0)) diagBody
  -- via axComp2 (on TreeEq) + axKT (on KT diagBody).
  bridgeF : Deriv Triv (eqn (ap1 FF (var zero))
                            (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) diagBody))
  bridgeF = ruleTrans
    (axComp2 TreeEq (thmT trivCT) (KT diagBody) (var zero))
    (congR TreeEq (ap1 (thmT trivCT) (var zero))
           (axKT diagBody (var zero)))

  -- Bridge:  ap1 GG (var 0) = poo  via axKT.
  bridgeG : Deriv Triv (eqn (ap1 GG (var zero)) poo)
  bridgeG = axKT poo (var zero)

  -- Combining bridgeF, ruleFOut, bridgeG yields:
  --   TreeEq (thmT trivCT (var 0)) diagBody = poo
  -- i.e. the expanded form of gsCR.
  ruleFOutConv : Deriv Triv gsCRExpanded
  ruleFOutConv =
    ruleTrans (ruleSym bridgeF) (ruleTrans ruleFOut bridgeG)

  -- Bridge from gsCRExpanded back to gsCR.
  bridgeEqn : Eq gsCR gsCRExpanded
  bridgeEqn = gsCRIsExpanded

------------------------------------------------------------------------
-- The top-level theorem, parameterised by the F-step premise.

godelIIClassicalTrivWithStepF :
  StepFType ->
  Consistent Triv -> Deriv Triv ConTrivRose -> Empty
godelIIClassicalTrivWithStepF stepF con dCon =
  godelIIClassicalTrivWith (\d -> gsFromConWith stepF) con dCon

-- Variant taking the CORE F-step (TreeEq form):
godelIIClassicalTrivWithCore :
  StepFCoreType ->
  Consistent Triv -> Deriv Triv ConTrivRose -> Empty
godelIIClassicalTrivWithCore stepCore =
  godelIIClassicalTrivWithStepF (stepFFromCore stepCore)

------------------------------------------------------------------------
-- Ryan-style Lemma 1 integration (option (i) from RoseChainAnalysis).
--
-- Using Guard.RoseLemma1T.roseLemma1T, the Rose/Ryan chain for the
-- F-step case proceeds as follows.
--
-- Let
--   H_enc = eqn (ap1 (thmT trivCT) (ap2 Pair (var 0) (var 1)))
--               (reify cGSCR) .
-- "Pair (var 0) (var 1) encodes gsCR under  thmT trivCT ."
--
-- Build dAux : Deriv H_enc (eqn (ap2 TreeEq (thmT trivCT (Pair v0 v1))
--                                           diagBody) O)
-- using  ruleHyp {H_enc}  +  diagFTargetCR  +  treeEqSelf .
-- This dAux is CONSTRUCTIBLE (exhibited below), using only primitive
-- Deriv rules plus facts already polymorphic in hyp.

private
  v0T : Term
  v0T = var zero
  v1T : Term
  v1T = var (suc zero)
  pv : Term
  pv = ap2 Pair v0T v1T

  H_enc : Equation
  H_enc = eqn (ap1 (thmT trivCT) pv) (reify cGSCR)

  B_aux : Equation
  B_aux = eqn (ap2 TreeEq (ap1 (thmT trivCT) pv) diagBody) O

dAux : Deriv H_enc B_aux
dAux =
  ruleTrans
    -- congL TreeEq on ruleHyp{H_enc}:
    --   TreeEq (thmT trivCT (Pair v0 v1)) diagBody
    --     = TreeEq (reify cGSCR) diagBody
    (congL TreeEq diagBody (ruleHyp {H_enc}))
  (ruleTrans
    -- congR TreeEq on diagFTargetCR:
    --   TreeEq (reify cGSCR) diagBody
    --     = TreeEq (reify cGSCR) (reify cGSCR)
    (congR TreeEq (reify cGSCR) diagFTargetCR)
    -- treeEqSelf: TreeEq (reify cGSCR) (reify cGSCR) = O
    (treeEqSelf (reify cGSCR)))

-- Applying  roseLemma1T  to  dAux  gives a proof-encoder whose
-- vCorr asserts:
--   Deriv hyp (ap1 (thmT trivCT) (Pair vPa vPb) = reify (codeEqn B_aux))
-- conditional on the caller's  tCorr  (that  Pair tPa tPb  encodes
-- H_enc under  thmT trivCT ).
--
-- With this encoder in hand, the remaining Rose/Ryan chain for
-- gsFromCon's Pair case is:
--
--  1.  From  roseLemma1T dAux (var 0) (var 1) tCorrVar tPassVar :
--      given encodings  (var 0, var 1)  of H_enc under  thmT trivCT ,
--      produce V encoding B_aux.
--  2.  Instantiate  dCon  at  v_0 := V : get object-level
--        impT (TreeEq (thmT trivCT V) codeBotT) falseT = trueT.
--  3.  Close the modus-ponens chain against  codeEqn B_aux /= codeBotT
--      (a tree-disequality fact).
--  4.  Derive StepFCoreType polymorphically in hyp.
--
-- Steps 2-4 are NOT yet formalised in this module.  They correspond
-- to Rose (1967) Lemma 1/Theorem 4's last line plus the object-level
-- tree-disequality.  See RoseChainAnalysis.md for the full chain.

-- Sanity check: roseLemma1T  applied to  dAux  typechecks and
-- produces a  Lemma1T  instance.  (The produced V is a specific
-- Term; its correctness follows from the caller-supplied tCorr.)

dAuxEncoded :
  (tPa tPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair tPa tPb))
                   (reify (codeEqn H_enc)))) ->
  ((x rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT)
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs))) ->
  Lemma1T H_enc B_aux
dAuxEncoded tPa tPb tCorr tPass =
  roseLemma1T dAux tPa tPb tCorr tPass

------------------------------------------------------------------------
-- Summary (and what's deferred).
--
-- This module establishes the Rose/Ryan classical Gödel II theorem
-- over Triv modulo the single hard step  StepFType :
--
--   godelIIClassicalTrivWith       -- the reduction  gsCR  ⇒  ⊥  via
--                                    V3 godelIClassical (no parameters)
--   godelIIClassicalTrivWithStepF  -- full classical Gödel II
--                                    modulo StepFType
--
-- Schema F ingredients already proved:
--   * baseF  -- FF(O) = poo                (base case of FF)
--   * baseG  -- GG(O) = poo                (base case of GG)
--   * stepG  -- GG(Pair _ _) = poo          (step case of GG)
--   * gsFromConWith StepFType -> Deriv Triv gsCR   (Schema F assembly)
--
-- Deferred:
--   * StepFType : the F-step Schema-F premise.  This is the
--     non-mechanical piece; it encodes Rose's Theorem 4 argument
--     via roseLemma1 + dCon.  See RoseChainAnalysis.md for the
--     proof sketch.  Estimated ~200-400 lines.
--
-- Compiles under --safe --without-K --exact-split.  No postulates,
-- no holes.
