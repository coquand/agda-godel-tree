{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIClassicalTrivStrong -- classical Gödel II over Triv with
-- Rose-style consistency (two-parameter e-negation form).
--
-- Target theorem:
--
--   godelIIClassicalTrivStrong :
--     Consistent Triv ->
--     Deriv Triv ConTrivRoseStrong ->
--     Empty
--
-- where the consistency is stated in Rose (1967) / Ryan (1978) style:
--
--   ConTrivRoseStrong = eqn
--     (impT (ap2 TreeEq
--              (ap1 (thmT trivCT) (var zero))
--              (ap1 eT (ap1 (thmT trivCT) (var (suc zero)))))
--           falseT)
--     trueT
--
-- Reads: "for all proof-encodings x and z, thmT trivCT x != eT(thmT
-- trivCT z)", i.e., "no theorem-index x's image equals the e-negation
-- of any theorem-index z's image" = "no theorem is the e-negation of
-- any theorem".
--
-- This is STRICTLY STRONGER than ConTrivRose (which uses the fixed
-- closed term codeBotT in place of eT(thmT trivCT (var 1)))  -- see
-- Guard/ROSE-CHAIN-DESIGN.md for the analysis of why the weaker form
-- cannot directly support Rose's Thm 18 chain.
--
-- Strategy (as in GodelIIClassicalTriv):
--
-- 1. Build  gsFromConStrong : Deriv Triv ConTrivRoseStrong ->
--                              Deriv Triv gsCR
-- 2. Compose with  godelIClassical : Deriv Triv gsCR -> Deriv Triv bot.
-- 3. Apply  Consistent Triv  to obtain Empty.
--
-- The Schema-F ingredients baseF / baseG / stepG / gsFromConWith are
-- SHARED with GodelIIClassicalTriv.agda (they do not depend on the
-- form of ConTrivRose); only the F-step premise (StepFCoreTypeStrong,
-- analogous to StepFCoreType in GodelIIClassicalTriv) is specific to
-- this variant.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.GodelIIClassicalTrivStrong where

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
open import Guard.RoseEFun using (eT ; eTCorrect ; eTReduces)
open import Guard.ThFunTForV3 using (ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)
open import Guard.GodelIIClassicalTriv
  using ( diagBody
        ; gsCRExpanded
        ; gsCRIsExpanded
        ; FF ; GG ; zz ; ss
        ; baseF ; baseG ; stepG
        ; gsFromConWith
        ; StepFType
        ; StepFCoreType
        ; stepFFromCore
        ; H_enc ; B_aux ; B_negGs
        ; dAux ; dNegGsRose
        )

------------------------------------------------------------------------
-- Local abbreviations.

private
  v1 : Nat ; v1 = suc zero
  poo : Term ; poo = ap2 Pair O O
  v0T : Term ; v0T = var zero
  v1T : Term ; v1T = var v1
  pv : Term ; pv = ap2 Pair v0T v1T

------------------------------------------------------------------------
-- The Rose-style consistency sentence over Triv (strong form).

ConTrivRoseStrong : Equation
ConTrivRoseStrong =
  eqn (impT (ap2 TreeEq
               (ap1 (thmT trivCT) (var zero))
               (ap1 eT (ap1 (thmT trivCT) (var v1))))
            falseT)
      trueT

------------------------------------------------------------------------
-- StepFCoreFromConStrong: the F-step Schema-F premise, parameterised
-- by dConStrong.
--
-- This is the key open piece.  Unlike the naive StepFCoreType (which
-- would require deriving the F-step unconditionally from Triv -- which
-- is impossible, since that would make gsCR derivable and hence Triv
-- inconsistent), StepFCoreFromConStrong takes dConStrong and produces
-- the F-step derivation.  Rose's Thm 18 chain is the intended
-- construction.

StepFCoreFromConStrong : Set
StepFCoreFromConStrong =
  Deriv Triv ConTrivRoseStrong -> StepFCoreType

------------------------------------------------------------------------
-- Top-level theorem (parameterised form).
--
-- Given a procedure that turns dConStrong into the F-step core (i.e.,
-- Rose's Thm 18 chain), produce classical Gödel II over Triv (strong
-- consistency form).
--
-- This correctly models the dependency: stepCoreFromCon needs dConStrong
-- to produce its conclusion; without dConStrong, the F-step is not
-- derivable in Triv.

godelIIClassicalTrivStrongWithCoreFromCon :
  StepFCoreFromConStrong ->
  Consistent Triv ->
  Deriv Triv ConTrivRoseStrong ->
  Empty
godelIIClassicalTrivStrongWithCoreFromCon stepCoreFromCon con dConStrong =
  con (godelIClassical
    (gsFromConWith (stepFFromCore (stepCoreFromCon dConStrong))))

------------------------------------------------------------------------
-- Rose-chain infrastructure: building blocks for stepFCoreStrong.
--
-- These are the pieces needed to assemble the Rose Thm 18 chain.
-- The remaining work is assembling them into a full
-- StepFCoreTypeStrong derivation.

------------------------------------------------------------------------
-- The universal form of dNegGsRose.
--
-- dNegGsRoseUniv: under the universal H_encUniv ("var 0 encodes
-- gsCR"), derive "TreeEq (TreeEq (thmT trivCT (var 0)) diagBody) poo
-- = falseT" (= the universal Rose-style negation of gsCR).
--
-- This is the "universal" version of dNegGsRose and is the derivation
-- that should be encoded via roseLemma1T to produce a V encoding
-- ¬gsCR.

H_encUniv : Equation
H_encUniv = eqn (ap1 (thmT trivCT) (var zero)) (reify cGSCR)

B_negGsUniv : Equation
B_negGsUniv = eqn (ap2 TreeEq (ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                                            diagBody)
                               poo)
                  (ap2 Pair O O)

dNegGsRoseUniv : Deriv H_encUniv B_negGsUniv
dNegGsRoseUniv =
  ruleTrans
    (congL TreeEq poo dAuxUniv)
    (axTreeEqLN O O)
  where
  -- dAuxUniv: under H_encUniv, derive "TreeEq (thmT trivCT (var 0))
  -- diagBody = O" (analogous to dAux but at the universal var 0).
  dAuxUniv : Deriv H_encUniv
    (eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) diagBody) O)
  dAuxUniv =
    ruleTrans
      (congL TreeEq diagBody (ruleHyp {H_encUniv}))
      (ruleTrans
        (congR TreeEq (reify cGSCR) diagFTargetCR)
        (treeEqSelf (reify cGSCR)))

-- Encoded form of dNegGsRoseUniv: applies roseLemma1T to produce a
-- Lemma1T instance for H_encUniv and B_negGsUniv, parameterised by
-- caller tPa, tPb, tCorr, tPass.

dNegGsRoseUnivEncoded :
  (tPa tPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair tPa tPb))
                   (reify (codeEqn H_encUniv)))) ->
  ((x rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT)
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs))) ->
  Lemma1T H_encUniv B_negGsUniv
dNegGsRoseUnivEncoded tPa tPb tCorr tPass =
  roseLemma1T dNegGsRoseUniv tPa tPb tCorr tPass

------------------------------------------------------------------------
-- Summary of infrastructure
--
-- Delivered in this module:
--   * ConTrivRoseStrong   : Rose-style two-parameter consistency.
--   * StepFCoreFromConStrong : correctly-typed F-step premise
--     (parameterised by dConStrong, as the F-step is NOT derivable
--     without the consistency hypothesis).
--   * godelIIClassicalTrivStrongWithCoreFromCon : the full theorem
--     reduced to StepFCoreFromConStrong.
--   * H_encUniv, B_negGsUniv, dNegGsRoseUniv : universal-var-0 form
--     of the Rose-style negation of gsCR.
--   * dNegGsRoseUnivEncoded : Lemma1T application, parameterised by
--     caller tCorr + tPass.
--
-- Reused from Guard.GodelIIClassicalTriv:
--   * diagBody, gsCRExpanded, gsCRIsExpanded
--   * FF, GG, zz, ss : Schema F ingredients
--   * baseF, baseG, stepG : Schema F premises (A), (C), (D)
--   * gsFromConWith : Schema F assembly
--   * StepFType / StepFCoreType / stepFFromCore : the F-step forms
--   * dAux / dNegGsRose : the Pair-v0-v1 instances
--
-- Reused from Guard.RoseEFun:
--   * eT : Fun1         -- the object-level e-function
--   * eTCorrect         -- ap1 eT (reify (codeEqn (eqn A B)))
--                          = reify (codeEqn (eqn (ap2 TreeEq A B)
--                                                 falseT))
--
-- The remaining open premise  StepFCoreTypeStrong  (= StepFCoreType)
-- is the Deriv:
--
--   Deriv Triv (eqn (ap2 TreeEq (ap1 (thmT trivCT) (Pair v0 v1))
--                                diagBody)
--                    poo)
--
-- for FREE v0, v1 : Term (the var 0, var 1 of gsCR).
--
-- Rose/Ryan Thm 18 chain (option alpha, Guard/ROSE-CHAIN-DESIGN.md)
-- for this premise:
--
--  1. Construct V' (a Term combinator) = Lemma1T output applied to
--     dNegGsRoseUniv with tPa, tPb = specific terms representing a
--     hypothetical gsCR-proof-encoding.  V' should satisfy:
--       under hyp = H_encUniv,  thmT trivCT V' = reify (eTree cGSCR)
--                                              = reify (codeEqn B_negGsUniv).
--  2. The key is supplying tCorr for H_encUniv polymorphically in
--     hyp.  This requires a thm14EV3-style encoder applicable at
--     non-Triv hyp, or the chain must be re-expressed via impT
--     internalisation.
--  3. Instantiate dConStrong at (var 0 := V', var 1 := Pair v0 v1)
--     and combine with eTCorrect to produce
--       impT (TreeEq (thmT trivCT V')
--                     (reify (eTree cGSCR))) falseT = trueT.
--  4. Under the assumption "Pair v0 v1 encodes gsCR":
--     - thmT trivCT V' = reify (eTree cGSCR)  (by step 1)
--     - TreeEq of equal trees = O  (treeEqSelf)
--     - impT O falseT = falseT  (impTTrueAnt)
--     - but (from step 3) impT ... = trueT -- contradiction.
--  5. Lift to Triv via contrapositive: under Triv (no H_enc),
--     Pair v0 v1 does NOT encode gsCR, so TreeEq (thmT trivCT (Pair
--     v0 v1)) (reify cGSCR) = poo.
--  6. diagBody = reify cGSCR (diagFTargetCR), so TreeEq (thmT trivCT
--     (Pair v0 v1)) diagBody = poo -- this is StepFCoreTypeStrong.
--
-- The sticky point is step 1 (supplying tCorr polymorphically).  See
-- Guard/ROSE-CHAIN-DESIGN.md for the analysis.
