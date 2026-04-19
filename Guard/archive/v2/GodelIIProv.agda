{-# OPTIONS --safe --without-K --exact-split #-}

-- Goedel II, presented through the Prov modality.
--
-- This file is a parallel, modal-style presentation of the result
-- already proved in Guard.GodelIIFull; the original file is kept
-- unchanged.  The proof reads:
--
--   provBot : Prov (eqn trueT falseT)          -- Goedel I internalized
--   conToBot dCon =                            -- Goedel II
--     let step = rewrite thFunTFor(enc provBot) = codeBotT into
--                        (conSentence at enc provBot)
--     in diagContradict codeBotT step
--
-- which is essentially the Dijk--Gietelink-Oldenziel Cantor-diagonal
-- argument applied at the level of Prov instead of at the level of
-- AU subobjects.

module Guard.GodelIIProv where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.SubstTForPrecomp
  using (godelSentence ; cGS ; cGSdef ; cstf ;
         templateCode ; crTC ;
         substGodelSentence ; instForm2)
open import Guard.SubstTFor using (substTFor)
open import Guard.GodelII using (treeEqSelf ; diagFTarget)
open import Guard.Thm14E using (ProofE ; thm14E)
open import Guard.ProofEAny using (mkProofEAny)
open import Guard.Prov

------------------------------------------------------------------------
-- Consistency statement.

codeBot : Tree
codeBot = codeEqn (eqn trueT falseT)

codeBotT : Term
codeBotT = reify codeBot

conSentence : Equation
conSentence = eqn (ap2 TreeEq (ap1 thFunTFor (var zero)) codeBotT) falseT

------------------------------------------------------------------------
-- Goedel I, internalized.
--
-- We build the standard Goedel-I derivation (with hyp = godelSentence),
-- then package it via `necessitation` into Prov.  The tail of the
-- derivation is written with `diagContradict` to make visible that
-- Goedel I itself ends in the same Cantor-diagonal collapse.

private
  v1  : Nat ; v1  = suc zero
  v11 : Nat
  v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat ; v12 = suc v11
  tgtT : Term ; tgtT = reify (natCode v1)

  mkPH : (eq : Equation) -> ProofE eq
  mkPH (eqn l r) = mkProofEAny l r

  godelIDeriv : Deriv godelSentence (eqn trueT falseT)
  godelIDeriv =
    let hyp    = godelSentence
        dG     = ruleHyp {godelSentence}
        ph     = mkPH godelSentence
        pe     = thm14E dG ph
        enc    = ap2 Pair (reify (fst pe)) (reify (fst (snd pe)))
        corrPf : Deriv hyp (eqn (ap1 thFunTFor enc) (reify cGS))
        corrPf = eqSubst (\t -> Deriv hyp (eqn (ap1 thFunTFor enc) (reify t)))
                          (eqSym cGSdef)
                          (fst (snd (snd (snd pe))) {hyp})
        chain  = ruleTrans corrPf (ruleSym (diagFTarget {hyp}))
        instD  = eqSubst (\eq -> Deriv hyp eq)
                          (substGodelSentence enc)
                          (ruleInst zero enc dG)
        step1  = ruleTrans
                   (ruleSym (congL TreeEq (ap1 substTFor (reify templateCode)) chain))
                   instD
        step2  = eqSubst (\eq -> Deriv hyp eq) instForm2
                          (ruleInst v12 tgtT (ruleInst v11 (reify crTC) step1))
    in diagContradict (ap1 cstf (reify templateCode)) step2

provBot : Prov (eqn trueT falseT)
provBot = necessitation (mkPH godelSentence) godelIDeriv

------------------------------------------------------------------------
-- Goedel II via diagContradict.

conToBot : {hyp : Equation} ->
           Deriv hyp conSentence ->
           Deriv hyp (eqn trueT falseT)
conToBot {hyp} dCon =
  let conInst = ruleInst zero (enc provBot) dCon
      step    = ruleTrans
                  (ruleSym (congL TreeEq codeBotT (corr provBot {hyp})))
                  conInst
  in diagContradict codeBotT step

godelII : {hyp : Equation} ->
          Consistent hyp ->
          Deriv hyp conSentence ->
          Empty
godelII con dCon = con (conToBot dCon)
