{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProofEncFormula -- formula-level proof encoders.
--
-- Extends Guard.ProofEnc with encoders for the propositional axioms
-- (Ax 11 = K, Ax 12 = S, Ax 13 = axNeg) and formula-level modus
-- ponens (encMp).  Each encoder pairs with a correctness lemma at
-- the thmT validator and a tag-opaque pass lemma for use as a sub-
-- encoding.
--
-- Tags used: n30 (K), n31 (S), n32 (Neg), n33 (Mp).  Dispatches
-- live in Guard.ThFunTForV3 (case30..case33).
--
-- Pattern mirrors Guard.ProofEnc's existing encAx*/encAx*Corr/
-- encAx*Pass combinators.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.ProofEncFormula where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs using (ndBranchHit ; ndBranchMiss)
open import Guard.ThFunTForV3
open import Guard.ThFunTForV3Defs
open import Guard.ThFunTForV3Pass
open import Guard.ExtractorRed
open import Guard.Formula using (Formula ; tagImp ; tagNeg ; codeFormula)

private
  n0  : Nat ; n0  = zero
  n1  : Nat ; n1  = suc n0
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n4  : Nat ; n4  = suc n3
  n5  : Nat ; n5  = suc n4
  n6  : Nat ; n6  = suc n5
  n7  : Nat ; n7  = suc n6
  n8  : Nat ; n8  = suc n7
  n9  : Nat ; n9  = suc n8
  n10 : Nat ; n10 = suc n9
  n11 : Nat ; n11 = suc n10
  n12 : Nat ; n12 = suc n11
  n13 : Nat ; n13 = suc n12
  n14 : Nat ; n14 = suc n13
  n15 : Nat ; n15 = suc n14
  n16 : Nat ; n16 = suc n15
  n17 : Nat ; n17 = suc n16
  n18 : Nat ; n18 = suc n17
  n19 : Nat ; n19 = suc n18
  n20 : Nat ; n20 = suc n19
  n21 : Nat ; n21 = suc n20
  n22 : Nat ; n22 = suc n21
  n23 : Nat ; n23 = suc n22
  n24 : Nat ; n24 = suc n23
  n25 : Nat ; n25 = suc n24
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29

  tagImpT : Term
  tagImpT = reify tagImp

  tagNegT : Term
  tagNegT = reify tagNeg

------------------------------------------------------------------------
-- encAxK: encoder for Ax 11 (P ⊃ (Q ⊃ P)).
--
-- Encoding shape:  Pair (natCode n30) (Pair pC qC) .
-- Correctness:  thmT hCode (encAxK pC qC) = codeFormula (P imp (Q imp P))
--            = Pair tagImp (Pair pC (Pair tagImp (Pair qC pC))).

encAxK : Term -> Term -> Term
encAxK pC qC = ap2 Pair (reify (natCode n30)) (ap2 Pair pC qC)

encAxKCorr : (hCode pC qC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxK pC qC))
    (ap2 Pair tagImpT (ap2 Pair pC
      (ap2 Pair tagImpT (ap2 Pair qC pC)))))
encAxKCorr hCode pC qC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR pC qC recs)
  (ruleTrans (ndBranchMiss n30 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n12 case12 (ndT13V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n13 case13 (ndT14V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n14 case14 (ndT15V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n15 case15 (ndT16V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n16 case16 (ndT17V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n17 case17 (ndT18V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n18 case18 (ndT19V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n19 case19V3 (ndT20V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n20 case20 (ndT21V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n21 case21 (ndT22V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n22 case22 (ndT23V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n23 case23V3 (ndT24V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n24 case24 (ndT25V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n25 case25 (ndT26V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n30 n26 (case26 hCode) ndT27V3 body recs refl)
  (ruleTrans (ndBranchMiss n30 n27 case27 ndT28V3 body recs refl)
  (ruleTrans (ndBranchMiss n30 n28 case28 ndT29V3 body recs refl)
  (ruleTrans (ndBranchMiss n30 n29 case29 ndT30V3 body recs refl)
  (ruleTrans (ndBranchHit n30 case30 ndT31V3 body recs)
  -- case30 = mkImpF origA (mkImpF origB origA)
  -- Evaluated at (enc, recs), expands step-by-step to the target Pair.
  case30Red))))))))))))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n30)
  body : Term ; body = ap2 Pair pC qC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  -- Inner target: Pair tagImpT (Pair qC pC) — reified codeFormula (Q imp P).
  innerTarget : Term
  innerTarget = ap2 Pair tagImpT (ap2 Pair qC pC)

  -- Outer target: Pair tagImpT (Pair pC innerTarget).
  outerTarget : Term
  outerTarget = ap2 Pair tagImpT (ap2 Pair pC innerTarget)

  -- Reduce case30 at (enc, recs).
  --
  -- case30 = mkImpF origA (mkImpF origB origA)
  --        = Fan (kF2 tagImpT) (Fan origA innerF Pair) Pair
  -- where innerF = mkImpF origB origA = Fan (kF2 tagImpT) (Fan origB origA Pair) Pair.
  --
  -- At (enc, recs):
  --   origA enc recs = ap1 (Comp Fst Snd) enc (via Lift+Comp)
  --                  = Fst (Snd enc) = Fst (body) = pC.
  --   origB enc recs = Snd (body) = qC.
  --   (kF2 tagImpT) enc recs = tagImpT.

  innerF : Fun2
  innerF = Fan (kF2 tagImpT) (Fan origB origA Pair) Pair

  -- Inner reduction: innerF enc recs = ap2 Pair tagImpT (ap2 Pair qC pC) = innerTarget.
  innerRed : Deriv hyp (eqn (ap2 innerF enc recs) innerTarget)
  innerRed =
    ruleTrans (fanRed (kF2 tagImpT) (Fan origB origA Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan origB origA Pair) enc recs)
                 (kF2Red tagImpT enc recs))
               (congR Pair tagImpT
                 (ruleTrans (fanRed origB origA Pair enc recs)
                 (ruleTrans (congL Pair (ap2 origA enc recs) (origBRed tagR pC qC recs))
                            (congR Pair qC (origARed tagR pC qC recs))))))

  -- Outer reduction: case30 enc recs = ap2 Pair tagImpT (ap2 Pair pC innerTarget)
  --                                  = outerTarget.
  case30Red : Deriv hyp (eqn (ap2 case30 enc recs) outerTarget)
  case30Red =
    ruleTrans (fanRed (kF2 tagImpT) (Fan origA innerF Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan origA innerF Pair) enc recs)
                 (kF2Red tagImpT enc recs))
               (congR Pair tagImpT
                 (ruleTrans (fanRed origA innerF Pair enc recs)
                 (ruleTrans (congL Pair (ap2 innerF enc recs)
                              (origARed tagR pC qC recs))
                            (congR Pair pC innerRed)))))

------------------------------------------------------------------------
-- encAxKPass: tag-opaque pass, for using encAxK as a sub-encoding.

encAxKPass :
  (hCode : Term) (P Q : Formula) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxK (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxK (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs))
encAxKPass hCode P Q x rcs =
  passthroughSucV3 hCode n29 (nd (codeFormula P) (codeFormula Q)) x rcs
