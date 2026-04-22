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

------------------------------------------------------------------------
-- encAxS: encoder for Ax 12 ((P ⊃ Q ⊃ R) ⊃ ((P ⊃ Q) ⊃ (P ⊃ R))).
--
-- Encoding:  encAxS pC qC rC = Pair (natCode n31) (Pair pC (Pair qC rC)) .
-- Correctness output: encoded  (P imp (Q imp R)) imp ((P imp Q) imp (P imp R)) .

private
  n31 : Nat ; n31 = suc n30

encAxS : Term -> Term -> Term -> Term
encAxS pC qC rC = ap2 Pair (reify (natCode n31)) (ap2 Pair pC (ap2 Pair qC rC))

encAxSCorr : (hCode pC qC rC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxS pC qC rC))
    (ap2 Pair tagImpT (ap2 Pair
      (ap2 Pair tagImpT (ap2 Pair pC
        (ap2 Pair tagImpT (ap2 Pair qC rC))))
      (ap2 Pair tagImpT (ap2 Pair
        (ap2 Pair tagImpT (ap2 Pair pC qC))
        (ap2 Pair tagImpT (ap2 Pair pC rC)))))))
encAxSCorr hCode pC qC rC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR pC (ap2 Pair qC rC) recs)
  (ruleTrans (ndBranchMiss n31 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n12 case12 (ndT13V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n13 case13 (ndT14V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n14 case14 (ndT15V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n15 case15 (ndT16V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n16 case16 (ndT17V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n17 case17 (ndT18V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n18 case18 (ndT19V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n19 case19V3 (ndT20V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n20 case20 (ndT21V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n21 case21 (ndT22V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n22 case22 (ndT23V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n23 case23V3 (ndT24V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n24 case24 (ndT25V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n25 case25 (ndT26V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n31 n26 (case26 hCode) ndT27V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n27 case27 ndT28V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n28 case28 ndT29V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n29 case29 ndT30V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n30 case30 ndT31V3 body recs refl)
  (ruleTrans (ndBranchHit n31 case31 ndT32V3 body recs)
  case31Red)))))))))))))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n31)
  body : Term ; body = ap2 Pair pC (ap2 Pair qC rC)
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  -- Sub-terms for the target.
  qImpR : Term
  qImpR = ap2 Pair tagImpT (ap2 Pair qC rC)

  pImp_qImpR : Term
  pImp_qImpR = ap2 Pair tagImpT (ap2 Pair pC qImpR)

  pImpQ : Term
  pImpQ = ap2 Pair tagImpT (ap2 Pair pC qC)

  pImpR : Term
  pImpR = ap2 Pair tagImpT (ap2 Pair pC rC)

  pqr : Term
  pqr = ap2 Pair tagImpT (ap2 Pair pImpQ pImpR)

  outerTarget : Term
  outerTarget = ap2 Pair tagImpT (ap2 Pair pImp_qImpR pqr)

  -- Step-by-step reductions of origA/origB/origB1/origB2 at (enc, recs).
  origARed' : Deriv hyp (eqn (ap2 origA enc recs) pC)
  origARed' = origARed tagR pC (ap2 Pair qC rC) recs

  origBRed' : Deriv hyp (eqn (ap2 origB enc recs) (ap2 Pair qC rC))
  origBRed' = origBRed tagR pC (ap2 Pair qC rC) recs

  origB1Red' : Deriv hyp (eqn (ap2 origB1 enc recs) qC)
  origB1Red' = origB1Red tagR pC qC rC recs

  origB2Red' : Deriv hyp (eqn (ap2 origB2 enc recs) rC)
  origB2Red' = origB2Red tagR pC qC rC recs

  -- Reduction of mkImpF aF bF at (enc, recs) when aF enc recs = aT and bF enc recs = bT.
  -- Output: Pair tagImpT (Pair aT bT).
  mkImpFRed : (aF bF : Fun2) (aT bT : Term) ->
              Deriv hyp (eqn (ap2 aF enc recs) aT) ->
              Deriv hyp (eqn (ap2 bF enc recs) bT) ->
              Deriv hyp (eqn (ap2 (mkImpF aF bF) enc recs)
                             (ap2 Pair tagImpT (ap2 Pair aT bT)))
  mkImpFRed aF bF aT bT dA dB =
    ruleTrans (fanRed (kF2 tagImpT) (Fan aF bF Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan aF bF Pair) enc recs)
                 (kF2Red tagImpT enc recs))
               (congR Pair tagImpT
                 (ruleTrans (fanRed aF bF Pair enc recs)
                 (ruleTrans (congL Pair (ap2 bF enc recs) dA)
                            (congR Pair aT dB)))))

  -- Individual mkImpF reductions.
  qImpRRed : Deriv hyp (eqn (ap2 (mkImpF origB1 origB2) enc recs) qImpR)
  qImpRRed = mkImpFRed origB1 origB2 qC rC origB1Red' origB2Red'

  pImp_qImpRRed : Deriv hyp
    (eqn (ap2 (mkImpF origA (mkImpF origB1 origB2)) enc recs) pImp_qImpR)
  pImp_qImpRRed = mkImpFRed origA (mkImpF origB1 origB2) pC qImpR origARed' qImpRRed

  pImpQRed : Deriv hyp (eqn (ap2 (mkImpF origA origB1) enc recs) pImpQ)
  pImpQRed = mkImpFRed origA origB1 pC qC origARed' origB1Red'

  pImpRRed : Deriv hyp (eqn (ap2 (mkImpF origA origB2) enc recs) pImpR)
  pImpRRed = mkImpFRed origA origB2 pC rC origARed' origB2Red'

  pqrRed : Deriv hyp (eqn (ap2 (mkImpF (mkImpF origA origB1) (mkImpF origA origB2))
                               enc recs)
                         pqr)
  pqrRed = mkImpFRed (mkImpF origA origB1) (mkImpF origA origB2) pImpQ pImpR
             pImpQRed pImpRRed

  case31Red : Deriv hyp (eqn (ap2 case31 enc recs) outerTarget)
  case31Red =
    mkImpFRed (mkImpF origA (mkImpF origB1 origB2))
              (mkImpF (mkImpF origA origB1) (mkImpF origA origB2))
              pImp_qImpR pqr
              pImp_qImpRRed pqrRed

encAxSPass :
  (hCode : Term) (P Q R : Formula) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxS (reify (codeFormula P)) (reify (codeFormula Q))
                                      (reify (codeFormula R))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxS (reify (codeFormula P)) (reify (codeFormula Q))
                                      (reify (codeFormula R))) x) rcs))
encAxSPass hCode P Q R x rcs =
  passthroughSucV3 hCode n30 (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R))) x rcs

------------------------------------------------------------------------
-- encAxNeg: encoder for Ax 13 (~P ⊃ (~Q ⊃ (Q ⊃ P))).
--
-- Encoding:  encAxNeg pC qC = Pair (natCode n32) (Pair pC qC) .
-- Correctness output: encoded  ~P imp (~Q imp (Q imp P)) .

private
  n32 : Nat ; n32 = suc n31

encAxNeg : Term -> Term -> Term
encAxNeg pC qC = ap2 Pair (reify (natCode n32)) (ap2 Pair pC qC)

encAxNegCorr : (hCode pC qC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxNeg pC qC))
    (ap2 Pair tagImpT (ap2 Pair
      (ap2 Pair tagNegT pC)
      (ap2 Pair tagImpT (ap2 Pair
        (ap2 Pair tagNegT qC)
        (ap2 Pair tagImpT (ap2 Pair qC pC)))))))
encAxNegCorr hCode pC qC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR pC qC recs)
  (ruleTrans (ndBranchMiss n32 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n12 case12 (ndT13V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n13 case13 (ndT14V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n14 case14 (ndT15V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n15 case15 (ndT16V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n16 case16 (ndT17V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n17 case17 (ndT18V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n18 case18 (ndT19V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n19 case19V3 (ndT20V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n20 case20 (ndT21V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n21 case21 (ndT22V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n22 case22 (ndT23V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n23 case23V3 (ndT24V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n24 case24 (ndT25V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n25 case25 (ndT26V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n32 n26 (case26 hCode) ndT27V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n27 case27 ndT28V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n28 case28 ndT29V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n29 case29 ndT30V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n30 case30 ndT31V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n31 case31 ndT32V3 body recs refl)
  (ruleTrans (ndBranchHit n32 case32 ndT33V3 body recs)
  case32Red))))))))))))))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n32)
  body : Term ; body = ap2 Pair pC qC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  -- Sub-terms for target.
  notP : Term
  notP = ap2 Pair tagNegT pC

  notQ : Term
  notQ = ap2 Pair tagNegT qC

  qImpP : Term
  qImpP = ap2 Pair tagImpT (ap2 Pair qC pC)

  notQ_imp_qImpP : Term
  notQ_imp_qImpP = ap2 Pair tagImpT (ap2 Pair notQ qImpP)

  outerTarget : Term
  outerTarget = ap2 Pair tagImpT (ap2 Pair notP notQ_imp_qImpP)

  origARed' : Deriv hyp (eqn (ap2 origA enc recs) pC)
  origARed' = origARed tagR pC qC recs

  origBRed' : Deriv hyp (eqn (ap2 origB enc recs) qC)
  origBRed' = origBRed tagR pC qC recs

  mkNegFRed : (pF : Fun2) (pT : Term) ->
              Deriv hyp (eqn (ap2 pF enc recs) pT) ->
              Deriv hyp (eqn (ap2 (mkNegF pF) enc recs)
                             (ap2 Pair tagNegT pT))
  mkNegFRed pF pT dP =
    ruleTrans (fanRed (kF2 tagNegT) pF Pair enc recs)
    (ruleTrans (congL Pair (ap2 pF enc recs) (kF2Red tagNegT enc recs))
               (congR Pair tagNegT dP))

  mkImpFRed : (aF bF : Fun2) (aT bT : Term) ->
              Deriv hyp (eqn (ap2 aF enc recs) aT) ->
              Deriv hyp (eqn (ap2 bF enc recs) bT) ->
              Deriv hyp (eqn (ap2 (mkImpF aF bF) enc recs)
                             (ap2 Pair tagImpT (ap2 Pair aT bT)))
  mkImpFRed aF bF aT bT dA dB =
    ruleTrans (fanRed (kF2 tagImpT) (Fan aF bF Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan aF bF Pair) enc recs) (kF2Red tagImpT enc recs))
               (congR Pair tagImpT
                 (ruleTrans (fanRed aF bF Pair enc recs)
                 (ruleTrans (congL Pair (ap2 bF enc recs) dA)
                            (congR Pair aT dB)))))

  notPRed : Deriv hyp (eqn (ap2 (mkNegF origA) enc recs) notP)
  notPRed = mkNegFRed origA pC origARed'

  notQRed : Deriv hyp (eqn (ap2 (mkNegF origB) enc recs) notQ)
  notQRed = mkNegFRed origB qC origBRed'

  qImpPRed : Deriv hyp (eqn (ap2 (mkImpF origB origA) enc recs) qImpP)
  qImpPRed = mkImpFRed origB origA qC pC origBRed' origARed'

  notQ_imp_qImpPRed :
    Deriv hyp (eqn (ap2 (mkImpF (mkNegF origB) (mkImpF origB origA)) enc recs)
                   notQ_imp_qImpP)
  notQ_imp_qImpPRed =
    mkImpFRed (mkNegF origB) (mkImpF origB origA) notQ qImpP notQRed qImpPRed

  case32Red : Deriv hyp (eqn (ap2 case32 enc recs) outerTarget)
  case32Red = mkImpFRed (mkNegF origA)
                        (mkImpF (mkNegF origB) (mkImpF origB origA))
                        notP notQ_imp_qImpP notPRed notQ_imp_qImpPRed

encAxNegPass :
  (hCode : Term) (P Q : Formula) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxNeg (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxNeg (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs))
encAxNegPass hCode P Q x rcs =
  passthroughSucV3 hCode n31 (nd (codeFormula P) (codeFormula Q)) x rcs
