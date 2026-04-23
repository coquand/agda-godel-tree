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
open import Guard.Formula
open import Guard.DerivF
open import Guard.StepReduceUnify
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefsUnify using (ndBranchHit ; ndBranchMiss ; branchHit)
open import Guard.ThFunTForHF
open import Guard.ThFunTForV3DefsUnify
open import Guard.ThFunTForV3PassUnify
open import Guard.ExtractorRedUnify
open import Guard.TreeEqSelfUnify using (treeEqSelfReify)
open import Guard.Formula using (Formula ; _imp_ ; tagImp ; tagNeg ; codeFormula)

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
-- Correctness:  thmT (encAxK pC qC) = codeFormula (P imp (Q imp P))
--            = Pair tagImp (Pair pC (Pair tagImp (Pair qC pC))).

encAxK : Term -> Term -> Term
encAxK pC qC = ap2 Pair (reify (natCode n30)) (ap2 Pair pC qC)

encAxKCorr : (pC qC : Term) ->
  Deriv (eqF (ap1 (thmT) (encAxK pC qC))
    (ap2 Pair tagImpT (ap2 Pair pC
      (ap2 Pair tagImpT (ap2 Pair qC pC)))))
encAxKCorr pC qC =
  ruleTrans (recNdRed O (thmTStep) tagR body)
  (ruleTrans (guardNdV3 tagR pC qC recs)
  (ruleTrans (ndBranchMiss n30 n0  case0  (ndT1V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n1  case1  (ndT2V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n2  case2  (ndT3V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n3  case3  (ndT4V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n4  case4  (ndT5V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n5  case5  (ndT6V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n6  case6  (ndT7V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n7  case7  (ndT8V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n8  case8  (ndT9V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n9  case9  (ndT10V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n10 case10 (ndT11V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n11 case11 (ndT12V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n12 case12 (ndT13V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n13 case13 (ndT14V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n14 case14 (ndT15V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n15 case15 (ndT16V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n16 case16 (ndT17V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n17 case17 (ndT18V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n18 case18 (ndT19V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n19 case19V3 (ndT20V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n20 case20 (ndT21V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n21 case21 (ndT22V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n22 case22 (ndT23V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n23 case23V3 (ndT24V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n24 case24 (ndT25V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n25 case25 (ndT26V3) body recs refl)
  (ruleTrans (ndBranchMiss n30 n27 case27 ndT28V3 body recs refl)
  (ruleTrans (ndBranchMiss n30 n28 case28 ndT29V3 body recs refl)
  (ruleTrans (ndBranchMiss n30 n29 case29 ndT30V3 body recs refl)
  (ruleTrans (ndBranchHit n30 case30 ndT31V3 body recs)
  -- case30 = mkImpF origA (mkImpF origB origA)
  -- Evaluated at (enc, recs), expands step-by-step to the target Pair.
  case30Red)))))))))))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n30)
  body : Term ; body = ap2 Pair pC qC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT) tagR) (ap1 (thmT) body)

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
  innerRed : Deriv (eqF (ap2 innerF enc recs) innerTarget)
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
  case30Red : Deriv (eqF (ap2 case30 enc recs) outerTarget)
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
  (P Q : Formula) (x rcs : Term) -> 
  Deriv (eqF (ap2 (ndDispatchV3)
                   (ap2 Pair (encAxK (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxK (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs))
encAxKPass P Q x rcs =
  passthroughSucV3 n29 (nd (codeFormula P) (codeFormula Q)) x rcs

------------------------------------------------------------------------
-- encAxS: encoder for Ax 12 ((P ⊃ Q ⊃ R) ⊃ ((P ⊃ Q) ⊃ (P ⊃ R))).
--
-- Encoding:  encAxS pC qC rC = Pair (natCode n31) (Pair pC (Pair qC rC)) .
-- Correctness output: encoded  (P imp (Q imp R)) imp ((P imp Q) imp (P imp R)) .

private
  n31 : Nat ; n31 = suc n30

encAxS : Term -> Term -> Term -> Term
encAxS pC qC rC = ap2 Pair (reify (natCode n31)) (ap2 Pair pC (ap2 Pair qC rC))

encAxSCorr : (pC qC rC : Term) ->
  Deriv (eqF (ap1 (thmT) (encAxS pC qC rC))
    (ap2 Pair tagImpT (ap2 Pair
      (ap2 Pair tagImpT (ap2 Pair pC
        (ap2 Pair tagImpT (ap2 Pair qC rC))))
      (ap2 Pair tagImpT (ap2 Pair
        (ap2 Pair tagImpT (ap2 Pair pC qC))
        (ap2 Pair tagImpT (ap2 Pair pC rC)))))))
encAxSCorr pC qC rC =
  ruleTrans (recNdRed O (thmTStep) tagR body)
  (ruleTrans (guardNdV3 tagR pC (ap2 Pair qC rC) recs)
  (ruleTrans (ndBranchMiss n31 n0  case0  (ndT1V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n1  case1  (ndT2V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n2  case2  (ndT3V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n3  case3  (ndT4V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n4  case4  (ndT5V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n5  case5  (ndT6V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n6  case6  (ndT7V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n7  case7  (ndT8V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n8  case8  (ndT9V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n9  case9  (ndT10V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n10 case10 (ndT11V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n11 case11 (ndT12V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n12 case12 (ndT13V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n13 case13 (ndT14V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n14 case14 (ndT15V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n15 case15 (ndT16V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n16 case16 (ndT17V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n17 case17 (ndT18V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n18 case18 (ndT19V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n19 case19V3 (ndT20V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n20 case20 (ndT21V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n21 case21 (ndT22V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n22 case22 (ndT23V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n23 case23V3 (ndT24V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n24 case24 (ndT25V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n25 case25 (ndT26V3) body recs refl)
  (ruleTrans (ndBranchMiss n31 n27 case27 ndT28V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n28 case28 ndT29V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n29 case29 ndT30V3 body recs refl)
  (ruleTrans (ndBranchMiss n31 n30 case30 ndT31V3 body recs refl)
  (ruleTrans (ndBranchHit n31 case31 ndT32V3 body recs)
  case31Red))))))))))))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n31)
  body : Term ; body = ap2 Pair pC (ap2 Pair qC rC)
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT) tagR) (ap1 (thmT) body)

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
  origARed' : Deriv (eqF (ap2 origA enc recs) pC)
  origARed' = origARed tagR pC (ap2 Pair qC rC) recs

  origBRed' : Deriv (eqF (ap2 origB enc recs) (ap2 Pair qC rC))
  origBRed' = origBRed tagR pC (ap2 Pair qC rC) recs

  origB1Red' : Deriv (eqF (ap2 origB1 enc recs) qC)
  origB1Red' = origB1Red tagR pC qC rC recs

  origB2Red' : Deriv (eqF (ap2 origB2 enc recs) rC)
  origB2Red' = origB2Red tagR pC qC rC recs

  -- Reduction of mkImpF aF bF at (enc, recs) when aF enc recs = aT and bF enc recs = bT.
  -- Output: Pair tagImpT (Pair aT bT).
  mkImpFRed : (aF bF : Fun2) (aT bT : Term) ->
              Deriv (eqF (ap2 aF enc recs) aT) ->
              Deriv (eqF (ap2 bF enc recs) bT) ->
              Deriv (eqF (ap2 (mkImpF aF bF) enc recs)
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
  qImpRRed : Deriv (eqF (ap2 (mkImpF origB1 origB2) enc recs) qImpR)
  qImpRRed = mkImpFRed origB1 origB2 qC rC origB1Red' origB2Red'

  pImp_qImpRRed : Deriv
    (eqF (ap2 (mkImpF origA (mkImpF origB1 origB2)) enc recs) pImp_qImpR)
  pImp_qImpRRed = mkImpFRed origA (mkImpF origB1 origB2) pC qImpR origARed' qImpRRed

  pImpQRed : Deriv (eqF (ap2 (mkImpF origA origB1) enc recs) pImpQ)
  pImpQRed = mkImpFRed origA origB1 pC qC origARed' origB1Red'

  pImpRRed : Deriv (eqF (ap2 (mkImpF origA origB2) enc recs) pImpR)
  pImpRRed = mkImpFRed origA origB2 pC rC origARed' origB2Red'

  pqrRed : Deriv (eqF (ap2 (mkImpF (mkImpF origA origB1) (mkImpF origA origB2))
                               enc recs)
                         pqr)
  pqrRed = mkImpFRed (mkImpF origA origB1) (mkImpF origA origB2) pImpQ pImpR
             pImpQRed pImpRRed

  case31Red : Deriv (eqF (ap2 case31 enc recs) outerTarget)
  case31Red =
    mkImpFRed (mkImpF origA (mkImpF origB1 origB2))
              (mkImpF (mkImpF origA origB1) (mkImpF origA origB2))
              pImp_qImpR pqr
              pImp_qImpRRed pqrRed

encAxSPass :
  (P Q R : Formula) (x rcs : Term) -> 
  Deriv (eqF (ap2 (ndDispatchV3)
                   (ap2 Pair (encAxS (reify (codeFormula P)) (reify (codeFormula Q))
                                      (reify (codeFormula R))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxS (reify (codeFormula P)) (reify (codeFormula Q))
                                      (reify (codeFormula R))) x) rcs))
encAxSPass P Q R x rcs =
  passthroughSucV3 n30 (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R))) x rcs

------------------------------------------------------------------------
-- encAxNeg: encoder for Ax 13 (~P ⊃ (~Q ⊃ (Q ⊃ P))).
--
-- Encoding:  encAxNeg pC qC = Pair (natCode n32) (Pair pC qC) .
-- Correctness output: encoded  ~P imp (~Q imp (Q imp P)) .

private
  n32 : Nat ; n32 = suc n31

encAxNeg : Term -> Term -> Term
encAxNeg pC qC = ap2 Pair (reify (natCode n32)) (ap2 Pair pC qC)

encAxNegCorr : (pC qC : Term) ->
  Deriv (eqF (ap1 (thmT) (encAxNeg pC qC))
    (ap2 Pair tagImpT (ap2 Pair
      (ap2 Pair tagNegT pC)
      (ap2 Pair tagImpT (ap2 Pair
        (ap2 Pair tagNegT qC)
        (ap2 Pair tagImpT (ap2 Pair qC pC)))))))
encAxNegCorr pC qC =
  ruleTrans (recNdRed O (thmTStep) tagR body)
  (ruleTrans (guardNdV3 tagR pC qC recs)
  (ruleTrans (ndBranchMiss n32 n0  case0  (ndT1V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n1  case1  (ndT2V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n2  case2  (ndT3V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n3  case3  (ndT4V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n4  case4  (ndT5V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n5  case5  (ndT6V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n6  case6  (ndT7V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n7  case7  (ndT8V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n8  case8  (ndT9V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n9  case9  (ndT10V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n10 case10 (ndT11V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n11 case11 (ndT12V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n12 case12 (ndT13V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n13 case13 (ndT14V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n14 case14 (ndT15V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n15 case15 (ndT16V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n16 case16 (ndT17V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n17 case17 (ndT18V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n18 case18 (ndT19V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n19 case19V3 (ndT20V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n20 case20 (ndT21V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n21 case21 (ndT22V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n22 case22 (ndT23V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n23 case23V3 (ndT24V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n24 case24 (ndT25V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n25 case25 (ndT26V3) body recs refl)
  (ruleTrans (ndBranchMiss n32 n27 case27 ndT28V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n28 case28 ndT29V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n29 case29 ndT30V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n30 case30 ndT31V3 body recs refl)
  (ruleTrans (ndBranchMiss n32 n31 case31 ndT32V3 body recs refl)
  (ruleTrans (ndBranchHit n32 case32 ndT33V3 body recs)
  case32Red)))))))))))))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n32)
  body : Term ; body = ap2 Pair pC qC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT) tagR) (ap1 (thmT) body)

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

  origARed' : Deriv (eqF (ap2 origA enc recs) pC)
  origARed' = origARed tagR pC qC recs

  origBRed' : Deriv (eqF (ap2 origB enc recs) qC)
  origBRed' = origBRed tagR pC qC recs

  mkNegFRed : (pF : Fun2) (pT : Term) ->
              Deriv (eqF (ap2 pF enc recs) pT) ->
              Deriv (eqF (ap2 (mkNegF pF) enc recs)
                             (ap2 Pair tagNegT pT))
  mkNegFRed pF pT dP =
    ruleTrans (fanRed (kF2 tagNegT) pF Pair enc recs)
    (ruleTrans (congL Pair (ap2 pF enc recs) (kF2Red tagNegT enc recs))
               (congR Pair tagNegT dP))

  mkImpFRed : (aF bF : Fun2) (aT bT : Term) ->
              Deriv (eqF (ap2 aF enc recs) aT) ->
              Deriv (eqF (ap2 bF enc recs) bT) ->
              Deriv (eqF (ap2 (mkImpF aF bF) enc recs)
                             (ap2 Pair tagImpT (ap2 Pair aT bT)))
  mkImpFRed aF bF aT bT dA dB =
    ruleTrans (fanRed (kF2 tagImpT) (Fan aF bF Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan aF bF Pair) enc recs) (kF2Red tagImpT enc recs))
               (congR Pair tagImpT
                 (ruleTrans (fanRed aF bF Pair enc recs)
                 (ruleTrans (congL Pair (ap2 bF enc recs) dA)
                            (congR Pair aT dB)))))

  notPRed : Deriv (eqF (ap2 (mkNegF origA) enc recs) notP)
  notPRed = mkNegFRed origA pC origARed'

  notQRed : Deriv (eqF (ap2 (mkNegF origB) enc recs) notQ)
  notQRed = mkNegFRed origB qC origBRed'

  qImpPRed : Deriv (eqF (ap2 (mkImpF origB origA) enc recs) qImpP)
  qImpPRed = mkImpFRed origB origA qC pC origBRed' origARed'

  notQ_imp_qImpPRed :
    Deriv (eqF (ap2 (mkImpF (mkNegF origB) (mkImpF origB origA)) enc recs)
                   notQ_imp_qImpP)
  notQ_imp_qImpPRed =
    mkImpFRed (mkNegF origB) (mkImpF origB origA) notQ qImpP notQRed qImpPRed

  case32Red : Deriv (eqF (ap2 case32 enc recs) outerTarget)
  case32Red = mkImpFRed (mkNegF origA)
                        (mkImpF (mkNegF origB) (mkImpF origB origA))
                        notP notQ_imp_qImpP notPRed notQ_imp_qImpPRed

encAxNegPass :
  (P Q : Formula) (x rcs : Term) -> 
  Deriv (eqF (ap2 (ndDispatchV3)
                   (ap2 Pair (encAxNeg (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxNeg (reify (codeFormula P)) (reify (codeFormula Q))) x) rcs))
encAxNegPass P Q x rcs =
  passthroughSucV3 n31 (nd (codeFormula P) (codeFormula Q)) x rcs

------------------------------------------------------------------------
-- encMp: encoder for formula-level modus ponens (Ax rule mp).
--
-- Encoding:  encMp sub1 sub2 = Pair (natCode n33) (Pair sub1 sub2)
-- where sub1 encodes a proof of  P  and sub2 encodes a proof of
--  P imp Q .
--
-- The case33 dispatch at the validator  thmT  checks:
--   (1) that  thmT sub2 's outer tag is  tagImp  (i.e., sub2 encodes
--       an implication);
--   (2) that  thmT sub2 's antecedent code equals  thmT sub1 .
-- On both matches, the output is the consequent code — i.e.  codeQ .
--
-- In the chain setting, both checks are guaranteed to pass because
-- sub1 and sub2 are constructed correctly (sub1 encodes  P , sub2
-- encodes  P imp Q ).
--
-- Signature design choice: we take a single  bodyCorr  precondition
-- witnessing that  thmT (Pair sub1 sub2) = Pair codeP codePimpQ ,
-- rather than separate  sub1Corr / sub2Corr / dispMiss1  lemmas and
-- doing the  intermediateGenericV3  dance inside this module.  The
-- caller composes their sub-correctness lemmas into  bodyCorr  using
--  intermediateGenericV3  (when sub2 is a Pair) or a direct Rec
-- unfolding.  This keeps encMpCorr agnostic to the shape of sub1/sub2
-- and modular with the existing  passthroughSucV3  / dispMiss
-- machinery.

private
  n33 : Nat ; n33 = suc n32

encMp : Term -> Term -> Term
encMp sub1 sub2 = ap2 Pair (reify (natCode n33)) (ap2 Pair sub1 sub2)

encMpCorr :
  (sub1 sub2 : Term) (P Q : Formula) ->
  Deriv (eqF (ap1 (thmT) (ap2 Pair sub1 sub2))
                 (ap2 Pair (reify (codeFormula P))
                           (reify (codeFormula (P imp Q))))) ->
  Deriv (eqF (ap1 (thmT) (encMp sub1 sub2))
                 (reify (codeFormula Q)))
encMpCorr sub1 sub2 P Q bodyCorr =
  ruleTrans (recNdRed O (thmTStep) tagR body)
  (ruleTrans (congR (thmTStep) enc
               (congR Pair (ap1 (thmT) tagR) bodyCorr))
  (ruleTrans (guardNdV3 tagR sub1 sub2 recs')
  (ruleTrans (ndBranchMiss n33 n0  case0  (ndT1V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n1  case1  (ndT2V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n2  case2  (ndT3V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n3  case3  (ndT4V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n4  case4  (ndT5V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n5  case5  (ndT6V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n6  case6  (ndT7V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n7  case7  (ndT8V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n8  case8  (ndT9V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n9  case9  (ndT10V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n10 case10 (ndT11V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n11 case11 (ndT12V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n12 case12 (ndT13V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n13 case13 (ndT14V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n14 case14 (ndT15V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n15 case15 (ndT16V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n16 case16 (ndT17V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n17 case17 (ndT18V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n18 case18 (ndT19V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n19 case19V3 (ndT20V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n20 case20 (ndT21V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n21 case21 (ndT22V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n22 case22 (ndT23V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n23 case23V3 (ndT24V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n24 case24 (ndT25V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n25 case25 (ndT26V3) body recs' refl)
  (ruleTrans (ndBranchMiss n33 n27 case27 ndT28V3 body recs' refl)
  (ruleTrans (ndBranchMiss n33 n28 case28 ndT29V3 body recs' refl)
  (ruleTrans (ndBranchMiss n33 n29 case29 ndT30V3 body recs' refl)
  (ruleTrans (ndBranchMiss n33 n30 case30 ndT31V3 body recs' refl)
  (ruleTrans (ndBranchMiss n33 n31 case31 ndT32V3 body recs' refl)
  (ruleTrans (ndBranchMiss n33 n32 case32 ndT33V3 body recs' refl)
  (ruleTrans (ndBranchHit n33 case33 ndT34V3 body recs')
   case33Red)))))))))))))))))))))))))))))))))))
  where
  codeP : Term ; codeP = reify (codeFormula P)
  codeQ : Term ; codeQ = reify (codeFormula Q)
  codePimpQ : Term
  codePimpQ = ap2 Pair tagImpT (ap2 Pair codeP codeQ)

  pqBody : Term
  pqBody = ap2 Pair codeP codePimpQ

  tagR : Term ; tagR = reify (natCode n33)
  body : Term ; body = ap2 Pair sub1 sub2
  enc  : Term ; enc  = ap2 Pair tagR body
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT) tagR) pqBody

  -- recsB(enc, recs') = Snd(Snd(recs')) = codePimpQ.
  recsBRedLocal : Deriv (eqF (ap2 recsB enc recs') codePimpQ)
  recsBRedLocal = recsBRed enc (ap1 (thmT) tagR) codeP codePimpQ

  -- recsA(enc, recs') = Fst(Snd(recs')) = codeP.
  recsARedLocal : Deriv (eqF (ap2 recsA enc recs') codeP)
  recsARedLocal = recsARed enc (ap1 (thmT) tagR) codeP codePimpQ

  -- rbFst(enc, recs') = Fst(recsB(enc, recs')) = Fst(codePimpQ) = tagImpT.
  rbFstRed : Deriv (eqF (ap2 rbFst enc recs') tagImpT)
  rbFstRed =
    ruleTrans (postRed Fst recsB enc recs')
    (ruleTrans (cong1 Fst recsBRedLocal)
               (axFst tagImpT (ap2 Pair codeP codeQ)))

  -- rbSnd(enc, recs') = Snd(codePimpQ) = Pair codeP codeQ.
  rbSndRed : Deriv (eqF (ap2 rbSnd enc recs') (ap2 Pair codeP codeQ))
  rbSndRed =
    ruleTrans (postRed Snd recsB enc recs')
    (ruleTrans (cong1 Snd recsBRedLocal)
               (axSnd tagImpT (ap2 Pair codeP codeQ)))

  -- rbSndFst(enc, recs') = Fst(Pair codeP codeQ) = codeP.
  rbSndFstRed : Deriv (eqF (ap2 rbSndFst enc recs') codeP)
  rbSndFstRed =
    ruleTrans (postRed Fst rbSnd enc recs')
    (ruleTrans (cong1 Fst rbSndRed)
               (axFst codeP codeQ))

  -- rbSndSnd(enc, recs') = Snd(Pair codeP codeQ) = codeQ.
  rbSndSndRed : Deriv (eqF (ap2 rbSndSnd enc recs') codeQ)
  rbSndSndRed =
    ruleTrans (postRed Snd rbSnd enc recs')
    (ruleTrans (cong1 Snd rbSndRed)
               (axSnd codeP codeQ))

  -- check1mp(enc, recs') = TreeEq(rbFst, tagImpT) = TreeEq(tagImpT, tagImpT) = O.
  check1mpRed : Deriv (eqF (ap2 check1mp enc recs') O)
  check1mpRed =
    ruleTrans (fanRed rbFst (kF2 tagImpT) TreeEq enc recs')
    (ruleTrans (congL TreeEq (ap2 (kF2 tagImpT) enc recs') rbFstRed)
    (ruleTrans (congR TreeEq tagImpT (kF2Red tagImpT enc recs'))
               (treeEqSelfReify tagImp)))

  -- check2mp(enc, recs') = TreeEq(rbSndFst, recsA) = TreeEq(codeP, codeP) = O.
  check2mpRed : Deriv (eqF (ap2 check2mp enc recs') O)
  check2mpRed =
    ruleTrans (fanRed rbSndFst recsA TreeEq enc recs')
    (ruleTrans (congL TreeEq (ap2 recsA enc recs') rbSndFstRed)
    (ruleTrans (congR TreeEq codeP recsARedLocal)
               (treeEqSelfReify (codeFormula P))))

  -- Inner branch: branch check2mp rbSndSnd (kF2 codeTrueT) at (enc, recs') → rbSndSnd(enc, recs') = codeQ.
  innerBranchRed : Deriv
    (eqF (ap2 (branch check2mp rbSndSnd (kF2 codeTrueT)) enc recs') codeQ)
  innerBranchRed =
    ruleTrans (branchHit check2mp rbSndSnd (kF2 codeTrueT) enc recs' check2mpRed)
              rbSndSndRed

  -- Outer branch: branch check1mp (inner) (kF2 codeTrueT) at (enc, recs') → inner(enc, recs') = codeQ.
  case33Red : Deriv (eqF (ap2 case33 enc recs') codeQ)
  case33Red =
    ruleTrans (branchHit check1mp
                (branch check2mp rbSndSnd (kF2 codeTrueT)) (kF2 codeTrueT)
                enc recs' check1mpRed)
              innerBranchRed

------------------------------------------------------------------------
-- encMpPass: tag-opaque pass for using encMp as a sub-encoding.
--
-- Note: unlike encAxK/S/Neg, encMp's body is  Pair sub1 sub2  where
-- sub1, sub2 are arbitrary Term constructions — not  reify (codeFormula _) .
-- We parameterise over the raw  Pair sub1 sub2  body.

encMpPass :
  (sub1 sub2 : Term) (x rcs : Term) -> 
  Deriv (eqF (ap2 (ndDispatchV3)
                   (ap2 Pair (encMp sub1 sub2) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encMp sub1 sub2) x) rcs))
encMpPass sub1 sub2 x rcs =
  ndDispatchV3PairMiss O (reify (natCode n32)) (ap2 Pair sub1 sub2) x rcs
