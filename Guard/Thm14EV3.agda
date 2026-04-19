{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm14EV3 — hypothesis-aware Theorem 14.
--
-- Phase C of the Gödel-II redesign (see GODEL-II-REDESIGN.md).
--
-- ProofE3 H eq is a record containing an encoding term encT and a
-- proof that  ap1 (thmT (reify (codeEqn H))) encT = reify (codeEqn eq)
-- in every ambient hypothesis.  Constructors per rule of the
-- derivation system will be ported one at a time.
--
-- This file starts with the base case for axI (tag n0).

module Guard.Thm14EV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCorrectDefs using (ndBranchHit ; ndBranchMiss)
open import Guard.ThFunTForV3
open import Guard.ThFunTForV3Defs
open import Guard.ExtractorRed

private
  n0 : Nat ; n0 = zero
  n1 : Nat ; n1 = suc n0
  n2 : Nat ; n2 = suc n1
  n3 : Nat ; n3 = suc n2

------------------------------------------------------------------------
-- ProofE3: V3 correctness witness.
--
-- The H parameter is the ambient hypothesis used by the derivation
-- being witnessed.  hCode = reify (codeEqn H) is the Term encoding
-- of H passed to thmT.

record ProofE3 (H : Equation) (eq : Equation) : Set where
  constructor mkProofE3
  field
    encT : Term
    corr : {hyp : Equation} ->
           Deriv hyp (eqn (ap1 (thmT (reify (codeEqn H))) encT)
                          (reify (codeEqn eq)))
open ProofE3 public

------------------------------------------------------------------------
-- Case 0: axI t.
--
-- Encoding at Tree level:  encAxI (code t) = nd (natCode n0) (nd (code t) lf).
-- At Term level:            reify(encAxI (code t)) = ap2 Pair O (ap2 Pair tC O).
-- Expected conclusion:      codeEqn (eqn (ap1 I t) t).

thm14EV3AxI : (H : Equation) (t : Term) -> ProofE3 H (eqn (ap1 I t) t)
thm14EV3AxI H t = mkProofE3 enc correct
  where
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  tagR  : Term ; tagR  = O
  body  : Term ; body  = ap2 Pair tC O
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  codeIF : Term ; codeIF = reify (codeF1 I)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 I t) t))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR tC O recs)
    (ruleTrans (ndBranchHit n0 case0 (ndT1V3 hCode) body recs)
    (mkEqFRed (mkAp1F (kF2 codeIF) origA) origA enc recs
      (ap2 Pair (reify tagAp1) (ap2 Pair codeIF tC)) tC
      (mkAp1FRed (kF2 codeIF) origA enc recs codeIF tC
        (kF2Red codeIF enc recs)
        (origARed tagR tC O recs))
      (origARed tagR tC O recs))))

------------------------------------------------------------------------
-- Case 1: axFst a b.
--
-- Encoding at Tree level: encAxFst (code a) (code b) = nd (natCode n1) (nd (code a) (code b)).

thm14EV3AxFst : (H : Equation) (a b : Term) ->
                ProofE3 H (eqn (ap1 Fst (ap2 Pair a b)) a)
thm14EV3AxFst H a b = mkProofE3 enc correct
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n1)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  codeFstF : Term ; codeFstF = reify (codeF1 Fst)
  pairCF   : Term ; pairCF   = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 Fst (ap2 Pair a b)) a))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR aC bC recs)
    -- navigate ndDispatchV3 hCode from n0 (miss) to n1 (hit)
    (ruleTrans (ndBranchMiss n1 n0 case0 (ndT1V3 hCode) body recs refl)
    (ruleTrans (ndBranchHit n1 case1 (ndT2V3 hCode) body recs)
    (mkEqFRed (mkAp1F (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB))
              origA enc recs
      (ap2 Pair (reify tagAp1) (ap2 Pair codeFstF
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
      aC
      (mkAp1FRed (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB)
        enc recs codeFstF
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red codeFstF enc recs)
        (mkAp2FRed (kF2 pairCF) origA origB enc recs pairCF aC bC
          (kF2Red pairCF enc recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (origARed tagR aC bC recs)))))
