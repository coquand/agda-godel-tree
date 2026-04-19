{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Thm14E where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.ThFunCorrect
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs
open import Guard.NdDispatchProofs
open import Guard.ExtractorRed
open import Guard.SubstCorrect
open import Guard.IntermediatePassthrough
open import Guard.PairPassthroughAll
open import Guard.SubstTFor using (substTFor)

------------------------------------------------------------------------
-- ProofE: enhanced proof witness with thFunTFor correctness
-- pa = tag part, pb = data part of the encoding tree nd(pa, pb).
-- Components:
--   1. thFun(nd pa pb) = codeEqn eq
--   2. thFunTFor(Pair(reify pa, reify pb)) = reify(codeEqn eq)
--   3. Passthrough: ndDispatch at this encoding falls through to sndArg2

ProofE : Equation -> Set
ProofE eq = Sigma Tree (\pa -> Sigma Tree (\pb ->
  Sigma (Eq (thFun (nd pa pb)) (codeEqn eq)) (\_ ->
  Sigma ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify pa) (reify pb)))
                   (reify (codeEqn eq)))) (\_ ->
    (x recs : Term) -> {hyp : Equation} ->
      Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair (reify pa) (reify pb)) x) recs)
                     (ap2 sndArg2 (ap2 Pair (ap2 Pair (reify pa) (reify pb)) x) recs))))))

------------------------------------------------------------------------
-- Smart constructor

mkProofE : {eq : Equation} (pa pb : Tree) ->
  Eq (thFun (nd pa pb)) (codeEqn eq) ->
  ({hyp : Equation} -> Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify pa) (reify pb))) (reify (codeEqn eq)))) ->
  ((x rcs : Term) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair (reify pa) (reify pb)) x) rcs) (ap2 sndArg2 (ap2 Pair (ap2 Pair (reify pa) (reify pb)) x) rcs))) ->
  ProofE eq
mkProofE pa pb thfEq corr pass = mkSigma pa (mkSigma pb (mkSigma thfEq (mkSigma corr pass)))

------------------------------------------------------------------------
-- Nat abbreviations

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

------------------------------------------------------------------------
-- Passthrough helpers

passthroughSuc : (n : Nat) (dat : Tree) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch
    (ap2 Pair (ap2 Pair (ap2 Pair O (reify (natCode n))) (reify dat)) x) rcs)
    (ap2 sndArg2
    (ap2 Pair (ap2 Pair (ap2 Pair O (reify (natCode n))) (reify dat)) x) rcs))
passthroughSuc n dat x rcs = ndDispatchPairMiss O (reify (natCode n)) (reify dat) x rcs

-- For encAxI (tag 0): case-split on Term since code(t) is stuck for generic t
private
  axIPassthrough : (t : Term) (x rcs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 ndDispatch
      (ap2 Pair (ap2 Pair O (ap2 Pair (reify (code t)) O)) x) rcs)
      (ap2 sndArg2
      (ap2 Pair (ap2 Pair O (ap2 Pair (reify (code t)) O)) x) rcs))
  axIPassthrough O x rcs = ndDispatchOPairMiss O O O x rcs
  axIPassthrough (var n) x rcs =
    ndDispatchOPairMiss
      (ap2 Pair (ap2 Pair (ap2 Pair O O) O) O) (reify (natCode n)) O x rcs
  axIPassthrough (ap1 f t) x rcs =
    ndDispatchOPairMiss
      (ap2 Pair O (ap2 Pair O O)) (ap2 Pair (reify (codeF1 f)) (reify (code t))) O x rcs
  axIPassthrough (ap2 g a b) x rcs =
    ndDispatchOPairMiss
      (ap2 Pair O (ap2 Pair O (ap2 Pair O O)))
      (ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code a)) (reify (code b)))) O x rcs

------------------------------------------------------------------------
-- Case 0: axI t

thm14EAxI : (t : Term) -> ProofE (eqn (ap1 I t) t)
thm14EAxI t = mkProofE {eqn (ap1 I t) t} (natCode n0) (nd (code t) lf) refl correct
  (\x rcs -> axIPassthrough t x rcs)
  where
  tC : Term ; tC = reify (code t)
  tagR : Term ; tagR = O
  orig : Term ; orig = ap2 Pair tagR (ap2 Pair tC O)
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor (ap2 Pair tC O))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair O (ap2 Pair tC O)))
                   (reify (codeEqn (eqn (ap1 I t) t))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR (ap2 Pair tC O))
    (ruleTrans (guardNd tagR tC O recs)
    (ruleTrans (ndDisp0 (ap2 Pair tC O) recs)
    (mkEqFRed (mkAp1F (kF2 (reify (codeF1 I))) origA) origA orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) tC)) tC
      (mkAp1FRed (kF2 (reify (codeF1 I))) origA orig recs (reify (codeF1 I)) tC
        (kF2Red (reify (codeF1 I)) orig recs)
        (origARed tagR tC O recs))
      (origARed tagR tC O recs))))

------------------------------------------------------------------------
-- Case 1: axFst a b

thm14EAxFst : (a b : Term) -> ProofE (eqn (ap1 Fst (ap2 Pair a b)) a)
thm14EAxFst a b = mkProofE {eqn (ap1 Fst (ap2 Pair a b)) a} (natCode n1) (nd (code a) (code b)) refl correct
  (\x' r' -> passthroughSuc n0 (nd (code a) (code b)) x' r')
  where
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n1)
  orig : Term ; orig = ap2 Pair tagR (ap2 Pair aC bC)
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor (ap2 Pair aC bC))
  pairCF : Term ; pairCF = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify (natCode n1)) (ap2 Pair aC bC)))
                   (reify (codeEqn (eqn (ap1 Fst (ap2 Pair a b)) a))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR (ap2 Pair aC bC))
    (ruleTrans (guardNd tagR aC bC recs)
    (ruleTrans (ndDisp1 (ap2 Pair aC bC) recs)
    (mkEqFRed (mkAp1F (kF2 (reify (codeF1 Fst))) (mkAp2F (kF2 pairCF) origA origB))
              origA orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
      aC
      (mkAp1FRed (kF2 (reify (codeF1 Fst))) (mkAp2F (kF2 pairCF) origA origB)
        orig recs (reify (codeF1 Fst))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red (reify (codeF1 Fst)) orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB orig recs pairCF aC bC
          (kF2Red pairCF orig recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (origARed tagR aC bC recs))))

------------------------------------------------------------------------
-- Case 2: axSnd a b

thm14EAxSnd : (a b : Term) -> ProofE (eqn (ap1 Snd (ap2 Pair a b)) b)
thm14EAxSnd a b = mkProofE {eqn (ap1 Snd (ap2 Pair a b)) b} (natCode n2) (nd (code a) (code b)) refl correct
  (\x' r' -> passthroughSuc n1 (nd (code a) (code b)) x' r')
  where
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n2)
  orig : Term ; orig = ap2 Pair tagR (ap2 Pair aC bC)
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor (ap2 Pair aC bC))
  pairCF : Term ; pairCF = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify (natCode n2)) (ap2 Pair aC bC)))
                   (reify (codeEqn (eqn (ap1 Snd (ap2 Pair a b)) b))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR (ap2 Pair aC bC))
    (ruleTrans (guardNd tagR aC bC recs)
    (ruleTrans (ndDisp2 (ap2 Pair aC bC) recs)
    (mkEqFRed (mkAp1F (kF2 (reify (codeF1 Snd))) (mkAp2F (kF2 pairCF) origA origB))
              origB orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
      bC
      (mkAp1FRed (kF2 (reify (codeF1 Snd))) (mkAp2F (kF2 pairCF) origA origB)
        orig recs (reify (codeF1 Snd))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red (reify (codeF1 Snd)) orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB orig recs pairCF aC bC
          (kF2Red pairCF orig recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (origBRed tagR aC bC recs))))

------------------------------------------------------------------------
-- Case 3: axConst a b

thm14EAxConst : (a b : Term) -> ProofE (eqn (ap2 Const a b) a)
thm14EAxConst a b = mkProofE {eqn (ap2 Const a b) a} (natCode n3) (nd (code a) (code b)) refl correct
  (\x' r' -> passthroughSuc n2 (nd (code a) (code b)) x' r')
  where
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n3)
  orig : Term ; orig = ap2 Pair tagR (ap2 Pair aC bC)
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor (ap2 Pair aC bC))
  constCF : Term ; constCF = reify (codeF2 Const)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify (natCode n3)) (ap2 Pair aC bC)))
                   (reify (codeEqn (eqn (ap2 Const a b) a))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR (ap2 Pair aC bC))
    (ruleTrans (guardNd tagR aC bC recs)
    (ruleTrans (ndDisp3 (ap2 Pair aC bC) recs)
    (mkEqFRed (mkAp2F (kF2 constCF) origA origB) origA orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair constCF (ap2 Pair aC bC)))
      aC
      (mkAp2FRed (kF2 constCF) origA origB orig recs constCF aC bC
        (kF2Red constCF orig recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs))
      (origARed tagR aC bC recs))))

------------------------------------------------------------------------
-- Case 17: axRefl t

thm14ERefl : (t : Term) -> ProofE (eqn t t)
thm14ERefl t = mkProofE {eqn t t} (natCode n17) (nd (code t) lf) refl correctRefl
  (\x' r' -> passthroughSuc n16 (nd (code t) lf) x' r')
  where
  tagR : Term ; tagR = reify (natCode n17)
  dataA : Term ; dataA = reify (code t)
  orig : Term ; orig = ap2 Pair tagR (ap2 Pair dataA O)
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor (ap2 Pair dataA O))

  correctRefl : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (reify (encRefl (code t)))) (reify (codeEqn (eqn t t))))
  correctRefl =
    ruleTrans (recNdRed O thFunStep tagR (ap2 Pair dataA O))
    (ruleTrans (guardNd tagR dataA O recs)
    (ruleTrans (ndDisp17 (ap2 Pair dataA O) recs)
    (mkEqFRed origA origA orig recs dataA dataA
      (origARed tagR dataA O recs)
      (origARed tagR dataA O recs))))

------------------------------------------------------------------------
-- Remaining axiom cases: holes
-- Cases 4-16, 25 have pre-existing issues in ThFunTForCases
-- (tag offsets and oC definition need fixing before proofs work).

thm14EAxComp : (f g : Fun1) (t : Term) -> ProofE (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))
thm14EAxComp f g t = mkProofE {eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))}
  (natCode n4) (nd (codeF1 f) (nd (codeF1 g) (code t))) refl correct
  (\x' r' -> passthroughSuc n3 (nd (codeF1 f) (nd (codeF1 g) (code t))) x' r')
  where
  fC : Term ; fC = reify (codeF1 f)
  gC : Term ; gC = reify (codeF1 g)
  tC : Term ; tC = reify (code t)
  tagR : Term ; tagR = reify (natCode n4)
  dat : Term ; dat = ap2 Pair fC (ap2 Pair gC tC)
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  compCTag : Term ; compCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR fC (ap2 Pair gC tC) recs)
    (ruleTrans (ndDisp4 dat recs)
    (mkEqFRed (mkAp1F (Fan (kF2 compCTag) (Fan origA origB1 Pair) Pair) origB2)
              (mkAp1F origA (mkAp1F origB1 origB2)) orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair compCTag (ap2 Pair fC gC))
        tC))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC
        (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))))
      (mkAp1FRed (Fan (kF2 compCTag) (Fan origA origB1 Pair) Pair) origB2
        orig recs
        (ap2 Pair compCTag (ap2 Pair fC gC))
        tC
        (ruleTrans (fanRed (kF2 compCTag) (Fan origA origB1 Pair) Pair orig recs)
        (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) orig recs)
                     (kF2Red compCTag orig recs))
        (congR Pair compCTag
          (ruleTrans (fanRed origA origB1 Pair orig recs)
          (ruleTrans (congL Pair (ap2 origB1 orig recs)
                       (origARed tagR fC (ap2 Pair gC tC) recs))
                     (congR Pair fC
                       (origB1Red tagR fC gC tC recs)))))))
        (origB2Red tagR fC gC tC recs))
      (mkAp1FRed origA (mkAp1F origB1 origB2) orig recs fC
        (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))
        (origARed tagR fC (ap2 Pair gC tC) recs)
        (mkAp1FRed origB1 origB2 orig recs gC tC
          (origB1Red tagR fC gC tC recs)
          (origB2Red tagR fC gC tC recs))))))

thm14EAxComp2 : (h : Fun2) (f g : Fun1) (t : Term) ->
  ProofE (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t)))
thm14EAxComp2 h f g t = mkProofE {eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))}
  (natCode n5) (nd (codeF2 h) (nd (codeF1 f) (nd (codeF1 g) (code t)))) refl correct
  (\x' r' -> passthroughSuc n4 (nd (codeF2 h) (nd (codeF1 f) (nd (codeF1 g) (code t)))) x' r')
  where
  hC : Term ; hC = reify (codeF2 h)
  fC : Term ; fC = reify (codeF1 f)
  gC : Term ; gC = reify (codeF1 g)
  tC : Term ; tC = reify (code t)
  tagR : Term ; tagR = reify (natCode n5)
  dat : Term ; dat = ap2 Pair hC (ap2 Pair fC (ap2 Pair gC tC))
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  comp2CTag : Term
  comp2CTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR hC (ap2 Pair fC (ap2 Pair gC tC)) recs)
    (ruleTrans (ndDisp5 dat recs)
    (mkEqFRed
      (mkAp1F (Fan (kF2 comp2CTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origB2b)
      (mkAp2F origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b))
      orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair comp2CTag (ap2 Pair hC (ap2 Pair fC gC)))
        tC))
      (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair
        (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
        (ap2 Pair (reify tagAp1) (ap2 Pair gC tC)))))
      (mkAp1FRed
        (Fan (kF2 comp2CTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origB2b
        orig recs
        (ap2 Pair comp2CTag (ap2 Pair hC (ap2 Pair fC gC)))
        tC
        (ruleTrans (fanRed (kF2 comp2CTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair orig recs)
        (ruleTrans (congL Pair (ap2 (Fan origA (Fan origB1 origB2a Pair) Pair) orig recs)
                     (kF2Red comp2CTag orig recs))
        (congR Pair comp2CTag
          (ruleTrans (fanRed origA (Fan origB1 origB2a Pair) Pair orig recs)
          (ruleTrans (congL Pair (ap2 (Fan origB1 origB2a Pair) orig recs)
                       (origARed tagR hC (ap2 Pair fC (ap2 Pair gC tC)) recs))
          (congR Pair hC
            (ruleTrans (fanRed origB1 origB2a Pair orig recs)
            (ruleTrans (congL Pair (ap2 origB2a orig recs)
                         (origB1Red tagR hC fC (ap2 Pair gC tC) recs))
                       (congR Pair fC
                         (origB2aRed tagR hC fC gC tC recs))))))))))
        (origB2bRed tagR hC fC gC tC recs))
      (mkAp2FRed origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b) orig recs
        hC
        (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
        (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))
        (origARed tagR hC (ap2 Pair fC (ap2 Pair gC tC)) recs)
        (mkAp1FRed origB1 origB2b orig recs fC tC
          (origB1Red tagR hC fC (ap2 Pair gC tC) recs)
          (origB2bRed tagR hC fC gC tC recs))
        (mkAp1FRed origB2a origB2b orig recs gC tC
          (origB2aRed tagR hC fC gC tC recs)
          (origB2bRed tagR hC fC gC tC recs))))))

thm14EAxLift : (f : Fun1) (a b : Term) -> ProofE (eqn (ap2 (Lift f) a b) (ap1 f a))
thm14EAxLift f a b = mkProofE {eqn (ap2 (Lift f) a b) (ap1 f a)}
  (natCode n6) (nd (codeF1 f) (nd (code a) (code b))) refl correct
  (\x' r' -> passthroughSuc n5 (nd (codeF1 f) (nd (code a) (code b))) x' r')
  where
  fC : Term ; fC = reify (codeF1 f)
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n6)
  dat : Term ; dat = ap2 Pair fC (ap2 Pair aC bC)
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  liftCTag : Term
  liftCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 (Lift f) a b) (ap1 f a)))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR fC (ap2 Pair aC bC) recs)
    (ruleTrans (ndDisp6 dat recs)
    (mkEqFRed (mkAp2F (Fan (kF2 liftCTag) origA Pair) origB1 origB2)
              (mkAp1F origA origB1) orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair
        (ap2 Pair liftCTag fC)
        (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC aC))
      (mkAp2FRed (Fan (kF2 liftCTag) origA Pair) origB1 origB2 orig recs
        (ap2 Pair liftCTag fC) aC bC
        (ruleTrans (fanRed (kF2 liftCTag) origA Pair orig recs)
        (ruleTrans (congL Pair (ap2 origA orig recs) (kF2Red liftCTag orig recs))
                   (congR Pair liftCTag (origARed tagR fC (ap2 Pair aC bC) recs))))
        (origB1Red tagR fC aC bC recs)
        (origB2Red tagR fC aC bC recs))
      (mkAp1FRed origA origB1 orig recs fC aC
        (origARed tagR fC (ap2 Pair aC bC) recs)
        (origB1Red tagR fC aC bC recs)))))

thm14EAxPost : (f : Fun1) (h : Fun2) (a b : Term) ->
  ProofE (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b)))
thm14EAxPost f h a b = mkProofE {eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))}
  (natCode n7) (nd (codeF1 f) (nd (codeF2 h) (nd (code a) (code b)))) refl correct
  (\x' r' -> passthroughSuc n6 (nd (codeF1 f) (nd (codeF2 h) (nd (code a) (code b)))) x' r')
  where
  fC : Term ; fC = reify (codeF1 f)
  hC : Term ; hC = reify (codeF2 h)
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n7)
  dat : Term ; dat = ap2 Pair fC (ap2 Pair hC (ap2 Pair aC bC))
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  postCTag : Term
  postCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR fC (ap2 Pair hC (ap2 Pair aC bC)) recs)
    (ruleTrans (ndDisp7 dat recs)
    (mkEqFRed
      (mkAp2F (Fan (kF2 postCTag) (Fan origA origB1 Pair) Pair) origB2a origB2b)
      (mkAp1F origA (mkAp2F origB1 origB2a origB2b))
      orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair
        (ap2 Pair postCTag (ap2 Pair fC hC))
        (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC
        (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair aC bC)))))
      (mkAp2FRed (Fan (kF2 postCTag) (Fan origA origB1 Pair) Pair) origB2a origB2b
        orig recs
        (ap2 Pair postCTag (ap2 Pair fC hC))
        aC bC
        (ruleTrans (fanRed (kF2 postCTag) (Fan origA origB1 Pair) Pair orig recs)
        (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) orig recs)
                     (kF2Red postCTag orig recs))
        (congR Pair postCTag
          (ruleTrans (fanRed origA origB1 Pair orig recs)
          (ruleTrans (congL Pair (ap2 origB1 orig recs)
                       (origARed tagR fC (ap2 Pair hC (ap2 Pair aC bC)) recs))
                     (congR Pair fC
                       (origB1Red tagR fC hC (ap2 Pair aC bC) recs)))))))
        (origB2aRed tagR fC hC aC bC recs)
        (origB2bRed tagR fC hC aC bC recs))
      (mkAp1FRed origA (mkAp2F origB1 origB2a origB2b) orig recs fC
        (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair aC bC)))
        (origARed tagR fC (ap2 Pair hC (ap2 Pair aC bC)) recs)
        (mkAp2FRed origB1 origB2a origB2b orig recs hC aC bC
          (origB1Red tagR fC hC (ap2 Pair aC bC) recs)
          (origB2aRed tagR fC hC aC bC recs)
          (origB2bRed tagR fC hC aC bC recs))))))

thm14EAxFan : (h1 h2 h : Fun2) (a b : Term) ->
  ProofE (eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b)))
thm14EAxFan h1 h2 h a b = mkProofE {eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b))}
  (natCode n8) (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h) (nd (code a) (code b))))) refl correct
  (\x' r' -> passthroughSuc n7 (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h) (nd (code a) (code b))))) x' r')
  where
  h1C : Term ; h1C = reify (codeF2 h1)
  h2C : Term ; h2C = reify (codeF2 h2)
  hC : Term ; hC = reify (codeF2 h)
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n8)
  dat : Term ; dat = ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC)))
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  fanCTag : Term
  fanCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))
  ob2b1F : Fun2 ; ob2b1F = Post Fst origB2b
  ob2b2F : Fun2 ; ob2b2F = Post Snd origB2b

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b))))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))) recs)
    (ruleTrans (ndDisp8 dat recs)
    (mkEqFRed
      (mkAp2F (Fan (kF2 fanCTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) ob2b1F ob2b2F)
      (mkAp2F origB2a (mkAp2F origA ob2b1F ob2b2F) (mkAp2F origB1 ob2b1F ob2b2F))
      orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair (ap2 Pair fanCTag (ap2 Pair h1C (ap2 Pair h2C hC))) (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC))))))
      (mkAp2FRed (Fan (kF2 fanCTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) ob2b1F ob2b2F
        orig recs (ap2 Pair fanCTag (ap2 Pair h1C (ap2 Pair h2C hC))) aC bC
        (ruleTrans (fanRed (kF2 fanCTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair orig recs)
        (ruleTrans (congL Pair (ap2 (Fan origA (Fan origB1 origB2a Pair) Pair) orig recs) (kF2Red fanCTag orig recs))
        (congR Pair fanCTag
          (ruleTrans (fanRed origA (Fan origB1 origB2a Pair) Pair orig recs)
          (ruleTrans (congL Pair (ap2 (Fan origB1 origB2a Pair) orig recs)
                       (origARed tagR h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))) recs))
          (congR Pair h1C
            (ruleTrans (fanRed origB1 origB2a Pair orig recs)
            (ruleTrans (congL Pair (ap2 origB2a orig recs)
                         (origB1Red tagR h1C h2C (ap2 Pair hC (ap2 Pair aC bC)) recs))
                       (congR Pair h2C (origB2aRed tagR h1C h2C hC (ap2 Pair aC bC) recs))))))))))
        (origB2b1Red tagR h1C h2C hC aC bC recs)
        (origB2b2Red tagR h1C h2C hC aC bC recs))
      (mkAp2FRed origB2a (mkAp2F origA ob2b1F ob2b2F) (mkAp2F origB1 ob2b1F ob2b2F)
        orig recs hC
        (ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC)))
        (origB2aRed tagR h1C h2C hC (ap2 Pair aC bC) recs)
        (mkAp2FRed origA ob2b1F ob2b2F orig recs h1C aC bC
          (origARed tagR h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))) recs)
          (origB2b1Red tagR h1C h2C hC aC bC recs)
          (origB2b2Red tagR h1C h2C hC aC bC recs))
        (mkAp2FRed origB1 ob2b1F ob2b2F orig recs h2C aC bC
          (origB1Red tagR h1C h2C (ap2 Pair hC (ap2 Pair aC bC)) recs)
          (origB2b1Red tagR h1C h2C hC aC bC recs)
          (origB2b2Red tagR h1C h2C hC aC bC recs))))))

thm14EAxRecLf : (z : Term) (s : Fun2) -> ProofE (eqn (ap1 (Rec z s) O) z)
thm14EAxRecLf z s = mkProofE {eqn (ap1 (Rec z s) O) z}
  (natCode n9) (nd (code z) (codeF2 s)) refl correct
  (\x' r' -> passthroughSuc n8 (nd (code z) (codeF2 s)) x' r')
  where
  zC : Term ; zC = reify (code z)
  sC : Term ; sC = reify (codeF2 s)
  tagR : Term ; tagR = reify (natCode n9)
  dat : Term ; dat = ap2 Pair zC sC
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  oCC : Term ; oCC = ap2 Pair O O
  recTagC : Term
  recTagC = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap1 (Rec z s) O) z))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR zC sC recs)
    (ruleTrans (ndDisp9 dat recs)
    (mkEqFRed (mkAp1F (Fan (kF2 recTagC) (Fan origA origB Pair) Pair) (kF2 oCC))
              origA orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair recTagC (ap2 Pair zC sC))
        oCC))
      zC
      (mkAp1FRed (Fan (kF2 recTagC) (Fan origA origB Pair) Pair) (kF2 oCC)
        orig recs
        (ap2 Pair recTagC (ap2 Pair zC sC))
        oCC
        (ruleTrans (fanRed (kF2 recTagC) (Fan origA origB Pair) Pair orig recs)
        (ruleTrans (congL Pair (ap2 (Fan origA origB Pair) orig recs)
                     (kF2Red recTagC orig recs))
        (congR Pair recTagC
          (ruleTrans (fanRed origA origB Pair orig recs)
          (ruleTrans (congL Pair (ap2 origB orig recs)
                       (origARed tagR zC sC recs))
                     (congR Pair zC
                       (origBRed tagR zC sC recs)))))))
        (kF2Red oCC orig recs))
      (origARed tagR zC sC recs))))

thm14EAxRecNd : (z : Term) (s : Fun2) (a b : Term) ->
  ProofE (eqn (ap1 (Rec z s) (ap2 Pair a b))
              (ap2 s (ap2 Pair a b) (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b))))
thm14EAxRecNd z s a b = mkProofE {eqn (ap1 (Rec z s) (ap2 Pair a b))
              (ap2 s (ap2 Pair a b) (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b)))}
  (natCode n10) (nd (code z) (nd (codeF2 s) (nd (code a) (code b)))) refl correct
  (\x' r' -> passthroughSuc n9 (nd (code z) (nd (codeF2 s) (nd (code a) (code b)))) x' r')
  where
  zC : Term ; zC = reify (code z)
  sC : Term ; sC = reify (codeF2 s)
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n10)
  dat : Term ; dat = ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC))
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  oCC : Term ; oCC = ap2 Pair O O
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  recTagC : Term
  recTagC = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))
  recF : Fun2 ; recF = Fan (kF2 recTagC) (Fan origA origB1 Pair) Pair
  pairAB : Fun2 ; pairAB = mkAp2F (kF2 pairCF) origB2a origB2b

  recFVal : Term ; recFVal = ap2 Pair recTagC (ap2 Pair zC sC)
  pairABVal : Term
  pairABVal = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))

  recFPf : {hyp : Equation} -> Deriv hyp (eqn (ap2 recF orig recs) recFVal)
  recFPf =
    ruleTrans (fanRed (kF2 recTagC) (Fan origA origB1 Pair) Pair orig recs)
    (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) orig recs) (kF2Red recTagC orig recs))
    (congR Pair recTagC
      (ruleTrans (fanRed origA origB1 Pair orig recs)
      (ruleTrans (congL Pair (ap2 origB1 orig recs)
                   (origARed tagR zC (ap2 Pair sC (ap2 Pair aC bC)) recs))
                 (congR Pair zC (origB1Red tagR zC sC (ap2 Pair aC bC) recs))))))

  pairABPf : {hyp : Equation} -> Deriv hyp (eqn (ap2 pairAB orig recs) pairABVal)
  pairABPf =
    mkAp2FRed (kF2 pairCF) origB2a origB2b orig recs pairCF aC bC
      (kF2Red pairCF orig recs)
      (origB2aRed tagR zC sC aC bC recs)
      (origB2bRed tagR zC sC aC bC recs)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap1 (Rec z s) (ap2 Pair a b))
                     (ap2 s (ap2 Pair a b) (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b)))))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR zC (ap2 Pair sC (ap2 Pair aC bC)) recs)
    (ruleTrans (ndDisp10 dat recs)
    (mkEqFRed (mkAp1F recF pairAB)
              (mkAp2F origB1 pairAB (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b)))
      orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair recFVal pairABVal))
      (ap2 Pair (reify tagAp2) (ap2 Pair sC (ap2 Pair pairABVal
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC))))))))
      (mkAp1FRed recF pairAB orig recs recFVal pairABVal recFPf pairABPf)
      (mkAp2FRed origB1 pairAB
        (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b))
        orig recs sC pairABVal
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC)))))
        (origB1Red tagR zC sC (ap2 Pair aC bC) recs)
        pairABPf
        (mkAp2FRed (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b) orig recs
          pairCF
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC))
          (kF2Red pairCF orig recs)
          (mkAp1FRed recF origB2a orig recs recFVal aC recFPf
            (origB2aRed tagR zC sC aC bC recs))
          (mkAp1FRed recF origB2b orig recs recFVal bC recFPf
            (origB2bRed tagR zC sC aC bC recs)))))))

thm14EAxIfLfL : (a b : Term) -> ProofE (eqn (ap2 IfLf O (ap2 Pair a b)) a)
thm14EAxIfLfL a b = mkProofE {eqn (ap2 IfLf O (ap2 Pair a b)) a}
  (natCode n11) (nd (code a) (code b)) refl correct
  (\x' r' -> passthroughSuc n10 (nd (code a) (code b)) x' r')
  where
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n11)
  dat : Term ; dat = ap2 Pair aC bC
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  oCC : Term ; oCC = ap2 Pair O O

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 IfLf O (ap2 Pair a b)) a))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR aC bC recs)
    (ruleTrans (ndDisp11 dat recs)
    (mkEqFRed (mkAp2F (kF2 iflfCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB))
              origA orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair oCC
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))))
      aC
      (mkAp2FRed (kF2 iflfCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB)
        orig recs iflfCF oCC
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red iflfCF orig recs)
        (kF2Red oCC orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB orig recs pairCF aC bC
          (kF2Red pairCF orig recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (origARed tagR aC bC recs))))

thm14EAxIfLfN : (x y a b : Term) ->
  ProofE (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b)
thm14EAxIfLfN x y a b = mkProofE {eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b}
  (natCode n12) (nd (code x) (nd (code y) (nd (code a) (code b)))) refl correct
  (\x' r' -> passthroughSuc n11 (nd (code x) (nd (code y) (nd (code a) (code b)))) x' r')
  where
  xC : Term ; xC = reify (code x)
  yC : Term ; yC = reify (code y)
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n12)
  dat : Term ; dat = ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC))
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  pairCF : Term ; pairCF = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR xC (ap2 Pair yC (ap2 Pair aC bC)) recs)
    (ruleTrans (ndDisp12 dat recs)
    (mkEqFRed
      (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                            (mkAp2F (kF2 pairCF) origB2a origB2b))
      origB2b orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair xC yC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))))
      bC
      (mkAp2FRed (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                               (mkAp2F (kF2 pairCF) origB2a origB2b) orig recs
        iflfCF
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair xC yC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red iflfCF orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB1 orig recs pairCF xC yC
          (kF2Red pairCF orig recs)
          (origARed tagR xC (ap2 Pair yC (ap2 Pair aC bC)) recs)
          (origB1Red tagR xC yC (ap2 Pair aC bC) recs))
        (mkAp2FRed (kF2 pairCF) origB2a origB2b orig recs pairCF aC bC
          (kF2Red pairCF orig recs)
          (origB2aRed tagR xC yC aC bC recs)
          (origB2bRed tagR xC yC aC bC recs)))
      (origB2bRed tagR xC yC aC bC recs))))

thm14EAxTreeEqLL : ProofE (eqn (ap2 TreeEq O O) O)
thm14EAxTreeEqLL = mkProofE {eqn (ap2 TreeEq O O) O}
  (natCode n13) lf refl correct
  (\x' r' -> passthroughSuc n12 lf x' r')
  where
  tagR : Term ; tagR = reify (natCode n13)
  orig : Term ; orig = ap2 Pair tagR O
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor O)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  oC : Term ; oC = reify lf
  reifyTagAp2 : Term ; reifyTagAp2 = reify tagAp2
  pairCF : Term ; pairCF = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR O))
                   (reify (codeEqn (eqn (ap2 TreeEq O O) O))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR O)
    (ruleTrans (guardLf tagR recs)
    (ruleTrans (ndBranchHit n13 case13 (kF2 O) O recs)
    (mkEqFRed (mkAp2F (kF2 treeeqCF) (kF2 oCC) (kF2 oCC)) (kF2 oCC) orig recs
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCF (ap2 Pair oCC oCC)))
      oCC
      (mkAp2FRed (kF2 treeeqCF) (kF2 oCC) (kF2 oCC) orig recs treeeqCF oCC oCC
        (kF2Red treeeqCF orig recs)
        (kF2Red oCC orig recs)
        (kF2Red oCC orig recs))
      (kF2Red oCC orig recs))))
    where
    oCC : Term ; oCC = ap2 Pair O O

thm14EAxTreeEqLN : (a b : Term) ->
  ProofE (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O))
thm14EAxTreeEqLN a b = mkProofE {eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)}
  (natCode n14) (nd (code a) (code b)) refl correct
  (\x' r' -> passthroughSuc n13 (nd (code a) (code b)) x' r')
  where
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n14)
  dat : Term ; dat = ap2 Pair aC bC
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  oCC : Term ; oCC = ap2 Pair O O
  reifyTagAp2 : Term ; reifyTagAp2 = reify tagAp2
  oneC : Term ; oneC = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oCC oCC))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR aC bC recs)
    (ruleTrans (ndDisp14 dat recs)
    (mkEqFRed (mkAp2F (kF2 treeeqCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB))
              (kF2 oneC) orig recs
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCF (ap2 Pair oCC
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC))))))
      oneC
      (mkAp2FRed (kF2 treeeqCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB)
        orig recs treeeqCF oCC
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red treeeqCF orig recs)
        (kF2Red oCC orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB orig recs pairCF aC bC
          (kF2Red pairCF orig recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (kF2Red oneC orig recs))))

thm14EAxTreeEqNL : (a b : Term) ->
  ProofE (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O))
thm14EAxTreeEqNL a b = mkProofE {eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)}
  (natCode n15) (nd (code a) (code b)) refl correct
  (\x' r' -> passthroughSuc n14 (nd (code a) (code b)) x' r')
  where
  aC : Term ; aC = reify (code a)
  bC : Term ; bC = reify (code b)
  tagR : Term ; tagR = reify (natCode n15)
  dat : Term ; dat = ap2 Pair aC bC
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  oCC : Term ; oCC = ap2 Pair O O
  reifyTagAp2 : Term ; reifyTagAp2 = reify tagAp2
  oneC : Term ; oneC = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oCC oCC))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR aC bC recs)
    (ruleTrans (ndDisp15 dat recs)
    (mkEqFRed (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oCC))
              (kF2 oneC) orig recs
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCF (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC)))
        oCC)))
      oneC
      (mkAp2FRed (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oCC)
        orig recs treeeqCF
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC)))
        oCC
        (kF2Red treeeqCF orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB orig recs pairCF aC bC
          (kF2Red pairCF orig recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs))
        (kF2Red oCC orig recs))
      (kF2Red oneC orig recs))))

thm14EAxTreeEqNN : (a1 a2 b1 b2 : Term) ->
  ProofE (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
              (ap2 IfLf (ap2 TreeEq a1 b1)
                        (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O))))
thm14EAxTreeEqNN a1 a2 b1 b2 = mkProofE
  {eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
       (ap2 IfLf (ap2 TreeEq a1 b1) (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O)))}
  (natCode n16) (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))) refl correct
  (\x' r' -> passthroughSuc n15 (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))) x' r')
  where
  a1C : Term ; a1C = reify (code a1)
  a2C : Term ; a2C = reify (code a2)
  b1C : Term ; b1C = reify (code b1)
  b2C : Term ; b2C = reify (code b2)
  tagR : Term ; tagR = reify (natCode n16)
  dat : Term ; dat = ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C))
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  oCC : Term ; oCC = ap2 Pair O O
  reifyTagAp2 : Term
  reifyTagAp2 = ap2 Pair O (ap2 Pair O (ap2 Pair O O))
  oneCF : Term
  oneCF = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oCC oCC))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                     (ap2 IfLf (ap2 TreeEq a1 b1)
                               (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O)))))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
    (ruleTrans (ndDisp16 dat recs)
    (mkEqFRed
      (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                              (mkAp2F (kF2 pairCF) origB2a origB2b))
      (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                            (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b)
                                                  (kF2 oneCF)))
      orig recs
      (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair a1C a2C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair b1C b2C))))))
      (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a1C b1C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C))) oneCF))))))
      (mkAp2FRed (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                                 (mkAp2F (kF2 pairCF) origB2a origB2b) orig recs
        treeeqCF
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair a1C a2C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair b1C b2C)))
        (kF2Red treeeqCF orig recs)
        (mkAp2FRed (kF2 pairCF) origA origB1 orig recs pairCF a1C a2C
          (kF2Red pairCF orig recs)
          (origARed tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
          (origB1Red tagR a1C a2C (ap2 Pair b1C b2C) recs))
        (mkAp2FRed (kF2 pairCF) origB2a origB2b orig recs pairCF b1C b2C
          (kF2Red pairCF orig recs)
          (origB2aRed tagR a1C a2C b1C b2C recs)
          (origB2bRed tagR a1C a2C b1C b2C recs)))
      (mkAp2FRed (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                               (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b)
                                                     (kF2 oneCF))
        orig recs iflfCF
        (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a1C b1C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C))) oneCF)))
        (kF2Red iflfCF orig recs)
        (mkAp2FRed (kF2 treeeqCF) origA origB2a orig recs treeeqCF a1C b1C
          (kF2Red treeeqCF orig recs)
          (origARed tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
          (origB2aRed tagR a1C a2C b1C b2C recs))
        (mkAp2FRed (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneCF)
          orig recs pairCF
          (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C)))
          oneCF
          (kF2Red pairCF orig recs)
          (mkAp2FRed (kF2 treeeqCF) origB1 origB2b orig recs treeeqCF a2C b2C
            (kF2Red treeeqCF orig recs)
            (origB1Red tagR a1C a2C (ap2 Pair b1C b2C) recs)
            (origB2bRed tagR a1C a2C b1C b2C recs))
          (kF2Red oneCF orig recs))))))

thm14EAxKT : (t x : Term) -> ProofE (eqn (ap1 (KT t) x) t)
thm14EAxKT t x = mkProofE {eqn (ap1 (KT t) x) t}
  (natCode n25) (nd (code t) (code x)) refl correct
  (\x' r' -> passthroughSuc n24 (nd (code t) (code x)) x' r')
  where
  tC : Term ; tC = reify (code t)
  xC : Term ; xC = reify (code x)
  tagR : Term ; tagR = reify (natCode n25)
  dat : Term ; dat = ap2 Pair tC xC
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  codeKTTag : Term
  codeKTTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
                   (reify (codeEqn (eqn (ap1 (KT t) x) t))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (guardNd tagR tC xC recs)
    (ruleTrans (ndDisp25 dat recs)
    (mkEqFRed (mkAp1F (Fan (kF2 codeKTTag) origA Pair) origB) origA orig recs
      (ap2 Pair (reify tagAp1) (ap2 Pair (ap2 Pair codeKTTag tC) xC))
      tC
      (mkAp1FRed (Fan (kF2 codeKTTag) origA Pair) origB orig recs
        (ap2 Pair codeKTTag tC) xC
        (ruleTrans (fanRed (kF2 codeKTTag) origA Pair orig recs)
        (ruleTrans (congL Pair (ap2 origA orig recs) (kF2Red codeKTTag orig recs))
                   (congR Pair codeKTTag (origARed tagR tC xC recs))))
        (origBRed tagR tC xC recs))
      (origARed tagR tC xC recs))))

------------------------------------------------------------------------
-- Passthrough helpers for functor codes (case-split needed since codeF1/codeF2 are stuck)

private
  f1DispMiss : (f : Fun1) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (codeF1 f)) x') rc')
                   (ap2 sndArg2 (ap2 Pair (reify (codeF1 f)) x') rc'))
  f1DispMiss I x' rc' = ndDispatchPairMiss O (reify (natCode n25)) O x' rc'
  f1DispMiss Fst x' rc' = ndDispatchPairMiss O (reify (natCode (suc n25))) O x' rc'
  f1DispMiss Snd x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc n25)))) O x' rc'
  f1DispMiss (Comp f g) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc n25))))) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x' rc'
  f1DispMiss (Comp2 h f g) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc (suc n25)))))) (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))) x' rc'
  f1DispMiss (Rec z s) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc (suc (suc n25))))))) (ap2 Pair (reify (code z)) (reify (codeF2 s))) x' rc'
  f1DispMiss (KT t) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc (suc (suc (suc n25)))))))) (reify (code t)) x' rc'

  f2DispMiss : (g : Fun2) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (codeF2 g)) x') rc')
                   (ap2 sndArg2 (ap2 Pair (reify (codeF2 g)) x') rc'))
  f2DispMiss Pair x' rc' = ndDispatchPairMiss O (reify (natCode n25)) O x' rc'
  f2DispMiss Const x' rc' = ndDispatchPairMiss O (reify (natCode (suc n25))) O x' rc'
  f2DispMiss (Lift f) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc n25)))) (reify (codeF1 f)) x' rc'
  f2DispMiss (Post f h) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc n25))))) (ap2 Pair (reify (codeF1 f)) (reify (codeF2 h))) x' rc'
  f2DispMiss (Fan h1 h2 h) x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc (suc n25)))))) (ap2 Pair (reify (codeF2 h1)) (ap2 Pair (reify (codeF2 h2)) (reify (codeF2 h)))) x' rc'
  f2DispMiss IfLf x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc (suc (suc n25))))))) O x' rc'
  f2DispMiss TreeEq x' rc' = ndDispatchPairMiss O (reify (natCode (suc (suc (suc (suc (suc (suc n25)))))))) O x' rc'

  -- For Pair(reify(codeF2 g), reify(code x)) as tag: case-split on g
  -- ndDispatchPairMiss a1 a2 b x recs where Pair(a1,a2)=reify(codeF2 g), b=reify(code x)
  f2xDispMiss : (g : Fun2) (x : Term) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x))) x') rc')
                   (ap2 sndArg2 (ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x))) x') rc'))
  f2xDispMiss Pair x x' rc' = ndDispatchPairMiss (reify (natCode (suc n25))) O (reify (code x)) x' rc'
  f2xDispMiss Const x x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc n25)))) O (reify (code x)) x' rc'
  f2xDispMiss (Lift f) x x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc n25))))) (reify (codeF1 f)) (reify (code x)) x' rc'
  f2xDispMiss (Post f h) x x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc n25)))))) (ap2 Pair (reify (codeF1 f)) (reify (codeF2 h))) (reify (code x)) x' rc'
  f2xDispMiss (Fan h1 h2 h) x x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc (suc n25))))))) (ap2 Pair (reify (codeF2 h1)) (ap2 Pair (reify (codeF2 h2)) (reify (codeF2 h)))) (reify (code x)) x' rc'
  f2xDispMiss IfLf x x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc (suc (suc n25)))))))) O (reify (code x)) x' rc'
  f2xDispMiss TreeEq x x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc (suc (suc (suc n25))))))))) O (reify (code x)) x' rc'

------------------------------------------------------------------------
-- Structural cases

thm14ESym : {t u : Term} -> ProofE (eqn t u) -> ProofE (eqn u t)
thm14ESym {t} {u} (mkSigma pa (mkSigma pb (mkSigma thfPf (mkSigma corrPf passPf)))) =
  mkProofE {eqn u t} (natCode n18) (nd tagVar (nd pa pb))
    (eqCong (\eq -> nd (rightT eq) (leftT eq)) thfPf)
    correct
    (\x' r' -> passthroughSuc n17 (nd tagVar (nd pa pb)) x' r')
  where
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  spR : Term ; spR = ap2 Pair (reify pa) (reify pb)
  tagVarR : Term ; tagVarR = reify tagVar
  tagR : Term ; tagR = reify (natCode n18)
  dat : Term ; dat = ap2 Pair tagVarR spR
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  recs' : Term ; recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap1 thFunTFor tagVarR) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap1 thFunTFor tagVarR) (ap2 Pair tC uC)))
  datExpand = ruleTrans (intermediatePassthrough (ap2 Pair O O) O O spR (reify pa) (reify pb))
                        (congR Pair (ap1 thFunTFor tagVarR) corrPf)

  recsExpand : {hyp : Equation} -> Deriv hyp (eqn recs recs')
  recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat)) (ap2 Pair uC tC))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR tagVarR spR recs')
    (ruleTrans (ndDisp18 dat recs')
    (mkEqFRed recsBR recsBL orig recs' uC tC
      (recsBRRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor tagVarR) tC uC)
      (recsBLRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor tagVarR) tC uC)))))

thm14ETrans : {t u v : Term} -> ProofE (eqn t u) -> ProofE (eqn u v) -> ProofE (eqn t v)
thm14ETrans {t} {u} {v} (mkSigma pa1 (mkSigma pb1 (mkSigma thfPf1 (mkSigma corrPf1 passPf1))))
                        (mkSigma pa2 (mkSigma pb2 (mkSigma thfPf2 (mkSigma corrPf2 passPf2)))) =
  mkProofE {eqn t v} (natCode n19) (nd (nd pa1 pb1) (nd pa2 pb2))
    (eqCong2 (\eq1 eq2 -> nd (leftT eq1) (rightT eq2)) thfPf1 thfPf2)
    correct
    (\x' r' -> passthroughSuc n18 (nd (nd pa1 pb1) (nd pa2 pb2)) x' r')
  where
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  vC : Term ; vC = reify (code v)
  sp1R : Term ; sp1R = ap2 Pair (reify pa1) (reify pb1)
  sp2R : Term ; sp2R = ap2 Pair (reify pa2) (reify pb2)
  tagR : Term ; tagR = reify (natCode n19)
  dat : Term ; dat = ap2 Pair sp1R sp2R
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  recs' : Term
  recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC)))
  datExpand =
    ruleTrans (intermediateGeneric sp1R sp2R (reify pa2) (reify pb2)
      (\x' rc' -> passPf1 x' rc'))
    (ruleTrans (congL Pair (ap1 thFunTFor sp2R) corrPf1)
               (congR Pair (ap2 Pair tC uC) corrPf2))

  recsExpand : {hyp : Equation} -> Deriv hyp (eqn recs recs')
  recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat)) (ap2 Pair tC vC))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR sp1R sp2R recs')
    (ruleTrans (ndDisp19 dat recs')
    (mkEqFRed recsAL recsBR orig recs' tC vC
      (recsALRed orig (ap1 thFunTFor tagR) tC uC (ap2 Pair uC vC))
      (recsBRRed orig (ap1 thFunTFor tagR) (ap2 Pair tC uC) uC vC)))))

thm14ECong1 : {t u : Term} (f : Fun1) -> ProofE (eqn t u) -> ProofE (eqn (ap1 f t) (ap1 f u))
thm14ECong1 {t} {u} f (mkSigma pa (mkSigma pb (mkSigma thfPf (mkSigma corrPf passPf)))) =
  mkProofE {eqn (ap1 f t) (ap1 f u)} (natCode n20) (nd (codeF1 f) (nd pa pb))
    (eqCong (\eq -> nd (mkAp1 (codeF1 f) (leftT eq)) (mkAp1 (codeF1 f) (rightT eq))) thfPf)
    correct
    (\x' r' -> passthroughSuc n19 (nd (codeF1 f) (nd pa pb)) x' r')
  where
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  fC : Term ; fC = reify (codeF1 f)
  spR : Term ; spR = ap2 Pair (reify pa) (reify pb)
  tagR : Term ; tagR = reify (natCode n20)
  dat : Term ; dat = ap2 Pair fC spR
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  recs' : Term
  recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap1 thFunTFor fC) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap1 thFunTFor fC) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGeneric fC spR (reify pa) (reify pb) (\x' rc' -> f1DispMiss f x' rc'))
    (congR Pair (ap1 thFunTFor fC) corrPf)

  recsExpand : {hyp : Equation} -> Deriv hyp (eqn recs recs')
  recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
      (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
                (ap2 Pair (reify tagAp1) (ap2 Pair fC uC))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR fC spR recs')
    (ruleTrans (ndDisp20 dat recs')
    (mkEqFRed (mkAp1F origA recsBL) (mkAp1F origA recsBR) orig recs'
      (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC uC))
      (mkAp1FRed origA recsBL orig recs' fC tC
        (origARed tagR fC spR recs')
        (recsBLRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor fC) tC uC))
      (mkAp1FRed origA recsBR orig recs' fC uC
        (origARed tagR fC spR recs')
        (recsBRRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor fC) tC uC))))))

thm14ECongL : {t u : Term} (g : Fun2) (x : Term) -> ProofE (eqn t u) -> ProofE (eqn (ap2 g t x) (ap2 g u x))
thm14ECongL {t} {u} g x (mkSigma pa (mkSigma pb (mkSigma thfPf (mkSigma corrPf passPf)))) =
  mkProofE {eqn (ap2 g t x) (ap2 g u x)} (natCode n21) (nd (nd (codeF2 g) (code x)) (nd pa pb))
    (eqCong (\eq -> nd (mkAp2 (codeF2 g) (leftT eq) (code x))
                       (mkAp2 (codeF2 g) (rightT eq) (code x))) thfPf)
    correct
    (\x' r' -> passthroughSuc n20 (nd (nd (codeF2 g) (code x)) (nd pa pb)) x' r')
  where
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  gC : Term ; gC = reify (codeF2 g)
  xC : Term ; xC = reify (code x)
  spR : Term ; spR = ap2 Pair (reify pa) (reify pb)
  aR : Term ; aR = ap2 Pair gC xC
  tagR : Term ; tagR = reify (natCode n21)
  dat : Term ; dat = ap2 Pair aR spR
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  recs' : Term
  recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap1 thFunTFor aR) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap1 thFunTFor aR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGeneric aR spR (reify pa) (reify pb)
      (\x' rc' -> f2xDispMiss g x x' rc'))
    (congR Pair (ap1 thFunTFor aR) corrPf)

  recsExpand : {hyp : Equation} -> Deriv hyp (eqn recs recs')
  recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
      (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair tC xC)))
                (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair uC xC)))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR aR spR recs')
    (ruleTrans (ndDisp21 dat recs')
    (mkEqFRed (mkAp2F origAL recsBL origAR) (mkAp2F origAL recsBR origAR) orig recs'
      (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair tC xC)))
      (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair uC xC)))
      (mkAp2FRed origAL recsBL origAR orig recs' gC tC xC
        (origALRed tagR gC xC spR recs')
        (recsBLRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor aR) tC uC)
        (origARRed tagR gC xC spR recs'))
      (mkAp2FRed origAL recsBR origAR orig recs' gC uC xC
        (origALRed tagR gC xC spR recs')
        (recsBRRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor aR) tC uC)
        (origARRed tagR gC xC spR recs'))))))

thm14ECongR : {t u : Term} (g : Fun2) (x : Term) -> ProofE (eqn t u) -> ProofE (eqn (ap2 g x t) (ap2 g x u))
thm14ECongR {t} {u} g x (mkSigma pa (mkSigma pb (mkSigma thfPf (mkSigma corrPf passPf)))) =
  mkProofE {eqn (ap2 g x t) (ap2 g x u)} (natCode n22) (nd (nd (codeF2 g) (code x)) (nd pa pb))
    (eqCong (\eq -> nd (mkAp2 (codeF2 g) (code x) (leftT eq))
                       (mkAp2 (codeF2 g) (code x) (rightT eq))) thfPf)
    correct
    (\x' r' -> passthroughSuc n21 (nd (nd (codeF2 g) (code x)) (nd pa pb)) x' r')
  where
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  gC : Term ; gC = reify (codeF2 g)
  xC : Term ; xC = reify (code x)
  spR : Term ; spR = ap2 Pair (reify pa) (reify pb)
  aR : Term ; aR = ap2 Pair gC xC
  tagR : Term ; tagR = reify (natCode n22)
  dat : Term ; dat = ap2 Pair aR spR
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)
  recs' : Term
  recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap1 thFunTFor aR) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap1 thFunTFor aR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGeneric aR spR (reify pa) (reify pb)
      (\x' rc' -> f2xDispMiss g x x' rc'))
    (congR Pair (ap1 thFunTFor aR) corrPf)

  recsExpand : {hyp : Equation} -> Deriv hyp (eqn recs recs')
  recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
      (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC tC)))
                (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC uC)))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR aR spR recs')
    (ruleTrans (ndDisp22 dat recs')
    (mkEqFRed (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR) orig recs'
      (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC tC)))
      (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC uC)))
      (mkAp2FRed origAL origAR recsBL orig recs' gC xC tC
        (origALRed tagR gC xC spR recs')
        (origARRed tagR gC xC spR recs')
        (recsBLRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor aR) tC uC))
      (mkAp2FRed origAL origAR recsBR orig recs' gC xC uC
        (origALRed tagR gC xC spR recs')
        (origARRed tagR gC xC spR recs')
        (recsBRRed orig (ap1 thFunTFor tagR) (ap1 thFunTFor aR) tC uC))))))

thm14EInst : {l r' : Term} (x : Nat) (t : Term) -> ProofE (eqn l r') -> ProofE (eqn (subst x t l) (subst x t r'))
thm14EInst {l} {r'} x t pe =
  let l' = subst x t l
      r'' = subst x t r'
      pe1 = thm14ERefl l'
      pe2 = thm14ERefl r''
  in instAux l' r'' pe1 pe2
  where
  instAux : (l' r'' : Term) -> ProofE (eqn l' l') -> ProofE (eqn r'' r'') ->
    ProofE (eqn l' r'')
  instAux l' r'' (mkSigma pa1 (mkSigma pb1 (mkSigma thfPf1 (mkSigma corrPf1 passPf1))))
                 (mkSigma pa2 (mkSigma pb2 (mkSigma thfPf2 (mkSigma corrPf2 passPf2)))) =
    mkProofE {eqn l' r''} (natCode n19) (nd (nd pa1 pb1) (nd pa2 pb2))
      (eqCong2 (\eq1 eq2 -> nd (leftT eq1) (rightT eq2)) thfPf1 thfPf2)
      correct
      (\x' rc' -> passthroughSuc n18 (nd (nd pa1 pb1) (nd pa2 pb2)) x' rc')
    where
    l'C : Term ; l'C = reify (code l')
    r''C : Term ; r''C = reify (code r'')
    sp1R : Term ; sp1R = ap2 Pair (reify pa1) (reify pb1)
    sp2R : Term ; sp2R = ap2 Pair (reify pa2) (reify pb2)
    tagR : Term ; tagR = reify (natCode n19)
    dat : Term ; dat = ap2 Pair sp1R sp2R
    orig : Term ; orig = ap2 Pair tagR dat
    recs' : Term
    recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap2 Pair l'C l'C) (ap2 Pair r''C r''C))

    datExpand : {hyp : Equation} ->
      Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap2 Pair l'C l'C) (ap2 Pair r''C r''C)))
    datExpand =
      ruleTrans (intermediateGeneric sp1R sp2R (reify pa2) (reify pb2) (\x' rc' -> passPf1 x' rc'))
      (ruleTrans (congL Pair (ap1 thFunTFor sp2R) corrPf1) (congR Pair (ap2 Pair l'C l'C) corrPf2))

    recsExpand : {hyp : Equation} -> Deriv hyp (eqn (ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)) recs')
    recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

    correct : {hyp : Equation} ->
      Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat)) (ap2 Pair l'C r''C))
    correct =
      ruleTrans (recNdRed O thFunStep tagR dat)
      (ruleTrans (congR thFunStep orig recsExpand)
      (ruleTrans (guardNd tagR sp1R sp2R recs')
      (ruleTrans (ndDisp19 dat recs')
      (mkEqFRed recsAL recsBR orig recs' l'C r''C
        (recsALRed orig (ap1 thFunTFor tagR) l'C l'C (ap2 Pair r''C r''C))
        (recsBRRed orig (ap1 thFunTFor tagR) (ap2 Pair l'C l'C) r''C r''C)))))

thm14EF : (f g : Fun1) (z : Term) (s : Fun2) ->
  ProofE (eqn (ap1 f O) z) ->
  ProofE (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
              (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                     (ap2 Pair (ap1 f (var zero)) (ap1 f (var (suc zero)))))) ->
  ProofE (eqn (ap1 g O) z) ->
  ProofE (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
              (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                     (ap2 Pair (ap1 g (var zero)) (ap1 g (var (suc zero)))))) ->
  ProofE (eqn (ap1 f (var zero)) (ap1 g (var zero)))
thm14EF f g z s
  (mkSigma pa1 (mkSigma pb1 (mkSigma thfPf1 (mkSigma corrPf1 passPf1))))
  (mkSigma pa2 (mkSigma pb2 (mkSigma thfPf2 (mkSigma corrPf2 passPf2))))
  (mkSigma pa3 (mkSigma pb3 (mkSigma thfPf3 (mkSigma corrPf3 passPf3))))
  (mkSigma pa4 (mkSigma pb4 (mkSigma thfPf4 (mkSigma corrPf4 passPf4)))) =
  let pbTree = nd (nd (code z) (codeF2 s)) (nd (nd (nd pa1 pb1) (nd pa2 pb2)) (nd (nd pa3 pb3) (nd pa4 pb4)))
  in mkProofE {eqn (ap1 f (var zero)) (ap1 g (var zero))}
    (natCode n24) (nd (nd (codeF1 f) (codeF1 g)) pbTree)
    refl correct
    (\x' r' -> passthroughSuc n23 (nd (nd (codeF1 f) (codeF1 g)) pbTree) x' r')
  where
  fC : Term ; fC = reify (codeF1 f)
  gC' : Term ; gC' = reify (codeF1 g)
  v0C : Term
  v0C = reify (nd (nd (nd (nd lf lf) lf) lf) lf)
  tagR : Term ; tagR = reify (natCode n24)
  aR : Term ; aR = ap2 Pair fC gC'
  bChild1 : Term ; bChild1 = ap2 Pair (reify (code z)) (reify (codeF2 s))
  bChild2 : Term ; bChild2 = ap2 Pair (ap2 Pair (reify (nd pa1 pb1)) (reify (nd pa2 pb2))) (ap2 Pair (reify (nd pa3 pb3)) (reify (nd pa4 pb4)))
  bR : Term ; bR = ap2 Pair bChild1 bChild2
  dat : Term ; dat = ap2 Pair aR bR
  orig : Term ; orig = ap2 Pair tagR dat
  recs : Term ; recs = ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)

  -- For case24, we need the intermediate passthrough for nd(nd(fC,gC), nd(...))
  -- First child = nd(codeF1 f, codeF1 g). Case-split needed for dispatch miss.
  aDispMiss : (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair aR x') rc') (ap2 sndArg2 (ap2 Pair aR x') rc'))
  aDispMiss = f1gDispMiss f g
    where
    f1gDispMiss : (f' : Fun1) (g' : Fun1) (x' rc' : Term) -> {hyp : Equation} ->
      Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair (reify (codeF1 f')) (reify (codeF1 g'))) x') rc')
                     (ap2 sndArg2 (ap2 Pair (ap2 Pair (reify (codeF1 f')) (reify (codeF1 g'))) x') rc'))
    f1gDispMiss I g' x' rc' = ndDispatchPairMiss (reify (natCode (suc n25))) O (reify (codeF1 g')) x' rc'
    f1gDispMiss Fst g' x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc n25)))) O (reify (codeF1 g')) x' rc'
    f1gDispMiss Snd g' x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc n25))))) O (reify (codeF1 g')) x' rc'
    f1gDispMiss (Comp f1 f2) g' x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc n25)))))) (ap2 Pair (reify (codeF1 f1)) (reify (codeF1 f2))) (reify (codeF1 g')) x' rc'
    f1gDispMiss (Comp2 h f1 f2) g' x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc (suc n25))))))) (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f1)) (reify (codeF1 f2)))) (reify (codeF1 g')) x' rc'
    f1gDispMiss (Rec z' s') g' x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc (suc (suc n25)))))))) (ap2 Pair (reify (code z')) (reify (codeF2 s'))) (reify (codeF1 g')) x' rc'
    f1gDispMiss (KT t) g' x' rc' = ndDispatchPairMiss (reify (natCode (suc (suc (suc (suc (suc (suc (suc n25))))))))) (reify (code t)) (reify (codeF1 g')) x' rc'

  recs' : Term
  recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap1 thFunTFor aR) (ap1 thFunTFor bR))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap1 thFunTFor aR) (ap1 thFunTFor bR)))
  datExpand =
    intermediateGeneric aR bR bChild1 bChild2
      aDispMiss

  recsExpand : {hyp : Equation} -> Deriv hyp (eqn recs recs')
  recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagR dat))
      (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair fC v0C))
                (ap2 Pair (reify tagAp1) (ap2 Pair gC' v0C))))
  correct =
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR aR bR recs')
    (ruleTrans (ndDisp24 dat recs')
    (mkEqFRed (mkAp1F origAL (kF2 v0C)) (mkAp1F origAR (kF2 v0C)) orig recs'
      (ap2 Pair (reify tagAp1) (ap2 Pair fC v0C))
      (ap2 Pair (reify tagAp1) (ap2 Pair gC' v0C))
      (mkAp1FRed origAL (kF2 v0C) orig recs' fC v0C
        (origALRed tagR fC gC' bR recs')
        (kF2Red v0C orig recs'))
      (mkAp1FRed origAR (kF2 v0C) orig recs' gC' v0C
        (origARRed tagR fC gC' bR recs')
        (kF2Red v0C orig recs'))))))

------------------------------------------------------------------------
-- Main theorem

thm14E : {hyp : Equation} {eq : Equation} -> Deriv hyp eq -> ProofE hyp -> ProofE eq
thm14E (axI t) ph = thm14EAxI t
thm14E (axFst a b) ph = thm14EAxFst a b
thm14E (axSnd a b) ph = thm14EAxSnd a b
thm14E (axConst a b) ph = thm14EAxConst a b
thm14E (axComp f g t) ph = thm14EAxComp f g t
thm14E (axComp2 h f g t) ph = thm14EAxComp2 h f g t
thm14E (axLift f a b) ph = thm14EAxLift f a b
thm14E (axPost f h a b) ph = thm14EAxPost f h a b
thm14E (axFan h1 h2 h a b) ph = thm14EAxFan h1 h2 h a b
thm14E (axKT t x) ph = thm14EAxKT t x
thm14E (axRecLf z s) ph = thm14EAxRecLf z s
thm14E (axRecNd z s a b) ph = thm14EAxRecNd z s a b
thm14E (axIfLfL a b) ph = thm14EAxIfLfL a b
thm14E (axIfLfN x y a b) ph = thm14EAxIfLfN x y a b
thm14E axTreeEqLL ph = thm14EAxTreeEqLL
thm14E (axTreeEqLN a b) ph = thm14EAxTreeEqLN a b
thm14E (axTreeEqNL a b) ph = thm14EAxTreeEqNL a b
thm14E (axTreeEqNN a1 a2 b1 b2) ph = thm14EAxTreeEqNN a1 a2 b1 b2
thm14E (axRefl t) ph = thm14ERefl t
thm14E (ruleSym d) ph = thm14ESym (thm14E d ph)
thm14E (ruleTrans d1 d2) ph = thm14ETrans (thm14E d1 ph) (thm14E d2 ph)
thm14E (cong1 f d) ph = thm14ECong1 f (thm14E d ph)
thm14E (congL g x d) ph = thm14ECongL g x (thm14E d ph)
thm14E (congR g x d) ph = thm14ECongR g x (thm14E d ph)
thm14E (ruleInst x t {eqn l r'} d) ph = thm14EInst x t (thm14E d ph)
thm14E ruleHyp ph = ph
thm14E (ruleF f g z s bf sf bg sg) ph = thm14EF f g z s (thm14E bf ph) (thm14E sf ph) (thm14E bg ph) (thm14E sg ph)
