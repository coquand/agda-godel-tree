{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StepFrontEnd2 -- the TWO-FUEL-VARIABLE front end of the
-- surprise-GII inductive step ( clos Step 1 , two independent fuels ).
--
-- =====================================================================
-- GOAL.
-- =====================================================================
--
--   frontEnd2 :  S(r)  ->  (picks, bound)  ->
--     Deriv (imp (BigConjFormula consts (suc r) picks)              -- K_rest @ x0
--                (KdefBigConjF enum (var 1) M (natCode r)))          -- phi    @ x1
--
-- Unlike the SHIPPED single-fuel  StepFrontEnd.frontEnd  ( which pins BOTH the
-- antecedent  K_rest  and the consequent  phi  to the SAME fuel  var 0 ), here
-- the consequent's per-program negations live at the SECOND fuel  x1 = var 1 ,
-- kept distinct and free.   This is what lets the clash later instantiate  x0
-- ( for the Sigma_1-lift of  K_rest ) and  x1 ( := the diagonal's halt time )
-- INDEPENDENTLY.
--
-- The new content vs  frontEnd  is the per-program implication : to negate the
-- day- r  describe at fuel  x1 , both the assumed describe @ x1  and the
-- antecedent  K_rest @ x0  are lifted to the COMMON fuel  x0 + x1  ( = sigma
-- x0 x1 ) by the FORMULA-level run monotonicity  T4.RunProgMono.imp_runProgMonoPlus ;
-- at the common fuel the day- r -extended big conjunction contradicts  S(r)
-- instantiated at that fuel.   No  leq , no  max  -- the two additive gaps
-- ( x1  for the K_rest conjuncts ,  x0  for the day- r  describe , reconciled by
--  T36  commutativity ) land everything at the single fuel  sigma x0 x1 .

module T4.StepFrontEnd2 where

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right
                                 ; ruleInst2 )
open import BRA3.Church    using ( sigma ; T36 )
open import BRA3.Contrapositive using ( identP ; compI )
open import T4.Kdef         using ( runProg )
open import T4.Code         using ( falseF )
open import T4.Counting     using ( negToImpFalse ; impFalseToNeg_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impCongR ; impEqTrans )
open import T4.RunProgMono  using ( imp_runProgMonoPlus )
open import T4.SubstNoVar    using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )

open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula
  using ( BigConjFormula ; bigConjCountT ; conjF ; describeAtT ; trueF
        ; countDays ; openFuel )
open import T4.SurpriseG2.AndLemmas
  using ( negConjToImpRtoNegL ; liftedAndIntro ; fstAndImp ; sndAndImp )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF )

open import T4.SurpriseG2.StepFrontEnd
  using ( addO ; addO_suc_left ; countDays_step ; extPicks ; extAt_r
        ; extAt_above ; iteLe ; natEqb )

------------------------------------------------------------------------
-- The common fuel  x0 + x1  and the constant fuel function.

common : Term
common = ap2 sigma (var zero) (var (suc zero))

constHalts : Nat -> Term
constHalts _ = common

F1 : Term
F1 = var (suc zero)

------------------------------------------------------------------------
-- All helpers are parametric in the enumerator.

module _ (enum : Fun1) where

  ----------------------------------------------------------------------
  -- (a) bigConjCountT is extensional in  picks  ( common-fuel version of
  --     StepFrontEnd.bigConjExt , with the per-day fuel function threaded ).

  bigConjExtT :
    (count start : Nat) (halts : Nat -> Term) (p1 p2 : Nat -> Nat) ->
    ((i : Nat) -> Eq (p1 (addO start i)) (p2 (addO start i))) ->
    Eq (bigConjCountT enum count start p1 halts)
       (bigConjCountT enum count start p2 halts)
  bigConjExtT zero    start halts p1 p2 agree = refl
  bigConjExtT (suc c) start halts p1 p2 agree =
    let headEq : Eq (p1 start) (p2 start)
        headEq = agree zero
        tailAgree : (i : Nat) ->
          Eq (p1 (addO (suc start) i)) (p2 (addO (suc start) i))
        tailAgree i =
          eqTrans (eqCong p1 (addO_suc_left start i))
                  (eqTrans (agree (suc i))
                           (eqSym (eqCong p2 (addO_suc_left start i))))
        ih : Eq (bigConjCountT enum c (suc start) p1 halts)
                (bigConjCountT enum c (suc start) p2 halts)
        ih = bigConjExtT c (suc start) halts p1 p2 tailAgree
    in eqTrans (eqCong (\ pr -> conjF (describeAtT enum pr start (halts start))
                                       (bigConjCountT enum c (suc start) p1 halts)) headEq)
               (eqCong (\ T -> conjF (describeAtT enum (p2 start) start (halts start)) T) ih)

  ----------------------------------------------------------------------
  -- (b) Lift a whole open-fuel conjunction to the common fuel ( each positive
  --     describe conjunct  runProg p (var 0) = s d  lifts to  ... common  via
  --     imp_runProgMonoPlus  with the additive gap  x1 ;  common = x0 + x1 ).

  bigConjLift :
    (count start : Nat) (picks : Nat -> Nat) ->
    Deriv (imp (bigConjCountT enum count start picks openFuel)
               (bigConjCountT enum count start picks constHalts))
  bigConjLift zero    start picks = identP trueF
  bigConjLift (suc c) start picks =
    let hd0 : Formula
        hd0 = describeAtT enum (picks start) start (var zero)
        tl0 : Formula
        tl0 = bigConjCountT enum c (suc start) picks openFuel
        X0 : Formula
        X0 = conjF hd0 tl0
        prog : Term
        prog = ap1 enum (natCode (picks start))
        hHead : Deriv (imp X0 (describeAtT enum (picks start) start common))
        hHead = imp_runProgMonoPlus X0 prog (natCode start) (var zero) (var (suc zero))
                  (fstAndImp hd0 tl0)
        hTail : Deriv (imp X0 (bigConjCountT enum c (suc start) picks constHalts))
        hTail = compI (sndAndImp hd0 tl0) (bigConjLift c (suc start) picks)
    in liftedAndIntro X0 (describeAtT enum (picks start) start common)
                         (bigConjCountT enum c (suc start) picks constHalts) hHead hTail

  ----------------------------------------------------------------------
  -- (c) substF 0 common  distributes over the open-fuel conjunction, turning
  --     it into the constant-common-fuel conjunction ( META Eq , by induction ;
  --     each leaf reduces definitionally since  substT 0 common (var 0) = common ).

  substDescribe :
    (p d : Nat) ->
    Eq (substF zero common (describeAtT enum p d (var zero)))
       (describeAtT enum p d common)
  substDescribe p d =
    eqTrans
      (eqCong (\ z -> eqF (ap2 runProg (ap1 enum z) common)
                          (ap1 s (substT zero common (natCode d))))
              (substT_NoVar zero common (natCode p) (NoVar_natCode p)))
      (eqCong (\ z -> eqF (ap2 runProg (ap1 enum (natCode p)) common) (ap1 s z))
              (substT_NoVar zero common (natCode d) (NoVar_natCode d)))

  substBigConj :
    (count start : Nat) (picks : Nat -> Nat) ->
    Eq (substF zero common (bigConjCountT enum count start picks openFuel))
       (bigConjCountT enum count start picks constHalts)
  substBigConj zero    start picks = refl
  substBigConj (suc c) start picks =
    eqTrans
      (eqCong (\ Hd -> conjF Hd
                        (substF zero common (bigConjCountT enum c (suc start) picks openFuel)))
              (substDescribe (picks start) start))
      (eqCong (\ T -> conjF (describeAtT enum (picks start) start common) T)
              (substBigConj c (suc start) picks))

  ----------------------------------------------------------------------
  -- (d) Aggregate the per-program implications into  KdefBigConjF  ( mirror of
  --     StepFrontEnd.aggregateImp at the fuel- x1  shape ).

  aggregateImp2 :
    (Xf : Formula) (M' : Nat) (subj : Term) ->
    ((k : Nat) -> NatLe k M' ->
       Deriv (imp Xf (perProgNegF enum F1 subj k))) ->
    Deriv (imp Xf (KdefBigConjF enum F1 M' subj))
  aggregateImp2 Xf zero      subj negs = negs zero (le-zero zero)
  aggregateImp2 Xf (suc M'') subj negs =
    liftedAndIntro Xf (perProgNegF enum F1 subj (suc M''))
                      (KdefBigConjF enum F1 M'' subj)
      (negs (suc M'') (le-refl (suc M'')))
      (aggregateImp2 Xf M'' subj (\ k le -> negs k (le-suc-right le)))

------------------------------------------------------------------------
-- The two-fuel front end.

frontEnd2 :
  (consts : SurpriseConstsConj) (r : Nat) ->
  NatLe r (SurpriseConstsConj.N consts) ->
  StagePredF consts r ->
  (picks : Picks) (bound : PicksBound consts picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
              (KdefBigConjF (SurpriseConstsConj.enum consts) F1
                            (SurpriseConstsConj.M consts) (natCode r)))
frontEnd2 consts r rleN Sr picks bound =
  let N : Nat
      N = SurpriseConstsConj.N consts
      M : Nat
      M = SurpriseConstsConj.M consts
      enum : Fun1
      enum = SurpriseConstsConj.enum consts

      X : Formula
      X = BigConjFormula consts (suc r) picks    -- = bigConjCountT enum (countDays N (suc r)) (suc r) picks openFuel

      Xc : Formula
      Xc = bigConjCountT enum (countDays N (suc r)) (suc r) picks constHalts

      sigmaComm10 : Deriv (eqF (ap2 sigma (var (suc zero)) (var zero)) common)
      sigmaComm10 = ruleInst2 zero (var (suc zero)) (suc zero) (var zero) refl T36

      perProgImp :
        (kin : Nat) -> NatLe kin M ->
        Deriv (imp X (perProgNegF enum F1 (natCode r) kin))
      perProgImp kin kle =
        let picks' : Nat -> Nat
            picks' = extPicks picks r kin
            bound' : PicksBound consts picks'
            bound' d dleN =
              iteLe M (natEqb d r) kin (picks d) kle (bound d dleN)

            prog_kin : Term
            prog_kin = ap1 enum (natCode kin)

            D1 : Formula                    -- describe kin r  @ x1
            D1 = describeAtT enum kin r F1
            H : Formula
            H = conjF D1 X

            hD1 : Deriv (imp H D1)
            hD1 = fstAndImp D1 X
            hX : Deriv (imp H X)
            hX = sndAndImp D1 X

            -- D1 ( fuel x1 ) lifted to  describe kin r @ common .
            hD1plus : Deriv (imp H (eqF (ap2 runProg prog_kin (ap2 sigma (var (suc zero)) (var zero)))
                                        (ap1 s (natCode r))))
            hD1plus = imp_runProgMonoPlus H prog_kin (natCode r) (var (suc zero)) (var zero) hD1
            hD1c : Deriv (imp H (describeAtT enum kin r common))
            hD1c =
              impEqTrans {H} (ap2 runProg prog_kin common)
                (ap2 runProg prog_kin (ap2 sigma (var (suc zero)) (var zero)))
                (ap1 s (natCode r))
                (impCongR {H} runProg common (ap2 sigma (var (suc zero)) (var zero)) prog_kin
                          (impLift {H} (ruleSym sigmaComm10)))
                hD1plus

            -- K_rest ( fuel x0 ) lifted to common.
            hXc : Deriv (imp H Xc)
            hXc = compI hX (bigConjLift enum (countDays N (suc r)) (suc r) picks)

            -- the day- r -extended conjunction at the common fuel.
            conjHc : Deriv (imp H (conjF (describeAtT enum kin r common) Xc))
            conjHc = liftedAndIntro H (describeAtT enum kin r common) Xc hD1c hXc

            -- transport to  BigConjFormula picks'  at the common fuel.
            unfoldEqC :
              Eq (bigConjCountT enum (countDays N r) r picks' constHalts)
                 (conjF (describeAtT enum kin r common) Xc)
            unfoldEqC =
              let step_count : Eq (bigConjCountT enum (countDays N r) r picks' constHalts)
                                  (conjF (describeAtT enum (picks' r) r common)
                                         (bigConjCountT enum (countDays N (suc r)) (suc r) picks' constHalts))
                  step_count =
                    eqCong (\ c -> bigConjCountT enum c r picks' constHalts)
                           (countDays_step N r rleN)
                  step_progr : Eq (conjF (describeAtT enum (picks' r) r common)
                                          (bigConjCountT enum (countDays N (suc r)) (suc r) picks' constHalts))
                                  (conjF (describeAtT enum kin r common)
                                          (bigConjCountT enum (countDays N (suc r)) (suc r) picks' constHalts))
                  step_progr =
                    eqCong (\ ix -> conjF (describeAtT enum ix r common)
                                          (bigConjCountT enum (countDays N (suc r)) (suc r) picks' constHalts))
                           (extAt_r picks r kin)
                  tailEqC : Eq (bigConjCountT enum (countDays N (suc r)) (suc r) picks' constHalts) Xc
                  tailEqC =
                    bigConjExtT enum (countDays N (suc r)) (suc r) constHalts picks' picks
                                (extAt_above picks r kin)
                  step_tail : Eq (conjF (describeAtT enum kin r common)
                                         (bigConjCountT enum (countDays N (suc r)) (suc r) picks' constHalts))
                                 (conjF (describeAtT enum kin r common) Xc)
                  step_tail = eqCong (\ T -> conjF (describeAtT enum kin r common) T) tailEqC
              in eqTrans step_count (eqTrans step_progr step_tail)

            conjBC : Deriv (imp H (bigConjCountT enum (countDays N r) r picks' constHalts))
            conjBC = eqSubst (\ Ff -> Deriv (imp H Ff)) (eqSym unfoldEqC) conjHc

            -- S(r) at the common fuel.
            SrInst : Deriv (neg (substF zero common (BigConjFormula consts r picks')))
            SrInst = ruleInst zero common (Sr picks' bound')
            SrCommon : Deriv (neg (bigConjCountT enum (countDays N r) r picks' constHalts))
            SrCommon =
              eqSubst (\ Ff -> Deriv (neg Ff)) (substBigConj enum (countDays N r) r picks') SrInst

            impHfalse : Deriv (imp H falseF)
            impHfalse =
              compI conjBC
                    (negToImpFalse (bigConjCountT enum (countDays N r) r picks' constHalts) SrCommon)
            negH : Deriv (neg H)
            negH = mp (impFalseToNeg_imp H) impHfalse
        in mp (negConjToImpRtoNegL D1 X) negH
  in aggregateImp2 enum X M (natCode r) perProgImp
