{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepFrontEnd2N -- the TWO-FUEL number-code front end ( clos Step 1, two
-- independent fuels x0, x1 ) :  number-code mirror of  StepFrontEnd2.frontEnd2 .
--
--   frontEnd2N : (N M r) -> NatLe r N -> StagePredFN N M r -> (bound) ->
--     Deriv (imp (BigConjFormulaN N (suc r) picks)         -- K_rest @ x0 = var 0
--                (KdefBigConjNF (var 1) M r))               -- Q       @ x1 = var 1
--
-- The consequent's per-program negations live at the SECOND free fuel  x1 = var 1 ,
-- distinct from  K_rest 's  x0 = var 0 .   Per program  kin <= M , both an assumed
-- describe @ x1  and  K_rest @ x0  are lifted to the common fuel  x0 + x1 = sigma
-- (var 0)(var 1)  by  imp_runProgMonoPlusN  ( + T36 commutativity for the x1 side );
-- at that common fuel the day- r -extended conjunction contradicts  S(r)  instantiated
-- there ( ruleInst 0 common ).

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe ; le-zero ; le-refl ; le-suc-right ; ruleInst2 )
open import BRA3.Church    using ( sigma ; T36 )
open import BRA3.Contrapositive using ( identP ; compI )
open import T4.Code        using ( falseF )
open import T4.Counting    using ( negToImpFalse ; impFalseToNeg_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impCongR ; impEqTrans )
open import T4.RunProgMonoN using ( imp_runProgMonoPlusN )
open import T4.SubstNoVar   using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import T4.ParseN       using ( runProgN )
open import T4.SurpriseG2.BigConjFormula using ( conjF ; countDays )
open import T4.SurpriseG2.AndLemmas
  using ( negConjToImpRtoNegL ; liftedAndIntro ; fstAndImp ; sndAndImp )
open import T4.StagePredFN
  using ( describeAtN ; bigConjCountN ; openFuel ; BigConjFormulaN
        ; StagePredFN ; Picks ; PicksBound )
open import T4.StepFrontEndN
  using ( addO ; addO_suc_left ; countDays_step ; extPicks ; extAt_r
        ; extAt_above ; iteLe ; natEqb )

module T4.StepFrontEnd2N where

------------------------------------------------------------------------
-- The common fuel  x0 + x1  and  x1 .

common : Term
common = ap2 sigma (var zero) (var (suc zero))

constHalts : Nat -> Term
constHalts _ = common

F1 : Term
F1 = var (suc zero)

------------------------------------------------------------------------
-- The fuel-parametrised consequent ( per-program negation @ fuel F1 ).

perProgNegNF : (F1' : Term) (r : Nat) (k : Nat) -> Formula
perProgNegNF F1' r k = neg (describeAtN k r F1')

KdefBigConjNF : (F1' : Term) (M : Nat) (r : Nat) -> Formula
KdefBigConjNF F1' zero    r = perProgNegNF F1' r zero
KdefBigConjNF F1' (suc M) r = conjF (perProgNegNF F1' r (suc M)) (KdefBigConjNF F1' M r)

------------------------------------------------------------------------
-- bigConjCountN extensionality in picks ( fuel-parametrised ).

bigConjExtTN :
  (count start : Nat) (halts : Nat -> Term) (p1 p2 : Nat -> Nat) ->
  ((i : Nat) -> Eq (p1 (addO start i)) (p2 (addO start i))) ->
  Eq (bigConjCountN count start p1 halts) (bigConjCountN count start p2 halts)
bigConjExtTN zero    start halts p1 p2 agree = refl
bigConjExtTN (suc c) start halts p1 p2 agree =
  let headEq : Eq (p1 start) (p2 start)
      headEq = agree zero
      tailAgree : (i : Nat) -> Eq (p1 (addO (suc start) i)) (p2 (addO (suc start) i))
      tailAgree i =
        eqTrans (eqCong p1 (addO_suc_left start i))
                (eqTrans (agree (suc i))
                         (eqSym (eqCong p2 (addO_suc_left start i))))
      ih : Eq (bigConjCountN c (suc start) p1 halts) (bigConjCountN c (suc start) p2 halts)
      ih = bigConjExtTN c (suc start) halts p1 p2 tailAgree
  in eqTrans (eqCong (\ pr -> conjF (describeAtN pr start (halts start))
                                     (bigConjCountN c (suc start) p1 halts)) headEq)
             (eqCong (\ T -> conjF (describeAtN (p2 start) start (halts start)) T) ih)

------------------------------------------------------------------------
-- (b) Lift a whole open-fuel conjunction to the common fuel.

bigConjLiftN :
  (count start : Nat) (picks : Nat -> Nat) ->
  Deriv (imp (bigConjCountN count start picks openFuel)
             (bigConjCountN count start picks constHalts))
bigConjLiftN zero    start picks = identP (bigConjCountN zero start picks openFuel)
bigConjLiftN (suc c) start picks =
  let hd0 : Formula
      hd0 = describeAtN (picks start) start (var zero)
      tl0 : Formula
      tl0 = bigConjCountN c (suc start) picks openFuel
      X0 : Formula
      X0 = conjF hd0 tl0
      hHead : Deriv (imp X0 (describeAtN (picks start) start common))
      hHead = imp_runProgMonoPlusN X0 (natCode (picks start)) (natCode start)
                (var zero) (var (suc zero)) (fstAndImp hd0 tl0)
      hTail : Deriv (imp X0 (bigConjCountN c (suc start) picks constHalts))
      hTail = compI (sndAndImp hd0 tl0) (bigConjLiftN c (suc start) picks)
  in liftedAndIntro X0 (describeAtN (picks start) start common)
                       (bigConjCountN c (suc start) picks constHalts) hHead hTail

------------------------------------------------------------------------
-- (c) substF 0 common distributes over the open-fuel conjunction.

substDescribeN :
  (p d : Nat) ->
  Eq (substF zero common (describeAtN p d (var zero)))
     (describeAtN p d common)
substDescribeN p d =
  eqTrans
    (eqCong (\ X -> eqF (ap2 runProgN X common)
                        (ap1 s (substT zero common (natCode d))))
            (substT_NoVar zero common (natCode p) (NoVar_natCode p)))
    (eqCong (\ Y -> eqF (ap2 runProgN (natCode p) common) (ap1 s Y))
            (substT_NoVar zero common (natCode d) (NoVar_natCode d)))

substBigConjN :
  (count start : Nat) (picks : Nat -> Nat) ->
  Eq (substF zero common (bigConjCountN count start picks openFuel))
     (bigConjCountN count start picks constHalts)
substBigConjN zero    start picks = refl
substBigConjN (suc c) start picks =
  eqTrans
    (eqCong (\ Hd -> conjF Hd
              (substF zero common (bigConjCountN c (suc start) picks openFuel)))
            (substDescribeN (picks start) start))
    (eqCong (\ T -> conjF (describeAtN (picks start) start common) T)
            (substBigConjN c (suc start) picks))

------------------------------------------------------------------------
-- (d) Aggregate into  KdefBigConjNF .

aggregateImp2N :
  (Xf : Formula) (M' : Nat) (r : Nat) ->
  ((k : Nat) -> NatLe k M' -> Deriv (imp Xf (perProgNegNF F1 r k))) ->
  Deriv (imp Xf (KdefBigConjNF F1 M' r))
aggregateImp2N Xf zero      r negs = negs zero (le-zero zero)
aggregateImp2N Xf (suc M'') r negs =
  liftedAndIntro Xf (perProgNegNF F1 r (suc M'')) (KdefBigConjNF F1 M'' r)
    (negs (suc M'') (le-refl (suc M'')))
    (aggregateImp2N Xf M'' r (\ k le -> negs k (le-suc-right le)))

------------------------------------------------------------------------
-- The two-fuel front end.

module _ (picks : Nat -> Nat) where

  frontEnd2N :
    (N M r : Nat) -> NatLe r N -> StagePredFN N M r ->
    (bound : PicksBound N M picks) ->
    Deriv (imp (BigConjFormulaN N (suc r) picks) (KdefBigConjNF F1 M r))
  frontEnd2N N M r rleN Sr bound =
    let X : Formula
        X = BigConjFormulaN N (suc r) picks
        Xc : Formula
        Xc = bigConjCountN (countDays N (suc r)) (suc r) picks constHalts

        sigmaComm10 : Deriv (eqF (ap2 sigma (var (suc zero)) (var zero)) common)
        sigmaComm10 = ruleInst2 zero (var (suc zero)) (suc zero) (var zero) refl T36

        perProgImp :
          (kin : Nat) -> NatLe kin M ->
          Deriv (imp X (perProgNegNF F1 r kin))
        perProgImp kin kle =
          let picks' : Nat -> Nat
              picks' = extPicks picks r kin
              bound' : PicksBound N M picks'
              bound' d dleN =
                iteLe M (natEqb d r) kin (picks d) kle (bound d dleN)

              D1 : Formula
              D1 = describeAtN kin r F1
              H : Formula
              H = conjF D1 X
              hD1 : Deriv (imp H D1)
              hD1 = fstAndImp D1 X
              hX : Deriv (imp H X)
              hX = sndAndImp D1 X

              hD1plus : Deriv (imp H (eqF (ap2 runProgN (natCode kin)
                                                  (ap2 sigma (var (suc zero)) (var zero)))
                                         (ap1 s (natCode r))))
              hD1plus = imp_runProgMonoPlusN H (natCode kin) (natCode r)
                          (var (suc zero)) (var zero) hD1
              hD1c : Deriv (imp H (describeAtN kin r common))
              hD1c =
                impEqTrans {H} (ap2 runProgN (natCode kin) common)
                  (ap2 runProgN (natCode kin) (ap2 sigma (var (suc zero)) (var zero)))
                  (ap1 s (natCode r))
                  (impCongR {H} runProgN common (ap2 sigma (var (suc zero)) (var zero))
                            (natCode kin) (impLift {H} (ruleSym sigmaComm10)))
                  hD1plus

              hXc : Deriv (imp H Xc)
              hXc = compI hX (bigConjLiftN (countDays N (suc r)) (suc r) picks)

              conjHc : Deriv (imp H (conjF (describeAtN kin r common) Xc))
              conjHc = liftedAndIntro H (describeAtN kin r common) Xc hD1c hXc

              unfoldEqC :
                Eq (bigConjCountN (countDays N r) r picks' constHalts)
                   (conjF (describeAtN kin r common) Xc)
              unfoldEqC =
                let step_count :
                      Eq (bigConjCountN (countDays N r) r picks' constHalts)
                         (conjF (describeAtN (picks' r) r common)
                                (bigConjCountN (countDays N (suc r)) (suc r) picks' constHalts))
                    step_count =
                      eqCong (\ c -> bigConjCountN c r picks' constHalts)
                             (countDays_step N r rleN)
                    step_progr :
                      Eq (conjF (describeAtN (picks' r) r common)
                                (bigConjCountN (countDays N (suc r)) (suc r) picks' constHalts))
                         (conjF (describeAtN kin r common)
                                (bigConjCountN (countDays N (suc r)) (suc r) picks' constHalts))
                    step_progr =
                      eqCong (\ ix -> conjF (describeAtN ix r common)
                                (bigConjCountN (countDays N (suc r)) (suc r) picks' constHalts))
                             (extAt_r picks r kin)
                    tailEqC :
                      Eq (bigConjCountN (countDays N (suc r)) (suc r) picks' constHalts) Xc
                    tailEqC =
                      bigConjExtTN (countDays N (suc r)) (suc r) constHalts picks' picks
                                   (extAt_above picks r kin)
                    step_tail :
                      Eq (conjF (describeAtN kin r common)
                                (bigConjCountN (countDays N (suc r)) (suc r) picks' constHalts))
                         (conjF (describeAtN kin r common) Xc)
                    step_tail = eqCong (\ T -> conjF (describeAtN kin r common) T) tailEqC
                in eqTrans step_count (eqTrans step_progr step_tail)

              conjBC : Deriv (imp H (bigConjCountN (countDays N r) r picks' constHalts))
              conjBC = eqSubst (\ Ff -> Deriv (imp H Ff)) (eqSym unfoldEqC) conjHc

              SrInst : Deriv (neg (substF zero common (BigConjFormulaN N r picks')))
              SrInst = ruleInst zero common (Sr picks' bound')
              SrCommon : Deriv (neg (bigConjCountN (countDays N r) r picks' constHalts))
              SrCommon =
                eqSubst (\ Ff -> Deriv (neg Ff))
                        (substBigConjN (countDays N r) r picks') SrInst

              impHfalse : Deriv (imp H falseF)
              impHfalse =
                compI conjBC
                  (negToImpFalse (bigConjCountN (countDays N r) r picks' constHalts) SrCommon)
              negH : Deriv (neg H)
              negH = mp (impFalseToNeg_imp H) impHfalse
          in mp (negConjToImpRtoNegL D1 X) negH
    in aggregateImp2N X M r perProgImp
