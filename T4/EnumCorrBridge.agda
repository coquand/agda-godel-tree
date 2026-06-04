{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EnumCorrBridge -- the NEW-clos Step "by enum correctness" ( T4/clos line
-- 38-40 ) : collapse the big conjunction to the single incompressibility atom
-- BEFORE the encode.
--
-- =====================================================================
-- clos line 38-40 :  Deriv K(x0,..) => (K(r) > L*) .
-- =====================================================================
--
--   Deriv (imp (KdefBigConjF enum (var 1) M (natCode r))      -- ⋀_{k≤M} ¬def_{enum k}
--              (neg (eqF (ap2 (CK enum M) (natCode r) (var 1)) O)))   -- CK(r,x1) ≠ 0  =  K(r) > L*
--
-- The conjunction "no enumerated program describes day r at fuel x1" implies
-- the single CK-atom "K(r) > L*" :  each conjunct  ¬(runProg(enum k) x1 = s r)
-- forces the indicator  defInd(enum k, (r,x1)) = natEqF(runProg(enum k) x1)(s r)
-- to 0 ( T4.NatEqReflect.natEqF_complete ) ; summing ( defCount = sumRec defInd )
-- the count is 0 ; so  CK = isZero 0 = s O <> 0 .   This is the SHIPPED CK-fold
-- ( T4.CKProg.CK_eq , T4.DefInd ) , so the diagonal downstream is the SMALL
-- CK-atom, NOT the enum-embedding conjunction ( the size fix ).
--
-- CK is instantiated at  N := M  so the fold range  0..M  matches the
-- conjunction's  0..M .

module T4.EnumCorrBridge where

open import T4.Base
open import BRA3.Church   using ( isZero ; pi ; sigma ; T33 ; TisZeroZ )
open import T4.Code       using ( falseF )
open import T4.Kdef       using ( runProg )
open import BRA3.SubT.NatEq using ( natEqF )
open import T4.DefInd     using ( defInd ; defInd_eq ; defCount ; defCount_at_O ; defCount_succ )
open import T4.CKProg     using ( CK ; CK_eq )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF )
open import T4.NatEqReflect using ( natEqF_complete ; app2 )
open import T4.RunProgMono  using ( impEqTrans2 )
open import T4.SurpriseG2.AndLemmas using ( fstAndImp ; sndAndImp )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongL ; impCongR ; impEqTrans ; impRuleSym )
open import BRA3.Contrapositive using ( identP ; compI ; bComb )
open import BRA3.Logic          using ( prependEqLeft )
open import BRA3.ChurchT80      using ( succEqO_to_anything )
open import T4.Counting          using ( impFalseToNeg_imp )

module _ (enum : Fun1) (M : Nat) (r : Nat) where

  F1 : Term
  F1 = var (suc zero)

  qT : Term                          -- (r , x1)
  qT = ap2 pi (natCode r) F1

  ----------------------------------------------------------------------
  -- SECTION 1.  Each conjunct forces its indicator to 0.

  defIndZero :
    (k : Nat) ->
    Deriv (imp (perProgNegF enum F1 (natCode r) k)
               (eqF (ap2 defInd (ap1 enum (natCode k)) qT) O))
  defIndZero k =
    let p : Term
        p = ap1 enum (natCode k)
        runT : Term
        runT = ap2 runProg p F1

        -- defInd p qT = natEqF (runProg p x1) (s r) , reducing Snd qT / Fst qT.
        dEq : Deriv (eqF (ap2 defInd p qT)
                         (ap2 natEqF runT (ap1 s (natCode r))))
        dEq =
          ruleTrans (defInd_eq p qT)
            (ruleTrans
              (congL natEqF (ap1 s (ap1 Fst qT))
                     (congR runProg p (axSnd (natCode r) F1)))
              (congR natEqF runT (cong1 s (axFst (natCode r) F1))))

        ncomp : Deriv (imp (neg (eqF runT (ap1 s (natCode r))))
                           (eqF (ap2 natEqF runT (ap1 s (natCode r))) O))
        ncomp = natEqF_complete runT (ap1 s (natCode r))
    in compI ncomp
         (prependEqLeft (ap2 defInd p qT)
            (ap2 natEqF runT (ap1 s (natCode r))) O dEq)

  ----------------------------------------------------------------------
  -- SECTION 2.  The conjunction forces the whole count to 0  ( induction on M ).

  defCountZero :
    (m : Nat) ->
    Deriv (imp (KdefBigConjF enum F1 m (natCode r))
               (eqF (ap2 (defCount enum) qT (natCode m)) O))
  defCountZero zero =
    compI (defIndZero zero)
          (prependEqLeft (ap2 (defCount enum) qT O)
             (ap2 defInd (ap1 enum O) qT) O (defCount_at_O enum qT))
  defCountZero (suc m) =
    let Kf : Formula
        Kf = KdefBigConjF enum F1 (suc m) (natCode r)
        dc_m : Term
        dc_m = ap2 (defCount enum) qT (natCode m)
        di_sm : Term
        di_sm = ap2 defInd (ap1 enum (ap1 s (natCode m))) qT

        -- head conjunct ->  defInd(enum (suc m)) = O ;  tail -> defCount@m = O .
        dHead : Deriv (imp Kf (eqF di_sm O))
        dHead = compI (fstAndImp (perProgNegF enum F1 (natCode r) (suc m))
                                 (KdefBigConjF enum F1 m (natCode r)))
                      (defIndZero (suc m))
        dTail : Deriv (imp Kf (eqF dc_m O))
        dTail = compI (sndAndImp (perProgNegF enum F1 (natCode r) (suc m))
                                 (KdefBigConjF enum F1 m (natCode r)))
                      (defCountZero m)

        -- defCount@(s m) = sigma dc_m di_sm  ->  sigma O O  ->  O .
        e1 : Deriv (imp Kf (eqF (ap2 (defCount enum) qT (ap1 s (natCode m)))
                                (ap2 sigma dc_m di_sm)))
        e1 = impLift {Kf} (defCount_succ enum qT (natCode m))
        e2 : Deriv (imp Kf (eqF (ap2 sigma dc_m di_sm) (ap2 sigma O di_sm)))
        e2 = impCongL {Kf} sigma dc_m O di_sm dTail
        e3 : Deriv (imp Kf (eqF (ap2 sigma O di_sm) (ap2 sigma O O)))
        e3 = impCongR {Kf} sigma di_sm O O dHead
        e4 : Deriv (imp Kf (eqF (ap2 sigma O O) O))
        e4 = impLift {Kf} (T33 O)
    in impEqTrans {Kf} (ap2 (defCount enum) qT (ap1 s (natCode m))) (ap2 sigma dc_m di_sm) O
         e1
         (impEqTrans {Kf} (ap2 sigma dc_m di_sm) (ap2 sigma O di_sm) O
            e2
            (impEqTrans {Kf} (ap2 sigma O di_sm) (ap2 sigma O O) O e3 e4))

  ----------------------------------------------------------------------
  -- SECTION 3.  The bridge :  conjunction  ->  CK(r,x1) <> 0  ( = K(r) > L* ).

  incBridge :
    Deriv (imp (KdefBigConjF enum F1 M (natCode r))
               (neg (eqF (ap2 (CK enum M) (natCode r) F1) O)))
  incBridge =
    let Kf : Formula
        Kf = KdefBigConjF enum F1 M (natCode r)
        ckT : Term
        ckT = ap2 (CK enum M) (natCode r) F1
        dcM : Term
        dcM = ap2 (defCount enum) qT (natCode M)

        -- CK(r,x1) = isZero (defCount @ M) = isZero O = s O   ( under  Kf ).
        ckSO : Deriv (imp Kf (eqF ckT (ap1 s O)))
        ckSO =
          impEqTrans {Kf} ckT (ap1 isZero dcM) (ap1 s O)
            (impLift {Kf} (CK_eq enum M (natCode r) F1))
            (impEqTrans {Kf} (ap1 isZero dcM) (ap1 isZero O) (ap1 s O)
               (impCong1 {Kf} isZero dcM O (defCountZero M))
               (impLift {Kf} TisZeroZ))

        -- under  (Kf , CK = O) :  s O = O  ->  falseF .
        f1 : Deriv (imp Kf (imp (eqF ckT O) (eqF (ap1 s O) ckT)))
        f1 = bComb (impLift {Kf} (axK (eqF (ap1 s O) ckT) (eqF ckT O)))
                   (impRuleSym ckSO)
        f2 : Deriv (imp Kf (imp (eqF ckT O) (eqF ckT O)))
        f2 = impLift {Kf} (identP (eqF ckT O))
        sOeqO : Deriv (imp Kf (imp (eqF ckT O) (eqF (ap1 s O) O)))
        sOeqO = impEqTrans2 {Kf} {eqF ckT O} (ap1 s O) ckT O f1 f2
        toFalse : Deriv (imp Kf (imp (eqF ckT O) falseF))
        toFalse = app2 (impLift {Kf} (impLift {eqF ckT O} (succEqO_to_anything O falseF))) sOeqO
    in compI toFalse (impFalseToNeg_imp (eqF ckT O))
