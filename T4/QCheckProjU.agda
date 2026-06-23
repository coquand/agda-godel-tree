{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.QCheckProjU -- the projection bridge for the bundled unsized CR step,
-- the analogue of T4.QCheckProj.  Under PhiKU = (bigC qcheckU O K = O), any
-- child code c <= K satisfies  Q c := imp (wfRed c = O) (conj3 c = O) .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.QCheckProjU where

open import T4.Base

open import T4.BoundedConj     using ( bigC )
open import T4.BoundedConjProj using ( bigCLe )
open import T4.QCheckU         using ( qcheckU ; qcheckU_sound ; conj3 )
open import T4.WfRed           using ( wfRed )

open import BRA3.Church        using ( sigma ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import T4.Counting        using ( sigma_both_zero_imp )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )

------------------------------------------------------------------------

PhiKU : Formula
PhiKU = eqF (ap2 (bigC qcheckU) O (var 0)) O

qcheckProjU : (c : Term) -> Deriv (leq c (var 0)) ->
  Deriv (imp PhiKU (eqF (ap1 qcheckU c) O))
qcheckProjU c leqc =
  let inst : Deriv (imp (eqF (ap2 sigma (ap2 sub c (var 0))
                                        (ap2 (bigC qcheckU) O (var 0))) O)
                        (eqF (ap1 qcheckU c) O))
      inst = ruleInst 1 c (bigCLe qcheckU)
      conj : Deriv (imp PhiKU
               (eqF (ap2 sigma (ap2 sub c (var 0))
                               (ap2 (bigC qcheckU) O (var 0))) O))
      conj = sigma_both_zero_imp PhiKU (ap2 sub c (var 0))
               (ap2 (bigC qcheckU) O (var 0))
               (liftP PhiKU leqc) (identP PhiKU)
  in compI conj inst

QofChildU : (c : Term) -> Deriv (leq c (var 0)) ->
  Deriv (imp PhiKU (imp (eqF (ap1 wfRed c) O) (eqF (ap1 conj3 c) O)))
QofChildU c leqc = compI (qcheckProjU c leqc) (qcheckU_sound c)
