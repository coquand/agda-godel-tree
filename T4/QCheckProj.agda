{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.QCheckProj -- the projection BRIDGE for the main course-of-values step.
--
-- Under the loop invariant  PhiK = (bigC qcheck O K = O)   (K = var 0), for any
-- child code  c  with a bare bound  leq c K , the projection lemma bigCLe gives
-- qcheck c = O , and hence (via qcheck_sound)  Q c , under PhiK :
--
--   qcheckProj c : imp PhiK (qcheck c = O)
--   QofChild  c : imp PhiK (imp (wfRedSized c = O) (wfRedSized (triFSized c) = O))
--
-- The single sigma-conjunction antecedent of bigCLe is assembled from PhiK
-- (identity) + the bare leq bound, via sigma_both_zero_imp.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.QCheckProj where

open import T4.Base

open import T4.BoundedConj     using ( bigC )
open import T4.BoundedConjProj using ( bigCLe )
open import T4.QCheck          using ( qcheck ; qcheck_sound )
open import T4.WfRedSized      using ( wfRedSized )
open import T4.DerTriS         using ( triFSized )

open import BRA3.Church        using ( sigma ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import T4.Counting        using ( sigma_both_zero_imp )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )

------------------------------------------------------------------------
-- The loop invariant  PhiK = (bigC qcheck O (var 0) = O) .

PhiK : Formula
PhiK = eqF (ap2 (bigC qcheck) O (var 0)) O

------------------------------------------------------------------------
-- qcheckProj : under PhiK, every child  c <= K  satisfies  qcheck c = O .

qcheckProj : (c : Term) -> Deriv (leq c (var 0)) ->
  Deriv (imp PhiK (eqF (ap1 qcheck c) O))
qcheckProj c leqc =
  let inst : Deriv (imp (eqF (ap2 sigma (ap2 sub c (var 0))
                                        (ap2 (bigC qcheck) O (var 0))) O)
                        (eqF (ap1 qcheck c) O))
      inst = ruleInst 1 c (bigCLe qcheck)
      conj : Deriv (imp PhiK
               (eqF (ap2 sigma (ap2 sub c (var 0))
                               (ap2 (bigC qcheck) O (var 0))) O))
      conj = sigma_both_zero_imp PhiK (ap2 sub c (var 0))
               (ap2 (bigC qcheck) O (var 0))
               (liftP PhiK leqc) (identP PhiK)
  in compI conj inst

------------------------------------------------------------------------
-- QofChild : under PhiK, every child  c <= K  satisfies  Q c .

QofChild : (c : Term) -> Deriv (leq c (var 0)) ->
  Deriv (imp PhiK (imp (eqF (ap1 wfRedSized c) O)
                       (eqF (ap1 wfRedSized (ap1 triFSized c)) O)))
QofChild c leqc = compI (qcheckProj c leqc) (qcheck_sound c)
