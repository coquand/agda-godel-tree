{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.OpaqueLookup -- BRICK 3 of the opaque local diamond: CHILD-RECOVERY.
--
-- The structure-carrying recursive-call recovery (T4.ParsObj, module NP,
-- np_lookup_gen) turns an internal table lookup at a sub-position into the
-- recursive fold value:
--
--   np_lookup_gen idx ct (idx_eq : idx input_pkg = ct)(leq ct P_outer)
--     : lookupAt idx input_pkg = fold g (Post stepBody pi) ct .
--
-- Crucially its PROOF never uses the built node form  pi_succ_outer A b  --
-- it is GENERIC in  P_outer , using only  get_K_at_pi / get_table_at_pi /
-- lookupAt_unfold / lookup_eq_fold .  So it lifts verbatim to an OPAQUE code:
-- after T4.TriFUnfold exposes the package  pi (pred d) (Snd (cov_spec …)) ,
-- a child code  ct  read out by  idx  and proved  leq ct (pred d)  (by
-- T4.DescSnd.descSnd, the value-bound discharge) has its recursive fold value
-- recovered -- NO surjective pairing, the descent is exactly "sub-proof =
-- sub-code < code".
--
-- This is the generic engine; the opaque triF/isCert/devF preservation
-- (brick 4) instantiates it with the right base  g , step body, child index
-- idx, and  descSnd  bound per constructor case.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.OpaqueLookup where

open import T4.Base
open import T4.FoldRec
open import T4.CoVSpecUniv using ( HistP_sbt )
open import T4.Stability   using ( HPsbt )
open import T4.CoVSpec     using ( cov_spec )

open import BRA3.Church         using ( pi ; sub )
open import BRA3.ChurchLeq      using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra    using ( Post )

------------------------------------------------------------------------
-- Generic course-of-values child recovery at an opaque recovery package
--   pkg = pi P_outer (Snd (cov_spec g (Post stepBody pi) O P_outer)) .
-- (Verbatim T4.ParsObj.NP.np_lookup_gen, abstracted over P_outer / stepBody.)

lookup_op :
  (g stepBody idx : Fun1) (P_outer ct : Term) ->
  Deriv (eqF (ap1 idx
               (ap2 pi P_outer
                 (ap1 Snd (ap2 (cov_spec g (Post stepBody pi)) O P_outer))))
             ct) ->
  Deriv (leq ct P_outer) ->
  Deriv (eqF (ap1 (lookupAt idx)
               (ap2 pi P_outer
                 (ap1 Snd (ap2 (cov_spec g (Post stepBody pi)) O P_outer))))
             (ap1 (fold g (Post stepBody pi)) ct))
lookup_op g stepBody idx P_outer ct idx_eq leq_ct =
  let h : Fun2
      h = Post stepBody pi
      prevS : Term
      prevS = ap1 Snd (ap2 (cov_spec g h) O P_outer)
      input_pkg : Term
      input_pkg = ap2 pi P_outer prevS
      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer prevS
      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg) (HistP_sbt g h O P_outer))
      get_table_value = get_table_at_pi P_outer prevS
      u1 : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                      (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)))))
      u1 = lookupAt_unfold idx input_pkg
      sub_eq : Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                          (ap2 sub P_outer ct))
      sub_eq = ruleTrans (congL sub (ap1 idx input_pkg) get_K_value)
                         (congR sub P_outer idx_eq)
      iter_eq : Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                            (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)))
                            (ap2 (iter Snd) (HistP_sbt g h O P_outer)
                            (ap2 sub P_outer ct)))
      iter_eq =
        ruleTrans (congL (iter Snd)
                    (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                    get_table_value)
                  (congR (iter Snd) (HistP_sbt g h O P_outer) sub_eq)
      lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                (HPsbt g h O ct P_outer))
      lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
      HP_to_fold : Deriv (eqF (HPsbt g h O ct P_outer)
                              (ap1 (fold g h) ct))
      HP_to_fold = lookup_eq_fold g h ct P_outer leq_ct
  in ruleTrans lookup_to_HP HP_to_fold
