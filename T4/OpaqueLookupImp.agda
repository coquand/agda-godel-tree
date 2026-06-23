{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.OpaqueLookupImp -- the IMP-FORM (Carneiro) child recovery: lookup_op
-- with its  idx_eq  and  leq  hypotheses carried as antecedents under a single
-- formula  phi .  Needed because the object tag dispatch supplies these
-- hypotheses as antecedents (no deduction theorem), in particular for the
-- Ad_Su critical pair whose left child  pL  is OPAQUE.
--
-- Strategy.  lookup_op uses leq ONLY via lookup_eq_fold (-> ... ->
-- lookup_eq_readoff_under_leq, whose single  leq  use is
-- mp (stabilityP_sbt_at ..) leq , and stabilityP_sbt_at is already imp-form),
-- and  idx_eq  ONLY via  congR sub P_outer idx_eq .  Everything else is bare,
-- impLift'd.  No induction is lifted.  The tag-independent "rest" of the
-- readoff bridge is recovered by calling the bare lemma at K := ct .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.OpaqueLookupImp where

open import T4.Base

open import T4.FoldRec
  using ( fold ; lookupAt ; lookupAt_unfold
        ; get_K ; get_table ; get_K_at_pi ; get_table_at_pi
        ; lookup_eq_readoff_under_leq ; fold_unfold )
open import T4.Stability using ( HPsbt ; stabilityP_sbt_at )
open import T4.CoVSpecUniv using ( HistP_sbt )
open import T4.CoVSpec using ( cov_spec ; readOff_spec )

open import BRA3.Church         using ( pi ; sub )
open import BRA3.ChurchLeq      using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra    using ( Post )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.Contrapositive using ( compI )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongL ; impCongR ; impEqTrans )

------------------------------------------------------------------------
-- The readoff bridge, imp-form over phi.  The single leq use composes phi's
-- bound with the already imp-form stabilityP_sbt_at ; the rest is recovered
-- bare from the bare lemma at K := ct (where leq ct ct = sub_self).

lookup_eq_readoff_under_leq_imp :
  (phi : Formula) (g : Fun1) (h : Fun2) (spec ct K : Term) ->
  Deriv (imp phi (leq ct K)) ->
  Deriv (imp phi (eqF (HPsbt g h spec ct K)
                      (ap1 readOff_spec (ap2 (cov_spec g h) spec ct))))
lookup_eq_readoff_under_leq_imp phi g h spec ct K leqImp =
  let stab_imp : Deriv (imp phi (eqF (HPsbt g h spec ct K) (HPsbt g h spec ct ct)))
      stab_imp = compI leqImp (stabilityP_sbt_at g h spec ct K)
      rest : Deriv (eqF (HPsbt g h spec ct ct)
                        (ap1 readOff_spec (ap2 (cov_spec g h) spec ct)))
      rest = lookup_eq_readoff_under_leq g h spec ct ct (sub_self ct)
  in impEqTrans (HPsbt g h spec ct K) (HPsbt g h spec ct ct)
                (ap1 readOff_spec (ap2 (cov_spec g h) spec ct))
       stab_imp (impLift rest)

------------------------------------------------------------------------
-- The fold-form recovery, imp-form over phi.

lookup_eq_fold_imp :
  (phi : Formula) (g : Fun1) (h : Fun2) (ct K : Term) ->
  Deriv (imp phi (leq ct K)) ->
  Deriv (imp phi (eqF (HPsbt g h O ct K) (ap1 (fold g h) ct)))
lookup_eq_fold_imp phi g h ct K leqImp =
  impEqTrans (HPsbt g h O ct K)
             (ap1 readOff_spec (ap2 (cov_spec g h) O ct))
             (ap1 (fold g h) ct)
    (lookup_eq_readoff_under_leq_imp phi g h O ct K leqImp)
    (impLift (ruleSym (fold_unfold g h ct)))

------------------------------------------------------------------------
-- lookup_op_imp : the full child recovery, idx_eq and leq carried under phi.
-- Faithful transcription of T4.OpaqueLookup.lookup_op .

lookup_op_imp :
  (phi : Formula) (g stepBody idx : Fun1) (P_outer ct : Term) ->
  Deriv (imp phi
          (eqF (ap1 idx
                 (ap2 pi P_outer
                   (ap1 Snd (ap2 (cov_spec g (Post stepBody pi)) O P_outer))))
               ct)) ->
  Deriv (imp phi (leq ct P_outer)) ->
  Deriv (imp phi
          (eqF (ap1 (lookupAt idx)
                 (ap2 pi P_outer
                   (ap1 Snd (ap2 (cov_spec g (Post stepBody pi)) O P_outer))))
               (ap1 (fold g (Post stepBody pi)) ct)))
lookup_op_imp phi g stepBody idx P_outer ct idx_eq leq_ct =
  let h : Fun2
      h = Post stepBody pi
      prevS : Term
      prevS = ap1 Snd (ap2 (cov_spec g h) O P_outer)
      input_pkg : Term
      input_pkg = ap2 pi P_outer prevS
      X : Term                                  -- sub (get_K ipkg) (idx ipkg)
      X = ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)
      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer prevS
      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg) (HistP_sbt g h O P_outer))
      get_table_value = get_table_at_pi P_outer prevS
      u1 : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                      (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg) X)))
      u1 = lookupAt_unfold idx input_pkg
      -- sub_eq : X = sub P_outer ct   (uses idx_eq via the second leg)
      sub_eq : Deriv (imp phi (eqF X (ap2 sub P_outer ct)))
      sub_eq =
        impEqTrans X (ap2 sub P_outer (ap1 idx input_pkg)) (ap2 sub P_outer ct)
          (impLift (congL sub (ap1 idx input_pkg) get_K_value))
          (impCongR sub (ap1 idx input_pkg) ct P_outer idx_eq)
      -- iter_eq : iter Snd (get_table ipkg) X = iter Snd (HistP..) (sub P_outer ct)
      iter_eq :
        Deriv (imp phi (eqF (ap2 (iter Snd) (ap1 get_table input_pkg) X)
                            (ap2 (iter Snd) (HistP_sbt g h O P_outer)
                              (ap2 sub P_outer ct))))
      iter_eq =
        impEqTrans (ap2 (iter Snd) (ap1 get_table input_pkg) X)
                   (ap2 (iter Snd) (HistP_sbt g h O P_outer) X)
                   (ap2 (iter Snd) (HistP_sbt g h O P_outer) (ap2 sub P_outer ct))
          (impLift (congL (iter Snd) X get_table_value))
          (impCongR (iter Snd) X (ap2 sub P_outer ct) (HistP_sbt g h O P_outer) sub_eq)
      -- lookup_to_HP : lookupAt idx ipkg = HPsbt g h O ct P_outer
      lookup_to_HP : Deriv (imp phi (eqF (ap1 (lookupAt idx) input_pkg)
                                         (HPsbt g h O ct P_outer)))
      lookup_to_HP =
        impEqTrans (ap1 (lookupAt idx) input_pkg)
                   (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg) X))
                   (HPsbt g h O ct P_outer)
          (impLift u1)
          (impCong1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg) X)
                        (ap2 (iter Snd) (HistP_sbt g h O P_outer) (ap2 sub P_outer ct))
                    iter_eq)
      HP_to_fold : Deriv (imp phi (eqF (HPsbt g h O ct P_outer)
                                       (ap1 (fold g h) ct)))
      HP_to_fold = lookup_eq_fold_imp phi g h ct P_outer leq_ct
  in impEqTrans (ap1 (lookupAt idx) input_pkg)
                (HPsbt g h O ct P_outer)
                (ap1 (fold g h) ct)
       lookup_to_HP HP_to_fold
