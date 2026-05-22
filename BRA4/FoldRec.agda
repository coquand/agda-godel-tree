{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.FoldRec -- a modular structural-fold recursor for BRA4, built by
-- FACTORING BRA4's own course-of-values machinery (BRA4.CoVSpec +
-- BRA4.Stability + BRA4.CoVSpecFst/Spec).  Phase A0 of
-- KRIVINE-BERRY-PLAN.md.
--
-- Goal: a clean fold-with-closures API on the BRA4 bare-Pair + explicit-
-- tag encoding (the SAME encoding thmT reads), imitating the SHAPE of
-- BRA3.TreeRecAPI (treeRec / treeRec_at_O / treeRec_at_node) WITHOUT
-- importing its foreign  pi_safe  encoding.  The single ruleIndNat is
-- the parametric stability already proved (parametrically in base/step)
-- in BRA4.Stability / CoVSpecFst / CoVSpecSpec; FoldRec assembles those
-- into the node closure -- it adds no new induction.
--
-- API (this file):
--   fold         : Fun1 -> Fun2 -> Fun1            -- spec fixed to O
--   fold_unfold  : ap1 (fold g h) t = readOff_spec (cov_spec g h O t)
--   fold_at_O    : Deriv (eqF (ap1 (fold g h) O) (ap1 g O))
--   fold_node_unfold :  at a node  pi (s A) b  (= s P_outer),
--       ap1 (fold g h) (pi (s A) b)
--         = ap2 h P_outer (ap1 Snd (cov_spec g h O P_outer))
--     i.e. the step  h  fires on  (P_outer, inner-bundle) .
--   lookup_eq_fold :  under  leq ct K , the table lookup of position ct
--     equals  ap1 (fold g h) ct  -- the recursive-call recovery bridge.
--
-- ----------------------------------------------------------------------
-- DESIGN NOTE (corrects KRIVINE-BERRY-PLAN.md Phase A0 / the memory note).
--
-- The plan proposed a BINARY Cantor-tree fold whose node closure recurses
-- on BOTH Cantor children  a = Fst K  and  b = Snd K  of a node  K =
-- Pair a b , claimed unconditional by "Cantor monotonicity  a, b < K".
-- That is FALSE for the first projection:  Cantor  Fst  is not a strict
-- (nor even non-strict) decrease.  Concretely  code (var 0) =
-- pi (natCode tag_var) (natCode 0) = pi 1 0 = 1 , and  Fst 1 = 1 , so the
-- first child equals the node.  A fold recursing on  Fst  is therefore
-- non-well-founded.  Only the SECOND projection strictly decreases for
-- K > 0  (since  pi a b = b  iff  a = b = 0  iff  K = 0).
--
-- The correct, provable recursor (matching the shipped  sbt , which only
-- ever recurses on right-nested sub-positions) is course-of-values: the
-- step  h  receives the node and the FULL history table, and looks up the
-- fold-value at whatever sub-positions it can prove are  <= K  (non-strict
-- leq is what  stabilityP_sbt_at  needs).  So instead of one uniform
-- fold_at_node we expose:
--   * fold_node_unfold -- the step fires on (P_outer, inner-bundle);
--   * lookup_eq_fold   -- generic table-lookup -> recursive-call bridge.
-- Each Berry functor (Len/bin2nat/counting) supplies its own step body and
-- discharges the per-sub-position  leq  with the  LeqMono  chains, exactly
-- as  sbt_at_ap2  bounds  ca, cb .  No further  ruleIndNat : the single
-- induction lives once in  BRA4.Stability.stabilityP_sbt_v012  (already
-- parametric in base/step), which both bridges reuse.

module BRA4.FoldRec where

open import BRA4.Base
open import BRA4.CoVSpec
  using ( cov_spec ; cov_spec_base ; readOff_spec ; readOff_spec_eq
        ; state_step_spec )
open import BRA4.CoVSpecUniv
  using ( cov_spec_step_univ ; readOff_state_step_univ ; HistP_sbt )
open import BRA4.CoVSpecFst   using ( fst_cov_spec_eq )
open import BRA4.Stability    using ( HPsbt ; stabilityP_sbt_at )
open import BRA4.PiPositivity using ( pi_succ_outer ; pi_at_succ )

open import BRA3.Church     using ( pi ; sub )
open import BRA3.ChurchT117 using ( Fst )
open import BRA3.ChurchT116 using ( Snd )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.PairAlgebra using ( Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; iter_base_univ )

------------------------------------------------------------------------
-- Base case of recursor-correctness: read-off at fuel O.
--
--   cov_spec g h spec O   = pi O (pi spec (pi (g spec) O))     [cov_spec_base]
--   readOff_spec state    = Fst (Snd (Snd state))              [readOff_spec_eq]
--   Fst (Snd (Snd (pi O (pi spec (pi (g spec) O)))))
--     = Fst (Snd (pi spec (pi (g spec) O)))                    [axSnd]
--     = Fst (pi (g spec) O)                                    [axSnd]
--     = g spec                                                 [axFst]

fold_readoff_at_O :
  (g : Fun1) (h : Fun2) (spec : Term) ->
  Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec g h) spec O)) (ap1 g spec))
fold_readoff_at_O g h spec =
  let
    state0 : Term
    state0 = ap2 (cov_spec g h) spec O

    -- readOff_spec state0 = Fst (Snd (Snd state0)).
    e1 :
      Deriv (eqF (ap1 readOff_spec state0)
                  (ap1 Fst (ap1 Snd (ap1 Snd state0))))
    e1 = readOff_spec_eq state0

    -- state0 = pi O (pi spec (pi (g spec) O)).
    base :
      Deriv (eqF state0
                  (ap2 pi O (ap2 pi spec (ap2 pi (ap1 g spec) O))))
    base = cov_spec_base g h spec

    -- Snd state0 = pi spec (pi (g spec) O).
    snd0 :
      Deriv (eqF (ap1 Snd state0)
                  (ap2 pi spec (ap2 pi (ap1 g spec) O)))
    snd0 =
      ruleTrans (cong1 Snd base)
                (axSnd O (ap2 pi spec (ap2 pi (ap1 g spec) O)))

    -- Snd (Snd state0) = pi (g spec) O.
    sndSnd0 :
      Deriv (eqF (ap1 Snd (ap1 Snd state0))
                  (ap2 pi (ap1 g spec) O))
    sndSnd0 =
      ruleTrans (cong1 Snd snd0)
                (axSnd spec (ap2 pi (ap1 g spec) O))

    -- Fst (Snd (Snd state0)) = g spec.
    fstSndSnd0 :
      Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd state0)))
                  (ap1 g spec))
    fstSndSnd0 =
      ruleTrans (cong1 Fst sndSnd0)
                (axFst (ap1 g spec) O)
  in ruleTrans e1 fstSndSnd0

------------------------------------------------------------------------
-- fold : Fun1 -> Fun2 -> Fun1 -- the recursor, with spec fixed to O.
--
--   ap1 (fold g h) t  =  readOff_spec (cov_spec g h O t)
--
-- Built as  C (Post readOff_spec (cov_spec g h)) o u :  applied to t this
-- is  (Post readOff_spec (cov_spec g h)) (o t) (u t) = readOff_spec
-- (cov_spec g h O t) .

fold : Fun1 -> Fun2 -> Fun1
fold g h = C (Post readOff_spec (cov_spec g h)) o u

fold_unfold :
  (g : Fun1) (h : Fun2) (t : Term) ->
  Deriv (eqF (ap1 (fold g h) t)
              (ap1 readOff_spec (ap2 (cov_spec g h) O t)))
fold_unfold g h t =
  let P : Fun2
      P = Post readOff_spec (cov_spec g h)

      e1 :
        Deriv (eqF (ap1 (fold g h) t)
                    (ap2 P (ap1 o t) (ap1 u t)))
      e1 = ax_C P o u t

      ot : Deriv (eqF (ap1 o t) O)
      ot = ax_o t

      ut : Deriv (eqF (ap1 u t) t)
      ut = ax_u t

      e2 :
        Deriv (eqF (ap2 P (ap1 o t) (ap1 u t)) (ap2 P O (ap1 u t)))
      e2 = congL P (ap1 u t) ot

      e3 :
        Deriv (eqF (ap2 P O (ap1 u t)) (ap2 P O t))
      e3 = congR P O ut

      e4 :
        Deriv (eqF (ap2 P O t) (ap1 readOff_spec (ap2 (cov_spec g h) O t)))
      e4 = axPost readOff_spec (cov_spec g h) O t
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))

------------------------------------------------------------------------
-- fold_at_O :  ap1 (fold g h) O = ap1 g O .
--
-- Corollary of fold_unfold (at t = O) + fold_readoff_at_O (at spec = O).

fold_at_O :
  (g : Fun1) (h : Fun2) ->
  Deriv (eqF (ap1 (fold g h) O) (ap1 g O))
fold_at_O g h =
  ruleTrans (fold_unfold g h O) (fold_readoff_at_O g h O)

------------------------------------------------------------------------
-- fold_node_unfold :  the step  h  fires on a node.
--
-- For a node  pi (s A) b  (every BRA4 code node is  pi (natCode tag) rest
-- with  tag >= 1 , hence of this  pi (s _) _  shape), with predecessor
--   P_outer = pi_succ_outer A b   (so  pi (s A) b = s P_outer  by pi_at_succ):
--
--   ap1 (fold g h) (pi (s A) b)
--     =  ap2 h P_outer (ap1 Snd (cov_spec g h O P_outer))
--
-- i.e. the recursion at the node reduces to one application of the step
--  h  to the prior counter  P_outer  and the prior inner bundle
--  Snd prev = pi O table .  No  Closed  premise, universal in A, b.

fold_node_unfold :
  (g : Fun1) (h : Fun2) (A b : Term) ->
  Deriv (eqF (ap1 (fold g h) (ap2 pi (ap1 s A) b))
              (ap2 h (pi_succ_outer A b)
                     (ap1 Snd (ap2 (cov_spec g h) O (pi_succ_outer A b)))))
fold_node_unfold g h A b =
  let input : Term
      input = ap2 pi (ap1 s A) b

      P_outer : Term
      P_outer = pi_succ_outer A b

      prev : Term
      prev = ap2 (cov_spec g h) O P_outer

      -- Step 1: fold_unfold.
      step1 :
        Deriv (eqF (ap1 (fold g h) input)
                    (ap1 readOff_spec (ap2 (cov_spec g h) O input)))
      step1 = fold_unfold g h input

      -- Step 2: input = s P_outer ; fire cov_spec_step_univ.
      input_eq_sP :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP = pi_at_succ A b

      cov_lift :
        Deriv (eqF (ap2 (cov_spec g h) O input)
                    (ap2 (cov_spec g h) O (ap1 s P_outer)))
      cov_lift = congR (cov_spec g h) O input_eq_sP

      cov_step :
        Deriv (eqF (ap2 (cov_spec g h) O (ap1 s P_outer))
                    (ap1 (state_step_spec h) prev))
      cov_step = cov_spec_step_univ g h O P_outer

      sbtState_eq :
        Deriv (eqF (ap2 (cov_spec g h) O input)
                    (ap1 (state_step_spec h) prev))
      sbtState_eq = ruleTrans cov_lift cov_step

      -- Step 3: readOff_state_step_univ.
      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec g h) O input))
                    (ap1 readOff_spec (ap1 (state_step_spec h) prev)))
      readOff_lift = cong1 readOff_spec sbtState_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec h) prev))
                    (ap2 h (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ h prev

      -- Step 4: Fst prev = P_outer.
      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq g h O P_outer

      stepFun_lift :
        Deriv (eqF (ap2 h (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 h P_outer (ap1 Snd prev)))
      stepFun_lift = congL h (ap1 Snd prev) Fst_prev_eq
  in ruleTrans step1
       (ruleTrans readOff_lift
         (ruleTrans readOff_eval stepFun_lift))

------------------------------------------------------------------------
-- lookup_eq_readoff_under_leq :  the table-lookup -> readoff bridge.
--
-- Parametric analog of  BRA4.SbtAtAp.HP_sbt_eq_sbt_under_leq , stopping at
--  readOff_spec  rather than tying to  sbt .  Under  leq ct K , the
-- HPsbt-lookup of position  ct  in the  K-table equals the readoff at
-- fuel  ct :
--
--   HPsbt g h spec ct K  =  readOff_spec (cov_spec g h spec ct) .
--
-- Reuses  stabilityP_sbt_at  (the single ruleIndNat, parametric in g,h),
--  sub_self ,  iter_base_univ ,  readOff_spec_eq .  No new induction.

lookup_eq_readoff_under_leq :
  (g : Fun1) (h : Fun2) (spec ct K : Term) ->
  Deriv (leq ct K) ->
  Deriv (eqF (HPsbt g h spec ct K)
              (ap1 readOff_spec (ap2 (cov_spec g h) spec ct)))
lookup_eq_readoff_under_leq g h spec ct K leq_ct_K =
  let -- Step A: stability collapses the K-table lookup to the ct-table.
      stab :
        Deriv (eqF (HPsbt g h spec ct K) (HPsbt g h spec ct ct))
      stab = mp (stabilityP_sbt_at g h spec ct K) leq_ct_K

      -- Step B: HPsbt ... ct ct = Fst (HistP_sbt g h spec ct).
      subCT_O : Deriv (eqF (ap2 sub ct ct) O)
      subCT_O = sub_self ct

      iter_arg :
        Deriv (eqF (ap2 (iter Snd) (HistP_sbt g h spec ct) (ap2 sub ct ct))
                    (ap2 (iter Snd) (HistP_sbt g h spec ct) O))
      iter_arg = congR (iter Snd) (HistP_sbt g h spec ct) subCT_O

      iter_base :
        Deriv (eqF (ap2 (iter Snd) (HistP_sbt g h spec ct) O)
                    (HistP_sbt g h spec ct))
      iter_base = iter_base_univ Snd (HistP_sbt g h spec ct)

      iter_full :
        Deriv (eqF (ap2 (iter Snd) (HistP_sbt g h spec ct) (ap2 sub ct ct))
                    (HistP_sbt g h spec ct))
      iter_full = ruleTrans iter_arg iter_base

      HP_at_ct :
        Deriv (eqF (HPsbt g h spec ct ct)
                    (ap1 Fst (HistP_sbt g h spec ct)))
      HP_at_ct = cong1 Fst iter_full

      -- Step C: Fst (HistP_sbt g h spec ct) = readOff_spec (cov_spec g h spec ct).
      readOff_eq :
        Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec g h) spec ct))
                    (ap1 Fst (HistP_sbt g h spec ct)))
      readOff_eq = readOff_spec_eq (ap2 (cov_spec g h) spec ct)

      readOff_eq_sym :
        Deriv (eqF (ap1 Fst (HistP_sbt g h spec ct))
                    (ap1 readOff_spec (ap2 (cov_spec g h) spec ct)))
      readOff_eq_sym = ruleSym readOff_eq
  in ruleTrans stab (ruleTrans HP_at_ct readOff_eq_sym)

------------------------------------------------------------------------
-- lookup_eq_fold :  the recursive-call recovery, in fold form.
--
-- At  spec = O ,  readOff_spec (cov_spec g h O ct) = ap1 (fold g h) ct
-- (fold_unfold reversed), so under  leq ct K  the table lookup IS the
-- recursive fold value:
--
--   HPsbt g h O ct K  =  ap1 (fold g h) ct .
--
-- This is the workhorse each Berry functor uses to turn an internal
-- table lookup at a sub-position  ct  (proved  leq ct K  via LeqMono)
-- into the recursive call  fold g h ct .

lookup_eq_fold :
  (g : Fun1) (h : Fun2) (ct K : Term) ->
  Deriv (leq ct K) ->
  Deriv (eqF (HPsbt g h O ct K) (ap1 (fold g h) ct))
lookup_eq_fold g h ct K leq_ct_K =
  ruleTrans (lookup_eq_readoff_under_leq g h O ct K leq_ct_K)
            (ruleSym (fold_unfold g h ct))

------------------------------------------------------------------------
-- Generic step-body combinators.
--
-- A step body sees the packaged input  pi K_term inner , where
--  inner = pi spec table  (spec = O for fold).  These accessors and their
-- unfold lemmas at a packaged input  pi A Y  let each fold instance read
-- the counter / node / table and look up table values.  Same shapes as
-- BRA4.SbT's get_* / lookupAt (reproduced here, public, so the Berry
-- functors do not depend on the sbt module).

get_K : Fun1
get_K = Fst

get_inner : Fun1
get_inner = Snd

get_table : Fun1                                  -- Snd (Snd input) = table
get_table = compose1U Snd get_inner

get_newK : Fun1                                   -- s K_term = the node code
get_newK = compose1U s get_K

-- lookupAt idx : look up the table value at position (K_term - idx),
--   = Fst (iter Snd table (sub K_term (idx input))) .

lookupAt : Fun1 -> Fun1
lookupAt idx_F1 =
  compose1U Fst (C (iter Snd) get_table (C sub get_K idx_F1))

------------------------------------------------------------------------
-- Accessor unfold lemmas at a packaged input  pi A Y .

get_K_at_pi :
  (A Y : Term) -> Deriv (eqF (ap1 get_K (ap2 pi A Y)) A)
get_K_at_pi A Y = axFst A Y

get_inner_at_pi :
  (A Y : Term) -> Deriv (eqF (ap1 get_inner (ap2 pi A Y)) Y)
get_inner_at_pi A Y = axSnd A Y

get_newK_at_pi :
  (A Y : Term) -> Deriv (eqF (ap1 get_newK (ap2 pi A Y)) (ap1 s A))
get_newK_at_pi A Y =
  ruleTrans (compose1U_eq s get_K (ap2 pi A Y))
            (cong1 s (get_K_at_pi A Y))

get_table_at_pi :
  (A Y : Term) -> Deriv (eqF (ap1 get_table (ap2 pi A Y)) (ap1 Snd Y))
get_table_at_pi A Y =
  ruleTrans (compose1U_eq Snd get_inner (ap2 pi A Y))
            (cong1 Snd (get_inner_at_pi A Y))

lookupAt_unfold :
  (idx_F1 : Fun1) (input : Term) ->
  Deriv (eqF (ap1 (lookupAt idx_F1) input)
              (ap1 Fst (ap2 (iter Snd) (ap1 get_table input)
                        (ap2 sub (ap1 get_K input) (ap1 idx_F1 input)))))
lookupAt_unfold idx_F1 input =
  let s1 :
        Deriv (eqF (ap1 (lookupAt idx_F1) input)
                    (ap1 Fst (ap1 (C (iter Snd) get_table (C sub get_K idx_F1)) input)))
      s1 = compose1U_eq Fst (C (iter Snd) get_table (C sub get_K idx_F1)) input

      s2 :
        Deriv (eqF (ap1 (C (iter Snd) get_table (C sub get_K idx_F1)) input)
                    (ap2 (iter Snd) (ap1 get_table input) (ap1 (C sub get_K idx_F1) input)))
      s2 = ax_C (iter Snd) get_table (C sub get_K idx_F1) input

      s3 :
        Deriv (eqF (ap1 (C sub get_K idx_F1) input)
                    (ap2 sub (ap1 get_K input) (ap1 idx_F1 input)))
      s3 = ax_C sub get_K idx_F1 input

      s23 :
        Deriv (eqF (ap1 (C (iter Snd) get_table (C sub get_K idx_F1)) input)
                    (ap2 (iter Snd) (ap1 get_table input)
                          (ap2 sub (ap1 get_K input) (ap1 idx_F1 input))))
      s23 = ruleTrans s2 (congR (iter Snd) (ap1 get_table input) s3)
  in ruleTrans s1 (cong1 Fst s23)
