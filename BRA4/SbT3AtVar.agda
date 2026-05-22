{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbT3AtVar -- discharge of the SbContract3 sbt3 closures at the
-- four var-shape inputs:
--
-- spec3 = pi (pi (natCode k1) S1) (pi (pi (natCode k2) S2) (pi (natCode k3) S3))
--
--   sbt3_at_var_match_one : ap2 sbt3 spec3 (pi nck_var nck1) = S1
--   sbt3_at_var_match_two : k1/=k2 -> ap2 sbt3 spec3 (pi nck_var nck2) = S2
--   sbt3_at_var_match_three :
--     k1/=k3 -> k2/=k3 -> ap2 sbt3 spec3 (pi nck_var nck3) = S3
--   sbt3_at_var_nomatch :
--     k1/=m -> k2/=m -> k3/=m -> ap2 sbt3 spec3 (pi nck_var nckm)
--       = pi nck_var nckm
--
-- Three-level nested condFork in var_branch.
--
-- Shared skeleton with BRA4.SbtAtVar (single-var):
--   1.  sbt3_unfold      :  sbt3 spec t = readOff_spec (sbt3State spec t)
--   2.  readOff_at_pi_natCode  :  reduce sbt3State ... t to stateMeta (cantor 1 m).
--   3.  cantor_var_succ_decomp :  cantor 1 m = suc (cantorVarPred m).
--   4.  readOff_stateMeta_succ_via_natCode :  = stepFun_sbt3 (natCode K_pred) (Snd ...).
--   5.  Unfold stepFun_sbt3 = Post stepBody_sbt3 pi.  Dispatch through
--       isVar (tag = tag_var)  +  isVarMatch1 + isVarMatch2 (nested condFork).
--   6.  Take Fst/Snd projections of the nested var_branch to obtain
--       S1 / S2 / get_newK input as appropriate.

module BRA4.SbT3AtVar where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.SbT3
open import BRA4.StabilityNatFuel
open import BRA4.SbtAtVar using ( cantorVarPred ; cantor_var_succ_decomp )

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( Closed ; closed_O ; closed_natCode ; closed_ap1 ; closed_ap2
  ; condFork ; condFork_true_nc ; condFork_false
  ; constN ; constN_eq
  ; tagOf_cantor ; bodyOf_cantor )
open import BRA3.Numerals        using ( pi_natCode )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq ; natEq_neq_gt )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; gtW ; ltW ; natEqF_at_neq ; decideNatNeq ; Not )
open import BRA3.RuleInst2       using
  ( natEq-refl ; true_neq_false )
open import BRA3.Code.Tag        using
  ( cantor )

------------------------------------------------------------------------
-- E.1  Bridge from  Eq (natEq k m) false  to  NatNeqWitness m k .

private
  natEqFalse_to_NotEq :
    (k m : Nat) -> Eq (natEq k m) false -> Not (Eq k m)
  natEqFalse_to_NotEq k m hyp eqKM =
    let trueEq : Eq (natEq k m) true
        trueEq = eqSubst (\ z -> Eq (natEq k z) true) eqKM (natEq-refl k)

        contradict : Eq true false
        contradict = eqTrans (eqSym trueEq) hyp
    in true_neq_false contradict

  natEqFalse_to_witness_flipped :
    (k m : Nat) -> Eq (natEq k m) false -> NatNeqWitness m k
  natEqFalse_to_witness_flipped k m hyp =
    let notEqKM : Not (Eq k m)
        notEqKM = natEqFalse_to_NotEq k m hyp

        notEqMK : Not (Eq m k)
        notEqMK eqMK = notEqKM (eqSym eqMK)
    in decideNatNeq m k notEqMK

------------------------------------------------------------------------
-- Section A.  Stepwise unfolding of the dispatch helpers at a packaged
-- input  pi A Y  (where A is intended to be  natCode K_pred  and Y is
-- intended to be  Snd state ).

private
  -- ap1 get_K (pi A Y) = A.
  get_K_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_K (ap2 pi A Y)) A)
  get_K_at_pi A Y = axFst A Y

  -- ap1 get_inner (pi A Y) = Y.
  get_inner_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_inner (ap2 pi A Y)) Y)
  get_inner_at_pi A Y = axSnd A Y

  -- ap1 get_newK (pi A Y) = ap1 s A.
  get_newK_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_newK (ap2 pi A Y)) (ap1 s A))
  get_newK_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_newK (ap2 pi A Y))
                      (ap1 s (ap1 get_K (ap2 pi A Y))))
        s1 = compose1U_eq s get_K (ap2 pi A Y)
    in ruleTrans s1 (cong1 s (get_K_at_pi A Y))

  -- ap1 get_tag (pi A Y) = ap1 Fst (ap1 s A).
  get_tag_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (ap1 Fst (ap1 s A)))
  get_tag_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_tag (ap2 pi A Y))
                      (ap1 Fst (ap1 get_newK (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_newK_at_pi A Y))

  -- ap1 get_body (pi A Y) = ap1 Snd (ap1 s A).
  get_body_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_body (ap2 pi A Y)) (ap1 Snd (ap1 s A)))
  get_body_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_body (ap2 pi A Y))
                      (ap1 Snd (ap1 get_newK (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_newK_at_pi A Y))

  -- ap1 get_spec (pi A Y) = ap1 Fst Y.
  get_spec_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec (ap2 pi A Y)) (ap1 Fst Y))
  get_spec_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec (ap2 pi A Y))
                      (ap1 Fst (ap1 get_inner (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_inner (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_inner_at_pi A Y))

  -- ap1 get_spec_left (pi A Y) = ap1 Fst (ap1 Fst Y).
  get_spec_left_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec_left (ap2 pi A Y)) (ap1 Fst (ap1 Fst Y)))
  get_spec_left_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec_left (ap2 pi A Y))
                      (ap1 Fst (ap1 get_spec (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_spec (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_spec_at_pi A Y))

  -- ap1 get_spec_right (pi A Y) = ap1 Snd (ap1 Fst Y).
  get_spec_right_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec_right (ap2 pi A Y)) (ap1 Snd (ap1 Fst Y)))
  get_spec_right_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec_right (ap2 pi A Y))
                      (ap1 Snd (ap1 get_spec (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_spec (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_spec_at_pi A Y))

  -- ap1 get_spec1Fst (pi A Y) = ap1 Fst (ap1 Fst (ap1 Fst Y)).
  get_spec1Fst_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec1Fst (ap2 pi A Y)) (ap1 Fst (ap1 Fst (ap1 Fst Y))))
  get_spec1Fst_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec1Fst (ap2 pi A Y))
                      (ap1 Fst (ap1 get_spec_left (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_spec_left (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_spec_left_at_pi A Y))

  -- ap1 get_spec1Snd (pi A Y) = ap1 Snd (ap1 Fst (ap1 Fst Y)).
  get_spec1Snd_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec1Snd (ap2 pi A Y)) (ap1 Snd (ap1 Fst (ap1 Fst Y))))
  get_spec1Snd_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec1Snd (ap2 pi A Y))
                      (ap1 Snd (ap1 get_spec_left (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_spec_left (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_spec_left_at_pi A Y))

  -- ap1 get_spec_mid_left (pi A Y) = ap1 Fst (ap1 Snd (ap1 Fst Y)).
  get_spec_mid_left_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec_mid_left (ap2 pi A Y))
                (ap1 Fst (ap1 Snd (ap1 Fst Y))))
  get_spec_mid_left_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec_mid_left (ap2 pi A Y))
                      (ap1 Fst (ap1 get_spec_right (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_spec_right (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_spec_right_at_pi A Y))

  -- ap1 get_spec_mid_right (pi A Y) = ap1 Snd (ap1 Snd (ap1 Fst Y)).
  get_spec_mid_right_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec_mid_right (ap2 pi A Y))
                (ap1 Snd (ap1 Snd (ap1 Fst Y))))
  get_spec_mid_right_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec_mid_right (ap2 pi A Y))
                      (ap1 Snd (ap1 get_spec_right (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_spec_right (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_spec_right_at_pi A Y))

  -- ap1 get_spec2Fst (pi A Y) = ap1 Fst (ap1 Fst (ap1 Snd (ap1 Fst Y))).
  get_spec2Fst_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec2Fst (ap2 pi A Y))
                (ap1 Fst (ap1 Fst (ap1 Snd (ap1 Fst Y)))))
  get_spec2Fst_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec2Fst (ap2 pi A Y))
                      (ap1 Fst (ap1 get_spec_mid_left (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_spec_mid_left (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_spec_mid_left_at_pi A Y))

  -- ap1 get_spec2Snd (pi A Y) = ap1 Snd (ap1 Fst (ap1 Snd (ap1 Fst Y))).
  get_spec2Snd_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec2Snd (ap2 pi A Y))
                (ap1 Snd (ap1 Fst (ap1 Snd (ap1 Fst Y)))))
  get_spec2Snd_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec2Snd (ap2 pi A Y))
                      (ap1 Snd (ap1 get_spec_mid_left (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_spec_mid_left (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_spec_mid_left_at_pi A Y))

  -- ap1 get_spec3Fst (pi A Y) = ap1 Fst (ap1 Snd (ap1 Snd (ap1 Fst Y))).
  get_spec3Fst_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec3Fst (ap2 pi A Y))
                (ap1 Fst (ap1 Snd (ap1 Snd (ap1 Fst Y)))))
  get_spec3Fst_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec3Fst (ap2 pi A Y))
                      (ap1 Fst (ap1 get_spec_mid_right (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_spec_mid_right (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_spec_mid_right_at_pi A Y))

  -- ap1 get_spec3Snd (pi A Y) = ap1 Snd (ap1 Snd (ap1 Snd (ap1 Fst Y))).
  get_spec3Snd_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec3Snd (ap2 pi A Y))
                (ap1 Snd (ap1 Snd (ap1 Snd (ap1 Fst Y)))))
  get_spec3Snd_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_spec3Snd (ap2 pi A Y))
                      (ap1 Snd (ap1 get_spec_mid_right (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_spec_mid_right (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_spec_mid_right_at_pi A Y))

------------------------------------------------------------------------
-- Section B.  Tag-dispatch helpers, identical in form to SbtAtVar's.

private
  -- ap1 stepBody_sbt3 input = condFork (C pi var_branch ap1_or_above input) (isVar input).
  stepBody_sbt3_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 stepBody_sbt3 input)
                (ap2 condFork
                  (ap1 (C pi var_branch ap1_or_above) input)
                  (ap1 isVar input)))
  stepBody_sbt3_unfold input =
    ax_C condFork (C pi var_branch ap1_or_above) isVar input

  pi_var_ap1_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
  pi_var_ap1_unfold input = ax_C pi var_branch ap1_or_above input

  -- ap1 var_branch input = condFork (C pi get_spec1Snd var_branch_match2 input) (isVarMatch1 input).
  var_branch_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 var_branch input)
                (ap2 condFork
                  (ap1 (C pi get_spec1Snd var_branch_match2) input)
                  (ap1 isVarMatch1 input)))
  var_branch_unfold input =
    ax_C condFork (C pi get_spec1Snd var_branch_match2) isVarMatch1 input

  pi_spec1Snd_match2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_spec1Snd var_branch_match2) input)
                (ap2 pi (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)))
  pi_spec1Snd_match2_unfold input = ax_C pi get_spec1Snd var_branch_match2 input

  -- ap1 var_branch_match2 input = condFork (C pi get_spec2Snd var_branch_match3 input) (isVarMatch2 input).
  var_branch_match2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 var_branch_match2 input)
                (ap2 condFork
                  (ap1 (C pi get_spec2Snd var_branch_match3) input)
                  (ap1 isVarMatch2 input)))
  var_branch_match2_unfold input =
    ax_C condFork (C pi get_spec2Snd var_branch_match3) isVarMatch2 input

  pi_spec2Snd_match3_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_spec2Snd var_branch_match3) input)
                (ap2 pi (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)))
  pi_spec2Snd_match3_unfold input = ax_C pi get_spec2Snd var_branch_match3 input

  -- ap1 var_branch_match3 input = condFork (C pi get_spec3Snd get_newK input) (isVarMatch3 input).
  var_branch_match3_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 var_branch_match3 input)
                (ap2 condFork
                  (ap1 (C pi get_spec3Snd get_newK) input)
                  (ap1 isVarMatch3 input)))
  var_branch_match3_unfold input =
    ax_C condFork (C pi get_spec3Snd get_newK) isVarMatch3 input

  pi_spec3Snd_newK_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_spec3Snd get_newK) input)
                (ap2 pi (ap1 get_spec3Snd input) (ap1 get_newK input)))
  pi_spec3Snd_newK_unfold input = ax_C pi get_spec3Snd get_newK input

  -- ap1 isVar input = ap2 natEqF (get_tag input) (natCode tag_var).
  isVar_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isVar input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_var)))
  isVar_unfold input =
    let s1 :
          Deriv (eqF (ap1 isVar input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_var) input)))
        s1 = ax_C natEqF get_tag (constN tag_var) input

        s2 :
          Deriv (eqF (ap1 (constN tag_var) input) (natCode tag_var))
        s2 = constN_eq tag_var input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  -- ap1 isVarMatch1 input = ap2 natEqF (get_body input) (get_spec1Fst input).
  isVarMatch1_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch1 input)
                (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input)))
  isVarMatch1_unfold input =
    ax_C natEqF get_body get_spec1Fst input

  -- ap1 isVarMatch2 input = ap2 natEqF (get_body input) (get_spec2Fst input).
  isVarMatch2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch2 input)
                (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input)))
  isVarMatch2_unfold input =
    ax_C natEqF get_body get_spec2Fst input

  -- ap1 isVarMatch3 input = ap2 natEqF (get_body input) (get_spec3Fst input).
  isVarMatch3_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch3 input)
                (ap2 natEqF (ap1 get_body input) (ap1 get_spec3Fst input)))
  isVarMatch3_unfold input =
    ax_C natEqF get_body get_spec3Fst input

------------------------------------------------------------------------
-- Section C.  natCode/cantor bridges (same as SbtAtVar's, reproved
-- locally since they were private there).

private
  natCode_succ_eq_cantor :
    (m : Nat) ->
    Eq (suc (cantorVarPred m)) (cantor (suc zero) m)
  natCode_succ_eq_cantor m = eqSym (cantor_var_succ_decomp m)

  natCode_bridge :
    (m : Nat) ->
    Deriv (eqF (ap1 s (natCode (cantorVarPred m)))
                (natCode (cantor (suc zero) m)))
  natCode_bridge m =
    eqSubst (\ z -> Deriv (eqF (ap1 s (natCode (cantorVarPred m)))
                                 (natCode z)))
             (natCode_succ_eq_cantor m)
             (axRefl (ap1 s (natCode (cantorVarPred m))))

  Fst_s_natCode_at_var :
    (m : Nat) ->
    Deriv (eqF (ap1 Fst (ap1 s (natCode (cantorVarPred m))))
                (natCode tag_var))
  Fst_s_natCode_at_var m =
    let bridge :
          Deriv (eqF (ap1 Fst (ap1 s (natCode (cantorVarPred m))))
                      (ap1 Fst (natCode (cantor (suc zero) m))))
        bridge = cong1 Fst (natCode_bridge m)

        tagEq :
          Deriv (eqF (ap1 Fst (natCode (cantor (suc zero) m)))
                      (natCode (suc zero)))
        tagEq = tagOf_cantor (suc zero) m
    in ruleTrans bridge tagEq

  Snd_s_natCode_at_var :
    (m : Nat) ->
    Deriv (eqF (ap1 Snd (ap1 s (natCode (cantorVarPred m))))
                (natCode m))
  Snd_s_natCode_at_var m =
    let bridge :
          Deriv (eqF (ap1 Snd (ap1 s (natCode (cantorVarPred m))))
                      (ap1 Snd (natCode (cantor (suc zero) m))))
        bridge = cong1 Snd (natCode_bridge m)

        bodyEq :
          Deriv (eqF (ap1 Snd (natCode (cantor (suc zero) m)))
                      (natCode m))
        bodyEq = bodyOf_cantor (suc zero) m
    in ruleTrans bridge bodyEq

------------------------------------------------------------------------
-- Section D.  Common get_X reductions under
--   Fst Y = spec3 = pi (pi (natCode k1) S1)
--                      (pi (pi (natCode k2) S2) (pi (natCode k3) S3)) .

private
  spec3Term : (k1 k2 k3 : Nat) (S1 S2 S3 : Term) -> Term
  spec3Term k1 k2 k3 S1 S2 S3 =
    ap2 pi (ap2 pi (natCode k1) S1)
           (ap2 pi (ap2 pi (natCode k2) S2) (ap2 pi (natCode k3) S3))

  -- Convenience: spec3 = pi pair1 mid, mid = pi pair2 pair3.
  pair1 : (k1 : Nat) (S1 : Term) -> Term
  pair1 k1 S1 = ap2 pi (natCode k1) S1

  pair2 : (k2 : Nat) (S2 : Term) -> Term
  pair2 k2 S2 = ap2 pi (natCode k2) S2

  pair3 : (k3 : Nat) (S3 : Term) -> Term
  pair3 k3 S3 = ap2 pi (natCode k3) S3

  mid : (k2 k3 : Nat) (S2 S3 : Term) -> Term
  mid k2 k3 S2 S3 = ap2 pi (pair2 k2 S2) (pair3 k3 S3)

  -- get_spec1Fst input = natCode k1, given Fst Y = spec3.
  get_spec1Fst_value :
    (A Y : Term) (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
    Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
    Deriv (eqF (ap1 get_spec1Fst (ap2 pi A Y)) (natCode k1))
  get_spec1Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq =
    let s1 :
          Deriv (eqF (ap1 get_spec1Fst (ap2 pi A Y)) (ap1 Fst (ap1 Fst (ap1 Fst Y))))
        s1 = get_spec1Fst_at_pi A Y

        s2 :
          Deriv (eqF (ap1 Fst (ap1 Fst Y))
                      (ap1 Fst (spec3Term k1 k2 k3 S1 S2 S3)))
        s2 = cong1 Fst fstY_eq

        s3 :
          Deriv (eqF (ap1 Fst (spec3Term k1 k2 k3 S1 S2 S3)) (pair1 k1 S1))
        s3 = axFst (pair1 k1 S1) (mid k2 k3 S2 S3)

        s4 :
          Deriv (eqF (ap1 Fst (pair1 k1 S1)) (natCode k1))
        s4 = axFst (natCode k1) S1
    in ruleTrans s1
         (ruleTrans (cong1 Fst s2)
           (ruleTrans (cong1 Fst s3) s4))

  get_spec1Snd_value :
    (A Y : Term) (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
    Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
    Deriv (eqF (ap1 get_spec1Snd (ap2 pi A Y)) S1)
  get_spec1Snd_value A Y k1 k2 k3 S1 S2 S3 fstY_eq =
    let s1 :
          Deriv (eqF (ap1 get_spec1Snd (ap2 pi A Y)) (ap1 Snd (ap1 Fst (ap1 Fst Y))))
        s1 = get_spec1Snd_at_pi A Y

        s2 :
          Deriv (eqF (ap1 Fst (ap1 Fst Y))
                      (ap1 Fst (spec3Term k1 k2 k3 S1 S2 S3)))
        s2 = cong1 Fst fstY_eq

        s3 :
          Deriv (eqF (ap1 Fst (spec3Term k1 k2 k3 S1 S2 S3)) (pair1 k1 S1))
        s3 = axFst (pair1 k1 S1) (mid k2 k3 S2 S3)

        s4 :
          Deriv (eqF (ap1 Snd (pair1 k1 S1)) S1)
        s4 = axSnd (natCode k1) S1
    in ruleTrans s1
         (ruleTrans (cong1 Snd s2)
           (ruleTrans (cong1 Snd s3) s4))

  -- Snd Y = mid (Fst Y = spec3 → Snd = mid).  Use this to derive
  -- Snd (Fst Y) = mid through chain.

  -- get_spec2Fst input = natCode k2.  Path: Fst (Fst (Snd (Fst Y))).
  get_spec2Fst_value :
    (A Y : Term) (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
    Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
    Deriv (eqF (ap1 get_spec2Fst (ap2 pi A Y)) (natCode k2))
  get_spec2Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq =
    let s1 :
          Deriv (eqF (ap1 get_spec2Fst (ap2 pi A Y))
                      (ap1 Fst (ap1 Fst (ap1 Snd (ap1 Fst Y)))))
        s1 = get_spec2Fst_at_pi A Y

        -- Snd (Fst Y) = Snd (spec3) = mid.
        s2 :
          Deriv (eqF (ap1 Snd (ap1 Fst Y))
                      (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)))
        s2 = cong1 Snd fstY_eq

        s3 :
          Deriv (eqF (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)) (mid k2 k3 S2 S3))
        s3 = axSnd (pair1 k1 S1) (mid k2 k3 S2 S3)

        -- Fst mid = pair2.
        s4 :
          Deriv (eqF (ap1 Fst (mid k2 k3 S2 S3)) (pair2 k2 S2))
        s4 = axFst (pair2 k2 S2) (pair3 k3 S3)

        -- Fst pair2 = natCode k2.
        s5 :
          Deriv (eqF (ap1 Fst (pair2 k2 S2)) (natCode k2))
        s5 = axFst (natCode k2) S2
    in ruleTrans s1
         (ruleTrans (cong1 Fst (cong1 Fst s2))
           (ruleTrans (cong1 Fst (cong1 Fst s3))
             (ruleTrans (cong1 Fst s4) s5)))

  get_spec2Snd_value :
    (A Y : Term) (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
    Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
    Deriv (eqF (ap1 get_spec2Snd (ap2 pi A Y)) S2)
  get_spec2Snd_value A Y k1 k2 k3 S1 S2 S3 fstY_eq =
    let s1 :
          Deriv (eqF (ap1 get_spec2Snd (ap2 pi A Y))
                      (ap1 Snd (ap1 Fst (ap1 Snd (ap1 Fst Y)))))
        s1 = get_spec2Snd_at_pi A Y

        s2 :
          Deriv (eqF (ap1 Snd (ap1 Fst Y))
                      (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)))
        s2 = cong1 Snd fstY_eq

        s3 :
          Deriv (eqF (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)) (mid k2 k3 S2 S3))
        s3 = axSnd (pair1 k1 S1) (mid k2 k3 S2 S3)

        s4 :
          Deriv (eqF (ap1 Fst (mid k2 k3 S2 S3)) (pair2 k2 S2))
        s4 = axFst (pair2 k2 S2) (pair3 k3 S3)

        s5 :
          Deriv (eqF (ap1 Snd (pair2 k2 S2)) S2)
        s5 = axSnd (natCode k2) S2
    in ruleTrans s1
         (ruleTrans (cong1 Snd (cong1 Fst s2))
           (ruleTrans (cong1 Snd (cong1 Fst s3))
             (ruleTrans (cong1 Snd s4) s5)))

  -- get_spec3Fst input = natCode k3.  Path: Fst (Snd (Snd (Fst Y))).
  get_spec3Fst_value :
    (A Y : Term) (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
    Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
    Deriv (eqF (ap1 get_spec3Fst (ap2 pi A Y)) (natCode k3))
  get_spec3Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq =
    let s1 :
          Deriv (eqF (ap1 get_spec3Fst (ap2 pi A Y))
                      (ap1 Fst (ap1 Snd (ap1 Snd (ap1 Fst Y)))))
        s1 = get_spec3Fst_at_pi A Y

        s2 :
          Deriv (eqF (ap1 Snd (ap1 Fst Y))
                      (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)))
        s2 = cong1 Snd fstY_eq

        s3 :
          Deriv (eqF (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)) (mid k2 k3 S2 S3))
        s3 = axSnd (pair1 k1 S1) (mid k2 k3 S2 S3)

        s4 :
          Deriv (eqF (ap1 Snd (mid k2 k3 S2 S3)) (pair3 k3 S3))
        s4 = axSnd (pair2 k2 S2) (pair3 k3 S3)

        s5 :
          Deriv (eqF (ap1 Fst (pair3 k3 S3)) (natCode k3))
        s5 = axFst (natCode k3) S3
    in ruleTrans s1
         (ruleTrans (cong1 Fst (cong1 Snd s2))
           (ruleTrans (cong1 Fst (cong1 Snd s3))
             (ruleTrans (cong1 Fst s4) s5)))

  get_spec3Snd_value :
    (A Y : Term) (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
    Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
    Deriv (eqF (ap1 get_spec3Snd (ap2 pi A Y)) S3)
  get_spec3Snd_value A Y k1 k2 k3 S1 S2 S3 fstY_eq =
    let s1 :
          Deriv (eqF (ap1 get_spec3Snd (ap2 pi A Y))
                      (ap1 Snd (ap1 Snd (ap1 Snd (ap1 Fst Y)))))
        s1 = get_spec3Snd_at_pi A Y

        s2 :
          Deriv (eqF (ap1 Snd (ap1 Fst Y))
                      (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)))
        s2 = cong1 Snd fstY_eq

        s3 :
          Deriv (eqF (ap1 Snd (spec3Term k1 k2 k3 S1 S2 S3)) (mid k2 k3 S2 S3))
        s3 = axSnd (pair1 k1 S1) (mid k2 k3 S2 S3)

        s4 :
          Deriv (eqF (ap1 Snd (mid k2 k3 S2 S3)) (pair3 k3 S3))
        s4 = axSnd (pair2 k2 S2) (pair3 k3 S3)

        s5 :
          Deriv (eqF (ap1 Snd (pair3 k3 S3)) S3)
        s5 = axSnd (natCode k3) S3
    in ruleTrans s1
         (ruleTrans (cong1 Snd (cong1 Snd s2))
           (ruleTrans (cong1 Snd (cong1 Snd s3))
             (ruleTrans (cong1 Snd s4) s5)))

------------------------------------------------------------------------
-- Section E.  Common dispatch steps:  stepBody -> var_branch (under isVar
-- = sO), then var_branch -> get_spec1Snd (under isVarMatch1 = sO), or
-- var_branch -> var_branch_match2 (under isVarMatch1 = O), etc.

private
  -- Step: under isVar input = sO, stepBody_sbt3 input = var_branch input.
  stepBody_to_var_branch :
    (input : Term) ->
    Deriv (eqF (ap1 isVar input) (ap1 s O)) ->
    Deriv (eqF (ap1 stepBody_sbt3 input) (ap1 var_branch input))
  stepBody_to_var_branch input isVar_sO =
    let e1 :
          Deriv (eqF (ap1 stepBody_sbt3 input)
                      (ap2 condFork
                        (ap1 (C pi var_branch ap1_or_above) input)
                        (ap1 isVar input)))
        e1 = stepBody_sbt3_unfold input

        isVar_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi var_branch ap1_or_above) input)
                       (ap1 isVar input))
                      (ap2 condFork
                       (ap1 (C pi var_branch ap1_or_above) input)
                       (ap1 s O)))
        isVar_subst =
          congR condFork (ap1 (C pi var_branch ap1_or_above) input) isVar_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi var_branch ap1_or_above) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi var_branch ap1_or_above) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi var_branch ap1_or_above) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                      (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
        pi_eq = pi_var_ap1_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
                      (ap1 var_branch input))
        Fst_pi = axFst (ap1 var_branch input) (ap1 ap1_or_above input)
    in ruleTrans e1
         (ruleTrans isVar_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  -- Step: under isVarMatch1 input = sO, var_branch input = get_spec1Snd input.
  var_branch_to_spec1Snd :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch1 input) (ap1 s O)) ->
    Deriv (eqF (ap1 var_branch input) (ap1 get_spec1Snd input))
  var_branch_to_spec1Snd input isVM1_sO =
    let e1 :
          Deriv (eqF (ap1 var_branch input)
                      (ap2 condFork
                        (ap1 (C pi get_spec1Snd var_branch_match2) input)
                        (ap1 isVarMatch1 input)))
        e1 = var_branch_unfold input

        isVM1_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec1Snd var_branch_match2) input)
                       (ap1 isVarMatch1 input))
                      (ap2 condFork
                       (ap1 (C pi get_spec1Snd var_branch_match2) input)
                       (ap1 s O)))
        isVM1_subst =
          congR condFork (ap1 (C pi get_spec1Snd var_branch_match2) input) isVM1_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec1Snd var_branch_match2) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi get_spec1Snd var_branch_match2) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi get_spec1Snd var_branch_match2) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi get_spec1Snd var_branch_match2) input)
                      (ap2 pi (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)))
        pi_eq = pi_spec1Snd_match2_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)))
                      (ap1 get_spec1Snd input))
        Fst_pi = axFst (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)
    in ruleTrans e1
         (ruleTrans isVM1_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  -- Step: under isVarMatch1 input = O, var_branch input = var_branch_match2 input.
  var_branch_to_match2 :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch1 input) O) ->
    Deriv (eqF (ap1 var_branch input) (ap1 var_branch_match2 input))
  var_branch_to_match2 input isVM1_O =
    let e1 :
          Deriv (eqF (ap1 var_branch input)
                      (ap2 condFork
                        (ap1 (C pi get_spec1Snd var_branch_match2) input)
                        (ap1 isVarMatch1 input)))
        e1 = var_branch_unfold input

        isVM1_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec1Snd var_branch_match2) input)
                       (ap1 isVarMatch1 input))
                      (ap2 condFork
                       (ap1 (C pi get_spec1Snd var_branch_match2) input)
                       O))
        isVM1_subst =
          congR condFork (ap1 (C pi get_spec1Snd var_branch_match2) input) isVM1_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec1Snd var_branch_match2) input) O)
                      (ap1 Snd (ap1 (C pi get_spec1Snd var_branch_match2) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi get_spec1Snd var_branch_match2) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi get_spec1Snd var_branch_match2) input)
                      (ap2 pi (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)))
        pi_eq = pi_spec1Snd_match2_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)))
                      (ap1 var_branch_match2 input))
        Snd_pi = axSnd (ap1 get_spec1Snd input) (ap1 var_branch_match2 input)
    in ruleTrans e1
         (ruleTrans isVM1_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  -- Step: under isVarMatch2 input = sO, var_branch_match2 input = get_spec2Snd input.
  match2_to_spec2Snd :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch2 input) (ap1 s O)) ->
    Deriv (eqF (ap1 var_branch_match2 input) (ap1 get_spec2Snd input))
  match2_to_spec2Snd input isVM2_sO =
    let e1 :
          Deriv (eqF (ap1 var_branch_match2 input)
                      (ap2 condFork
                        (ap1 (C pi get_spec2Snd var_branch_match3) input)
                        (ap1 isVarMatch2 input)))
        e1 = var_branch_match2_unfold input

        isVM2_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec2Snd var_branch_match3) input)
                       (ap1 isVarMatch2 input))
                      (ap2 condFork
                       (ap1 (C pi get_spec2Snd var_branch_match3) input)
                       (ap1 s O)))
        isVM2_subst =
          congR condFork (ap1 (C pi get_spec2Snd var_branch_match3) input) isVM2_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec2Snd var_branch_match3) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi get_spec2Snd var_branch_match3) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi get_spec2Snd var_branch_match3) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi get_spec2Snd var_branch_match3) input)
                      (ap2 pi (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)))
        pi_eq = pi_spec2Snd_match3_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)))
                      (ap1 get_spec2Snd input))
        Fst_pi = axFst (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)
    in ruleTrans e1
         (ruleTrans isVM2_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  -- Step: under isVarMatch2 input = O, var_branch_match2 input = var_branch_match3 input.
  match2_to_match3 :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch2 input) O) ->
    Deriv (eqF (ap1 var_branch_match2 input) (ap1 var_branch_match3 input))
  match2_to_match3 input isVM2_O =
    let e1 :
          Deriv (eqF (ap1 var_branch_match2 input)
                      (ap2 condFork
                        (ap1 (C pi get_spec2Snd var_branch_match3) input)
                        (ap1 isVarMatch2 input)))
        e1 = var_branch_match2_unfold input

        isVM2_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec2Snd var_branch_match3) input)
                       (ap1 isVarMatch2 input))
                      (ap2 condFork
                       (ap1 (C pi get_spec2Snd var_branch_match3) input)
                       O))
        isVM2_subst =
          congR condFork (ap1 (C pi get_spec2Snd var_branch_match3) input) isVM2_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec2Snd var_branch_match3) input) O)
                      (ap1 Snd (ap1 (C pi get_spec2Snd var_branch_match3) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi get_spec2Snd var_branch_match3) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi get_spec2Snd var_branch_match3) input)
                      (ap2 pi (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)))
        pi_eq = pi_spec2Snd_match3_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)))
                      (ap1 var_branch_match3 input))
        Snd_pi = axSnd (ap1 get_spec2Snd input) (ap1 var_branch_match3 input)
    in ruleTrans e1
         (ruleTrans isVM2_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  -- Step: under isVarMatch3 input = sO, var_branch_match3 input = get_spec3Snd input.
  match3_to_spec3Snd :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch3 input) (ap1 s O)) ->
    Deriv (eqF (ap1 var_branch_match3 input) (ap1 get_spec3Snd input))
  match3_to_spec3Snd input isVM3_sO =
    let e1 :
          Deriv (eqF (ap1 var_branch_match3 input)
                      (ap2 condFork
                        (ap1 (C pi get_spec3Snd get_newK) input)
                        (ap1 isVarMatch3 input)))
        e1 = var_branch_match3_unfold input

        isVM3_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec3Snd get_newK) input)
                       (ap1 isVarMatch3 input))
                      (ap2 condFork
                       (ap1 (C pi get_spec3Snd get_newK) input)
                       (ap1 s O)))
        isVM3_subst =
          congR condFork (ap1 (C pi get_spec3Snd get_newK) input) isVM3_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec3Snd get_newK) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi get_spec3Snd get_newK) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi get_spec3Snd get_newK) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi get_spec3Snd get_newK) input)
                      (ap2 pi (ap1 get_spec3Snd input) (ap1 get_newK input)))
        pi_eq = pi_spec3Snd_newK_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 get_spec3Snd input) (ap1 get_newK input)))
                      (ap1 get_spec3Snd input))
        Fst_pi = axFst (ap1 get_spec3Snd input) (ap1 get_newK input)
    in ruleTrans e1
         (ruleTrans isVM3_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  -- Step: under isVarMatch3 input = O, var_branch_match3 input = get_newK input.
  match3_to_newK :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch3 input) O) ->
    Deriv (eqF (ap1 var_branch_match3 input) (ap1 get_newK input))
  match3_to_newK input isVM3_O =
    let e1 :
          Deriv (eqF (ap1 var_branch_match3 input)
                      (ap2 condFork
                        (ap1 (C pi get_spec3Snd get_newK) input)
                        (ap1 isVarMatch3 input)))
        e1 = var_branch_match3_unfold input

        isVM3_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec3Snd get_newK) input)
                       (ap1 isVarMatch3 input))
                      (ap2 condFork
                       (ap1 (C pi get_spec3Snd get_newK) input)
                       O))
        isVM3_subst =
          congR condFork (ap1 (C pi get_spec3Snd get_newK) input) isVM3_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi get_spec3Snd get_newK) input) O)
                      (ap1 Snd (ap1 (C pi get_spec3Snd get_newK) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi get_spec3Snd get_newK) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi get_spec3Snd get_newK) input)
                      (ap2 pi (ap1 get_spec3Snd input) (ap1 get_newK input)))
        pi_eq = pi_spec3Snd_newK_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 get_spec3Snd input) (ap1 get_newK input)))
                      (ap1 get_newK input))
        Snd_pi = axSnd (ap1 get_spec3Snd input) (ap1 get_newK input)
    in ruleTrans e1
         (ruleTrans isVM3_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

------------------------------------------------------------------------
-- Section F.  Compute isVar / isVarMatch1 / isVarMatch2 values at the
-- specific input shape  pi A Y  where A = natCode (cantorVarPred m) and
-- Fst Y = spec2.

private
  -- isVar input = sO at packaged input  pi (natCode (cantorVarPred m)) Y .
  isVar_at_var_input :
    (Y : Term) (m : Nat) ->
    Deriv (eqF (ap1 isVar (ap2 pi (natCode (cantorVarPred m)) Y)) (ap1 s O))
  isVar_at_var_input Y m =
    let A : Term
        A = natCode (cantorVarPred m)

        s1 :
          Deriv (eqF (ap1 isVar (ap2 pi A Y))
                      (ap2 natEqF (ap1 get_tag (ap2 pi A Y)) (natCode tag_var)))
        s1 = isVar_unfold (ap2 pi A Y)

        s2 :
          Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (ap1 Fst (ap1 s A)))
        s2 = get_tag_at_pi A Y

        s3 :
          Deriv (eqF (ap1 Fst (ap1 s A)) (natCode tag_var))
        s3 = Fst_s_natCode_at_var m

        get_tag_value :
          Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (natCode tag_var))
        get_tag_value = ruleTrans s2 s3

        s4 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag (ap2 pi A Y)) (natCode tag_var))
                      (ap2 natEqF (natCode tag_var) (natCode tag_var)))
        s4 = congL natEqF (natCode tag_var) get_tag_value

        s5 :
          Deriv (eqF (ap2 natEqF (natCode tag_var) (natCode tag_var)) (ap1 s O))
        s5 = natEq_eq tag_var
    in ruleTrans s1 (ruleTrans s4 s5)

  -- get_body (pi (natCode (cantorVarPred m)) Y) = natCode m.
  get_body_value :
    (Y : Term) (m : Nat) ->
    Deriv (eqF (ap1 get_body (ap2 pi (natCode (cantorVarPred m)) Y)) (natCode m))
  get_body_value Y m =
    let A : Term
        A = natCode (cantorVarPred m)

        s1 :
          Deriv (eqF (ap1 get_body (ap2 pi A Y)) (ap1 Snd (ap1 s A)))
        s1 = get_body_at_pi A Y

        s2 :
          Deriv (eqF (ap1 Snd (ap1 s A)) (natCode m))
        s2 = Snd_s_natCode_at_var m
    in ruleTrans s1 s2

------------------------------------------------------------------------
-- Section G.  Core firing lemmas.
--
--   stepFun_sbt3_at_var_match_one_core :
--     (k1 k2 : Nat) (S1 S2 : Term) (Y : Term) ->
--     Deriv (eqF (ap1 Fst Y) (spec2Term k1 k2 S1 S2)) ->
--     Deriv (eqF (ap2 stepFun_sbt3 (natCode (cantorVarPred k1)) Y) S1)
--
-- And similarly for _match_2 / _nomatch.

stepFun_sbt3_at_var_match_one_core :
  (k1 k2 k3 : Nat) (S1 S2 S3 Y : Term) ->
  Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
  Deriv (eqF (ap2 stepFun_sbt3 (natCode (cantorVarPred k1)) Y) S1)
stepFun_sbt3_at_var_match_one_core k1 k2 k3 S1 S2 S3 Y fstY_eq =
  let A : Term
      A = natCode (cantorVarPred k1)

      input : Term
      input = ap2 pi A Y

      e1 : Deriv (eqF (ap2 stepFun_sbt3 A Y) (ap1 stepBody_sbt3 input))
      e1 = axPost stepBody_sbt3 pi A Y

      isVar_value : Deriv (eqF (ap1 isVar input) (ap1 s O))
      isVar_value = isVar_at_var_input Y k1

      to_var_branch :
        Deriv (eqF (ap1 stepBody_sbt3 input) (ap1 var_branch input))
      to_var_branch = stepBody_to_var_branch input isVar_value

      e3_unfold :
        Deriv (eqF (ap1 isVarMatch1 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input)))
      e3_unfold = isVarMatch1_unfold input

      body_value : Deriv (eqF (ap1 get_body input) (natCode k1))
      body_value = get_body_value Y k1

      spec1Fst_value :
        Deriv (eqF (ap1 get_spec1Fst input) (natCode k1))
      spec1Fst_value = get_spec1Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e3_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input))
                    (ap2 natEqF (natCode k1) (natCode k1)))
      e3_args =
        ruleTrans (congL natEqF (ap1 get_spec1Fst input) body_value)
                   (congR natEqF (natCode k1) spec1Fst_value)

      e3_eq :
        Deriv (eqF (ap2 natEqF (natCode k1) (natCode k1)) (ap1 s O))
      e3_eq = natEq_eq k1

      isVM1_value : Deriv (eqF (ap1 isVarMatch1 input) (ap1 s O))
      isVM1_value = ruleTrans e3_unfold (ruleTrans e3_args e3_eq)

      var_to_s1Snd :
        Deriv (eqF (ap1 var_branch input) (ap1 get_spec1Snd input))
      var_to_s1Snd = var_branch_to_spec1Snd input isVM1_value

      s1Snd_value : Deriv (eqF (ap1 get_spec1Snd input) S1)
      s1Snd_value = get_spec1Snd_value A Y k1 k2 k3 S1 S2 S3 fstY_eq
  in ruleTrans e1
       (ruleTrans to_var_branch
         (ruleTrans var_to_s1Snd s1Snd_value))

stepFun_sbt3_at_var_match_two_core :
  (k1 k2 k3 : Nat) (S1 S2 S3 Y : Term) ->
  Eq (natEq k1 k2) false ->
  Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
  Deriv (eqF (ap2 stepFun_sbt3 (natCode (cantorVarPred k2)) Y) S2)
stepFun_sbt3_at_var_match_two_core k1 k2 k3 S1 S2 S3 Y k1_neq_k2 fstY_eq =
  let A : Term
      A = natCode (cantorVarPred k2)

      input : Term
      input = ap2 pi A Y

      witness_k2_neq_k1 : NatNeqWitness k2 k1
      witness_k2_neq_k1 = natEqFalse_to_witness_flipped k1 k2 k1_neq_k2

      e1 : Deriv (eqF (ap2 stepFun_sbt3 A Y) (ap1 stepBody_sbt3 input))
      e1 = axPost stepBody_sbt3 pi A Y

      isVar_value : Deriv (eqF (ap1 isVar input) (ap1 s O))
      isVar_value = isVar_at_var_input Y k2

      to_var_branch :
        Deriv (eqF (ap1 stepBody_sbt3 input) (ap1 var_branch input))
      to_var_branch = stepBody_to_var_branch input isVar_value

      e3_unfold :
        Deriv (eqF (ap1 isVarMatch1 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input)))
      e3_unfold = isVarMatch1_unfold input

      body_value : Deriv (eqF (ap1 get_body input) (natCode k2))
      body_value = get_body_value Y k2

      spec1Fst_value :
        Deriv (eqF (ap1 get_spec1Fst input) (natCode k1))
      spec1Fst_value = get_spec1Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e3_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input))
                    (ap2 natEqF (natCode k2) (natCode k1)))
      e3_args =
        ruleTrans (congL natEqF (ap1 get_spec1Fst input) body_value)
                   (congR natEqF (natCode k2) spec1Fst_value)

      e3_O :
        Deriv (eqF (ap2 natEqF (natCode k2) (natCode k1)) O)
      e3_O = natEqF_at_neq k2 k1 witness_k2_neq_k1

      isVM1_value : Deriv (eqF (ap1 isVarMatch1 input) O)
      isVM1_value = ruleTrans e3_unfold (ruleTrans e3_args e3_O)

      var_to_match2 :
        Deriv (eqF (ap1 var_branch input) (ap1 var_branch_match2 input))
      var_to_match2 = var_branch_to_match2 input isVM1_value

      e5_unfold :
        Deriv (eqF (ap1 isVarMatch2 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input)))
      e5_unfold = isVarMatch2_unfold input

      spec2Fst_value :
        Deriv (eqF (ap1 get_spec2Fst input) (natCode k2))
      spec2Fst_value = get_spec2Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e5_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input))
                    (ap2 natEqF (natCode k2) (natCode k2)))
      e5_args =
        ruleTrans (congL natEqF (ap1 get_spec2Fst input) body_value)
                   (congR natEqF (natCode k2) spec2Fst_value)

      e5_eq :
        Deriv (eqF (ap2 natEqF (natCode k2) (natCode k2)) (ap1 s O))
      e5_eq = natEq_eq k2

      isVM2_value : Deriv (eqF (ap1 isVarMatch2 input) (ap1 s O))
      isVM2_value = ruleTrans e5_unfold (ruleTrans e5_args e5_eq)

      match2_to_s2Snd :
        Deriv (eqF (ap1 var_branch_match2 input) (ap1 get_spec2Snd input))
      match2_to_s2Snd = match2_to_spec2Snd input isVM2_value

      s2Snd_value : Deriv (eqF (ap1 get_spec2Snd input) S2)
      s2Snd_value = get_spec2Snd_value A Y k1 k2 k3 S1 S2 S3 fstY_eq
  in ruleTrans e1
       (ruleTrans to_var_branch
         (ruleTrans var_to_match2
           (ruleTrans match2_to_s2Snd s2Snd_value)))

stepFun_sbt3_at_var_match_three_core :
  (k1 k2 k3 : Nat) (S1 S2 S3 Y : Term) ->
  Eq (natEq k1 k3) false -> Eq (natEq k2 k3) false ->
  Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
  Deriv (eqF (ap2 stepFun_sbt3 (natCode (cantorVarPred k3)) Y) S3)
stepFun_sbt3_at_var_match_three_core k1 k2 k3 S1 S2 S3 Y k1_neq_k3 k2_neq_k3 fstY_eq =
  let A : Term
      A = natCode (cantorVarPred k3)

      input : Term
      input = ap2 pi A Y

      witness_k3_neq_k1 : NatNeqWitness k3 k1
      witness_k3_neq_k1 = natEqFalse_to_witness_flipped k1 k3 k1_neq_k3

      witness_k3_neq_k2 : NatNeqWitness k3 k2
      witness_k3_neq_k2 = natEqFalse_to_witness_flipped k2 k3 k2_neq_k3

      e1 : Deriv (eqF (ap2 stepFun_sbt3 A Y) (ap1 stepBody_sbt3 input))
      e1 = axPost stepBody_sbt3 pi A Y

      isVar_value : Deriv (eqF (ap1 isVar input) (ap1 s O))
      isVar_value = isVar_at_var_input Y k3

      to_var_branch :
        Deriv (eqF (ap1 stepBody_sbt3 input) (ap1 var_branch input))
      to_var_branch = stepBody_to_var_branch input isVar_value

      body_value : Deriv (eqF (ap1 get_body input) (natCode k3))
      body_value = get_body_value Y k3

      ----------------------------------------------------------------
      -- isVarMatch1 input = O  (k3 /= k1).
      e3_unfold :
        Deriv (eqF (ap1 isVarMatch1 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input)))
      e3_unfold = isVarMatch1_unfold input

      spec1Fst_value :
        Deriv (eqF (ap1 get_spec1Fst input) (natCode k1))
      spec1Fst_value = get_spec1Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e3_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input))
                    (ap2 natEqF (natCode k3) (natCode k1)))
      e3_args =
        ruleTrans (congL natEqF (ap1 get_spec1Fst input) body_value)
                   (congR natEqF (natCode k3) spec1Fst_value)

      e3_O : Deriv (eqF (ap2 natEqF (natCode k3) (natCode k1)) O)
      e3_O = natEqF_at_neq k3 k1 witness_k3_neq_k1

      isVM1_value : Deriv (eqF (ap1 isVarMatch1 input) O)
      isVM1_value = ruleTrans e3_unfold (ruleTrans e3_args e3_O)

      var_to_match2 :
        Deriv (eqF (ap1 var_branch input) (ap1 var_branch_match2 input))
      var_to_match2 = var_branch_to_match2 input isVM1_value

      ----------------------------------------------------------------
      -- isVarMatch2 input = O  (k3 /= k2).
      e5_unfold :
        Deriv (eqF (ap1 isVarMatch2 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input)))
      e5_unfold = isVarMatch2_unfold input

      spec2Fst_value :
        Deriv (eqF (ap1 get_spec2Fst input) (natCode k2))
      spec2Fst_value = get_spec2Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e5_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input))
                    (ap2 natEqF (natCode k3) (natCode k2)))
      e5_args =
        ruleTrans (congL natEqF (ap1 get_spec2Fst input) body_value)
                   (congR natEqF (natCode k3) spec2Fst_value)

      e5_O : Deriv (eqF (ap2 natEqF (natCode k3) (natCode k2)) O)
      e5_O = natEqF_at_neq k3 k2 witness_k3_neq_k2

      isVM2_value : Deriv (eqF (ap1 isVarMatch2 input) O)
      isVM2_value = ruleTrans e5_unfold (ruleTrans e5_args e5_O)

      match2_to_match3_eq :
        Deriv (eqF (ap1 var_branch_match2 input) (ap1 var_branch_match3 input))
      match2_to_match3_eq = match2_to_match3 input isVM2_value

      ----------------------------------------------------------------
      -- isVarMatch3 input = sO  (k3 = k3).
      e7_unfold :
        Deriv (eqF (ap1 isVarMatch3 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec3Fst input)))
      e7_unfold = isVarMatch3_unfold input

      spec3Fst_value :
        Deriv (eqF (ap1 get_spec3Fst input) (natCode k3))
      spec3Fst_value = get_spec3Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e7_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec3Fst input))
                    (ap2 natEqF (natCode k3) (natCode k3)))
      e7_args =
        ruleTrans (congL natEqF (ap1 get_spec3Fst input) body_value)
                   (congR natEqF (natCode k3) spec3Fst_value)

      e7_eq :
        Deriv (eqF (ap2 natEqF (natCode k3) (natCode k3)) (ap1 s O))
      e7_eq = natEq_eq k3

      isVM3_value : Deriv (eqF (ap1 isVarMatch3 input) (ap1 s O))
      isVM3_value = ruleTrans e7_unfold (ruleTrans e7_args e7_eq)

      match3_to_s3Snd_eq :
        Deriv (eqF (ap1 var_branch_match3 input) (ap1 get_spec3Snd input))
      match3_to_s3Snd_eq = match3_to_spec3Snd input isVM3_value

      s3Snd_value : Deriv (eqF (ap1 get_spec3Snd input) S3)
      s3Snd_value = get_spec3Snd_value A Y k1 k2 k3 S1 S2 S3 fstY_eq
  in ruleTrans e1
       (ruleTrans to_var_branch
         (ruleTrans var_to_match2
           (ruleTrans match2_to_match3_eq
             (ruleTrans match3_to_s3Snd_eq s3Snd_value))))

stepFun_sbt3_at_var_nomatch_core :
  (k1 k2 k3 m : Nat) (S1 S2 S3 Y : Term) ->
  Eq (natEq k1 m) false -> Eq (natEq k2 m) false -> Eq (natEq k3 m) false ->
  Deriv (eqF (ap1 Fst Y) (spec3Term k1 k2 k3 S1 S2 S3)) ->
  Deriv (eqF (ap2 stepFun_sbt3 (natCode (cantorVarPred m)) Y)
              (ap1 s (natCode (cantorVarPred m))))
stepFun_sbt3_at_var_nomatch_core k1 k2 k3 m S1 S2 S3 Y k1_neq_m k2_neq_m k3_neq_m fstY_eq =
  let A : Term
      A = natCode (cantorVarPred m)

      input : Term
      input = ap2 pi A Y

      witness_m_neq_k1 : NatNeqWitness m k1
      witness_m_neq_k1 = natEqFalse_to_witness_flipped k1 m k1_neq_m

      witness_m_neq_k2 : NatNeqWitness m k2
      witness_m_neq_k2 = natEqFalse_to_witness_flipped k2 m k2_neq_m

      witness_m_neq_k3 : NatNeqWitness m k3
      witness_m_neq_k3 = natEqFalse_to_witness_flipped k3 m k3_neq_m

      e1 : Deriv (eqF (ap2 stepFun_sbt3 A Y) (ap1 stepBody_sbt3 input))
      e1 = axPost stepBody_sbt3 pi A Y

      isVar_value : Deriv (eqF (ap1 isVar input) (ap1 s O))
      isVar_value = isVar_at_var_input Y m

      to_var_branch :
        Deriv (eqF (ap1 stepBody_sbt3 input) (ap1 var_branch input))
      to_var_branch = stepBody_to_var_branch input isVar_value

      body_value : Deriv (eqF (ap1 get_body input) (natCode m))
      body_value = get_body_value Y m

      ----------------------------------------------------------------
      -- isVarMatch1 input = O.
      e3_unfold :
        Deriv (eqF (ap1 isVarMatch1 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input)))
      e3_unfold = isVarMatch1_unfold input

      spec1Fst_value :
        Deriv (eqF (ap1 get_spec1Fst input) (natCode k1))
      spec1Fst_value = get_spec1Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e3_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec1Fst input))
                    (ap2 natEqF (natCode m) (natCode k1)))
      e3_args =
        ruleTrans (congL natEqF (ap1 get_spec1Fst input) body_value)
                   (congR natEqF (natCode m) spec1Fst_value)

      e3_O :
        Deriv (eqF (ap2 natEqF (natCode m) (natCode k1)) O)
      e3_O = natEqF_at_neq m k1 witness_m_neq_k1

      isVM1_value : Deriv (eqF (ap1 isVarMatch1 input) O)
      isVM1_value = ruleTrans e3_unfold (ruleTrans e3_args e3_O)

      var_to_match2 :
        Deriv (eqF (ap1 var_branch input) (ap1 var_branch_match2 input))
      var_to_match2 = var_branch_to_match2 input isVM1_value

      ----------------------------------------------------------------
      -- isVarMatch2 input = O.
      e5_unfold :
        Deriv (eqF (ap1 isVarMatch2 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input)))
      e5_unfold = isVarMatch2_unfold input

      spec2Fst_value :
        Deriv (eqF (ap1 get_spec2Fst input) (natCode k2))
      spec2Fst_value = get_spec2Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e5_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec2Fst input))
                    (ap2 natEqF (natCode m) (natCode k2)))
      e5_args =
        ruleTrans (congL natEqF (ap1 get_spec2Fst input) body_value)
                   (congR natEqF (natCode m) spec2Fst_value)

      e5_O :
        Deriv (eqF (ap2 natEqF (natCode m) (natCode k2)) O)
      e5_O = natEqF_at_neq m k2 witness_m_neq_k2

      isVM2_value : Deriv (eqF (ap1 isVarMatch2 input) O)
      isVM2_value = ruleTrans e5_unfold (ruleTrans e5_args e5_O)

      match2_to_match3_eq :
        Deriv (eqF (ap1 var_branch_match2 input) (ap1 var_branch_match3 input))
      match2_to_match3_eq = match2_to_match3 input isVM2_value

      ----------------------------------------------------------------
      -- isVarMatch3 input = O.
      e7_unfold :
        Deriv (eqF (ap1 isVarMatch3 input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_spec3Fst input)))
      e7_unfold = isVarMatch3_unfold input

      spec3Fst_value :
        Deriv (eqF (ap1 get_spec3Fst input) (natCode k3))
      spec3Fst_value = get_spec3Fst_value A Y k1 k2 k3 S1 S2 S3 fstY_eq

      e7_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_spec3Fst input))
                    (ap2 natEqF (natCode m) (natCode k3)))
      e7_args =
        ruleTrans (congL natEqF (ap1 get_spec3Fst input) body_value)
                   (congR natEqF (natCode m) spec3Fst_value)

      e7_O :
        Deriv (eqF (ap2 natEqF (natCode m) (natCode k3)) O)
      e7_O = natEqF_at_neq m k3 witness_m_neq_k3

      isVM3_value : Deriv (eqF (ap1 isVarMatch3 input) O)
      isVM3_value = ruleTrans e7_unfold (ruleTrans e7_args e7_O)

      match3_to_newK_eq :
        Deriv (eqF (ap1 var_branch_match3 input) (ap1 get_newK input))
      match3_to_newK_eq = match3_to_newK input isVM3_value

      ----------------------------------------------------------------
      -- get_newK input = s A.
      newK_eq : Deriv (eqF (ap1 get_newK input) (ap1 s A))
      newK_eq = get_newK_at_pi A Y
  in ruleTrans e1
       (ruleTrans to_var_branch
         (ruleTrans var_to_match2
           (ruleTrans match2_to_match3_eq
             (ruleTrans match3_to_newK_eq newK_eq))))

------------------------------------------------------------------------
-- Section H.  Top-level closure equations.

sbt3_at_var_match_one :
  (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
  Deriv (eqF (ap2 sbt3 (spec3Term k1 k2 k3 S1 S2 S3)
                       (ap2 pi (natCode tag_var) (natCode k1))) S1)
sbt3_at_var_match_one k1 k2 k3 S1 S2 S3 =
  let spec : Term
      spec = spec3Term k1 k2 k3 S1 S2 S3

      t : Term
      t = ap2 pi (natCode tag_var) (natCode k1)

      base : Fun1
      base = baseValue_sbt3

      step : Fun2
      step = stepFun_sbt3

      K_pred : Nat
      K_pred = cantorVarPred k1

      stateK : Term
      stateK = stateMeta base step spec K_pred

      Y : Term
      Y = ap1 Snd stateK

      step1 :
        Deriv (eqF (ap2 sbt3 spec t) (ap1 readOff_spec (ap2 sbt3State spec t)))
      step1 = sbt3_unfold spec t

      step2 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbt3State spec t))
                    (ap1 readOff_spec
                          (stateMeta base step spec (cantor tag_var k1))))
      step2 = readOff_at_pi_natCode base step spec tag_var k1

      cantor_eq_succ : Eq (cantor (suc zero) k1) (suc K_pred)
      cantor_eq_succ = cantor_var_succ_decomp k1

      step3 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k1)))
                    (ap1 readOff_spec (stateMeta base step spec (suc K_pred))))
      step3 =
        eqSubst (\ z -> Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k1)))
                                      (ap1 readOff_spec (stateMeta base step spec z))))
                 cantor_eq_succ
                 (axRefl (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k1))))

      step4 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (suc K_pred)))
                    (ap2 step (natCode K_pred) Y))
      step4 = readOff_stateMeta_succ_via_natCode base step spec K_pred

      fstY_eq : Deriv (eqF (ap1 Fst Y) spec)
      fstY_eq = fstSnd_stateMeta base step spec K_pred

      step6 :
        Deriv (eqF (ap2 step (natCode K_pred) Y) S1)
      step6 = stepFun_sbt3_at_var_match_one_core k1 k2 k3 S1 S2 S3 Y fstY_eq
  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3
           (ruleTrans step4 step6)))

sbt3_at_var_match_two :
  (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
  Eq (natEq k1 k2) false ->
  Deriv (eqF (ap2 sbt3 (spec3Term k1 k2 k3 S1 S2 S3)
                       (ap2 pi (natCode tag_var) (natCode k2))) S2)
sbt3_at_var_match_two k1 k2 k3 S1 S2 S3 k1_neq_k2 =
  let spec : Term
      spec = spec3Term k1 k2 k3 S1 S2 S3

      t : Term
      t = ap2 pi (natCode tag_var) (natCode k2)

      base : Fun1
      base = baseValue_sbt3

      step : Fun2
      step = stepFun_sbt3

      K_pred : Nat
      K_pred = cantorVarPred k2

      stateK : Term
      stateK = stateMeta base step spec K_pred

      Y : Term
      Y = ap1 Snd stateK

      step1 :
        Deriv (eqF (ap2 sbt3 spec t) (ap1 readOff_spec (ap2 sbt3State spec t)))
      step1 = sbt3_unfold spec t

      step2 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbt3State spec t))
                    (ap1 readOff_spec
                          (stateMeta base step spec (cantor tag_var k2))))
      step2 = readOff_at_pi_natCode base step spec tag_var k2

      cantor_eq_succ : Eq (cantor (suc zero) k2) (suc K_pred)
      cantor_eq_succ = cantor_var_succ_decomp k2

      step3 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k2)))
                    (ap1 readOff_spec (stateMeta base step spec (suc K_pred))))
      step3 =
        eqSubst (\ z -> Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k2)))
                                      (ap1 readOff_spec (stateMeta base step spec z))))
                 cantor_eq_succ
                 (axRefl (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k2))))

      step4 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (suc K_pred)))
                    (ap2 step (natCode K_pred) Y))
      step4 = readOff_stateMeta_succ_via_natCode base step spec K_pred

      fstY_eq : Deriv (eqF (ap1 Fst Y) spec)
      fstY_eq = fstSnd_stateMeta base step spec K_pred

      step6 :
        Deriv (eqF (ap2 step (natCode K_pred) Y) S2)
      step6 = stepFun_sbt3_at_var_match_two_core k1 k2 k3 S1 S2 S3 Y k1_neq_k2 fstY_eq
  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3
           (ruleTrans step4 step6)))

sbt3_at_var_match_three :
  (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
  Eq (natEq k1 k3) false -> Eq (natEq k2 k3) false ->
  Deriv (eqF (ap2 sbt3 (spec3Term k1 k2 k3 S1 S2 S3)
                       (ap2 pi (natCode tag_var) (natCode k3))) S3)
sbt3_at_var_match_three k1 k2 k3 S1 S2 S3 k1_neq_k3 k2_neq_k3 =
  let spec : Term
      spec = spec3Term k1 k2 k3 S1 S2 S3

      t : Term
      t = ap2 pi (natCode tag_var) (natCode k3)

      base : Fun1
      base = baseValue_sbt3

      step : Fun2
      step = stepFun_sbt3

      K_pred : Nat
      K_pred = cantorVarPred k3

      stateK : Term
      stateK = stateMeta base step spec K_pred

      Y : Term
      Y = ap1 Snd stateK

      step1 :
        Deriv (eqF (ap2 sbt3 spec t) (ap1 readOff_spec (ap2 sbt3State spec t)))
      step1 = sbt3_unfold spec t

      step2 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbt3State spec t))
                    (ap1 readOff_spec
                          (stateMeta base step spec (cantor tag_var k3))))
      step2 = readOff_at_pi_natCode base step spec tag_var k3

      cantor_eq_succ : Eq (cantor (suc zero) k3) (suc K_pred)
      cantor_eq_succ = cantor_var_succ_decomp k3

      step3 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k3)))
                    (ap1 readOff_spec (stateMeta base step spec (suc K_pred))))
      step3 =
        eqSubst (\ z -> Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k3)))
                                      (ap1 readOff_spec (stateMeta base step spec z))))
                 cantor_eq_succ
                 (axRefl (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k3))))

      step4 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (suc K_pred)))
                    (ap2 step (natCode K_pred) Y))
      step4 = readOff_stateMeta_succ_via_natCode base step spec K_pred

      fstY_eq : Deriv (eqF (ap1 Fst Y) spec)
      fstY_eq = fstSnd_stateMeta base step spec K_pred

      step6 :
        Deriv (eqF (ap2 step (natCode K_pred) Y) S3)
      step6 = stepFun_sbt3_at_var_match_three_core k1 k2 k3 S1 S2 S3 Y
                k1_neq_k3 k2_neq_k3 fstY_eq
  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3
           (ruleTrans step4 step6)))

sbt3_at_var_nomatch :
  (k1 k2 k3 m : Nat) (S1 S2 S3 : Term) ->
  Eq (natEq k1 m) false -> Eq (natEq k2 m) false -> Eq (natEq k3 m) false ->
  Deriv (eqF (ap2 sbt3 (spec3Term k1 k2 k3 S1 S2 S3)
                       (ap2 pi (natCode tag_var) (natCode m)))
              (ap2 pi (natCode tag_var) (natCode m)))
sbt3_at_var_nomatch k1 k2 k3 m S1 S2 S3 k1_neq_m k2_neq_m k3_neq_m =
  let spec : Term
      spec = spec3Term k1 k2 k3 S1 S2 S3

      t : Term
      t = ap2 pi (natCode tag_var) (natCode m)

      base : Fun1
      base = baseValue_sbt3

      step : Fun2
      step = stepFun_sbt3

      K_pred : Nat
      K_pred = cantorVarPred m

      stateK : Term
      stateK = stateMeta base step spec K_pred

      Y : Term
      Y = ap1 Snd stateK

      step1 :
        Deriv (eqF (ap2 sbt3 spec t) (ap1 readOff_spec (ap2 sbt3State spec t)))
      step1 = sbt3_unfold spec t

      step2 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbt3State spec t))
                    (ap1 readOff_spec
                          (stateMeta base step spec (cantor tag_var m))))
      step2 = readOff_at_pi_natCode base step spec tag_var m

      cantor_eq_succ : Eq (cantor (suc zero) m) (suc K_pred)
      cantor_eq_succ = cantor_var_succ_decomp m

      step3 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var m)))
                    (ap1 readOff_spec (stateMeta base step spec (suc K_pred))))
      step3 =
        eqSubst (\ z -> Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var m)))
                                      (ap1 readOff_spec (stateMeta base step spec z))))
                 cantor_eq_succ
                 (axRefl (ap1 readOff_spec (stateMeta base step spec (cantor tag_var m))))

      step4 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (suc K_pred)))
                    (ap2 step (natCode K_pred) Y))
      step4 = readOff_stateMeta_succ_via_natCode base step spec K_pred

      fstY_eq : Deriv (eqF (ap1 Fst Y) spec)
      fstY_eq = fstSnd_stateMeta base step spec K_pred

      step6 :
        Deriv (eqF (ap2 step (natCode K_pred) Y) (ap1 s (natCode K_pred)))
      step6 = stepFun_sbt3_at_var_nomatch_core k1 k2 k3 m S1 S2 S3 Y
                k1_neq_m k2_neq_m k3_neq_m fstY_eq

      step7a :
        Deriv (eqF (ap1 s (natCode K_pred))
                    (natCode (cantor (suc zero) m)))
      step7a = natCode_bridge m

      step7b :
        Deriv (eqF (natCode (cantor (suc zero) m))
                    (ap2 pi (natCode (suc zero)) (natCode m)))
      step7b = ruleSym (pi_natCode (suc zero) m)
  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3
           (ruleTrans step4
             (ruleTrans step6
               (ruleTrans step7a step7b)))))
