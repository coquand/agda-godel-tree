{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbtAtAp -- discharge of the SbContract sbt closures at the two
-- ap-shape inputs:
--
--   sbt_at_ap1 :
--     (k : Nat) (S : Term) (f : Fun1) (ct : Term) ->
--     ap2 sbt (ap2 pi (natCode k) S)
--             (ap2 pi (natCode tag_ap1) (ap2 pi (codeFun1 f) ct))
--       =  ap2 pi (natCode tag_ap1)
--                (ap2 pi (codeFun1 f) (ap2 sbt (ap2 pi (natCode k) S) ct))
--
--   sbt_at_ap2 :  (analogous, with two recursive lookups)
--
-- Universal in  ct, ca, cb : Term  -- no Closed premise, no natCode
-- hypothesis on the sub-positions.
--
-- Proof strategy: pi positivity + cov_spec_step_univ + readOff +
-- stepFun_sbt dispatch + stabilityP_sbt_at to bridge the table lookup
-- to sbt spec ct.

module BRA4.SbtAtAp where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv
open import BRA4.CoVSpecFst
open import BRA4.SbT
open import BRA4.StabilityNatFuel
open import BRA4.Stability
open import BRA4.LeqMono
open import BRA4.PiPositivity

open import BRA3.Church          using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( condFork ; condFork_true_nc ; condFork_false
  ; constN ; constN_eq )
open import BRA3.Numerals        using ( pi_natCode )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq ; natEq_neq_gt )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; gtW ; ltW ; natEqF_at_neq ; decideNatNeq ; Not )
open import BRA3.RuleInst2       using ( ruleInst2 ; natEq-refl ; true_neq_false )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; iter_base_univ )
import BRA3.ChurchT92

------------------------------------------------------------------------
-- Witness construction:  NatNeqWitness  for distinct numeric tags.

private
  natEqFalse_to_NotEq :
    (k m : Nat) -> Eq (natEq k m) false -> Not (Eq k m)
  natEqFalse_to_NotEq k m hyp eqKM =
    let trueEq : Eq (natEq k m) true
        trueEq = eqSubst (\ z -> Eq (natEq k z) true) eqKM (natEq-refl k)

        contradict : Eq true false
        contradict = eqTrans (eqSym trueEq) hyp
    in true_neq_false contradict

  natEqFalse_to_witness :
    (k m : Nat) -> Eq (natEq k m) false -> NatNeqWitness m k
  natEqFalse_to_witness k m hyp =
    let notEqKM : Not (Eq k m)
        notEqKM = natEqFalse_to_NotEq k m hyp

        notEqMK : Not (Eq m k)
        notEqMK eqMK = notEqKM (eqSym eqMK)
    in decideNatNeq m k notEqMK

  -- The specific NatNeqWitness instances we need.
  --  natEqFalse_to_witness k m hyp : NatNeqWitness m k  (note flipped order).
  --  So pass arguments to get the desired direction.
  witness_var_neq_ap1 : NatNeqWitness tag_ap1 tag_var
  witness_var_neq_ap1 = natEqFalse_to_witness tag_var tag_ap1 refl

  witness_var_neq_ap2 : NatNeqWitness tag_ap2 tag_var
  witness_var_neq_ap2 = natEqFalse_to_witness tag_var tag_ap2 refl

------------------------------------------------------------------------
-- Standard fragment: closed-form equations for each get_X helper at a
-- packaged input  pi A Y .
--
-- (Same as BRA4/SbtAtVar.agda's helpers; reproduced here to avoid making
-- those `private`s public.)

private
  get_K_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_K (ap2 pi A Y)) A)
  get_K_at_pi A Y = axFst A Y

  get_inner_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_inner (ap2 pi A Y)) Y)
  get_inner_at_pi A Y = axSnd A Y

  get_newK_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_newK (ap2 pi A Y)) (ap1 s A))
  get_newK_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_newK (ap2 pi A Y)) (ap1 s (ap1 get_K (ap2 pi A Y))))
        s1 = compose1U_eq s get_K (ap2 pi A Y)
    in ruleTrans s1 (cong1 s (get_K_at_pi A Y))

  get_tag_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (ap1 Fst (ap1 s A)))
  get_tag_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_tag (ap2 pi A Y))
                      (ap1 Fst (ap1 get_newK (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_newK_at_pi A Y))

  get_body_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_body (ap2 pi A Y)) (ap1 Snd (ap1 s A)))
  get_body_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_body (ap2 pi A Y))
                      (ap1 Snd (ap1 get_newK (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_newK_at_pi A Y))

  -- get_table = compose1U Snd get_inner.
  get_table_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_table (ap2 pi A Y)) (ap1 Snd Y))
  get_table_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_table (ap2 pi A Y)) (ap1 Snd (ap1 get_inner (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_inner (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_inner_at_pi A Y))

------------------------------------------------------------------------
-- Specialized stepFun_sbt unfolding lemmas at packaged input.

private
  stepBody_sbt_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 stepBody_sbt input)
                (ap2 condFork
                  (ap1 (C pi var_branch ap1_or_above) input)
                  (ap1 isVar input)))
  stepBody_sbt_unfold input =
    ax_C condFork (C pi var_branch ap1_or_above) isVar input

  pi_var_ap1_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
  pi_var_ap1_unfold input = ax_C pi var_branch ap1_or_above input

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

  isAp1_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isAp1 input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_ap1)))
  isAp1_unfold input =
    let s1 :
          Deriv (eqF (ap1 isAp1 input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_ap1) input)))
        s1 = ax_C natEqF get_tag (constN tag_ap1) input

        s2 :
          Deriv (eqF (ap1 (constN tag_ap1) input) (natCode tag_ap1))
        s2 = constN_eq tag_ap1 input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isAp2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isAp2 input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_ap2)))
  isAp2_unfold input =
    let s1 :
          Deriv (eqF (ap1 isAp2 input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_ap2) input)))
        s1 = ax_C natEqF get_tag (constN tag_ap2) input

        s2 :
          Deriv (eqF (ap1 (constN tag_ap2) input) (natCode tag_ap2))
        s2 = constN_eq tag_ap2 input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  ap1_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ap1_or_above input)
                (ap2 condFork
                  (ap1 (C pi ap1_branch ap2_or_else) input)
                  (ap1 isAp1 input)))
  ap1_or_above_unfold input =
    ax_C condFork (C pi ap1_branch ap2_or_else) isAp1 input

  pi_ap1_ap2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi ap1_branch ap2_or_else) input)
                (ap2 pi (ap1 ap1_branch input) (ap1 ap2_or_else input)))
  pi_ap1_ap2_unfold input = ax_C pi ap1_branch ap2_or_else input

  ap2_or_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ap2_or_else input)
                (ap2 condFork
                  (ap1 (C pi ap2_branch else_branch) input)
                  (ap1 isAp2 input)))
  ap2_or_else_unfold input =
    ax_C condFork (C pi ap2_branch else_branch) isAp2 input

  pi_ap2_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi ap2_branch else_branch) input)
                (ap2 pi (ap1 ap2_branch input) (ap1 else_branch input)))
  pi_ap2_else_unfold input = ax_C pi ap2_branch else_branch input

------------------------------------------------------------------------
-- ap1_branch and ap2_branch unfoldings.

  ap1_branch_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ap1_branch input)
                (ap2 pi (ap1 (constN tag_ap1) input)
                        (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input)))
  ap1_branch_unfold input = ax_C pi (constN tag_ap1) (C pi get_bodyFst_ap1 get_val_ct_ap1) input

  C_pi_bodyFst_valct_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input)
                (ap2 pi (ap1 get_bodyFst_ap1 input) (ap1 get_val_ct_ap1 input)))
  C_pi_bodyFst_valct_unfold input = ax_C pi get_bodyFst_ap1 get_val_ct_ap1 input

  ap2_branch_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ap2_branch input)
                (ap2 pi (ap1 (constN tag_ap2) input)
                        (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input)))
  ap2_branch_unfold input =
    ax_C pi (constN tag_ap2) (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input

  C_pi_bodyFst_valab_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input)
                (ap2 pi (ap1 get_bodyFst_ap2 input)
                        (ap1 (C pi get_val_ca get_val_cb) input)))
  C_pi_bodyFst_valab_unfold input = ax_C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb) input

  C_pi_valca_valcb_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_val_ca get_val_cb) input)
                (ap2 pi (ap1 get_val_ca input) (ap1 get_val_cb input)))
  C_pi_valca_valcb_unfold input = ax_C pi get_val_ca get_val_cb input

------------------------------------------------------------------------
-- lookupAt unfolding.  lookupAt idx_F1 = compose1U Fst (C (iter Snd) get_table (C sub get_K idx_F1)).

  lookupAt_unfold :
    (idx_F1 : Fun1) (input : Term) ->
    Deriv (eqF (ap1 (lookupAt idx_F1) input)
                (ap1 Fst (ap2 (iter Snd) (ap1 get_table input) (ap2 sub (ap1 get_K input) (ap1 idx_F1 input)))))
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

        s4 :
          Deriv (eqF (ap2 (iter Snd) (ap1 get_table input) (ap1 (C sub get_K idx_F1) input))
                      (ap2 (iter Snd) (ap1 get_table input) (ap2 sub (ap1 get_K input) (ap1 idx_F1 input))))
        s4 = congR (iter Snd) (ap1 get_table input) s3

        s23 :
          Deriv (eqF (ap1 (C (iter Snd) get_table (C sub get_K idx_F1)) input)
                      (ap2 (iter Snd) (ap1 get_table input) (ap2 sub (ap1 get_K input) (ap1 idx_F1 input))))
        s23 = ruleTrans s2 s4
    in ruleTrans s1 (cong1 Fst s23)

  -- get_bodyFst_ap1 = compose1U Fst get_body.
  get_bodyFst_ap1_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_bodyFst_ap1 (ap2 pi A Y)) (ap1 Fst (ap1 Snd (ap1 s A))))
  get_bodyFst_ap1_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_bodyFst_ap1 (ap2 pi A Y)) (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  -- get_ct_ap1 = compose1U Snd get_body.
  get_ct_ap1_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_ct_ap1 (ap2 pi A Y)) (ap1 Snd (ap1 Snd (ap1 s A))))
  get_ct_ap1_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_ct_ap1 (ap2 pi A Y)) (ap1 Snd (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_body_at_pi A Y))

  -- get_bodyFst_ap2 = compose1U Fst get_body.
  get_bodyFst_ap2_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_bodyFst_ap2 (ap2 pi A Y)) (ap1 Fst (ap1 Snd (ap1 s A))))
  get_bodyFst_ap2_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_bodyFst_ap2 (ap2 pi A Y)) (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  -- get_ab_ap2 = compose1U Snd get_body.
  get_ab_ap2_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_ab_ap2 (ap2 pi A Y)) (ap1 Snd (ap1 Snd (ap1 s A))))
  get_ab_ap2_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_ab_ap2 (ap2 pi A Y)) (ap1 Snd (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_body_at_pi A Y))

  -- get_ca_ap2 = compose1U Fst get_ab_ap2.
  get_ca_ap2_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_ca_ap2 (ap2 pi A Y)) (ap1 Fst (ap1 Snd (ap1 Snd (ap1 s A)))))
  get_ca_ap2_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_ca_ap2 (ap2 pi A Y)) (ap1 Fst (ap1 get_ab_ap2 (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_ab_ap2 (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_ab_ap2_at_pi A Y))

  get_cb_ap2_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_cb_ap2 (ap2 pi A Y)) (ap1 Snd (ap1 Snd (ap1 Snd (ap1 s A)))))
  get_cb_ap2_at_pi A Y =
    let s1 :
          Deriv (eqF (ap1 get_cb_ap2 (ap2 pi A Y)) (ap1 Snd (ap1 get_ab_ap2 (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_ab_ap2 (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_ab_ap2_at_pi A Y))

------------------------------------------------------------------------
-- Leq monotonicity at the specific shape used by sbt_at_ap1 / sbt_at_ap2.

-- For ap1:  leq ct (pi_succ_outer (natCode 1) (pi (codeFun1 cf) ct)) .

leq_ct_P_outer_ap1 :
  (cf : Fun1) (ct : Term) ->
  Deriv (leq ct (pi_succ_outer (natCode (suc zero)) (ap2 pi (codeFun1 cf) ct)))
leq_ct_P_outer_ap1 cf ct =
  let Y : Term
      Y = ap2 pi (codeFun1 cf) ct

      X : Term
      X = ap2 sigma (ap2 sigma (natCode (suc zero)) Y) (ap1 tau (ap2 sigma (natCode (suc zero)) Y))

      l1 : Deriv (leq ct Y)
      l1 = leq_pi_right (codeFun1 cf) ct

      l2 : Deriv (leq Y (ap2 sigma X Y))
      l2 = leq_sigma_right X Y

      -- pi_succ_outer A B = sigma (sigma (sigma A B) (tau (sigma A B))) B = sigma X B.
  in leq_trans ct Y (pi_succ_outer (natCode (suc zero)) Y) l1 l2

-- For ap2:  leq ca (pi_succ_outer (natCode 2) (pi (codeFun2 g) (pi ca cb))) and same for cb.

leq_cb_P_outer_ap2 :
  (g : Fun2) (ca cb : Term) ->
  Deriv (leq cb (pi_succ_outer (natCode (suc (suc zero))) (ap2 pi (codeFun2 g) (ap2 pi ca cb))))
leq_cb_P_outer_ap2 g ca cb =
  let Y2 : Term
      Y2 = ap2 pi (codeFun2 g) (ap2 pi ca cb)

      X2 : Term
      X2 = ap2 sigma (ap2 sigma (natCode (suc (suc zero))) Y2) (ap1 tau (ap2 sigma (natCode (suc (suc zero))) Y2))

      -- leq cb (pi ca cb) by leq_pi_right.
      l1 : Deriv (leq cb (ap2 pi ca cb))
      l1 = leq_pi_right ca cb

      -- leq (pi ca cb) (pi (codeFun2 g) (pi ca cb)) by leq_pi_right.
      l2 : Deriv (leq (ap2 pi ca cb) Y2)
      l2 = leq_pi_right (codeFun2 g) (ap2 pi ca cb)

      -- leq Y2 (sigma X2 Y2) by leq_sigma_right.
      l3 : Deriv (leq Y2 (ap2 sigma X2 Y2))
      l3 = leq_sigma_right X2 Y2

      l12 : Deriv (leq cb Y2)
      l12 = leq_trans cb (ap2 pi ca cb) Y2 l1 l2
  in leq_trans cb Y2 (pi_succ_outer (natCode (suc (suc zero))) Y2) l12 l3

leq_ca_P_outer_ap2 :
  (g : Fun2) (ca cb : Term) ->
  Deriv (leq ca (pi_succ_outer (natCode (suc (suc zero))) (ap2 pi (codeFun2 g) (ap2 pi ca cb))))
leq_ca_P_outer_ap2 g ca cb =
  let Y2 : Term
      Y2 = ap2 pi (codeFun2 g) (ap2 pi ca cb)

      X2 : Term
      X2 = ap2 sigma (ap2 sigma (natCode (suc (suc zero))) Y2) (ap1 tau (ap2 sigma (natCode (suc (suc zero))) Y2))

      -- leq ca (pi ca cb) requires "first arg ≤ pair".  We get this via
      -- T114 + sigma_swap-or-leq_sigma_left.
      -- pi ca cb = sigma (tau (sigma ca cb)) cb.
      -- We need leq ca (sigma X cb).  Use leq_sigma_left to get leq ca (sigma ca X),
      -- but that doesn't match.  Need a different decomposition.
      --
      -- Alternative: ca ≤ sigma ca cb = sigma cb ca [by T36] (still doesn't help).
      -- Hmm; actually leq ca (pi ca cb) needs a different lemma.
      --
      -- Approach: pi ca cb = sigma (tau (sigma ca cb)) cb.  We have
      --   tau (sigma ca cb) ≥ sigma ca cb ≥ ca .  Then
      --   pi ca cb = sigma (tau (sigma ca cb)) cb ≥ tau (sigma ca cb) ≥ ca .
      -- This chain requires:
      --   1. leq ca (sigma ca cb)              [T85].
      --   2. leq (sigma ca cb) (tau (sigma ca cb))  [need leq_var0_tau].
      --   3. leq (tau (sigma ca cb)) (pi ca cb) [T85 applied to sigma (tau ...) cb].
      -- Step 2 = leq Y (tau Y).  We can prove this via T92.

      l1 : Deriv (leq ca (ap2 sigma ca cb))
      l1 = leq_sigma_left ca cb

      -- leq (sigma ca cb) (tau (sigma ca cb)) via T92.
      l2 : Deriv (leq (ap2 sigma ca cb) (ap1 tau (ap2 sigma ca cb)))
      l2 = ruleInst 0 (ap2 sigma ca cb) BRA3.ChurchT92.T92

      -- leq (tau (sigma ca cb)) (sigma (tau (sigma ca cb)) cb) via leq_sigma_left.
      l3 : Deriv (leq (ap1 tau (ap2 sigma ca cb)) (ap2 sigma (ap1 tau (ap2 sigma ca cb)) cb))
      l3 = leq_sigma_left (ap1 tau (ap2 sigma ca cb)) cb

      -- Bridge: sigma (tau (sigma ca cb)) cb = pi ca cb (by ruleSym T114_at).
      eqPi : Deriv (eqF (ap2 sigma (ap1 tau (ap2 sigma ca cb)) cb) (ap2 pi ca cb))
      eqPi = ruleSym (BRA4.LeqMono.T114_at ca cb)

      -- Lift l3 across the eqPi to get leq (tau (sigma ca cb)) (pi ca cb).
      -- Use congR sub for sub b (eqPi):
      cong_sub :
        Deriv (eqF (ap2 sub (ap1 tau (ap2 sigma ca cb)) (ap2 sigma (ap1 tau (ap2 sigma ca cb)) cb))
                    (ap2 sub (ap1 tau (ap2 sigma ca cb)) (ap2 pi ca cb)))
      cong_sub = congR sub (ap1 tau (ap2 sigma ca cb)) eqPi

      cong_sub_sym :
        Deriv (eqF (ap2 sub (ap1 tau (ap2 sigma ca cb)) (ap2 pi ca cb))
                    (ap2 sub (ap1 tau (ap2 sigma ca cb)) (ap2 sigma (ap1 tau (ap2 sigma ca cb)) cb)))
      cong_sub_sym = ruleSym cong_sub

      l3_pi : Deriv (leq (ap1 tau (ap2 sigma ca cb)) (ap2 pi ca cb))
      l3_pi = ruleTrans cong_sub_sym l3

      l12 : Deriv (leq ca (ap1 tau (ap2 sigma ca cb)))
      l12 = leq_trans ca (ap2 sigma ca cb) (ap1 tau (ap2 sigma ca cb)) l1 l2

      l123 : Deriv (leq ca (ap2 pi ca cb))
      l123 = leq_trans ca (ap1 tau (ap2 sigma ca cb)) (ap2 pi ca cb) l12 l3_pi

      -- leq (pi ca cb) Y2 by leq_pi_right.
      l4 : Deriv (leq (ap2 pi ca cb) Y2)
      l4 = leq_pi_right (codeFun2 g) (ap2 pi ca cb)

      -- leq Y2 (sigma X2 Y2) by leq_sigma_right.
      l5 : Deriv (leq Y2 (ap2 sigma X2 Y2))
      l5 = leq_sigma_right X2 Y2

      l_chain1 : Deriv (leq ca Y2)
      l_chain1 = leq_trans ca (ap2 pi ca cb) Y2 l123 l4
  in leq_trans ca Y2 (pi_succ_outer (natCode (suc (suc zero))) Y2) l_chain1 l5

------------------------------------------------------------------------
-- Stability bridge: under  leq ct K , the table-lookup value equals  sbt spec ct .
--
--   HP_sbt base step spec ct K = sbt spec ct
-- under  leq ct K .
--
-- Direct chain:
--   HP_sbt _ _ spec ct K = HP_sbt _ _ spec ct ct      [stabilityP_sbt_at]
--                        = Fst (iter Snd (HistP_sbt _ _ spec ct) (sub ct ct))
--                        = Fst (iter Snd (HistP_sbt _ _ spec ct) O)   [sub_self]
--                        = Fst (HistP_sbt _ _ spec ct)                 [iter_base_univ]
--                        = readOff_spec (cov_spec base step spec ct)   [readOff_spec_eq reverse]
--                        = sbt spec ct                                  [sbt_unfold reverse]

private
  HP_sbt_eq_sbt_under_leq :
    (spec ct K : Term) ->
    Deriv (leq ct K) ->
    Deriv (eqF (HPsbt baseValue_sbt stepFun_sbt spec ct K) (ap2 sbt spec ct))
  HP_sbt_eq_sbt_under_leq spec ct K leq_ct_K =
    let -- Step A: stability lemma.
        stab :
          Deriv (eqF (HPsbt baseValue_sbt stepFun_sbt spec ct K)
                      (HPsbt baseValue_sbt stepFun_sbt spec ct ct))
        stab = mp (stabilityP_sbt_at baseValue_sbt stepFun_sbt spec ct K) leq_ct_K

        -- Step B: HPsbt ... spec ct ct
        --   = Fst (iter Snd (HistP_sbt spec ct) (sub ct ct))
        --   = Fst (iter Snd (HistP_sbt spec ct) O)   [via sub_self]
        --   = Fst (HistP_sbt spec ct)                 [via iter_base_univ]

        subCT_O : Deriv (eqF (ap2 sub ct ct) O)
        subCT_O = sub_self ct

        iter_arg :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec ct) (ap2 sub ct ct))
                      (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec ct) O))
        iter_arg = congR (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec ct) subCT_O

        iter_base :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec ct) O)
                      (HistP_sbt baseValue_sbt stepFun_sbt spec ct))
        iter_base = iter_base_univ Snd (HistP_sbt baseValue_sbt stepFun_sbt spec ct)

        iter_full :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec ct) (ap2 sub ct ct))
                      (HistP_sbt baseValue_sbt stepFun_sbt spec ct))
        iter_full = ruleTrans iter_arg iter_base

        HP_at_ct :
          Deriv (eqF (HPsbt baseValue_sbt stepFun_sbt spec ct ct)
                      (ap1 Fst (HistP_sbt baseValue_sbt stepFun_sbt spec ct)))
        HP_at_ct = cong1 Fst iter_full

        -- Step C: Fst (HistP_sbt spec ct) = readOff_spec (cov_spec spec ct).
        -- HistP_sbt = Snd (Snd (cov_spec ... spec K)).
        -- readOff_spec X = Fst (Snd (Snd X)).
        -- So Fst (HistP_sbt spec ct) = Fst (Snd (Snd (cov_spec spec ct))) = readOff_spec (cov_spec spec ct).
        readOff_eq :
          Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec ct))
                      (ap1 Fst (HistP_sbt baseValue_sbt stepFun_sbt spec ct)))
        readOff_eq = readOff_spec_eq (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec ct)

        readOff_eq_sym :
          Deriv (eqF (ap1 Fst (HistP_sbt baseValue_sbt stepFun_sbt spec ct))
                      (ap1 readOff_spec (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec ct)))
        readOff_eq_sym = ruleSym readOff_eq

        -- Step D: ap1 readOff_spec (cov_spec spec ct) = ap2 sbt spec ct.
        sbt_eq :
          Deriv (eqF (ap2 sbt spec ct) (ap1 readOff_spec (ap2 sbtState spec ct)))
        sbt_eq = sbt_unfold spec ct

        sbt_eq_sym :
          Deriv (eqF (ap1 readOff_spec (ap2 sbtState spec ct)) (ap2 sbt spec ct))
        sbt_eq_sym = ruleSym sbt_eq

    in ruleTrans stab (ruleTrans HP_at_ct (ruleTrans readOff_eq_sym sbt_eq_sym))

------------------------------------------------------------------------
-- The core firing lemma for sbt_at_ap1.
--
--   stepFun_sbt_at_ap1_core :
--     (spec ct : Term) (f : Fun1) ->
--     Deriv (eqF (ap1 Fst Y) spec) ->                  -- spec invariant
--     Deriv (eqF (ap2 stepFun_sbt P_outer Y)
--                 (ap2 pi (natCode tag_ap1)
--                       (ap2 pi (codeFun1 f) (sbt spec ct))))
--
-- where P_outer = pi_succ_outer (natCode 1) (pi (codeFun1 f) ct) and Y is
-- the inner-state value (= Snd (cov_spec spec P_outer)).
--
-- Actually for the cleanest path, we incorporate the lookup-bridge to
-- sbt spec ct directly using HP_sbt_eq_sbt_under_leq.  The hypothesis
-- "Fst Y = spec" is used to dispatch through get_specFst etc.

-- For convenience, sbt_at_ap1 is built directly without an intermediate
-- "core" lemma (the structure is linear and bridging through a separate
-- core would not simplify).

------------------------------------------------------------------------
-- Tag dispatch witnesses.

private
  -- isVar at the ap1-input fires as  O .
  isVar_at_natCodeAp1_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ap1)) ->
    Deriv (eqF (ap1 isVar input) O)
  isVar_at_natCodeAp1_O input tag_eq =
    let s1 :
          Deriv (eqF (ap1 isVar input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_var)))
        s1 = isVar_unfold input

        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_var))
                      (ap2 natEqF (natCode tag_ap1) (natCode tag_var)))
        s2 = congL natEqF (natCode tag_var) tag_eq

        s3 : Deriv (eqF (ap2 natEqF (natCode tag_ap1) (natCode tag_var)) O)
        s3 = natEqF_at_neq tag_ap1 tag_var witness_var_neq_ap1
    in ruleTrans s1 (ruleTrans s2 s3)

  -- isVar at the ap2-input fires as  O .
  isVar_at_natCodeAp2_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ap2)) ->
    Deriv (eqF (ap1 isVar input) O)
  isVar_at_natCodeAp2_O input tag_eq =
    let s1 :
          Deriv (eqF (ap1 isVar input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_var)))
        s1 = isVar_unfold input

        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_var))
                      (ap2 natEqF (natCode tag_ap2) (natCode tag_var)))
        s2 = congL natEqF (natCode tag_var) tag_eq

        s3 : Deriv (eqF (ap2 natEqF (natCode tag_ap2) (natCode tag_var)) O)
        s3 = natEqF_at_neq tag_ap2 tag_var witness_var_neq_ap2
    in ruleTrans s1 (ruleTrans s2 s3)

  -- isAp1 at the ap1-input fires as  sO .
  isAp1_at_natCodeAp1_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ap1)) ->
    Deriv (eqF (ap1 isAp1 input) (ap1 s O))
  isAp1_at_natCodeAp1_sO input tag_eq =
    let s1 :
          Deriv (eqF (ap1 isAp1 input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_ap1)))
        s1 = isAp1_unfold input

        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_ap1))
                      (ap2 natEqF (natCode tag_ap1) (natCode tag_ap1)))
        s2 = congL natEqF (natCode tag_ap1) tag_eq

        s3 : Deriv (eqF (ap2 natEqF (natCode tag_ap1) (natCode tag_ap1)) (ap1 s O))
        s3 = natEq_eq tag_ap1
    in ruleTrans s1 (ruleTrans s2 s3)

  -- isAp2 at the ap2-input fires as  sO .
  isAp2_at_natCodeAp2_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ap2)) ->
    Deriv (eqF (ap1 isAp2 input) (ap1 s O))
  isAp2_at_natCodeAp2_sO input tag_eq =
    let s1 :
          Deriv (eqF (ap1 isAp2 input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_ap2)))
        s1 = isAp2_unfold input

        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_ap2))
                      (ap2 natEqF (natCode tag_ap2) (natCode tag_ap2)))
        s2 = congL natEqF (natCode tag_ap2) tag_eq

        s3 : Deriv (eqF (ap2 natEqF (natCode tag_ap2) (natCode tag_ap2)) (ap1 s O))
        s3 = natEq_eq tag_ap2
    in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Dispatch through stepBody_sbt's outer condFork.

private
  stepBody_sbt_to_ap1_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isVar input) O) ->
    Deriv (eqF (ap1 stepBody_sbt input) (ap1 ap1_or_above input))
  stepBody_sbt_to_ap1_or_above input isVar_O =
    let e1 :
          Deriv (eqF (ap1 stepBody_sbt input)
                      (ap2 condFork
                        (ap1 (C pi var_branch ap1_or_above) input)
                        (ap1 isVar input)))
        e1 = stepBody_sbt_unfold input

        isVar_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi var_branch ap1_or_above) input)
                       (ap1 isVar input))
                      (ap2 condFork
                       (ap1 (C pi var_branch ap1_or_above) input)
                       O))
        isVar_subst =
          congR condFork (ap1 (C pi var_branch ap1_or_above) input) isVar_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi var_branch ap1_or_above) input) O)
                      (ap1 Snd (ap1 (C pi var_branch ap1_or_above) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi var_branch ap1_or_above) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                      (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
        pi_eq = pi_var_ap1_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
                      (ap1 ap1_or_above input))
        Snd_pi = axSnd (ap1 var_branch input) (ap1 ap1_or_above input)
    in ruleTrans e1
         (ruleTrans isVar_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  -- Under isAp1 input = sO, ap1_or_above input = ap1_branch input.
  ap1_or_above_to_ap1_branch :
    (input : Term) ->
    Deriv (eqF (ap1 isAp1 input) (ap1 s O)) ->
    Deriv (eqF (ap1 ap1_or_above input) (ap1 ap1_branch input))
  ap1_or_above_to_ap1_branch input isAp1_sO =
    let e1 :
          Deriv (eqF (ap1 ap1_or_above input)
                      (ap2 condFork
                        (ap1 (C pi ap1_branch ap2_or_else) input)
                        (ap1 isAp1 input)))
        e1 = ap1_or_above_unfold input

        isAp1_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ap1_branch ap2_or_else) input)
                       (ap1 isAp1 input))
                      (ap2 condFork
                       (ap1 (C pi ap1_branch ap2_or_else) input)
                       (ap1 s O)))
        isAp1_subst =
          congR condFork (ap1 (C pi ap1_branch ap2_or_else) input) isAp1_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ap1_branch ap2_or_else) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi ap1_branch ap2_or_else) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi ap1_branch ap2_or_else) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi ap1_branch ap2_or_else) input)
                      (ap2 pi (ap1 ap1_branch input) (ap1 ap2_or_else input)))
        pi_eq = pi_ap1_ap2_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 ap1_branch input) (ap1 ap2_or_else input)))
                      (ap1 ap1_branch input))
        Fst_pi = axFst (ap1 ap1_branch input) (ap1 ap2_or_else input)
    in ruleTrans e1
         (ruleTrans isAp1_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  -- Under isAp1 input = O ∧ isAp2 input = sO, ap1_or_above input = ap2_branch input.
  ap1_or_above_to_ap2_branch :
    (input : Term) ->
    Deriv (eqF (ap1 isAp1 input) O) ->
    Deriv (eqF (ap1 isAp2 input) (ap1 s O)) ->
    Deriv (eqF (ap1 ap1_or_above input) (ap1 ap2_branch input))
  ap1_or_above_to_ap2_branch input isAp1_O isAp2_sO =
    let e1 :
          Deriv (eqF (ap1 ap1_or_above input)
                      (ap2 condFork
                        (ap1 (C pi ap1_branch ap2_or_else) input)
                        (ap1 isAp1 input)))
        e1 = ap1_or_above_unfold input

        isAp1_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ap1_branch ap2_or_else) input)
                       (ap1 isAp1 input))
                      (ap2 condFork
                       (ap1 (C pi ap1_branch ap2_or_else) input)
                       O))
        isAp1_subst =
          congR condFork (ap1 (C pi ap1_branch ap2_or_else) input) isAp1_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ap1_branch ap2_or_else) input) O)
                      (ap1 Snd (ap1 (C pi ap1_branch ap2_or_else) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi ap1_branch ap2_or_else) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi ap1_branch ap2_or_else) input)
                      (ap2 pi (ap1 ap1_branch input) (ap1 ap2_or_else input)))
        pi_eq = pi_ap1_ap2_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 ap1_branch input) (ap1 ap2_or_else input)))
                      (ap1 ap2_or_else input))
        Snd_pi = axSnd (ap1 ap1_branch input) (ap1 ap2_or_else input)

        e2 :
          Deriv (eqF (ap1 ap2_or_else input)
                      (ap2 condFork
                        (ap1 (C pi ap2_branch else_branch) input)
                        (ap1 isAp2 input)))
        e2 = ap2_or_else_unfold input

        isAp2_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ap2_branch else_branch) input)
                       (ap1 isAp2 input))
                      (ap2 condFork
                       (ap1 (C pi ap2_branch else_branch) input)
                       (ap1 s O)))
        isAp2_subst =
          congR condFork (ap1 (C pi ap2_branch else_branch) input) isAp2_sO

        condFork_to_Fst_ap2 :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ap2_branch else_branch) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi ap2_branch else_branch) input)))
        condFork_to_Fst_ap2 =
          condFork_true_nc (ap1 (C pi ap2_branch else_branch) input) O

        pi_eq_ap2 :
          Deriv (eqF (ap1 (C pi ap2_branch else_branch) input)
                      (ap2 pi (ap1 ap2_branch input) (ap1 else_branch input)))
        pi_eq_ap2 = pi_ap2_else_unfold input

        Fst_pi_ap2 :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 ap2_branch input) (ap1 else_branch input)))
                      (ap1 ap2_branch input))
        Fst_pi_ap2 = axFst (ap1 ap2_branch input) (ap1 else_branch input)

        ap2_or_else_to_ap2 :
          Deriv (eqF (ap1 ap2_or_else input) (ap1 ap2_branch input))
        ap2_or_else_to_ap2 =
          ruleTrans e2
            (ruleTrans isAp2_subst
              (ruleTrans condFork_to_Fst_ap2
                (ruleTrans (cong1 Fst pi_eq_ap2) Fst_pi_ap2)))
    in ruleTrans e1
         (ruleTrans isAp1_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq)
               (ruleTrans Snd_pi ap2_or_else_to_ap2))))

------------------------------------------------------------------------
-- sbt_at_ap1 :  the SbContract closure for ap1.
--
--   ap2 sbt (pi (natCode k) S) (pi (natCode tag_ap1) (pi (codeFun1 f) ct))
--     = pi (natCode tag_ap1) (pi (codeFun1 f) (sbt (pi (natCode k) S) ct))
--
-- Universal in  ct : Term ; no Closed premise.

sbt_at_ap1 :
  (k : Nat) (S : Term) (f : Fun1) (ct : Term) ->
  Deriv (eqF (ap2 sbt (ap2 pi (natCode k) S)
               (ap2 pi (natCode tag_ap1) (ap2 pi (codeFun1 f) ct)))
              (ap2 pi (natCode tag_ap1)
                (ap2 pi (codeFun1 f) (ap2 sbt (ap2 pi (natCode k) S) ct))))
sbt_at_ap1 k S f ct =
  let spec : Term
      spec = ap2 pi (natCode k) S

      Y : Term
      Y = ap2 pi (codeFun1 f) ct

      input : Term
      input = ap2 pi (natCode tag_ap1) Y

      -- tag_ap1 = 2 = suc (suc zero) = s (natCode 1) = s (s O).
      -- natCode 2 = ap1 s (ap1 s O) = ap1 s (natCode 1).
      P_outer : Term
      P_outer = pi_succ_outer (natCode (suc zero)) Y

      prev : Term
      prev = ap2 (cov_spec baseValue_sbt stepFun_sbt) spec P_outer

      input_pkg : Term
      input_pkg = ap2 pi (ap1 Fst prev) (ap1 Snd prev)

      ----------------------------------------------------------------
      -- Step 1: sbt_unfold.
      step1 :
        Deriv (eqF (ap2 sbt spec input) (ap1 readOff_spec (ap2 sbtState spec input)))
      step1 = sbt_unfold spec input

      ----------------------------------------------------------------
      -- Step 2: bridge input = s P_outer.
      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ (natCode (suc zero)) Y

      -- Lift through cov_spec spec.
      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec input)
                    (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec (ap1 s P_outer)))
      cov_lift = congR (cov_spec baseValue_sbt stepFun_sbt) spec input_eq_sP_outer

      -- cov_spec spec (s P_outer) = state_step_spec stepFun_sbt prev.
      cov_step :
        Deriv (eqF (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec (ap1 s P_outer))
                    (ap1 (state_step_spec stepFun_sbt) prev))
      cov_step = cov_spec_step_univ baseValue_sbt stepFun_sbt spec P_outer

      sbtState_eq :
        Deriv (eqF (ap2 sbtState spec input) (ap1 (state_step_spec stepFun_sbt) prev))
      sbtState_eq = ruleTrans cov_lift cov_step

      ----------------------------------------------------------------
      -- Step 3: readOff_state_step_univ gives stepFun_sbt (Fst prev) (Snd prev).
      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 sbtState spec input))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbt) prev)))
      readOff_lift = cong1 readOff_spec sbtState_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbt) prev))
                    (ap2 stepFun_sbt (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ stepFun_sbt prev

      ----------------------------------------------------------------
      -- Step 4: bridge Fst prev = P_outer via fst_cov_spec_eq.
      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq baseValue_sbt stepFun_sbt spec P_outer

      stepFun_lift :
        Deriv (eqF (ap2 stepFun_sbt (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun_sbt P_outer (ap1 Snd prev)))
      stepFun_lift = congL stepFun_sbt (ap1 Snd prev) Fst_prev_eq

      ----------------------------------------------------------------
      -- Step 5: stepFun_sbt = Post stepBody_sbt pi.  So
      --   stepFun_sbt P_outer (Snd prev) = stepBody_sbt (pi P_outer (Snd prev)).
      Post_eq :
        Deriv (eqF (ap2 stepFun_sbt P_outer (ap1 Snd prev))
                    (ap1 stepBody_sbt (ap2 pi P_outer (ap1 Snd prev))))
      Post_eq = axPost stepBody_sbt pi P_outer (ap1 Snd prev)

      -- The packaged input at K_term = P_outer.
      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      ----------------------------------------------------------------
      -- Step 6: tag dispatch.  In input_pkg', K_term = P_outer; s K_term = s P_outer = input.
      --
      --   get_K input_pkg' = P_outer.
      --   get_newK input_pkg' = s P_outer = input.
      --   get_tag input_pkg' = Fst (s P_outer) = Fst input = natCode tag_ap1.

      get_newK_eq :
        Deriv (eqF (ap1 get_newK input_pkg') (ap1 s P_outer))
      get_newK_eq = get_newK_at_pi P_outer (ap1 Snd prev)

      -- s P_outer = input (by ruleSym input_eq_sP_outer).
      newK_eq_input :
        Deriv (eqF (ap1 get_newK input_pkg') input)
      newK_eq_input = ruleTrans get_newK_eq (ruleSym input_eq_sP_outer)

      -- get_tag input_pkg' = Fst (s P_outer).
      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      -- Fst input = Fst (pi (natCode tag_ap1) Y) = natCode tag_ap1.
      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_ap1))
      Fst_input = axFst (natCode tag_ap1) Y

      -- Bridge Fst (s P_outer) -> Fst input -> natCode tag_ap1.
      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_ap1))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      ----------------------------------------------------------------
      -- Step 7: isVar input_pkg' = O.
      isVar_value : Deriv (eqF (ap1 isVar input_pkg') O)
      isVar_value = isVar_at_natCodeAp1_O input_pkg' get_tag_value

      -- Step 7b: dispatch to ap1_or_above.
      stepBody_to_ap1or :
        Deriv (eqF (ap1 stepBody_sbt input_pkg') (ap1 ap1_or_above input_pkg'))
      stepBody_to_ap1or = stepBody_sbt_to_ap1_or_above input_pkg' isVar_value

      ----------------------------------------------------------------
      -- Step 8: isAp1 input_pkg' = sO.
      isAp1_value : Deriv (eqF (ap1 isAp1 input_pkg') (ap1 s O))
      isAp1_value = isAp1_at_natCodeAp1_sO input_pkg' get_tag_value

      -- Step 8b: dispatch to ap1_branch.
      ap1or_to_ap1 :
        Deriv (eqF (ap1 ap1_or_above input_pkg') (ap1 ap1_branch input_pkg'))
      ap1or_to_ap1 = ap1_or_above_to_ap1_branch input_pkg' isAp1_value

      -- Combine:  stepBody_sbt input_pkg' = ap1_branch input_pkg'.
      stepBody_to_ap1 :
        Deriv (eqF (ap1 stepBody_sbt input_pkg') (ap1 ap1_branch input_pkg'))
      stepBody_to_ap1 = ruleTrans stepBody_to_ap1or ap1or_to_ap1

      ----------------------------------------------------------------
      -- Step 9: ap1_branch input_pkg'.
      --   ap1_branch input_pkg' =
      --     pi (constN tag_ap1 input_pkg')
      --        (pi (get_bodyFst_ap1 input_pkg') (get_val_ct_ap1 input_pkg'))
      --   = pi (natCode tag_ap1) (pi (codeFun1 f) (sbt spec ct))
      -- under leq ct P_outer.

      -- Step 9a: ap1_branch input_pkg' = pi (constN tag_ap1 ...) (pi bodyFst valCt).
      ap1br_unfold :
        Deriv (eqF (ap1 ap1_branch input_pkg')
                    (ap2 pi (ap1 (constN tag_ap1) input_pkg')
                            (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input_pkg')))
      ap1br_unfold = ap1_branch_unfold input_pkg'

      constN_at :
        Deriv (eqF (ap1 (constN tag_ap1) input_pkg') (natCode tag_ap1))
      constN_at = constN_eq tag_ap1 input_pkg'

      ap1br_step1 :
        Deriv (eqF (ap1 ap1_branch input_pkg')
                    (ap2 pi (natCode tag_ap1)
                            (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input_pkg')))
      ap1br_step1 = ruleTrans ap1br_unfold
                      (congL pi (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input_pkg') constN_at)

      -- Step 9b: unfold inner C pi.
      inner_unfold :
        Deriv (eqF (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input_pkg')
                    (ap2 pi (ap1 get_bodyFst_ap1 input_pkg') (ap1 get_val_ct_ap1 input_pkg')))
      inner_unfold = C_pi_bodyFst_valct_unfold input_pkg'

      ----------------------------------------------------------------
      -- Step 10: get_bodyFst_ap1 input_pkg' = codeFun1 f.
      --   get_bodyFst_ap1 input_pkg' = Fst (Snd (s P_outer)).
      --   s P_outer = input = pi (natCode tag_ap1) Y.
      --   Snd (pi (natCode tag_ap1) Y) = Y.
      --   Fst Y = Fst (pi (codeFun1 f) ct) = codeFun1 f.

      bodyFst_eq_Fst_Snd_sP :
        Deriv (eqF (ap1 get_bodyFst_ap1 input_pkg') (ap1 Fst (ap1 Snd (ap1 s P_outer))))
      bodyFst_eq_Fst_Snd_sP = get_bodyFst_ap1_at_pi P_outer (ap1 Snd prev)

      -- Replace s P_outer with input.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      -- Snd input = Snd (pi (natCode tag_ap1) Y) = Y.
      Snd_input_eq_Y :
        Deriv (eqF (ap1 Snd input) Y)
      Snd_input_eq_Y = axSnd (natCode tag_ap1) Y

      -- Fst Y = codeFun1 f.
      Fst_Y :
        Deriv (eqF (ap1 Fst Y) (codeFun1 f))
      Fst_Y = axFst (codeFun1 f) ct

      bodyFst_value :
        Deriv (eqF (ap1 get_bodyFst_ap1 input_pkg') (codeFun1 f))
      bodyFst_value =
        ruleTrans bodyFst_eq_Fst_Snd_sP
          (ruleTrans (cong1 Fst Snd_sP_eq)
            (ruleTrans (cong1 Fst Snd_input_eq_Y) Fst_Y))

      ----------------------------------------------------------------
      -- Step 11: get_val_ct_ap1 input_pkg' = sbt spec ct (under leq ct P_outer).
      --   get_val_ct_ap1 = lookupAt get_ct_ap1.
      --   lookupAt unfolding gives Fst (iter Snd (get_table input_pkg') (sub (get_K input_pkg') (get_ct_ap1 input_pkg'))).
      --   get_K input_pkg' = P_outer.
      --   get_ct_ap1 input_pkg' = Snd (Snd (s P_outer)) = Snd (Snd input) = Snd Y = ct.
      --   get_table input_pkg' = Snd Y' where Y' = Snd prev.  But Snd prev itself starts with spec... wait.
      --   Actually get_table = compose1U Snd get_inner; get_inner input_pkg' = Snd input_pkg' = Snd prev.
      --   So get_table input_pkg' = Snd (Snd prev) = HistP_sbt spec P_outer.

      -- Step 11a: lookupAt unfold.
      lookup_unfold :
        Deriv (eqF (ap1 get_val_ct_ap1 input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg') (ap1 get_ct_ap1 input_pkg')))))
      lookup_unfold = lookupAt_unfold get_ct_ap1 input_pkg'

      -- get_K input_pkg' = P_outer.
      get_K_value :
        Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      -- get_ct_ap1 input_pkg' = ct.
      get_ct_value : Deriv (eqF (ap1 get_ct_ap1 input_pkg') ct)
      get_ct_value =
        let s1 :
              Deriv (eqF (ap1 get_ct_ap1 input_pkg') (ap1 Snd (ap1 Snd (ap1 s P_outer))))
            s1 = get_ct_ap1_at_pi P_outer (ap1 Snd prev)

            -- Snd (s P_outer) = Snd input = Y.
            Snd_sP_to_Y :
              Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y)
            Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Y

            -- Snd Y = Snd (pi (codeFun1 f) ct) = ct.
            Snd_Y :
              Deriv (eqF (ap1 Snd Y) ct)
            Snd_Y = axSnd (codeFun1 f) ct
        in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      -- get_table input_pkg' = Snd (Snd prev) = HistP_sbt baseValue_sbt stepFun_sbt spec P_outer.
      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg') (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)
      -- Note: HistP_sbt b s spec P_outer = Snd (Snd (cov_spec b s spec P_outer)) = Snd (Snd prev).
      -- And get_table input_pkg' = Snd (Snd prev) = Snd (ap1 Snd prev). After get_table_at_pi:
      -- get_table input_pkg' = Snd (ap1 Snd prev) syntactically. We need this to equal HistP_sbt ... .

      -- Combine: (iter Snd table (sub K ct_idx)).
      iter_arg :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_ct_ap1 input_pkg'))
                    (ap2 sub P_outer ct))
      iter_arg = ruleTrans (congL sub (ap1 get_ct_ap1 input_pkg') get_K_value)
                  (congR sub P_outer get_ct_value)

      iter_full :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                          (ap2 sub (ap1 get_K input_pkg') (ap1 get_ct_ap1 input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer)
                          (ap2 sub P_outer ct)))
      iter_full = ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_ct_ap1 input_pkg')) get_table_value)
                   (congR (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer) iter_arg)

      -- Wrap with Fst: get HP_sbt form.
      val_ct_unfold :
        Deriv (eqF (ap1 get_val_ct_ap1 input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer)
                              (ap2 sub P_outer ct))))
      val_ct_unfold = ruleTrans lookup_unfold (cong1 Fst iter_full)
      -- The RHS is HPsbt baseValue_sbt stepFun_sbt spec ct P_outer.

      -- Step 11b: leq ct P_outer.
      leq_ct_P : Deriv (leq ct P_outer)
      leq_ct_P = leq_ct_P_outer_ap1 f ct

      -- Step 11c: HP_sbt → sbt spec ct.
      HP_to_sbt :
        Deriv (eqF (HPsbt baseValue_sbt stepFun_sbt spec ct P_outer) (ap2 sbt spec ct))
      HP_to_sbt = HP_sbt_eq_sbt_under_leq spec ct P_outer leq_ct_P

      val_ct_value :
        Deriv (eqF (ap1 get_val_ct_ap1 input_pkg') (ap2 sbt spec ct))
      val_ct_value = ruleTrans val_ct_unfold HP_to_sbt

      ----------------------------------------------------------------
      -- Step 12: assemble inner pi.
      inner_value :
        Deriv (eqF (ap1 (C pi get_bodyFst_ap1 get_val_ct_ap1) input_pkg')
                    (ap2 pi (codeFun1 f) (ap2 sbt spec ct)))
      inner_value =
        ruleTrans inner_unfold
          (ruleTrans (congL pi (ap1 get_val_ct_ap1 input_pkg') bodyFst_value)
                      (congR pi (codeFun1 f) val_ct_value))

      -- Outer pi: ap1_branch input_pkg' = pi (natCode tag_ap1) (pi (codeFun1 f) (sbt spec ct)).
      ap1br_value :
        Deriv (eqF (ap1 ap1_branch input_pkg')
                    (ap2 pi (natCode tag_ap1)
                            (ap2 pi (codeFun1 f) (ap2 sbt spec ct))))
      ap1br_value =
        ruleTrans ap1br_step1
          (congR pi (natCode tag_ap1) inner_value)

      ----------------------------------------------------------------
      -- Step 13: chain everything.
      chain_to_stepBody :
        Deriv (eqF (ap2 sbt spec input)
                    (ap1 stepBody_sbt input_pkg'))
      chain_to_stepBody =
        ruleTrans step1
          (ruleTrans readOff_lift
            (ruleTrans readOff_eval
              (ruleTrans stepFun_lift Post_eq)))

      chain_to_ap1br :
        Deriv (eqF (ap2 sbt spec input) (ap1 ap1_branch input_pkg'))
      chain_to_ap1br = ruleTrans chain_to_stepBody stepBody_to_ap1
  in ruleTrans chain_to_ap1br ap1br_value

------------------------------------------------------------------------
-- sbt_at_ap2 :  the SbContract closure for ap2.
--
-- Same skeleton as sbt_at_ap1, but with tag_ap2 instead of tag_ap1, and
-- two recursive lookups (for ca and cb).

sbt_at_ap2 :
  (k : Nat) (S : Term) (g : Fun2) (ca cb : Term) ->
  Deriv (eqF (ap2 sbt (ap2 pi (natCode k) S)
               (ap2 pi (natCode tag_ap2)
                 (ap2 pi (codeFun2 g) (ap2 pi ca cb))))
              (ap2 pi (natCode tag_ap2)
                (ap2 pi (codeFun2 g)
                  (ap2 pi
                    (ap2 sbt (ap2 pi (natCode k) S) ca)
                    (ap2 sbt (ap2 pi (natCode k) S) cb)))))
sbt_at_ap2 k S g ca cb =
  let spec : Term
      spec = ap2 pi (natCode k) S

      Y2 : Term
      Y2 = ap2 pi (codeFun2 g) (ap2 pi ca cb)

      input : Term
      input = ap2 pi (natCode tag_ap2) Y2

      -- tag_ap2 = 3 = s (s (s O)) = s (natCode 2).
      P_outer : Term
      P_outer = pi_succ_outer (natCode (suc (suc zero))) Y2

      prev : Term
      prev = ap2 (cov_spec baseValue_sbt stepFun_sbt) spec P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      ----------------------------------------------------------------
      step1 :
        Deriv (eqF (ap2 sbt spec input) (ap1 readOff_spec (ap2 sbtState spec input)))
      step1 = sbt_unfold spec input

      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ (natCode (suc (suc zero))) Y2

      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec input)
                    (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec (ap1 s P_outer)))
      cov_lift = congR (cov_spec baseValue_sbt stepFun_sbt) spec input_eq_sP_outer

      cov_step :
        Deriv (eqF (ap2 (cov_spec baseValue_sbt stepFun_sbt) spec (ap1 s P_outer))
                    (ap1 (state_step_spec stepFun_sbt) prev))
      cov_step = cov_spec_step_univ baseValue_sbt stepFun_sbt spec P_outer

      sbtState_eq :
        Deriv (eqF (ap2 sbtState spec input) (ap1 (state_step_spec stepFun_sbt) prev))
      sbtState_eq = ruleTrans cov_lift cov_step

      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 sbtState spec input))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbt) prev)))
      readOff_lift = cong1 readOff_spec sbtState_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbt) prev))
                    (ap2 stepFun_sbt (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ stepFun_sbt prev

      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq baseValue_sbt stepFun_sbt spec P_outer

      stepFun_lift :
        Deriv (eqF (ap2 stepFun_sbt (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun_sbt P_outer (ap1 Snd prev)))
      stepFun_lift = congL stepFun_sbt (ap1 Snd prev) Fst_prev_eq

      Post_eq :
        Deriv (eqF (ap2 stepFun_sbt P_outer (ap1 Snd prev))
                    (ap1 stepBody_sbt (ap2 pi P_outer (ap1 Snd prev))))
      Post_eq = axPost stepBody_sbt pi P_outer (ap1 Snd prev)

      ----------------------------------------------------------------
      -- Tag dispatch.  get_tag input_pkg' = natCode tag_ap2.

      get_newK_eq :
        Deriv (eqF (ap1 get_newK input_pkg') (ap1 s P_outer))
      get_newK_eq = get_newK_at_pi P_outer (ap1 Snd prev)

      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_ap2))
      Fst_input = axFst (natCode tag_ap2) Y2

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_ap2))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      ----------------------------------------------------------------
      isVar_value : Deriv (eqF (ap1 isVar input_pkg') O)
      isVar_value = isVar_at_natCodeAp2_O input_pkg' get_tag_value

      stepBody_to_ap1or :
        Deriv (eqF (ap1 stepBody_sbt input_pkg') (ap1 ap1_or_above input_pkg'))
      stepBody_to_ap1or = stepBody_sbt_to_ap1_or_above input_pkg' isVar_value

      -- isAp1 at ap2-input fires as O.
      isAp1_value : Deriv (eqF (ap1 isAp1 input_pkg') O)
      isAp1_value =
        let s1 :
              Deriv (eqF (ap1 isAp1 input_pkg')
                          (ap2 natEqF (ap1 get_tag input_pkg') (natCode tag_ap1)))
            s1 = isAp1_unfold input_pkg'

            s2 :
              Deriv (eqF (ap2 natEqF (ap1 get_tag input_pkg') (natCode tag_ap1))
                          (ap2 natEqF (natCode tag_ap2) (natCode tag_ap1)))
            s2 = congL natEqF (natCode tag_ap1) get_tag_value

            witness_ap2_neq_ap1 : NatNeqWitness tag_ap2 tag_ap1
            witness_ap2_neq_ap1 = natEqFalse_to_witness tag_ap1 tag_ap2 refl

            s3 : Deriv (eqF (ap2 natEqF (natCode tag_ap2) (natCode tag_ap1)) O)
            s3 = natEqF_at_neq tag_ap2 tag_ap1 witness_ap2_neq_ap1
        in ruleTrans s1 (ruleTrans s2 s3)

      isAp2_value : Deriv (eqF (ap1 isAp2 input_pkg') (ap1 s O))
      isAp2_value = isAp2_at_natCodeAp2_sO input_pkg' get_tag_value

      ap1or_to_ap2 :
        Deriv (eqF (ap1 ap1_or_above input_pkg') (ap1 ap2_branch input_pkg'))
      ap1or_to_ap2 = ap1_or_above_to_ap2_branch input_pkg' isAp1_value isAp2_value

      stepBody_to_ap2 :
        Deriv (eqF (ap1 stepBody_sbt input_pkg') (ap1 ap2_branch input_pkg'))
      stepBody_to_ap2 = ruleTrans stepBody_to_ap1or ap1or_to_ap2

      ----------------------------------------------------------------
      -- ap2_branch unfolding.

      ap2br_unfold :
        Deriv (eqF (ap1 ap2_branch input_pkg')
                    (ap2 pi (ap1 (constN tag_ap2) input_pkg')
                            (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input_pkg')))
      ap2br_unfold = ap2_branch_unfold input_pkg'

      constN_at :
        Deriv (eqF (ap1 (constN tag_ap2) input_pkg') (natCode tag_ap2))
      constN_at = constN_eq tag_ap2 input_pkg'

      ap2br_step1 :
        Deriv (eqF (ap1 ap2_branch input_pkg')
                    (ap2 pi (natCode tag_ap2)
                            (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input_pkg')))
      ap2br_step1 = ruleTrans ap2br_unfold
                      (congL pi (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input_pkg') constN_at)

      inner_unfold :
        Deriv (eqF (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input_pkg')
                    (ap2 pi (ap1 get_bodyFst_ap2 input_pkg') (ap1 (C pi get_val_ca get_val_cb) input_pkg')))
      inner_unfold = C_pi_bodyFst_valab_unfold input_pkg'

      ----------------------------------------------------------------
      -- get_bodyFst_ap2 input_pkg' = codeFun2 g.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_Y2 :
        Deriv (eqF (ap1 Snd input) Y2)
      Snd_input_eq_Y2 = axSnd (natCode tag_ap2) Y2

      Fst_Y2 :
        Deriv (eqF (ap1 Fst Y2) (codeFun2 g))
      Fst_Y2 = axFst (codeFun2 g) (ap2 pi ca cb)

      bodyFst_value :
        Deriv (eqF (ap1 get_bodyFst_ap2 input_pkg') (codeFun2 g))
      bodyFst_value =
        let s1 :
              Deriv (eqF (ap1 get_bodyFst_ap2 input_pkg') (ap1 Fst (ap1 Snd (ap1 s P_outer))))
            s1 = get_bodyFst_ap2_at_pi P_outer (ap1 Snd prev)
        in ruleTrans s1
             (ruleTrans (cong1 Fst Snd_sP_eq)
               (ruleTrans (cong1 Fst Snd_input_eq_Y2) Fst_Y2))

      ----------------------------------------------------------------
      -- get_val_ca input_pkg' = sbt spec ca (under leq ca P_outer).
      -- get_val_cb input_pkg' = sbt spec cb (under leq cb P_outer).

      inner_C_unfold :
        Deriv (eqF (ap1 (C pi get_val_ca get_val_cb) input_pkg')
                    (ap2 pi (ap1 get_val_ca input_pkg') (ap1 get_val_cb input_pkg')))
      inner_C_unfold = C_pi_valca_valcb_unfold input_pkg'

      -- val_ca: lookupAt get_ca_ap2 input_pkg'.
      val_ca_unfold :
        Deriv (eqF (ap1 get_val_ca input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg') (ap1 get_ca_ap2 input_pkg')))))
      val_ca_unfold = lookupAt_unfold get_ca_ap2 input_pkg'

      get_K_value :
        Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg') (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- get_ca_ap2 input_pkg' = ca.
      -- get_ca_ap2 input_pkg' = Fst (Snd (Snd (s P_outer))) = Fst (Snd (Snd input)) = Fst (Snd Y2) = Fst (pi ca cb) = ca.
      get_ca_value : Deriv (eqF (ap1 get_ca_ap2 input_pkg') ca)
      get_ca_value =
        let s1 :
              Deriv (eqF (ap1 get_ca_ap2 input_pkg')
                          (ap1 Fst (ap1 Snd (ap1 Snd (ap1 s P_outer)))))
            s1 = get_ca_ap2_at_pi P_outer (ap1 Snd prev)

            -- Snd (s P_outer) = Y2.
            Snd_sP_to_Y2 :
              Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y2)
            Snd_sP_to_Y2 = ruleTrans Snd_sP_eq Snd_input_eq_Y2

            -- Snd Y2 = Snd (pi (codeFun2 g) (pi ca cb)) = pi ca cb.
            Snd_Y2_eq :
              Deriv (eqF (ap1 Snd Y2) (ap2 pi ca cb))
            Snd_Y2_eq = axSnd (codeFun2 g) (ap2 pi ca cb)

            -- Fst (pi ca cb) = ca.
            Fst_pair :
              Deriv (eqF (ap1 Fst (ap2 pi ca cb)) ca)
            Fst_pair = axFst ca cb
        in ruleTrans s1
             (ruleTrans (cong1 Fst (cong1 Snd Snd_sP_to_Y2))
               (ruleTrans (cong1 Fst Snd_Y2_eq) Fst_pair))

      -- get_cb_ap2 input_pkg' = cb.
      get_cb_value : Deriv (eqF (ap1 get_cb_ap2 input_pkg') cb)
      get_cb_value =
        let s1 :
              Deriv (eqF (ap1 get_cb_ap2 input_pkg')
                          (ap1 Snd (ap1 Snd (ap1 Snd (ap1 s P_outer)))))
            s1 = get_cb_ap2_at_pi P_outer (ap1 Snd prev)

            Snd_sP_to_Y2 :
              Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y2)
            Snd_sP_to_Y2 = ruleTrans Snd_sP_eq Snd_input_eq_Y2

            Snd_Y2_eq :
              Deriv (eqF (ap1 Snd Y2) (ap2 pi ca cb))
            Snd_Y2_eq = axSnd (codeFun2 g) (ap2 pi ca cb)

            Snd_pair :
              Deriv (eqF (ap1 Snd (ap2 pi ca cb)) cb)
            Snd_pair = axSnd ca cb
        in ruleTrans s1
             (ruleTrans (cong1 Snd (cong1 Snd Snd_sP_to_Y2))
               (ruleTrans (cong1 Snd Snd_Y2_eq) Snd_pair))

      -- Reduce val_ca to HP_sbt ... ca P_outer.
      iter_arg_ca :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_ca_ap2 input_pkg'))
                    (ap2 sub P_outer ca))
      iter_arg_ca = ruleTrans (congL sub (ap1 get_ca_ap2 input_pkg') get_K_value)
                     (congR sub P_outer get_ca_value)

      iter_full_ca :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                          (ap2 sub (ap1 get_K input_pkg') (ap1 get_ca_ap2 input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer)
                          (ap2 sub P_outer ca)))
      iter_full_ca = ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_ca_ap2 input_pkg')) get_table_value)
                      (congR (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer) iter_arg_ca)

      val_ca_to_HP :
        Deriv (eqF (ap1 get_val_ca input_pkg')
                    (HPsbt baseValue_sbt stepFun_sbt spec ca P_outer))
      val_ca_to_HP = ruleTrans val_ca_unfold (cong1 Fst iter_full_ca)

      leq_ca_P : Deriv (leq ca P_outer)
      leq_ca_P = leq_ca_P_outer_ap2 g ca cb

      val_ca_value :
        Deriv (eqF (ap1 get_val_ca input_pkg') (ap2 sbt spec ca))
      val_ca_value = ruleTrans val_ca_to_HP
                       (HP_sbt_eq_sbt_under_leq spec ca P_outer leq_ca_P)

      -- Same for cb.
      val_cb_unfold :
        Deriv (eqF (ap1 get_val_cb input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg') (ap1 get_cb_ap2 input_pkg')))))
      val_cb_unfold = lookupAt_unfold get_cb_ap2 input_pkg'

      iter_arg_cb :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_cb_ap2 input_pkg'))
                    (ap2 sub P_outer cb))
      iter_arg_cb = ruleTrans (congL sub (ap1 get_cb_ap2 input_pkg') get_K_value)
                     (congR sub P_outer get_cb_value)

      iter_full_cb :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                          (ap2 sub (ap1 get_K input_pkg') (ap1 get_cb_ap2 input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer)
                          (ap2 sub P_outer cb)))
      iter_full_cb = ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_cb_ap2 input_pkg')) get_table_value)
                      (congR (iter Snd) (HistP_sbt baseValue_sbt stepFun_sbt spec P_outer) iter_arg_cb)

      val_cb_to_HP :
        Deriv (eqF (ap1 get_val_cb input_pkg')
                    (HPsbt baseValue_sbt stepFun_sbt spec cb P_outer))
      val_cb_to_HP = ruleTrans val_cb_unfold (cong1 Fst iter_full_cb)

      leq_cb_P : Deriv (leq cb P_outer)
      leq_cb_P = leq_cb_P_outer_ap2 g ca cb

      val_cb_value :
        Deriv (eqF (ap1 get_val_cb input_pkg') (ap2 sbt spec cb))
      val_cb_value = ruleTrans val_cb_to_HP
                       (HP_sbt_eq_sbt_under_leq spec cb P_outer leq_cb_P)

      ----------------------------------------------------------------
      -- Assemble inner pi (pi val_ca val_cb).
      pair_val_value :
        Deriv (eqF (ap1 (C pi get_val_ca get_val_cb) input_pkg')
                    (ap2 pi (ap2 sbt spec ca) (ap2 sbt spec cb)))
      pair_val_value =
        ruleTrans inner_C_unfold
          (ruleTrans (congL pi (ap1 get_val_cb input_pkg') val_ca_value)
                      (congR pi (ap2 sbt spec ca) val_cb_value))

      -- Assemble pi (codeFun2 g) (pi val_ca val_cb).
      inner_value :
        Deriv (eqF (ap1 (C pi get_bodyFst_ap2 (C pi get_val_ca get_val_cb)) input_pkg')
                    (ap2 pi (codeFun2 g) (ap2 pi (ap2 sbt spec ca) (ap2 sbt spec cb))))
      inner_value =
        ruleTrans inner_unfold
          (ruleTrans (congL pi (ap1 (C pi get_val_ca get_val_cb) input_pkg') bodyFst_value)
                      (congR pi (codeFun2 g) pair_val_value))

      ap2br_value :
        Deriv (eqF (ap1 ap2_branch input_pkg')
                    (ap2 pi (natCode tag_ap2)
                            (ap2 pi (codeFun2 g)
                                    (ap2 pi (ap2 sbt spec ca) (ap2 sbt spec cb)))))
      ap2br_value =
        ruleTrans ap2br_step1
          (congR pi (natCode tag_ap2) inner_value)

      ----------------------------------------------------------------
      chain_to_stepBody :
        Deriv (eqF (ap2 sbt spec input)
                    (ap1 stepBody_sbt input_pkg'))
      chain_to_stepBody =
        ruleTrans step1
          (ruleTrans readOff_lift
            (ruleTrans readOff_eval
              (ruleTrans stepFun_lift Post_eq)))

      chain_to_ap2br :
        Deriv (eqF (ap2 sbt spec input) (ap1 ap2_branch input_pkg'))
      chain_to_ap2br = ruleTrans chain_to_stepBody stepBody_to_ap2
  in ruleTrans chain_to_ap2br ap2br_value
