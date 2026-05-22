{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtSb -- discharge of the  sb  closure of  thmT  :
--
--   thmT_at_sb :
--     (cSpec cProofIdx : Term) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb) (ap2 pi cSpec cProofIdx)))
--                 (ap2 sbf cSpec (ap1 thmT cProofIdx)))
--
-- Universal in cSpec, cProofIdx : Term -- no Closed premise.
--
-- Architecture parallels  BRA4.SbfAtClosures.sbf_at_neg : tag dispatch
-- (isAx fails, isSb fires) + cov_spec_step_univ + readOff + Post +
-- sb_branch_thmT body = C sbf get_sb_spec get_sb_proof_val .  The sub-position
--  cProofIdx  is a formula code (an index into the thmT cov-table) ;
-- we use the standard lookupAt pattern against the thmT cov-table +
-- stability bridge  HP_thmT_eq_thmT_under_leq .

module BRA4.ThmTAtSb where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv
open import BRA4.CoVSpecFst
open import BRA4.SbT          using ( get_K ; get_inner ; get_table ; get_newK ; get_tag ; get_body
                                     ; lookupAt )
open import BRA4.SbF          using ( sbf )
open import BRA4.ThmT
open import BRA4.StabilityNatFuel
open import BRA4.Stability
open import BRA4.LeqMono
open import BRA4.PiPositivity

open import BRA3.Church          using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost ; I ; axI )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( condFork ; condFork_true_nc ; condFork_false
  ; constN ; constN_eq )
open import BRA3.Numerals        using ( pi_natCode )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq ; natEq_neq_gt )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; gtW ; ltW ; natEqF_at_neq ; decideNatNeq ; Not )
open import BRA3.RuleInst2       using ( natEq-refl ; true_neq_false )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; iter_base_univ )
import BRA3.ChurchT92

------------------------------------------------------------------------
-- NatNeqWitness for tag_sb /= tag_ax (so isAx fires O when tag = tag_sb).

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

  witness_sb_neq_ax : NatNeqWitness tag_sb tag_ax
  witness_sb_neq_ax = natEqFalse_to_witness tag_ax tag_sb refl

------------------------------------------------------------------------
-- Position-extraction closed forms at packaged input  pi A Y .
-- These mirror SbfAtClosures' private helpers (re-derived locally).

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
    let s1 : Deriv (eqF (ap1 get_newK (ap2 pi A Y))
                          (ap1 s (ap1 get_K (ap2 pi A Y))))
        s1 = compose1U_eq s get_K (ap2 pi A Y)
    in ruleTrans s1 (cong1 s (get_K_at_pi A Y))

  get_tag_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (ap1 Fst (ap1 s A)))
  get_tag_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_tag (ap2 pi A Y))
                          (ap1 Fst (ap1 get_newK (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_newK_at_pi A Y))

  get_body_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_body (ap2 pi A Y)) (ap1 Snd (ap1 s A)))
  get_body_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_body (ap2 pi A Y))
                          (ap1 Snd (ap1 get_newK (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_newK_at_pi A Y))

  get_table_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_table (ap2 pi A Y)) (ap1 Snd Y))
  get_table_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_table (ap2 pi A Y))
                          (ap1 Snd (ap1 get_inner (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_inner (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_inner_at_pi A Y))

  -- Branch-specific position closures.

  get_sb_spec_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_sb_spec (ap2 pi A Y))
                                  (ap1 Fst (ap1 Snd (ap1 s A))))
  get_sb_spec_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_sb_spec (ap2 pi A Y))
                          (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  get_sb_proof_idx_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_sb_proof_idx (ap2 pi A Y))
                                  (ap1 Snd (ap1 Snd (ap1 s A))))
  get_sb_proof_idx_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_sb_proof_idx (ap2 pi A Y))
                          (ap1 Snd (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_body_at_pi A Y))

------------------------------------------------------------------------
-- Cascade unfoldings.

private
  stepBody_thmT_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 stepBody_thmT input)
                (ap2 condFork
                  (ap1 (C pi ax_branch_thmT sb_or_above) input)
                  (ap1 isAx input)))
  stepBody_thmT_unfold input =
    ax_C condFork (C pi ax_branch_thmT sb_or_above) isAx input

  pi_ax_sbor_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi ax_branch_thmT sb_or_above) input)
                (ap2 pi (ap1 ax_branch_thmT input) (ap1 sb_or_above input)))
  pi_ax_sbor_unfold input =
    ax_C pi ax_branch_thmT sb_or_above input

  sb_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 sb_or_above input)
                (ap2 condFork
                  (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                  (ap1 isSb input)))
  sb_or_above_unfold input =
    ax_C condFork (C pi sb_branch_thmT sb3_or_above) isSb input

  pi_sb_mpor_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                (ap2 pi (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)))
  pi_sb_mpor_unfold input =
    ax_C pi sb_branch_thmT sb3_or_above input

  isAx_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isAx input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_ax)))
  isAx_unfold input =
    let s1 : Deriv (eqF (ap1 isAx input)
                          (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_ax) input)))
        s1 = ax_C natEqF get_tag (constN tag_ax) input
        s2 : Deriv (eqF (ap1 (constN tag_ax) input) (natCode tag_ax))
        s2 = constN_eq tag_ax input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isSb_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_sb)))
  isSb_unfold input =
    let s1 : Deriv (eqF (ap1 isSb input)
                          (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_sb) input)))
        s1 = ax_C natEqF get_tag (constN tag_sb) input
        s2 : Deriv (eqF (ap1 (constN tag_sb) input) (natCode tag_sb))
        s2 = constN_eq tag_sb input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

------------------------------------------------------------------------
-- Tag-firing helpers.

private
  isAx_at_natCodeSb_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_sb)) ->
    Deriv (eqF (ap1 isAx input) O)
  isAx_at_natCodeSb_O input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isAx input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_ax)))
        s1 = isAx_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_ax))
                      (ap2 natEqF (natCode tag_sb) (natCode tag_ax)))
        s2 = congL natEqF (natCode tag_ax) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_sb) (natCode tag_ax)) O)
        s3 = natEqF_at_neq tag_sb tag_ax witness_sb_neq_ax
    in ruleTrans s1 (ruleTrans s2 s3)

  isSb_at_natCodeSb_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_sb)) ->
    Deriv (eqF (ap1 isSb input) (ap1 s O))
  isSb_at_natCodeSb_sO input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isSb input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_sb)))
        s1 = isSb_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_sb))
                      (ap2 natEqF (natCode tag_sb) (natCode tag_sb)))
        s2 = congL natEqF (natCode tag_sb) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_sb) (natCode tag_sb)) (ap1 s O))
        s3 = natEq_eq tag_sb
    in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Cascade descents : stepBody_thmT -> sb_or_above -> sb_branch_thmT.

private
  stepBody_thmT_to_sb_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isAx input) O) ->
    Deriv (eqF (ap1 stepBody_thmT input) (ap1 sb_or_above input))
  stepBody_thmT_to_sb_or_above input isAx_O =
    let e1 :
          Deriv (eqF (ap1 stepBody_thmT input)
                      (ap2 condFork
                        (ap1 (C pi ax_branch_thmT sb_or_above) input)
                        (ap1 isAx input)))
        e1 = stepBody_thmT_unfold input

        isAx_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ax_branch_thmT sb_or_above) input)
                       (ap1 isAx input))
                      (ap2 condFork
                       (ap1 (C pi ax_branch_thmT sb_or_above) input)
                       O))
        isAx_subst =
          congR condFork (ap1 (C pi ax_branch_thmT sb_or_above) input) isAx_O

        cf_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ax_branch_thmT sb_or_above) input) O)
                      (ap1 Snd (ap1 (C pi ax_branch_thmT sb_or_above) input)))
        cf_to_Snd =
          condFork_false (ap1 (C pi ax_branch_thmT sb_or_above) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi ax_branch_thmT sb_or_above) input)
                      (ap2 pi (ap1 ax_branch_thmT input) (ap1 sb_or_above input)))
        pi_eq = pi_ax_sbor_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 ax_branch_thmT input) (ap1 sb_or_above input)))
                      (ap1 sb_or_above input))
        Snd_pi = axSnd (ap1 ax_branch_thmT input) (ap1 sb_or_above input)
    in ruleTrans e1
         (ruleTrans isAx_subst
           (ruleTrans cf_to_Snd
             (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  sb_or_above_to_sb :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input) (ap1 s O)) ->
    Deriv (eqF (ap1 sb_or_above input) (ap1 sb_branch_thmT input))
  sb_or_above_to_sb input isSb_sO =
    let e1 :
          Deriv (eqF (ap1 sb_or_above input)
                      (ap2 condFork
                        (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                        (ap1 isSb input)))
        e1 = sb_or_above_unfold input

        isSb_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                       (ap1 isSb input))
                      (ap2 condFork
                       (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                       (ap1 s O)))
        isSb_subst =
          congR condFork (ap1 (C pi sb_branch_thmT sb3_or_above) input) isSb_sO

        cf_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb_branch_thmT sb3_or_above) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi sb_branch_thmT sb3_or_above) input)))
        cf_to_Fst =
          condFork_true_nc (ap1 (C pi sb_branch_thmT sb3_or_above) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                      (ap2 pi (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)))
        pi_eq = pi_sb_mpor_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)))
                      (ap1 sb_branch_thmT input))
        Fst_pi = axFst (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)
    in ruleTrans e1
         (ruleTrans isSb_subst
           (ruleTrans cf_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

------------------------------------------------------------------------
-- HP_thmT stability bridge (mirrors HP_sbf_eq_sbf_under_leq).

private
  HP_thmT_eq_thmT_under_leq :
    (ct K : Term) ->
    Deriv (leq ct K) ->
    Deriv (eqF (HPsbt baseValue_thmT stepFun_thmT O ct K)
                (ap2 thmT_F2 O ct))
  HP_thmT_eq_thmT_under_leq ct K leq_ct_K =
    let stab :
          Deriv (eqF (HPsbt baseValue_thmT stepFun_thmT O ct K)
                      (HPsbt baseValue_thmT stepFun_thmT O ct ct))
        stab = mp (stabilityP_sbt_at baseValue_thmT stepFun_thmT O ct K) leq_ct_K

        subCT_O : Deriv (eqF (ap2 sub ct ct) O)
        subCT_O = sub_self ct

        iter_arg :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O ct) (ap2 sub ct ct))
                      (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O ct) O))
        iter_arg = congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O ct) subCT_O

        iter_base :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O ct) O)
                      (HistP_sbt baseValue_thmT stepFun_thmT O ct))
        iter_base = iter_base_univ Snd (HistP_sbt baseValue_thmT stepFun_thmT O ct)

        iter_full :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O ct) (ap2 sub ct ct))
                      (HistP_sbt baseValue_thmT stepFun_thmT O ct))
        iter_full = ruleTrans iter_arg iter_base

        HP_at_ct :
          Deriv (eqF (HPsbt baseValue_thmT stepFun_thmT O ct ct)
                      (ap1 Fst (HistP_sbt baseValue_thmT stepFun_thmT O ct)))
        HP_at_ct = cong1 Fst iter_full

        readOff_eq :
          Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseValue_thmT stepFun_thmT) O ct))
                      (ap1 Fst (HistP_sbt baseValue_thmT stepFun_thmT O ct)))
        readOff_eq = readOff_spec_eq (ap2 (cov_spec baseValue_thmT stepFun_thmT) O ct)

        readOff_eq_sym :
          Deriv (eqF (ap1 Fst (HistP_sbt baseValue_thmT stepFun_thmT O ct))
                      (ap1 readOff_spec (ap2 (cov_spec baseValue_thmT stepFun_thmT) O ct)))
        readOff_eq_sym = ruleSym readOff_eq

        thmTF2_eq :
          Deriv (eqF (ap2 thmT_F2 O ct)
                      (ap1 readOff_spec (ap2 thmTState O ct)))
        thmTF2_eq = thmT_unfold_F2 O ct

        thmTF2_eq_sym :
          Deriv (eqF (ap1 readOff_spec (ap2 thmTState O ct))
                      (ap2 thmT_F2 O ct))
        thmTF2_eq_sym = ruleSym thmTF2_eq

    in ruleTrans stab (ruleTrans HP_at_ct (ruleTrans readOff_eq_sym thmTF2_eq_sym))

------------------------------------------------------------------------
-- Leq lemma : leq cProofIdx (pi_succ_outer (natCode 1) (pi cSpec cProofIdx)).
--
-- Mirrors leq_cQ_P_outer_imp from SbfAtClosures : cProofIdx is the Snd
-- of the body pair  pi cSpec cProofIdx  and leq through  leq_pi_right
-- + leq_sigma_right .

leq_cProofIdx_P_outer_sb :
  (cSpec cProofIdx : Term) ->
  Deriv (leq cProofIdx (pi_succ_outer (natCode (suc zero)) (ap2 pi cSpec cProofIdx)))
leq_cProofIdx_P_outer_sb cSpec cProofIdx =
  let A : Term
      A = natCode (suc zero) -- natCode 1
      Y : Term
      Y = ap2 pi cSpec cProofIdx
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
      l1 : Deriv (leq cProofIdx Y)
      l1 = leq_pi_right cSpec cProofIdx
      l2 : Deriv (leq Y (ap2 sigma X Y))
      l2 = leq_sigma_right X Y
  in leq_trans cProofIdx Y (ap2 sigma X Y) l1 l2

------------------------------------------------------------------------
-- Branch body unfolding.

private
  sb_branch_thmT_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 sb_branch_thmT input)
                (ap2 sbf (ap1 get_sb_spec input) (ap1 get_sb_proof_val input)))
  sb_branch_thmT_unfold input =
    ax_C sbf get_sb_spec get_sb_proof_val input

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
        s4 :
          Deriv (eqF (ap2 (iter Snd) (ap1 get_table input) (ap1 (C sub get_K idx_F1) input))
                      (ap2 (iter Snd) (ap1 get_table input) (ap2 sub (ap1 get_K input) (ap1 idx_F1 input))))
        s4 = congR (iter Snd) (ap1 get_table input) s3
        s23 :
          Deriv (eqF (ap1 (C (iter Snd) get_table (C sub get_K idx_F1)) input)
                      (ap2 (iter Snd) (ap1 get_table input) (ap2 sub (ap1 get_K input) (ap1 idx_F1 input))))
        s23 = ruleTrans s2 s4
    in ruleTrans s1 (cong1 Fst s23)

------------------------------------------------------------------------
-- The main closure proof.

thmT_at_sb :
  (cSpec cProofIdx : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb) (ap2 pi cSpec cProofIdx)))
              (ap2 sbf cSpec (ap1 thmT cProofIdx)))
thmT_at_sb cSpec cProofIdx =
  let input : Term
      input = ap2 pi (natCode tag_sb) (ap2 pi cSpec cProofIdx)

      Y_body : Term
      Y_body = ap2 pi cSpec cProofIdx

      -- tag_sb = 2 , natCode tag_sb = s (natCode 1).
      A_outer : Term
      A_outer = natCode (suc zero) -- = natCode 1

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      -- (1) Unfold ap1 thmT input = ap2 thmT_F2 O input.
      step0 :
        Deriv (eqF (ap1 thmT input) (ap2 thmT_F2 O input))
      step0 = thmT_unfold input

      -- (2) thmT_F2 O input = readOff_spec (thmTState O input).
      step1 :
        Deriv (eqF (ap2 thmT_F2 O input) (ap1 readOff_spec (ap2 thmTState O input)))
      step1 = thmT_unfold_F2 O input

      -- (3) input = ap1 s P_outer via pi_at_succ.
      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ A_outer Y_body

      -- (4) cov_spec at s P_outer = state_step_spec stepFun_thmT prev.
      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseValue_thmT stepFun_thmT) O input)
                    (ap2 (cov_spec baseValue_thmT stepFun_thmT) O (ap1 s P_outer)))
      cov_lift = congR (cov_spec baseValue_thmT stepFun_thmT) O input_eq_sP_outer

      cov_step :
        Deriv (eqF (ap2 (cov_spec baseValue_thmT stepFun_thmT) O (ap1 s P_outer))
                    (ap1 (state_step_spec stepFun_thmT) prev))
      cov_step = cov_spec_step_univ baseValue_thmT stepFun_thmT O P_outer

      thmTState_eq :
        Deriv (eqF (ap2 thmTState O input)
                    (ap1 (state_step_spec stepFun_thmT) prev))
      thmTState_eq = ruleTrans cov_lift cov_step

      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 thmTState O input))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun_thmT) prev)))
      readOff_lift = cong1 readOff_spec thmTState_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun_thmT) prev))
                    (ap2 stepFun_thmT (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ stepFun_thmT prev

      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq baseValue_thmT stepFun_thmT O P_outer

      stepFun_lift :
        Deriv (eqF (ap2 stepFun_thmT (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun_thmT P_outer (ap1 Snd prev)))
      stepFun_lift = congL stepFun_thmT (ap1 Snd prev) Fst_prev_eq

      Post_eq :
        Deriv (eqF (ap2 stepFun_thmT P_outer (ap1 Snd prev))
                    (ap1 stepBody_thmT (ap2 pi P_outer (ap1 Snd prev))))
      Post_eq = axPost stepBody_thmT pi P_outer (ap1 Snd prev)

      -- (5) Tag dispatch.
      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_sb))
      Fst_input = axFst (natCode tag_sb) Y_body

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_sb))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isAx_value : Deriv (eqF (ap1 isAx input_pkg') O)
      isAx_value = isAx_at_natCodeSb_O input_pkg' get_tag_value

      isSb_value : Deriv (eqF (ap1 isSb input_pkg') (ap1 s O))
      isSb_value = isSb_at_natCodeSb_sO input_pkg' get_tag_value

      stepBody_to_sbor :
        Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 sb_or_above input_pkg'))
      stepBody_to_sbor = stepBody_thmT_to_sb_or_above input_pkg' isAx_value

      sbor_to_sb :
        Deriv (eqF (ap1 sb_or_above input_pkg') (ap1 sb_branch_thmT input_pkg'))
      sbor_to_sb = sb_or_above_to_sb input_pkg' isSb_value

      stepBody_to_sb :
        Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 sb_branch_thmT input_pkg'))
      stepBody_to_sb = ruleTrans stepBody_to_sbor sbor_to_sb

      -- (6) Branch body unfolding.
      sb_branch_value :
        Deriv (eqF (ap1 sb_branch_thmT input_pkg')
                    (ap2 sbf (ap1 get_sb_spec input_pkg')
                            (ap1 get_sb_proof_val input_pkg')))
      sb_branch_value = sb_branch_thmT_unfold input_pkg'

      -- (7) Compute get_sb_spec input_pkg' = cSpec.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_Yb :
        Deriv (eqF (ap1 Snd input) Y_body)
      Snd_input_eq_Yb = axSnd (natCode tag_sb) Y_body

      Snd_sP_to_Y :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y_body)
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

      get_sb_spec_value :
        Deriv (eqF (ap1 get_sb_spec input_pkg') cSpec)
      get_sb_spec_value =
        let s1 : Deriv (eqF (ap1 get_sb_spec input_pkg')
                              (ap1 Fst (ap1 Snd (ap1 s P_outer))))
            s1 = get_sb_spec_at_pi P_outer (ap1 Snd prev)
            Fst_Y : Deriv (eqF (ap1 Fst Y_body) cSpec)
            Fst_Y = axFst cSpec cProofIdx
        in ruleTrans s1 (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_sb_proof_idx_value :
        Deriv (eqF (ap1 get_sb_proof_idx input_pkg') cProofIdx)
      get_sb_proof_idx_value =
        let s1 : Deriv (eqF (ap1 get_sb_proof_idx input_pkg')
                              (ap1 Snd (ap1 Snd (ap1 s P_outer))))
            s1 = get_sb_proof_idx_at_pi P_outer (ap1 Snd prev)
            Snd_Y : Deriv (eqF (ap1 Snd Y_body) cProofIdx)
            Snd_Y = axSnd cSpec cProofIdx
        in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      get_K_value :
        Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg')
                    (HistP_sbt baseValue_thmT stepFun_thmT O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- (8) get_sb_proof_val input_pkg' = ap2 thmT_F2 O cProofIdx.
      val_unfold :
        Deriv (eqF (ap1 get_sb_proof_val input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg')
                                       (ap1 get_sb_proof_idx input_pkg')))))
      val_unfold = lookupAt_unfold get_sb_proof_idx input_pkg'

      iter_arg :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg')
                             (ap1 get_sb_proof_idx input_pkg'))
                    (ap2 sub P_outer cProofIdx))
      iter_arg = ruleTrans (congL sub (ap1 get_sb_proof_idx input_pkg') get_K_value)
                  (congR sub P_outer get_sb_proof_idx_value)

      iter_full :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                        (ap2 sub (ap1 get_K input_pkg') (ap1 get_sb_proof_idx input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                        (ap2 sub P_outer cProofIdx)))
      iter_full =
        ruleTrans
          (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_sb_proof_idx input_pkg'))
                  get_table_value)
          (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer) iter_arg)

      val_to_HP :
        Deriv (eqF (ap1 get_sb_proof_val input_pkg')
                    (HPsbt baseValue_thmT stepFun_thmT O cProofIdx P_outer))
      val_to_HP = ruleTrans val_unfold (cong1 Fst iter_full)

      leq_cP_P : Deriv (leq cProofIdx P_outer)
      leq_cP_P = leq_cProofIdx_P_outer_sb cSpec cProofIdx

      val_value :
        Deriv (eqF (ap1 get_sb_proof_val input_pkg') (ap2 thmT_F2 O cProofIdx))
      val_value = ruleTrans val_to_HP
                    (HP_thmT_eq_thmT_under_leq cProofIdx P_outer leq_cP_P)

      -- (9) Convert ap2 thmT_F2 O cProofIdx = ap1 thmT cProofIdx.
      thmT_cProof_eq :
        Deriv (eqF (ap2 thmT_F2 O cProofIdx) (ap1 thmT cProofIdx))
      thmT_cProof_eq = ruleSym (thmT_unfold cProofIdx)

      val_to_thmT :
        Deriv (eqF (ap1 get_sb_proof_val input_pkg') (ap1 thmT cProofIdx))
      val_to_thmT = ruleTrans val_value thmT_cProof_eq

      -- (10) Assemble sbf cSpec (ap1 thmT cProofIdx).
      sb_branch_to_sbf :
        Deriv (eqF (ap1 sb_branch_thmT input_pkg')
                    (ap2 sbf cSpec (ap1 thmT cProofIdx)))
      sb_branch_to_sbf =
        ruleTrans sb_branch_value
          (ruleTrans (congL sbf (ap1 get_sb_proof_val input_pkg') get_sb_spec_value)
                      (congR sbf cSpec val_to_thmT))

      -- (11) Chain everything.
      chain_to_stepBody :
        Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
      chain_to_stepBody =
        ruleTrans step0
          (ruleTrans step1
            (ruleTrans readOff_lift
              (ruleTrans readOff_eval
                (ruleTrans stepFun_lift Post_eq))))

      chain_to_sb_branch :
        Deriv (eqF (ap1 thmT input) (ap1 sb_branch_thmT input_pkg'))
      chain_to_sb_branch = ruleTrans chain_to_stepBody stepBody_to_sb
  in ruleTrans chain_to_sb_branch sb_branch_to_sbf
