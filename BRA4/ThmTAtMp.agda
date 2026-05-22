{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtMp -- discharge of the  mp  closure of  thmT  in the
-- UNIVERSAL form required by [[feedback-bra4-closures-universal-form]].
--
-- ======================================================================
-- PRIMARY closure :  thmT_at_mp  -- universal in arbitrary Terms.
-- ======================================================================
--
--   thmT_at_mp :
--     (cPImpIdx cAIdx : Term)
--     (cImpVal cAVal : Term)                                      -- ARBITRARY
--     (ih1 : Deriv (eqF (ap1 thmT cPImpIdx) cImpVal))
--     (ih2 : Deriv (eqF (ap1 thmT cAIdx)    cAVal))
--     (wf_tag : Deriv (eqF (ap1 Fst cImpVal) (natCode tag_imp)))
--     (wf_ant : Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)
--                          (ap1 s O))) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
--                 (ap1 Snd (ap1 Snd cImpVal)))
--
-- IH-consumable form per [[feedback-bra4-thmt-design]] : two recursive
-- thmT calls' values  cImpVal , cAVal  are passed in as ARBITRARY
-- Term-valued Deriv-equation hypotheses.  No codeFormula assumption.
-- Output is the raw  Snd (Snd cImpVal)  Term.
--
-- ======================================================================
-- COROLLARY :  thmT_at_mp_codeF  -- specialised to Formulas.
-- ======================================================================
--
-- Builds  wf_tag  via  axFst  on  codeFormula (imp P Q)  and  wf_ant  via
--  natEqF_codeF_refl + IH chain ; concludes the codeFormula-decoded output.

module BRA4.ThmTAtMp where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv
open import BRA4.CoVSpecFst
open import BRA4.SbT          using ( get_K ; get_inner ; get_table ; get_newK ; get_tag ; get_body
                                     ; lookupAt )
open import BRA4.ThmT
open import BRA4.StabilityNatFuel
open import BRA4.Stability
open import BRA4.LeqMono
open import BRA4.PiPositivity
open import BRA4.CodeCantorCollapse using ( natEqF_codeF_refl )

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

open import BRA4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impCong1 ; impCongL ; impCongR ; impEqTrans )

------------------------------------------------------------------------
-- NatNeqWitnesses : tag_mp /= tag_ax , tag_mp /= tag_sb .

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

  witness_mp_neq_ax : NatNeqWitness tag_mp tag_ax
  witness_mp_neq_ax = natEqFalse_to_witness tag_ax tag_mp refl

  witness_mp_neq_sb : NatNeqWitness tag_mp tag_sb
  witness_mp_neq_sb = natEqFalse_to_witness tag_sb tag_mp refl

  witness_mp_neq_sb2 : NatNeqWitness tag_mp tag_sb2
  witness_mp_neq_sb2 = natEqFalse_to_witness tag_sb2 tag_mp refl

  witness_mp_neq_sb3 : NatNeqWitness tag_mp tag_sb3
  witness_mp_neq_sb3 = natEqFalse_to_witness tag_sb3 tag_mp refl

------------------------------------------------------------------------
-- Position-extraction at packaged input  pi A Y .

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

  get_mp_pImp_idx_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_mp_pImp_idx (ap2 pi A Y))
                                  (ap1 Fst (ap1 Snd (ap1 s A))))
  get_mp_pImp_idx_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_mp_pImp_idx (ap2 pi A Y))
                          (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  get_mp_pA_idx_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_mp_pA_idx (ap2 pi A Y))
                                  (ap1 Snd (ap1 Snd (ap1 s A))))
  get_mp_pA_idx_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_mp_pA_idx (ap2 pi A Y))
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

  pi_sb_sb3or_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                (ap2 pi (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)))
  pi_sb_sb3or_unfold input =
    ax_C pi sb_branch_thmT sb3_or_above input

  sb3_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 sb3_or_above input)
                (ap2 condFork
                  (ap1 (C pi sb3_branch_thmT sb2_or_above) input)
                  (ap1 isSb3 input)))
  sb3_or_above_unfold input =
    ax_C condFork (C pi sb3_branch_thmT sb2_or_above) isSb3 input

  pi_sb3_sb2or_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi sb3_branch_thmT sb2_or_above) input)
                (ap2 pi (ap1 sb3_branch_thmT input) (ap1 sb2_or_above input)))
  pi_sb3_sb2or_unfold input =
    ax_C pi sb3_branch_thmT sb2_or_above input

  sb2_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 sb2_or_above input)
                (ap2 condFork
                  (ap1 (C pi sb2_branch_thmT mp_or_above) input)
                  (ap1 isSb2 input)))
  sb2_or_above_unfold input =
    ax_C condFork (C pi sb2_branch_thmT mp_or_above) isSb2 input

  pi_sb2_mpor_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi sb2_branch_thmT mp_or_above) input)
                (ap2 pi (ap1 sb2_branch_thmT input) (ap1 mp_or_above input)))
  pi_sb2_mpor_unfold input =
    ax_C pi sb2_branch_thmT mp_or_above input

  mp_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 mp_or_above input)
                (ap2 condFork
                  (ap1 (C pi mp_branch_thmT ind_or_else) input)
                  (ap1 isMp input)))
  mp_or_above_unfold input =
    ax_C condFork (C pi mp_branch_thmT ind_or_else) isMp input

  pi_mp_indor_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi mp_branch_thmT ind_or_else) input)
                (ap2 pi (ap1 mp_branch_thmT input) (ap1 ind_or_else input)))
  pi_mp_indor_unfold input =
    ax_C pi mp_branch_thmT ind_or_else input

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

  isMp_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isMp input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_mp)))
  isMp_unfold input =
    let s1 : Deriv (eqF (ap1 isMp input)
                          (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_mp) input)))
        s1 = ax_C natEqF get_tag (constN tag_mp) input
        s2 : Deriv (eqF (ap1 (constN tag_mp) input) (natCode tag_mp))
        s2 = constN_eq tag_mp input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isSb2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isSb2 input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_sb2)))
  isSb2_unfold input =
    let s1 : Deriv (eqF (ap1 isSb2 input)
                          (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_sb2) input)))
        s1 = ax_C natEqF get_tag (constN tag_sb2) input
        s2 : Deriv (eqF (ap1 (constN tag_sb2) input) (natCode tag_sb2))
        s2 = constN_eq tag_sb2 input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isSb3_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isSb3 input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_sb3)))
  isSb3_unfold input =
    let s1 : Deriv (eqF (ap1 isSb3 input)
                          (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_sb3) input)))
        s1 = ax_C natEqF get_tag (constN tag_sb3) input
        s2 : Deriv (eqF (ap1 (constN tag_sb3) input) (natCode tag_sb3))
        s2 = constN_eq tag_sb3 input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

------------------------------------------------------------------------
-- Tag-firing helpers.

private
  isAx_at_natCodeMp_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_mp)) ->
    Deriv (eqF (ap1 isAx input) O)
  isAx_at_natCodeMp_O input tag_eq_pf =
    let s1 : Deriv (eqF (ap1 isAx input)
                         (ap2 natEqF (ap1 get_tag input) (natCode tag_ax)))
        s1 = isAx_unfold input
        s2 : Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_ax))
                         (ap2 natEqF (natCode tag_mp) (natCode tag_ax)))
        s2 = congL natEqF (natCode tag_ax) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_mp) (natCode tag_ax)) O)
        s3 = natEqF_at_neq tag_mp tag_ax witness_mp_neq_ax
    in ruleTrans s1 (ruleTrans s2 s3)

  isSb_at_natCodeMp_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_mp)) ->
    Deriv (eqF (ap1 isSb input) O)
  isSb_at_natCodeMp_O input tag_eq_pf =
    let s1 : Deriv (eqF (ap1 isSb input)
                         (ap2 natEqF (ap1 get_tag input) (natCode tag_sb)))
        s1 = isSb_unfold input
        s2 : Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_sb))
                         (ap2 natEqF (natCode tag_mp) (natCode tag_sb)))
        s2 = congL natEqF (natCode tag_sb) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_mp) (natCode tag_sb)) O)
        s3 = natEqF_at_neq tag_mp tag_sb witness_mp_neq_sb
    in ruleTrans s1 (ruleTrans s2 s3)

  isSb2_at_natCodeMp_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_mp)) ->
    Deriv (eqF (ap1 isSb2 input) O)
  isSb2_at_natCodeMp_O input tag_eq_pf =
    let s1 : Deriv (eqF (ap1 isSb2 input)
                         (ap2 natEqF (ap1 get_tag input) (natCode tag_sb2)))
        s1 = isSb2_unfold input
        s2 : Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_sb2))
                         (ap2 natEqF (natCode tag_mp) (natCode tag_sb2)))
        s2 = congL natEqF (natCode tag_sb2) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_mp) (natCode tag_sb2)) O)
        s3 = natEqF_at_neq tag_mp tag_sb2 witness_mp_neq_sb2
    in ruleTrans s1 (ruleTrans s2 s3)

  isSb3_at_natCodeMp_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_mp)) ->
    Deriv (eqF (ap1 isSb3 input) O)
  isSb3_at_natCodeMp_O input tag_eq_pf =
    let s1 : Deriv (eqF (ap1 isSb3 input)
                         (ap2 natEqF (ap1 get_tag input) (natCode tag_sb3)))
        s1 = isSb3_unfold input
        s2 : Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_sb3))
                         (ap2 natEqF (natCode tag_mp) (natCode tag_sb3)))
        s2 = congL natEqF (natCode tag_sb3) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_mp) (natCode tag_sb3)) O)
        s3 = natEqF_at_neq tag_mp tag_sb3 witness_mp_neq_sb3
    in ruleTrans s1 (ruleTrans s2 s3)

  isMp_at_natCodeMp_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_mp)) ->
    Deriv (eqF (ap1 isMp input) (ap1 s O))
  isMp_at_natCodeMp_sO input tag_eq_pf =
    let s1 : Deriv (eqF (ap1 isMp input)
                         (ap2 natEqF (ap1 get_tag input) (natCode tag_mp)))
        s1 = isMp_unfold input
        s2 : Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_mp))
                         (ap2 natEqF (natCode tag_mp) (natCode tag_mp)))
        s2 = congL natEqF (natCode tag_mp) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_mp) (natCode tag_mp)) (ap1 s O))
        s3 = natEq_eq tag_mp
    in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Cascade descents : stepBody_thmT -> sb_or_above -> mp_or_above -> mp_branch_thmT.

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

        sub_isAx :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi ax_branch_thmT sb_or_above) input)
                       (ap1 isAx input))
                      (ap2 condFork
                       (ap1 (C pi ax_branch_thmT sb_or_above) input) O))
        sub_isAx =
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
    in ruleTrans e1 (ruleTrans sub_isAx
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  sb_or_above_to_sb3_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input) O) ->
    Deriv (eqF (ap1 sb_or_above input) (ap1 sb3_or_above input))
  sb_or_above_to_sb3_or_above input isSb_O =
    let e1 :
          Deriv (eqF (ap1 sb_or_above input)
                      (ap2 condFork
                        (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                        (ap1 isSb input)))
        e1 = sb_or_above_unfold input

        sub_isSb :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                       (ap1 isSb input))
                      (ap2 condFork
                       (ap1 (C pi sb_branch_thmT sb3_or_above) input) O))
        sub_isSb =
          congR condFork (ap1 (C pi sb_branch_thmT sb3_or_above) input) isSb_O

        cf_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb_branch_thmT sb3_or_above) input) O)
                      (ap1 Snd (ap1 (C pi sb_branch_thmT sb3_or_above) input)))
        cf_to_Snd =
          condFork_false (ap1 (C pi sb_branch_thmT sb3_or_above) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi sb_branch_thmT sb3_or_above) input)
                      (ap2 pi (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)))
        pi_eq = pi_sb_sb3or_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)))
                      (ap1 sb3_or_above input))
        Snd_pi = axSnd (ap1 sb_branch_thmT input) (ap1 sb3_or_above input)
    in ruleTrans e1 (ruleTrans sub_isSb
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  sb3_or_above_to_sb2_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isSb3 input) O) ->
    Deriv (eqF (ap1 sb3_or_above input) (ap1 sb2_or_above input))
  sb3_or_above_to_sb2_or_above input isSb3_O =
    let e1 :
          Deriv (eqF (ap1 sb3_or_above input)
                      (ap2 condFork
                        (ap1 (C pi sb3_branch_thmT sb2_or_above) input)
                        (ap1 isSb3 input)))
        e1 = sb3_or_above_unfold input

        sub_isSb3 :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb3_branch_thmT sb2_or_above) input)
                       (ap1 isSb3 input))
                      (ap2 condFork
                       (ap1 (C pi sb3_branch_thmT sb2_or_above) input) O))
        sub_isSb3 =
          congR condFork (ap1 (C pi sb3_branch_thmT sb2_or_above) input) isSb3_O

        cf_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb3_branch_thmT sb2_or_above) input) O)
                      (ap1 Snd (ap1 (C pi sb3_branch_thmT sb2_or_above) input)))
        cf_to_Snd =
          condFork_false (ap1 (C pi sb3_branch_thmT sb2_or_above) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi sb3_branch_thmT sb2_or_above) input)
                      (ap2 pi (ap1 sb3_branch_thmT input) (ap1 sb2_or_above input)))
        pi_eq = pi_sb3_sb2or_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 sb3_branch_thmT input) (ap1 sb2_or_above input)))
                      (ap1 sb2_or_above input))
        Snd_pi = axSnd (ap1 sb3_branch_thmT input) (ap1 sb2_or_above input)
    in ruleTrans e1 (ruleTrans sub_isSb3
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  sb2_or_above_to_mp_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isSb2 input) O) ->
    Deriv (eqF (ap1 sb2_or_above input) (ap1 mp_or_above input))
  sb2_or_above_to_mp_or_above input isSb2_O =
    let e1 :
          Deriv (eqF (ap1 sb2_or_above input)
                      (ap2 condFork
                        (ap1 (C pi sb2_branch_thmT mp_or_above) input)
                        (ap1 isSb2 input)))
        e1 = sb2_or_above_unfold input

        sub_isSb2 :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb2_branch_thmT mp_or_above) input)
                       (ap1 isSb2 input))
                      (ap2 condFork
                       (ap1 (C pi sb2_branch_thmT mp_or_above) input) O))
        sub_isSb2 =
          congR condFork (ap1 (C pi sb2_branch_thmT mp_or_above) input) isSb2_O

        cf_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi sb2_branch_thmT mp_or_above) input) O)
                      (ap1 Snd (ap1 (C pi sb2_branch_thmT mp_or_above) input)))
        cf_to_Snd =
          condFork_false (ap1 (C pi sb2_branch_thmT mp_or_above) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi sb2_branch_thmT mp_or_above) input)
                      (ap2 pi (ap1 sb2_branch_thmT input) (ap1 mp_or_above input)))
        pi_eq = pi_sb2_mpor_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 sb2_branch_thmT input) (ap1 mp_or_above input)))
                      (ap1 mp_or_above input))
        Snd_pi = axSnd (ap1 sb2_branch_thmT input) (ap1 mp_or_above input)
    in ruleTrans e1 (ruleTrans sub_isSb2
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  sb_or_above_to_mp_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input) O) ->
    Deriv (eqF (ap1 isSb3 input) O) ->
    Deriv (eqF (ap1 isSb2 input) O) ->
    Deriv (eqF (ap1 sb_or_above input) (ap1 mp_or_above input))
  sb_or_above_to_mp_or_above input isSb_O isSb3_O isSb2_O =
    ruleTrans (sb_or_above_to_sb3_or_above input isSb_O)
      (ruleTrans (sb3_or_above_to_sb2_or_above input isSb3_O)
                  (sb2_or_above_to_mp_or_above input isSb2_O))

  mp_or_above_to_mp :
    (input : Term) ->
    Deriv (eqF (ap1 isMp input) (ap1 s O)) ->
    Deriv (eqF (ap1 mp_or_above input) (ap1 mp_branch_thmT input))
  mp_or_above_to_mp input isMp_sO =
    let e1 :
          Deriv (eqF (ap1 mp_or_above input)
                      (ap2 condFork
                        (ap1 (C pi mp_branch_thmT ind_or_else) input)
                        (ap1 isMp input)))
        e1 = mp_or_above_unfold input

        sub_isMp :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi mp_branch_thmT ind_or_else) input)
                       (ap1 isMp input))
                      (ap2 condFork
                       (ap1 (C pi mp_branch_thmT ind_or_else) input) (ap1 s O)))
        sub_isMp =
          congR condFork (ap1 (C pi mp_branch_thmT ind_or_else) input) isMp_sO

        cf_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi mp_branch_thmT ind_or_else) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi mp_branch_thmT ind_or_else) input)))
        cf_to_Fst =
          condFork_true_nc (ap1 (C pi mp_branch_thmT ind_or_else) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi mp_branch_thmT ind_or_else) input)
                      (ap2 pi (ap1 mp_branch_thmT input) (ap1 ind_or_else input)))
        pi_eq = pi_mp_indor_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 mp_branch_thmT input) (ap1 ind_or_else input)))
                      (ap1 mp_branch_thmT input))
        Fst_pi = axFst (ap1 mp_branch_thmT input) (ap1 ind_or_else input)
    in ruleTrans e1 (ruleTrans sub_isMp
         (ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

------------------------------------------------------------------------
-- HP_thmT stability bridge (local re-derivation -- same as ThmTAtSb's).

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

        thmTF2_eq_sym :
          Deriv (eqF (ap1 readOff_spec (ap2 thmTState O ct))
                      (ap2 thmT_F2 O ct))
        thmTF2_eq_sym = ruleSym (thmT_unfold_F2 O ct)
    in ruleTrans stab
         (ruleTrans HP_at_ct (ruleTrans (ruleSym readOff_eq) thmTF2_eq_sym))

------------------------------------------------------------------------
-- Leq lemmas for the two sub-positions  cPImpIdx ,  cAIdx .

leq_cAIdx_P_outer_mp :
  (cPImpIdx cAIdx : Term) ->
  Deriv (leq cAIdx
            (pi_succ_outer (natCode (suc (suc zero)))
                           (ap2 pi cPImpIdx cAIdx)))
leq_cAIdx_P_outer_mp cPImpIdx cAIdx =
  let A : Term
      A = natCode (suc (suc zero))
      Y : Term
      Y = ap2 pi cPImpIdx cAIdx
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
      l1 : Deriv (leq cAIdx Y)
      l1 = leq_pi_right cPImpIdx cAIdx
      l2 : Deriv (leq Y (ap2 sigma X Y))
      l2 = leq_sigma_right X Y
  in leq_trans cAIdx Y (ap2 sigma X Y) l1 l2

leq_cPImpIdx_P_outer_mp :
  (cPImpIdx cAIdx : Term) ->
  Deriv (leq cPImpIdx
            (pi_succ_outer (natCode (suc (suc zero))) (ap2 pi cPImpIdx cAIdx)))
leq_cPImpIdx_P_outer_mp cPImpIdx cAIdx =
  let A : Term
      A = natCode (suc (suc zero))
      Y : Term
      Y = ap2 pi cPImpIdx cAIdx
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))

      l1 : Deriv (leq cPImpIdx (ap2 sigma cPImpIdx cAIdx))
      l1 = leq_sigma_left cPImpIdx cAIdx
      l2 : Deriv (leq (ap2 sigma cPImpIdx cAIdx) (ap1 tau (ap2 sigma cPImpIdx cAIdx)))
      l2 = ruleInst 0 (ap2 sigma cPImpIdx cAIdx) BRA3.ChurchT92.T92
      l3 : Deriv (leq (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                       (ap2 sigma (ap1 tau (ap2 sigma cPImpIdx cAIdx)) cAIdx))
      l3 = leq_sigma_left (ap1 tau (ap2 sigma cPImpIdx cAIdx)) cAIdx
      eqPi : Deriv (eqF (ap2 sigma (ap1 tau (ap2 sigma cPImpIdx cAIdx)) cAIdx)
                         (ap2 pi cPImpIdx cAIdx))
      eqPi = ruleSym (BRA4.LeqMono.T114_at cPImpIdx cAIdx)
      cong_sub :
        Deriv (eqF (ap2 sub (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                             (ap2 sigma (ap1 tau (ap2 sigma cPImpIdx cAIdx)) cAIdx))
                    (ap2 sub (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                             (ap2 pi cPImpIdx cAIdx)))
      cong_sub = congR sub (ap1 tau (ap2 sigma cPImpIdx cAIdx)) eqPi
      cong_sub_sym :
        Deriv (eqF (ap2 sub (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                             (ap2 pi cPImpIdx cAIdx))
                    (ap2 sub (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                             (ap2 sigma (ap1 tau (ap2 sigma cPImpIdx cAIdx)) cAIdx)))
      cong_sub_sym = ruleSym cong_sub
      l3_pi : Deriv (leq (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                         (ap2 pi cPImpIdx cAIdx))
      l3_pi = ruleTrans cong_sub_sym l3
      l12 : Deriv (leq cPImpIdx (ap1 tau (ap2 sigma cPImpIdx cAIdx)))
      l12 = leq_trans cPImpIdx (ap2 sigma cPImpIdx cAIdx)
                       (ap1 tau (ap2 sigma cPImpIdx cAIdx)) l1 l2
      l123 : Deriv (leq cPImpIdx (ap2 pi cPImpIdx cAIdx))
      l123 = leq_trans cPImpIdx (ap1 tau (ap2 sigma cPImpIdx cAIdx))
                        (ap2 pi cPImpIdx cAIdx) l12 l3_pi
      l5 : Deriv (leq Y (ap2 sigma X Y))
      l5 = leq_sigma_right X Y
  in leq_trans cPImpIdx Y (ap2 sigma X Y) l123 l5

------------------------------------------------------------------------
-- mp_branch_thmT / mp_inner unfoldings.

private
  mp_branch_thmT_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 mp_branch_thmT input)
                (ap2 condFork
                  (ap1 (C pi mp_inner baseValue_thmT) input)
                  (ap1 isMpTagOk input)))
  mp_branch_thmT_unfold input =
    ax_C condFork (C pi mp_inner baseValue_thmT) isMpTagOk input

  pi_mp_inner_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi mp_inner baseValue_thmT) input)
                (ap2 pi (ap1 mp_inner input) (ap1 baseValue_thmT input)))
  pi_mp_inner_unfold input =
    ax_C pi mp_inner baseValue_thmT input

  mp_inner_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 mp_inner input)
                (ap2 condFork
                  (ap1 (C pi get_pImp_cons baseValue_thmT) input)
                  (ap1 isMpAntOk input)))
  mp_inner_unfold input =
    ax_C condFork (C pi get_pImp_cons baseValue_thmT) isMpAntOk input

  pi_pImp_cons_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_pImp_cons baseValue_thmT) input)
                (ap2 pi (ap1 get_pImp_cons input) (ap1 baseValue_thmT input)))
  pi_pImp_cons_unfold input =
    ax_C pi get_pImp_cons baseValue_thmT input

  isMpTagOk_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isMpTagOk input)
                (ap2 natEqF (ap1 get_pImp_tag input) (natCode tag_imp)))
  isMpTagOk_unfold input =
    let s1 : Deriv (eqF (ap1 isMpTagOk input)
                         (ap2 natEqF (ap1 get_pImp_tag input) (ap1 (constN tag_imp) input)))
        s1 = ax_C natEqF get_pImp_tag (constN tag_imp) input
        s2 : Deriv (eqF (ap1 (constN tag_imp) input) (natCode tag_imp))
        s2 = constN_eq tag_imp input
    in ruleTrans s1 (congR natEqF (ap1 get_pImp_tag input) s2)

  isMpAntOk_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isMpAntOk input)
                (ap2 natEqF (ap1 get_pImp_ant input) (ap1 get_pA_val input)))
  isMpAntOk_unfold input =
    ax_C natEqF get_pImp_ant get_pA_val input

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

  get_pImp_tag_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_pImp_tag input)
                (ap1 Fst (ap1 get_pImp_val input)))
  get_pImp_tag_unfold input = compose1U_eq Fst get_pImp_val input

  get_pImp_body_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_pImp_body input)
                (ap1 Snd (ap1 get_pImp_val input)))
  get_pImp_body_unfold input = compose1U_eq Snd get_pImp_val input

  get_pImp_ant_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_pImp_ant input)
                (ap1 Fst (ap1 get_pImp_body input)))
  get_pImp_ant_unfold input = compose1U_eq Fst get_pImp_body input

  get_pImp_cons_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_pImp_cons input)
                (ap1 Snd (ap1 get_pImp_body input)))
  get_pImp_cons_unfold input = compose1U_eq Snd get_pImp_body input

------------------------------------------------------------------------
-- The main UNIVERSAL closure proof.

thmT_at_mp :
  (cPImpIdx cAIdx : Term)
  (cImpVal cAVal : Term)
  (ih1 : Deriv (eqF (ap1 thmT cPImpIdx) cImpVal))
  (ih2 : Deriv (eqF (ap1 thmT cAIdx)   cAVal))
  (wf_tag : Deriv (eqF (ap1 Fst cImpVal) (natCode tag_imp)))
  (wf_ant : Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)
                       (ap1 s O))) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
              (ap1 Snd (ap1 Snd cImpVal)))
thmT_at_mp cPImpIdx cAIdx cImpVal cAVal ih1 ih2 wf_tag wf_ant =
  let input : Term
      input = ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)

      Y_body : Term
      Y_body = ap2 pi cPImpIdx cAIdx

      A_outer : Term
      A_outer = natCode (suc (suc zero))

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      -- (1) Standard cov_spec_step_univ + readOff + Post chain.
      step0 :
        Deriv (eqF (ap1 thmT input) (ap2 thmT_F2 O input))
      step0 = thmT_unfold input

      step1 :
        Deriv (eqF (ap2 thmT_F2 O input)
                    (ap1 readOff_spec (ap2 thmTState O input)))
      step1 = thmT_unfold_F2 O input

      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ A_outer Y_body

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

      -- (2) Tag dispatch -> mp branch.
      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_mp))
      Fst_input = axFst (natCode tag_mp) Y_body

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_mp))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isAx_value : Deriv (eqF (ap1 isAx input_pkg') O)
      isAx_value = isAx_at_natCodeMp_O input_pkg' get_tag_value

      isSb_value : Deriv (eqF (ap1 isSb input_pkg') O)
      isSb_value = isSb_at_natCodeMp_O input_pkg' get_tag_value

      isSb3_value : Deriv (eqF (ap1 isSb3 input_pkg') O)
      isSb3_value = isSb3_at_natCodeMp_O input_pkg' get_tag_value

      isSb2_value : Deriv (eqF (ap1 isSb2 input_pkg') O)
      isSb2_value = isSb2_at_natCodeMp_O input_pkg' get_tag_value

      isMp_value : Deriv (eqF (ap1 isMp input_pkg') (ap1 s O))
      isMp_value = isMp_at_natCodeMp_sO input_pkg' get_tag_value

      stepBody_to_sbor :
        Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 sb_or_above input_pkg'))
      stepBody_to_sbor = stepBody_thmT_to_sb_or_above input_pkg' isAx_value

      sbor_to_mpor :
        Deriv (eqF (ap1 sb_or_above input_pkg') (ap1 mp_or_above input_pkg'))
      sbor_to_mpor = sb_or_above_to_mp_or_above input_pkg' isSb_value isSb3_value isSb2_value

      mpor_to_mp :
        Deriv (eqF (ap1 mp_or_above input_pkg') (ap1 mp_branch_thmT input_pkg'))
      mpor_to_mp = mp_or_above_to_mp input_pkg' isMp_value

      stepBody_to_mp :
        Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 mp_branch_thmT input_pkg'))
      stepBody_to_mp =
        ruleTrans stepBody_to_sbor (ruleTrans sbor_to_mpor mpor_to_mp)

      -- (3) Snd input_pkg' chain.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_Yb :
        Deriv (eqF (ap1 Snd input) Y_body)
      Snd_input_eq_Yb = axSnd (natCode tag_mp) Y_body

      Snd_sP_to_Y :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y_body)
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

      get_mp_pImp_idx_value :
        Deriv (eqF (ap1 get_mp_pImp_idx input_pkg') cPImpIdx)
      get_mp_pImp_idx_value =
        let s1 : Deriv (eqF (ap1 get_mp_pImp_idx input_pkg')
                              (ap1 Fst (ap1 Snd (ap1 s P_outer))))
            s1 = get_mp_pImp_idx_at_pi P_outer (ap1 Snd prev)
            Fst_Y : Deriv (eqF (ap1 Fst Y_body) cPImpIdx)
            Fst_Y = axFst cPImpIdx cAIdx
        in ruleTrans s1 (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_mp_pA_idx_value :
        Deriv (eqF (ap1 get_mp_pA_idx input_pkg') cAIdx)
      get_mp_pA_idx_value =
        let s1 : Deriv (eqF (ap1 get_mp_pA_idx input_pkg')
                              (ap1 Snd (ap1 Snd (ap1 s P_outer))))
            s1 = get_mp_pA_idx_at_pi P_outer (ap1 Snd prev)
            Snd_Y : Deriv (eqF (ap1 Snd Y_body) cAIdx)
            Snd_Y = axSnd cPImpIdx cAIdx
        in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      get_K_value :
        Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg')
                    (HistP_sbt baseValue_thmT stepFun_thmT O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- (4) pImp_val lookup = cImpVal (via IH1 + stability).
      pImp_val_unfold :
        Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg')
                                       (ap1 get_mp_pImp_idx input_pkg')))))
      pImp_val_unfold = lookupAt_unfold get_mp_pImp_idx input_pkg'

      pImp_iter_arg :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pImp_idx input_pkg'))
                    (ap2 sub P_outer cPImpIdx))
      pImp_iter_arg = ruleTrans (congL sub (ap1 get_mp_pImp_idx input_pkg') get_K_value)
                       (congR sub P_outer get_mp_pImp_idx_value)

      pImp_iter_full :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                        (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pImp_idx input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                        (ap2 sub P_outer cPImpIdx)))
      pImp_iter_full =
        ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                                (ap1 get_mp_pImp_idx input_pkg'))
                          get_table_value)
                  (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                          pImp_iter_arg)

      pImp_val_to_HP :
        Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg')
                    (HPsbt baseValue_thmT stepFun_thmT O cPImpIdx P_outer))
      pImp_val_to_HP = ruleTrans pImp_val_unfold (cong1 Fst pImp_iter_full)

      leq_pImp : Deriv (leq cPImpIdx P_outer)
      leq_pImp = leq_cPImpIdx_P_outer_mp cPImpIdx cAIdx

      pImp_val_value :
        Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg') (ap2 thmT_F2 O cPImpIdx))
      pImp_val_value = ruleTrans pImp_val_to_HP
                        (HP_thmT_eq_thmT_under_leq cPImpIdx P_outer leq_pImp)

      pImp_val_to_thmT :
        Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg') (ap1 thmT cPImpIdx))
      pImp_val_to_thmT = ruleTrans pImp_val_value (ruleSym (thmT_unfold cPImpIdx))

      get_pImp_val_eq :
        Deriv (eqF (ap1 get_pImp_val input_pkg') cImpVal)
      get_pImp_val_eq = ruleTrans pImp_val_to_thmT ih1

      -- (5) pA_val lookup = cAVal (via IH2 + stability).
      pA_val_unfold :
        Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg')
                                       (ap1 get_mp_pA_idx input_pkg')))))
      pA_val_unfold = lookupAt_unfold get_mp_pA_idx input_pkg'

      pA_iter_arg :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pA_idx input_pkg'))
                    (ap2 sub P_outer cAIdx))
      pA_iter_arg = ruleTrans (congL sub (ap1 get_mp_pA_idx input_pkg') get_K_value)
                     (congR sub P_outer get_mp_pA_idx_value)

      pA_iter_full :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                        (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pA_idx input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                        (ap2 sub P_outer cAIdx)))
      pA_iter_full =
        ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                                (ap1 get_mp_pA_idx input_pkg'))
                          get_table_value)
                  (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                          pA_iter_arg)

      pA_val_to_HP :
        Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg')
                    (HPsbt baseValue_thmT stepFun_thmT O cAIdx P_outer))
      pA_val_to_HP = ruleTrans pA_val_unfold (cong1 Fst pA_iter_full)

      leq_pA : Deriv (leq cAIdx P_outer)
      leq_pA = leq_cAIdx_P_outer_mp cPImpIdx cAIdx

      pA_val_value :
        Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg') (ap2 thmT_F2 O cAIdx))
      pA_val_value = ruleTrans pA_val_to_HP
                      (HP_thmT_eq_thmT_under_leq cAIdx P_outer leq_pA)

      pA_val_to_thmT :
        Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg') (ap1 thmT cAIdx))
      pA_val_to_thmT = ruleTrans pA_val_value (ruleSym (thmT_unfold cAIdx))

      get_pA_val_eq :
        Deriv (eqF (ap1 get_pA_val input_pkg') cAVal)
      get_pA_val_eq = ruleTrans pA_val_to_thmT ih2

      -- (6) isMpTagOk = sO via wf_tag (NO codeFormula assumption).
      -- get_pImp_tag input_pkg' = Fst (get_pImp_val input_pkg') = Fst cImpVal = natCode tag_imp.
      get_pImp_tag_step1 :
        Deriv (eqF (ap1 get_pImp_tag input_pkg')
                    (ap1 Fst (ap1 get_pImp_val input_pkg')))
      get_pImp_tag_step1 = get_pImp_tag_unfold input_pkg'

      get_pImp_tag_step2 :
        Deriv (eqF (ap1 Fst (ap1 get_pImp_val input_pkg'))
                    (ap1 Fst cImpVal))
      get_pImp_tag_step2 = cong1 Fst get_pImp_val_eq

      get_pImp_tag_value :
        Deriv (eqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp))
      get_pImp_tag_value =
        ruleTrans get_pImp_tag_step1 (ruleTrans get_pImp_tag_step2 wf_tag)

      isMpTagOk_step1 :
        Deriv (eqF (ap1 isMpTagOk input_pkg')
                    (ap2 natEqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp)))
      isMpTagOk_step1 = isMpTagOk_unfold input_pkg'

      isMpTagOk_step2 :
        Deriv (eqF (ap2 natEqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp))
                    (ap2 natEqF (natCode tag_imp) (natCode tag_imp)))
      isMpTagOk_step2 = congL natEqF (natCode tag_imp) get_pImp_tag_value

      isMpTagOk_step3 :
        Deriv (eqF (ap2 natEqF (natCode tag_imp) (natCode tag_imp)) (ap1 s O))
      isMpTagOk_step3 = natEq_eq tag_imp

      isMpTagOk_value :
        Deriv (eqF (ap1 isMpTagOk input_pkg') (ap1 s O))
      isMpTagOk_value = ruleTrans isMpTagOk_step1
                          (ruleTrans isMpTagOk_step2 isMpTagOk_step3)

      -- (7) isMpAntOk = sO via wf_ant + IH-substitution (NO codeFormula assumption).
      --
      -- get_pImp_ant input_pkg' = Fst (Snd cImpVal)
      --   (via IH1 substituted into get_pImp_val , then Snd , then Fst).
      -- get_pA_val input_pkg'   = cAVal  (via IH2).
      -- wf_ant : natEqF (Fst (Snd cImpVal)) cAVal = sO -- directly usable.

      get_pImp_body_eq :
        Deriv (eqF (ap1 get_pImp_body input_pkg')
                    (ap1 Snd (ap1 get_pImp_val input_pkg')))
      get_pImp_body_eq = get_pImp_body_unfold input_pkg'

      get_pImp_body_value :
        Deriv (eqF (ap1 get_pImp_body input_pkg') (ap1 Snd cImpVal))
      get_pImp_body_value =
        let s1 : Deriv (eqF (ap1 Snd (ap1 get_pImp_val input_pkg'))
                             (ap1 Snd cImpVal))
            s1 = cong1 Snd get_pImp_val_eq
        in ruleTrans get_pImp_body_eq s1

      get_pImp_ant_eq :
        Deriv (eqF (ap1 get_pImp_ant input_pkg')
                    (ap1 Fst (ap1 get_pImp_body input_pkg')))
      get_pImp_ant_eq = get_pImp_ant_unfold input_pkg'

      get_pImp_ant_value :
        Deriv (eqF (ap1 get_pImp_ant input_pkg') (ap1 Fst (ap1 Snd cImpVal)))
      get_pImp_ant_value =
        let s1 : Deriv (eqF (ap1 Fst (ap1 get_pImp_body input_pkg'))
                             (ap1 Fst (ap1 Snd cImpVal)))
            s1 = cong1 Fst get_pImp_body_value
        in ruleTrans get_pImp_ant_eq s1

      isMpAntOk_step1 :
        Deriv (eqF (ap1 isMpAntOk input_pkg')
                    (ap2 natEqF (ap1 get_pImp_ant input_pkg') (ap1 get_pA_val input_pkg')))
      isMpAntOk_step1 = isMpAntOk_unfold input_pkg'

      isMpAntOk_step2 :
        Deriv (eqF (ap2 natEqF (ap1 get_pImp_ant input_pkg') (ap1 get_pA_val input_pkg'))
                    (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) (ap1 get_pA_val input_pkg')))
      isMpAntOk_step2 = congL natEqF (ap1 get_pA_val input_pkg') get_pImp_ant_value

      isMpAntOk_step3 :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) (ap1 get_pA_val input_pkg'))
                    (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal))
      isMpAntOk_step3 = congR natEqF (ap1 Fst (ap1 Snd cImpVal)) get_pA_val_eq

      isMpAntOk_value :
        Deriv (eqF (ap1 isMpAntOk input_pkg') (ap1 s O))
      isMpAntOk_value =
        ruleTrans isMpAntOk_step1
          (ruleTrans isMpAntOk_step2
            (ruleTrans isMpAntOk_step3 wf_ant))

      -- (8) Descend mp_branch -> mp_inner -> get_pImp_cons.
      mp_branch_to_mp_inner :
        Deriv (eqF (ap1 mp_branch_thmT input_pkg') (ap1 mp_inner input_pkg'))
      mp_branch_to_mp_inner =
        let e1 :
              Deriv (eqF (ap1 mp_branch_thmT input_pkg')
                          (ap2 condFork
                            (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                            (ap1 isMpTagOk input_pkg')))
            e1 = mp_branch_thmT_unfold input_pkg'
            sub_isTag :
              Deriv (eqF (ap2 condFork
                           (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                           (ap1 isMpTagOk input_pkg'))
                          (ap2 condFork
                           (ap1 (C pi mp_inner baseValue_thmT) input_pkg') (ap1 s O)))
            sub_isTag = congR condFork (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                                       isMpTagOk_value
            cf_to_Fst :
              Deriv (eqF (ap2 condFork
                           (ap1 (C pi mp_inner baseValue_thmT) input_pkg') (ap1 s O))
                          (ap1 Fst (ap1 (C pi mp_inner baseValue_thmT) input_pkg')))
            cf_to_Fst = condFork_true_nc
                          (ap1 (C pi mp_inner baseValue_thmT) input_pkg') O
            pi_eq :
              Deriv (eqF (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                          (ap2 pi (ap1 mp_inner input_pkg') (ap1 baseValue_thmT input_pkg')))
            pi_eq = pi_mp_inner_unfold input_pkg'
            Fst_pi :
              Deriv (eqF (ap1 Fst (ap2 pi (ap1 mp_inner input_pkg')
                                             (ap1 baseValue_thmT input_pkg')))
                          (ap1 mp_inner input_pkg'))
            Fst_pi = axFst (ap1 mp_inner input_pkg') (ap1 baseValue_thmT input_pkg')
        in ruleTrans e1 (ruleTrans sub_isTag
             (ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

      mp_inner_to_pImp_cons :
        Deriv (eqF (ap1 mp_inner input_pkg') (ap1 get_pImp_cons input_pkg'))
      mp_inner_to_pImp_cons =
        let e1 :
              Deriv (eqF (ap1 mp_inner input_pkg')
                          (ap2 condFork
                            (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                            (ap1 isMpAntOk input_pkg')))
            e1 = mp_inner_unfold input_pkg'
            sub_isAnt :
              Deriv (eqF (ap2 condFork
                           (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                           (ap1 isMpAntOk input_pkg'))
                          (ap2 condFork
                           (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') (ap1 s O)))
            sub_isAnt = congR condFork (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                                       isMpAntOk_value
            cf_to_Fst :
              Deriv (eqF (ap2 condFork
                           (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') (ap1 s O))
                          (ap1 Fst (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')))
            cf_to_Fst = condFork_true_nc
                          (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') O
            pi_eq :
              Deriv (eqF (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                          (ap2 pi (ap1 get_pImp_cons input_pkg')
                                  (ap1 baseValue_thmT input_pkg')))
            pi_eq = pi_pImp_cons_unfold input_pkg'
            Fst_pi :
              Deriv (eqF (ap1 Fst (ap2 pi (ap1 get_pImp_cons input_pkg')
                                             (ap1 baseValue_thmT input_pkg')))
                          (ap1 get_pImp_cons input_pkg'))
            Fst_pi = axFst (ap1 get_pImp_cons input_pkg') (ap1 baseValue_thmT input_pkg')
        in ruleTrans e1 (ruleTrans sub_isAnt
             (ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

      -- (9) get_pImp_cons input_pkg' = Snd (Snd cImpVal) (raw output).
      get_pImp_cons_value :
        Deriv (eqF (ap1 get_pImp_cons input_pkg') (ap1 Snd (ap1 Snd cImpVal)))
      get_pImp_cons_value =
        let s1 : Deriv (eqF (ap1 get_pImp_cons input_pkg')
                             (ap1 Snd (ap1 get_pImp_body input_pkg')))
            s1 = get_pImp_cons_unfold input_pkg'
            s2 : Deriv (eqF (ap1 Snd (ap1 get_pImp_body input_pkg'))
                             (ap1 Snd (ap1 Snd cImpVal)))
            s2 = cong1 Snd get_pImp_body_value
        in ruleTrans s1 s2

      -- (10) Final assembly.
      chain_to_stepBody :
        Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
      chain_to_stepBody =
        ruleTrans step0
          (ruleTrans step1
            (ruleTrans readOff_lift
              (ruleTrans readOff_eval
                (ruleTrans stepFun_lift Post_eq))))

      chain_to_mp_branch :
        Deriv (eqF (ap1 thmT input) (ap1 mp_branch_thmT input_pkg'))
      chain_to_mp_branch = ruleTrans chain_to_stepBody stepBody_to_mp

      chain_to_mp_inner :
        Deriv (eqF (ap1 thmT input) (ap1 mp_inner input_pkg'))
      chain_to_mp_inner = ruleTrans chain_to_mp_branch mp_branch_to_mp_inner

      chain_to_pImp_cons :
        Deriv (eqF (ap1 thmT input) (ap1 get_pImp_cons input_pkg'))
      chain_to_pImp_cons = ruleTrans chain_to_mp_inner mp_inner_to_pImp_cons
  in ruleTrans chain_to_pImp_cons get_pImp_cons_value

------------------------------------------------------------------------
-- Corollary :  thmT_at_mp_codeF  -- specialised to Formulas.
--
-- Derives  wf_tag  via axFst on codeFormula (imp P Q) ;  wf_ant  via
--  natEqF_codeF_refl  on  codeFormula P  + IH-chained Leibniz substitution.
-- Concludes the codeFormula-decoded output.

thmT_at_mp_codeF :
  (cPImpIdx cAIdx : Term)
  (P Q : Formula)
  (ih_PQ : Deriv (eqF (ap1 thmT cPImpIdx) (codeFormula (imp P Q))))
  (ih_P  : Deriv (eqF (ap1 thmT cAIdx)   (codeFormula P))) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
              (codeFormula Q))
thmT_at_mp_codeF cPImpIdx cAIdx P Q ih_PQ ih_P =
  let cImpVal : Term
      cImpVal = codeFormula (imp P Q)

      cAVal : Term
      cAVal = codeFormula P

      -- wf_tag : Fst (codeFormula (imp P Q)) = natCode tag_imp.
      -- codeFormula (imp P Q) = pi (natCode tag_imp) (pi codeP codeQ).
      wf_tag : Deriv (eqF (ap1 Fst cImpVal) (natCode tag_imp))
      wf_tag = axFst (natCode tag_imp)
                     (ap2 pi (codeFormula P) (codeFormula Q))

      -- Fst (Snd cImpVal) = Fst (pi codeP codeQ) = codeFormula P = cAVal .
      -- So  natEqF (Fst (Snd cImpVal)) cAVal = natEqF codeP codeP = sO  via natEqF_codeF_refl P.
      Snd_imp :
        Deriv (eqF (ap1 Snd cImpVal) (ap2 pi (codeFormula P) (codeFormula Q)))
      Snd_imp = axSnd (natCode tag_imp) (ap2 pi (codeFormula P) (codeFormula Q))

      Fst_Snd_imp :
        Deriv (eqF (ap1 Fst (ap1 Snd cImpVal)) (codeFormula P))
      Fst_Snd_imp =
        ruleTrans (cong1 Fst Snd_imp) (axFst (codeFormula P) (codeFormula Q))

      ant_eq :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)
                    (ap2 natEqF (codeFormula P) (codeFormula P)))
      ant_eq = congL natEqF cAVal Fst_Snd_imp

      wf_ant :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal) (ap1 s O))
      wf_ant = ruleTrans ant_eq (natEqF_codeF_refl P)

      -- Output : Snd (Snd cImpVal) = Snd (pi codeP codeQ) = codeFormula Q .
      Snd_Snd_imp :
        Deriv (eqF (ap1 Snd (ap1 Snd cImpVal)) (codeFormula Q))
      Snd_Snd_imp =
        ruleTrans (cong1 Snd Snd_imp) (axSnd (codeFormula P) (codeFormula Q))

      raw : Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
                        (ap1 Snd (ap1 Snd cImpVal)))
      raw = thmT_at_mp cPImpIdx cAIdx cImpVal cAVal ih_PQ ih_P wf_tag wf_ant
  in ruleTrans raw Snd_Snd_imp

------------------------------------------------------------------------
-- Carneiro-lifted (imp P-prefixed) variant of thmT_at_mp .
--
-- The ih1 and ih2 inputs are imp-lifted ; wf_tag and wf_ant remain
-- unconditional (they depend only on cImpVal/cAVal's syntactic shape).
--
-- Construction: Mario's trick (ndw2.pdf p.19-20).  All closed
-- intermediate Derivs from thmT_at_mp's body are kept as-is (and
-- wrapped via impLift at use) ; only the post-IH chain is imp-translated
-- using impEqTrans / impCong* from BRA4.Thm12.ImpHelpers.

imp_thmT_at_mp :
  (P : Formula)
  (cPImpIdx cAIdx : Term)
  (cImpVal cAVal : Term)
  (imp_ih1 : Deriv (imp P (eqF (ap1 thmT cPImpIdx) cImpVal)))
  (imp_ih2 : Deriv (imp P (eqF (ap1 thmT cAIdx)   cAVal)))
  (wf_tag : Deriv (eqF (ap1 Fst cImpVal) (natCode tag_imp)))
  (wf_ant : Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)
                       (ap1 s O))) ->
  Deriv (imp P (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
                     (ap1 Snd (ap1 Snd cImpVal))))
imp_thmT_at_mp P cPImpIdx cAIdx cImpVal cAVal imp_ih1 imp_ih2 wf_tag wf_ant =
  let
    --========================================================================
    -- Closed pre-IH chain (replicated from thmT_at_mp's body, lines 844-1048).
    --========================================================================

    input : Term
    input = ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)

    Y_body : Term
    Y_body = ap2 pi cPImpIdx cAIdx

    A_outer : Term
    A_outer = natCode (suc (suc zero))

    P_outer : Term
    P_outer = pi_succ_outer A_outer Y_body

    prev : Term
    prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer

    input_pkg' : Term
    input_pkg' = ap2 pi P_outer (ap1 Snd prev)

    step0 : Deriv (eqF (ap1 thmT input) (ap2 thmT_F2 O input))
    step0 = thmT_unfold input

    step1 :
      Deriv (eqF (ap2 thmT_F2 O input)
                  (ap1 readOff_spec (ap2 thmTState O input)))
    step1 = thmT_unfold_F2 O input

    input_eq_sP_outer : Deriv (eqF input (ap1 s P_outer))
    input_eq_sP_outer = pi_at_succ A_outer Y_body

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

    Fst_prev_eq : Deriv (eqF (ap1 Fst prev) P_outer)
    Fst_prev_eq = fst_cov_spec_eq baseValue_thmT stepFun_thmT O P_outer

    stepFun_lift :
      Deriv (eqF (ap2 stepFun_thmT (ap1 Fst prev) (ap1 Snd prev))
                  (ap2 stepFun_thmT P_outer (ap1 Snd prev)))
    stepFun_lift = congL stepFun_thmT (ap1 Snd prev) Fst_prev_eq

    Post_eq :
      Deriv (eqF (ap2 stepFun_thmT P_outer (ap1 Snd prev))
                  (ap1 stepBody_thmT (ap2 pi P_outer (ap1 Snd prev))))
    Post_eq = axPost stepBody_thmT pi P_outer (ap1 Snd prev)

    get_tag_eq_Fst_sP :
      Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
    get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

    Fst_input : Deriv (eqF (ap1 Fst input) (natCode tag_mp))
    Fst_input = axFst (natCode tag_mp) Y_body

    Fst_sP_to_Fst_input : Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
    Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

    get_tag_value : Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_mp))
    get_tag_value = ruleTrans get_tag_eq_Fst_sP
                     (ruleTrans Fst_sP_to_Fst_input Fst_input)

    isAx_value : Deriv (eqF (ap1 isAx input_pkg') O)
    isAx_value = isAx_at_natCodeMp_O input_pkg' get_tag_value

    isSb_value : Deriv (eqF (ap1 isSb input_pkg') O)
    isSb_value = isSb_at_natCodeMp_O input_pkg' get_tag_value

    isSb3_value : Deriv (eqF (ap1 isSb3 input_pkg') O)
    isSb3_value = isSb3_at_natCodeMp_O input_pkg' get_tag_value

    isSb2_value : Deriv (eqF (ap1 isSb2 input_pkg') O)
    isSb2_value = isSb2_at_natCodeMp_O input_pkg' get_tag_value

    isMp_value : Deriv (eqF (ap1 isMp input_pkg') (ap1 s O))
    isMp_value = isMp_at_natCodeMp_sO input_pkg' get_tag_value

    stepBody_to_sbor :
      Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 sb_or_above input_pkg'))
    stepBody_to_sbor = stepBody_thmT_to_sb_or_above input_pkg' isAx_value

    sbor_to_mpor :
      Deriv (eqF (ap1 sb_or_above input_pkg') (ap1 mp_or_above input_pkg'))
    sbor_to_mpor = sb_or_above_to_mp_or_above input_pkg' isSb_value isSb3_value isSb2_value

    mpor_to_mp :
      Deriv (eqF (ap1 mp_or_above input_pkg') (ap1 mp_branch_thmT input_pkg'))
    mpor_to_mp = mp_or_above_to_mp input_pkg' isMp_value

    stepBody_to_mp :
      Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 mp_branch_thmT input_pkg'))
    stepBody_to_mp = ruleTrans stepBody_to_sbor (ruleTrans sbor_to_mpor mpor_to_mp)

    Snd_sP_eq : Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
    Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

    Snd_input_eq_Yb : Deriv (eqF (ap1 Snd input) Y_body)
    Snd_input_eq_Yb = axSnd (natCode tag_mp) Y_body

    Snd_sP_to_Y : Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y_body)
    Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

    get_mp_pImp_idx_value : Deriv (eqF (ap1 get_mp_pImp_idx input_pkg') cPImpIdx)
    get_mp_pImp_idx_value =
      let s1 : Deriv (eqF (ap1 get_mp_pImp_idx input_pkg')
                            (ap1 Fst (ap1 Snd (ap1 s P_outer))))
          s1 = get_mp_pImp_idx_at_pi P_outer (ap1 Snd prev)
          Fst_Y : Deriv (eqF (ap1 Fst Y_body) cPImpIdx)
          Fst_Y = axFst cPImpIdx cAIdx
      in ruleTrans s1 (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

    get_mp_pA_idx_value : Deriv (eqF (ap1 get_mp_pA_idx input_pkg') cAIdx)
    get_mp_pA_idx_value =
      let s1 : Deriv (eqF (ap1 get_mp_pA_idx input_pkg')
                            (ap1 Snd (ap1 Snd (ap1 s P_outer))))
          s1 = get_mp_pA_idx_at_pi P_outer (ap1 Snd prev)
          Snd_Y : Deriv (eqF (ap1 Snd Y_body) cAIdx)
          Snd_Y = axSnd cPImpIdx cAIdx
      in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

    get_K_value : Deriv (eqF (ap1 get_K input_pkg') P_outer)
    get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

    get_table_value :
      Deriv (eqF (ap1 get_table input_pkg')
                  (HistP_sbt baseValue_thmT stepFun_thmT O P_outer))
    get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

    pImp_val_unfold :
      Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg')
                  (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                            (ap2 sub (ap1 get_K input_pkg')
                                     (ap1 get_mp_pImp_idx input_pkg')))))
    pImp_val_unfold = lookupAt_unfold get_mp_pImp_idx input_pkg'

    pImp_iter_arg :
      Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pImp_idx input_pkg'))
                  (ap2 sub P_outer cPImpIdx))
    pImp_iter_arg = ruleTrans (congL sub (ap1 get_mp_pImp_idx input_pkg') get_K_value)
                     (congR sub P_outer get_mp_pImp_idx_value)

    pImp_iter_full :
      Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                      (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pImp_idx input_pkg')))
                  (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                      (ap2 sub P_outer cPImpIdx)))
    pImp_iter_full =
      ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                              (ap1 get_mp_pImp_idx input_pkg'))
                        get_table_value)
                (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                        pImp_iter_arg)

    pImp_val_to_HP :
      Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg')
                  (HPsbt baseValue_thmT stepFun_thmT O cPImpIdx P_outer))
    pImp_val_to_HP = ruleTrans pImp_val_unfold (cong1 Fst pImp_iter_full)

    leq_pImp : Deriv (leq cPImpIdx P_outer)
    leq_pImp = leq_cPImpIdx_P_outer_mp cPImpIdx cAIdx

    pImp_val_value :
      Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg') (ap2 thmT_F2 O cPImpIdx))
    pImp_val_value = ruleTrans pImp_val_to_HP
                      (HP_thmT_eq_thmT_under_leq cPImpIdx P_outer leq_pImp)

    pImp_val_to_thmT :
      Deriv (eqF (ap1 (lookupAt get_mp_pImp_idx) input_pkg') (ap1 thmT cPImpIdx))
    pImp_val_to_thmT = ruleTrans pImp_val_value (ruleSym (thmT_unfold cPImpIdx))

    --========================================================================
    -- *** IH-USE 1: imp-lift get_pImp_val_eq using imp_ih1 . ***
    --========================================================================

    imp_get_pImp_val_eq :
      Deriv (imp P (eqF (ap1 get_pImp_val input_pkg') cImpVal))
    imp_get_pImp_val_eq =
      impEqTrans _ (ap1 thmT cPImpIdx) cImpVal
        (impLift {P} pImp_val_to_thmT)
        imp_ih1

    -- (Continuing closed chain for pA.)

    pA_val_unfold :
      Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg')
                  (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                            (ap2 sub (ap1 get_K input_pkg')
                                     (ap1 get_mp_pA_idx input_pkg')))))
    pA_val_unfold = lookupAt_unfold get_mp_pA_idx input_pkg'

    pA_iter_arg :
      Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pA_idx input_pkg'))
                  (ap2 sub P_outer cAIdx))
    pA_iter_arg = ruleTrans (congL sub (ap1 get_mp_pA_idx input_pkg') get_K_value)
                   (congR sub P_outer get_mp_pA_idx_value)

    pA_iter_full :
      Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                      (ap2 sub (ap1 get_K input_pkg') (ap1 get_mp_pA_idx input_pkg')))
                  (ap2 (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                      (ap2 sub P_outer cAIdx)))
    pA_iter_full =
      ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                              (ap1 get_mp_pA_idx input_pkg'))
                        get_table_value)
                (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                        pA_iter_arg)

    pA_val_to_HP :
      Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg')
                  (HPsbt baseValue_thmT stepFun_thmT O cAIdx P_outer))
    pA_val_to_HP = ruleTrans pA_val_unfold (cong1 Fst pA_iter_full)

    leq_pA : Deriv (leq cAIdx P_outer)
    leq_pA = leq_cAIdx_P_outer_mp cPImpIdx cAIdx

    pA_val_value :
      Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg') (ap2 thmT_F2 O cAIdx))
    pA_val_value = ruleTrans pA_val_to_HP
                    (HP_thmT_eq_thmT_under_leq cAIdx P_outer leq_pA)

    pA_val_to_thmT :
      Deriv (eqF (ap1 (lookupAt get_mp_pA_idx) input_pkg') (ap1 thmT cAIdx))
    pA_val_to_thmT = ruleTrans pA_val_value (ruleSym (thmT_unfold cAIdx))

    --========================================================================
    -- *** IH-USE 2: imp-lift get_pA_val_eq using imp_ih2 . ***
    --========================================================================

    imp_get_pA_val_eq :
      Deriv (imp P (eqF (ap1 get_pA_val input_pkg') cAVal))
    imp_get_pA_val_eq =
      impEqTrans _ (ap1 thmT cAIdx) cAVal
        (impLift {P} pA_val_to_thmT)
        imp_ih2

    --========================================================================
    -- Post-IH imp-translated chain.
    --========================================================================

    -- (6) isMpTagOk via wf_tag + imp_get_pImp_val_eq .
    get_pImp_tag_step1 :
      Deriv (eqF (ap1 get_pImp_tag input_pkg')
                  (ap1 Fst (ap1 get_pImp_val input_pkg')))
    get_pImp_tag_step1 = get_pImp_tag_unfold input_pkg'

    imp_get_pImp_tag_step2 :
      Deriv (imp P (eqF (ap1 Fst (ap1 get_pImp_val input_pkg'))
                         (ap1 Fst cImpVal)))
    imp_get_pImp_tag_step2 =
      impCong1 Fst (ap1 get_pImp_val input_pkg') cImpVal imp_get_pImp_val_eq

    imp_get_pImp_tag_value :
      Deriv (imp P (eqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp)))
    imp_get_pImp_tag_value =
      impEqTrans _ (ap1 Fst (ap1 get_pImp_val input_pkg')) (natCode tag_imp)
        (impLift {P} get_pImp_tag_step1)
        (impEqTrans _ (ap1 Fst cImpVal) (natCode tag_imp)
          imp_get_pImp_tag_step2
          (impLift {P} wf_tag))

    isMpTagOk_step1 :
      Deriv (eqF (ap1 isMpTagOk input_pkg')
                  (ap2 natEqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp)))
    isMpTagOk_step1 = isMpTagOk_unfold input_pkg'

    imp_isMpTagOk_step2 :
      Deriv (imp P (eqF (ap2 natEqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp))
                         (ap2 natEqF (natCode tag_imp) (natCode tag_imp))))
    imp_isMpTagOk_step2 =
      impCongL natEqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp) (natCode tag_imp)
        imp_get_pImp_tag_value

    isMpTagOk_step3 :
      Deriv (eqF (ap2 natEqF (natCode tag_imp) (natCode tag_imp)) (ap1 s O))
    isMpTagOk_step3 = natEq_eq tag_imp

    imp_isMpTagOk_value :
      Deriv (imp P (eqF (ap1 isMpTagOk input_pkg') (ap1 s O)))
    imp_isMpTagOk_value =
      impEqTrans _ (ap2 natEqF (ap1 get_pImp_tag input_pkg') (natCode tag_imp)) (ap1 s O)
        (impLift {P} isMpTagOk_step1)
        (impEqTrans _ (ap2 natEqF (natCode tag_imp) (natCode tag_imp)) (ap1 s O)
          imp_isMpTagOk_step2
          (impLift {P} isMpTagOk_step3))

    -- (7) isMpAntOk via wf_ant + imp_get_pImp_val_eq + imp_get_pA_val_eq.
    get_pImp_body_eq :
      Deriv (eqF (ap1 get_pImp_body input_pkg')
                  (ap1 Snd (ap1 get_pImp_val input_pkg')))
    get_pImp_body_eq = get_pImp_body_unfold input_pkg'

    imp_get_pImp_body_value :
      Deriv (imp P (eqF (ap1 get_pImp_body input_pkg') (ap1 Snd cImpVal)))
    imp_get_pImp_body_value =
      impEqTrans _ (ap1 Snd (ap1 get_pImp_val input_pkg')) (ap1 Snd cImpVal)
        (impLift {P} get_pImp_body_eq)
        (impCong1 Snd (ap1 get_pImp_val input_pkg') cImpVal imp_get_pImp_val_eq)

    get_pImp_ant_eq :
      Deriv (eqF (ap1 get_pImp_ant input_pkg')
                  (ap1 Fst (ap1 get_pImp_body input_pkg')))
    get_pImp_ant_eq = get_pImp_ant_unfold input_pkg'

    imp_get_pImp_ant_value :
      Deriv (imp P (eqF (ap1 get_pImp_ant input_pkg') (ap1 Fst (ap1 Snd cImpVal))))
    imp_get_pImp_ant_value =
      impEqTrans _ (ap1 Fst (ap1 get_pImp_body input_pkg')) (ap1 Fst (ap1 Snd cImpVal))
        (impLift {P} get_pImp_ant_eq)
        (impCong1 Fst (ap1 get_pImp_body input_pkg') (ap1 Snd cImpVal) imp_get_pImp_body_value)

    isMpAntOk_step1 :
      Deriv (eqF (ap1 isMpAntOk input_pkg')
                  (ap2 natEqF (ap1 get_pImp_ant input_pkg') (ap1 get_pA_val input_pkg')))
    isMpAntOk_step1 = isMpAntOk_unfold input_pkg'

    imp_isMpAntOk_step2 :
      Deriv (imp P (eqF (ap2 natEqF (ap1 get_pImp_ant input_pkg') (ap1 get_pA_val input_pkg'))
                         (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) (ap1 get_pA_val input_pkg'))))
    imp_isMpAntOk_step2 =
      impCongL natEqF (ap1 get_pImp_ant input_pkg') (ap1 Fst (ap1 Snd cImpVal)) (ap1 get_pA_val input_pkg')
        imp_get_pImp_ant_value

    imp_isMpAntOk_step3 :
      Deriv (imp P (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) (ap1 get_pA_val input_pkg'))
                         (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)))
    imp_isMpAntOk_step3 =
      impCongR natEqF (ap1 get_pA_val input_pkg') cAVal (ap1 Fst (ap1 Snd cImpVal))
        imp_get_pA_val_eq

    imp_isMpAntOk_value :
      Deriv (imp P (eqF (ap1 isMpAntOk input_pkg') (ap1 s O)))
    imp_isMpAntOk_value =
      impEqTrans _ (ap2 natEqF (ap1 get_pImp_ant input_pkg') (ap1 get_pA_val input_pkg')) (ap1 s O)
        (impLift {P} isMpAntOk_step1)
        (impEqTrans _ (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) (ap1 get_pA_val input_pkg')) (ap1 s O)
          imp_isMpAntOk_step2
          (impEqTrans _ (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal) (ap1 s O)
            imp_isMpAntOk_step3
            (impLift {P} wf_ant)))

    -- (8) mp_branch -> mp_inner -> get_pImp_cons (imp-translated).
    imp_mp_branch_to_mp_inner :
      Deriv (imp P (eqF (ap1 mp_branch_thmT input_pkg') (ap1 mp_inner input_pkg')))
    imp_mp_branch_to_mp_inner =
      let e1 : Deriv (eqF (ap1 mp_branch_thmT input_pkg')
                          (ap2 condFork
                            (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                            (ap1 isMpTagOk input_pkg')))
          e1 = mp_branch_thmT_unfold input_pkg'

          imp_sub_isTag :
            Deriv (imp P (eqF (ap2 condFork
                                 (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                                 (ap1 isMpTagOk input_pkg'))
                                (ap2 condFork
                                 (ap1 (C pi mp_inner baseValue_thmT) input_pkg') (ap1 s O))))
          imp_sub_isTag =
            impCongR condFork (ap1 isMpTagOk input_pkg') (ap1 s O)
              (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
              imp_isMpTagOk_value

          cf_to_Fst :
            Deriv (eqF (ap2 condFork
                         (ap1 (C pi mp_inner baseValue_thmT) input_pkg') (ap1 s O))
                        (ap1 Fst (ap1 (C pi mp_inner baseValue_thmT) input_pkg')))
          cf_to_Fst = condFork_true_nc
                        (ap1 (C pi mp_inner baseValue_thmT) input_pkg') O

          pi_eq :
            Deriv (eqF (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                        (ap2 pi (ap1 mp_inner input_pkg') (ap1 baseValue_thmT input_pkg')))
          pi_eq = pi_mp_inner_unfold input_pkg'

          Fst_pi :
            Deriv (eqF (ap1 Fst (ap2 pi (ap1 mp_inner input_pkg')
                                           (ap1 baseValue_thmT input_pkg')))
                        (ap1 mp_inner input_pkg'))
          Fst_pi = axFst (ap1 mp_inner input_pkg') (ap1 baseValue_thmT input_pkg')

          tail_closed :
            Deriv (eqF (ap2 condFork
                         (ap1 (C pi mp_inner baseValue_thmT) input_pkg') (ap1 s O))
                        (ap1 mp_inner input_pkg'))
          tail_closed = ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)
      in impEqTrans _ (ap2 condFork (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                                     (ap1 isMpTagOk input_pkg'))
                      (ap1 mp_inner input_pkg')
           (impLift {P} e1)
           (impEqTrans _ (ap2 condFork (ap1 (C pi mp_inner baseValue_thmT) input_pkg')
                                        (ap1 s O))
                         (ap1 mp_inner input_pkg')
              imp_sub_isTag
              (impLift {P} tail_closed))

    imp_mp_inner_to_pImp_cons :
      Deriv (imp P (eqF (ap1 mp_inner input_pkg') (ap1 get_pImp_cons input_pkg')))
    imp_mp_inner_to_pImp_cons =
      let e1 : Deriv (eqF (ap1 mp_inner input_pkg')
                          (ap2 condFork
                            (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                            (ap1 isMpAntOk input_pkg')))
          e1 = mp_inner_unfold input_pkg'

          imp_sub_isAnt :
            Deriv (imp P (eqF (ap2 condFork
                                 (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                                 (ap1 isMpAntOk input_pkg'))
                                (ap2 condFork
                                 (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') (ap1 s O))))
          imp_sub_isAnt =
            impCongR condFork (ap1 isMpAntOk input_pkg') (ap1 s O)
              (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
              imp_isMpAntOk_value

          cf_to_Fst :
            Deriv (eqF (ap2 condFork
                         (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') (ap1 s O))
                        (ap1 Fst (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')))
          cf_to_Fst = condFork_true_nc
                        (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') O

          pi_eq :
            Deriv (eqF (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                        (ap2 pi (ap1 get_pImp_cons input_pkg')
                                (ap1 baseValue_thmT input_pkg')))
          pi_eq = pi_pImp_cons_unfold input_pkg'

          Fst_pi :
            Deriv (eqF (ap1 Fst (ap2 pi (ap1 get_pImp_cons input_pkg')
                                           (ap1 baseValue_thmT input_pkg')))
                        (ap1 get_pImp_cons input_pkg'))
          Fst_pi = axFst (ap1 get_pImp_cons input_pkg') (ap1 baseValue_thmT input_pkg')

          tail_closed :
            Deriv (eqF (ap2 condFork
                         (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg') (ap1 s O))
                        (ap1 get_pImp_cons input_pkg'))
          tail_closed = ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)
      in impEqTrans _ (ap2 condFork (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                                     (ap1 isMpAntOk input_pkg'))
                      (ap1 get_pImp_cons input_pkg')
           (impLift {P} e1)
           (impEqTrans _ (ap2 condFork (ap1 (C pi get_pImp_cons baseValue_thmT) input_pkg')
                                        (ap1 s O))
                         (ap1 get_pImp_cons input_pkg')
              imp_sub_isAnt
              (impLift {P} tail_closed))

    -- (9) get_pImp_cons input_pkg' = Snd (Snd cImpVal) .
    get_pImp_cons_unfold_eq :
      Deriv (eqF (ap1 get_pImp_cons input_pkg')
                  (ap1 Snd (ap1 get_pImp_body input_pkg')))
    get_pImp_cons_unfold_eq = get_pImp_cons_unfold input_pkg'

    imp_get_pImp_cons_value :
      Deriv (imp P (eqF (ap1 get_pImp_cons input_pkg') (ap1 Snd (ap1 Snd cImpVal))))
    imp_get_pImp_cons_value =
      impEqTrans _ (ap1 Snd (ap1 get_pImp_body input_pkg')) (ap1 Snd (ap1 Snd cImpVal))
        (impLift {P} get_pImp_cons_unfold_eq)
        (impCong1 Snd (ap1 get_pImp_body input_pkg') (ap1 Snd cImpVal) imp_get_pImp_body_value)

    -- (10) Final assembly.
    chain_to_stepBody :
      Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
    chain_to_stepBody =
      ruleTrans step0
        (ruleTrans step1
          (ruleTrans readOff_lift
            (ruleTrans readOff_eval
              (ruleTrans stepFun_lift Post_eq))))

    chain_to_mp_branch :
      Deriv (eqF (ap1 thmT input) (ap1 mp_branch_thmT input_pkg'))
    chain_to_mp_branch = ruleTrans chain_to_stepBody stepBody_to_mp

    imp_chain_to_mp_inner :
      Deriv (imp P (eqF (ap1 thmT input) (ap1 mp_inner input_pkg')))
    imp_chain_to_mp_inner =
      impEqTrans _ (ap1 mp_branch_thmT input_pkg') (ap1 mp_inner input_pkg')
        (impLift {P} chain_to_mp_branch)
        imp_mp_branch_to_mp_inner

    imp_chain_to_pImp_cons :
      Deriv (imp P (eqF (ap1 thmT input) (ap1 get_pImp_cons input_pkg')))
    imp_chain_to_pImp_cons =
      impEqTrans _ (ap1 mp_inner input_pkg') (ap1 get_pImp_cons input_pkg')
        imp_chain_to_mp_inner
        imp_mp_inner_to_pImp_cons

  in impEqTrans _ (ap1 get_pImp_cons input_pkg') (ap1 Snd (ap1 Snd cImpVal))
       imp_chain_to_pImp_cons
       imp_get_pImp_cons_value
