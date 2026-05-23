{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtInd -- discharge of the  ind  closure of  thmT  in the
-- UNIVERSAL form required by [[feedback-bra4-closures-universal-form]].
--
-- ======================================================================
-- PRIMARY closure :  thmT_at_ind  -- universal in arbitrary Terms.
-- ======================================================================
--
--   thmT_at_ind :
--     (cPBaseIdx cPStepIdx : Term)
--     (cBaseVal cStepVal : Term)                                  -- ARBITRARY
--     (ih_base : Deriv (eqF (ap1 thmT cPBaseIdx) cBaseVal))
--     (ih_step : Deriv (eqF (ap1 thmT cPStepIdx) cStepVal))
--     (wf_step_tag : Deriv (eqF (ap1 Fst cStepVal) (natCode tag_imp))) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ind) (ap2 pi cPBaseIdx cPStepIdx)))
--                 (ap1 Fst (ap1 Snd cStepVal)))
--
-- Mirrors the CURRENT shallow  ind_branch_thmT  in  BRA4.ThmT  : only
-- the tag-of-step check is performed.  Output = the "motive code" =
--  Fst (Snd cStepVal) .  Per learnt.md a complete validator would also
-- check that  sbf  on the antecedent with substituent  O  equals
--  cBaseVal  AND that  sbf  on the consequent with substituent
--  s var0  equals the encoded step-conclusion -- those deeper checks
-- are DEFERRED (require strengthening  ind_branch_thmT  in  ThmT.agda ).
--
-- ih_base  is currently UNUSED in the proof (no check uses cBaseVal) ;
-- it is kept in the signature for downstream interface uniformity and
-- so that strengthening ind_branch_thmT later -- which WILL use
-- cBaseVal -- is a non-breaking change of  thmT_at_ind 's body, not
-- its type.
--
-- ======================================================================
-- COROLLARY :  thmT_at_ind_codeF  -- specialised to Formulas.
-- ======================================================================

module BRA4.ThmTAtInd where

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
-- NatNeqWitnesses : tag_ind /= tag_ax / tag_sb / tag_mp .

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

  witness_ind_neq_ax : NatNeqWitness tag_ind tag_ax
  witness_ind_neq_ax = natEqFalse_to_witness tag_ax tag_ind refl

  witness_ind_neq_sb : NatNeqWitness tag_ind tag_sb
  witness_ind_neq_sb = natEqFalse_to_witness tag_sb tag_ind refl

  witness_ind_neq_mp : NatNeqWitness tag_ind tag_mp
  witness_ind_neq_mp = natEqFalse_to_witness tag_mp tag_ind refl

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

  get_ind_pBase_idx_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_ind_pBase_idx (ap2 pi A Y))
                                  (ap1 Fst (ap1 Snd (ap1 s A))))
  get_ind_pBase_idx_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_ind_pBase_idx (ap2 pi A Y))
                          (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  get_ind_pStep_idx_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_ind_pStep_idx (ap2 pi A Y))
                                  (ap1 Snd (ap1 Snd (ap1 s A))))
  get_ind_pStep_idx_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_ind_pStep_idx (ap2 pi A Y))
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
  pi_ax_sbor_unfold input = ax_C pi ax_branch_thmT sb_or_above input

  sb_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 sb_or_above input)
                (ap2 condFork
                  (ap1 (C pi sb_branch_thmT mp_or_above) input)
                  (ap1 isSb input)))
  sb_or_above_unfold input =
    ax_C condFork (C pi sb_branch_thmT mp_or_above) isSb input

  pi_sb_mpor_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi sb_branch_thmT mp_or_above) input)
                (ap2 pi (ap1 sb_branch_thmT input) (ap1 mp_or_above input)))
  pi_sb_mpor_unfold input = ax_C pi sb_branch_thmT mp_or_above input

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
  pi_mp_indor_unfold input = ax_C pi mp_branch_thmT ind_or_else input

  ind_or_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ind_or_else input)
                (ap2 condFork
                  (ap1 (C pi ind_branch_thmT else_branch_thmT) input)
                  (ap1 isInd input)))
  ind_or_else_unfold input =
    ax_C condFork (C pi ind_branch_thmT else_branch_thmT) isInd input

  pi_ind_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi ind_branch_thmT else_branch_thmT) input)
                (ap2 pi (ap1 ind_branch_thmT input) (ap1 else_branch_thmT input)))
  pi_ind_else_unfold input = ax_C pi ind_branch_thmT else_branch_thmT input

  isAx_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isAx input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_ax)))
  isAx_unfold input =
    let s1 = ax_C natEqF get_tag (constN tag_ax) input
        s2 = constN_eq tag_ax input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isSb_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_sb)))
  isSb_unfold input =
    let s1 = ax_C natEqF get_tag (constN tag_sb) input
        s2 = constN_eq tag_sb input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isMp_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isMp input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_mp)))
  isMp_unfold input =
    let s1 = ax_C natEqF get_tag (constN tag_mp) input
        s2 = constN_eq tag_mp input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isInd_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isInd input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_ind)))
  isInd_unfold input =
    let s1 = ax_C natEqF get_tag (constN tag_ind) input
        s2 = constN_eq tag_ind input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

------------------------------------------------------------------------
-- Tag-firing helpers.

private
  isAx_at_natCodeInd_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ind)) ->
    Deriv (eqF (ap1 isAx input) O)
  isAx_at_natCodeInd_O input tag_eq_pf =
    let s1 = isAx_unfold input
        s2 = congL natEqF (natCode tag_ax) tag_eq_pf
        s3 = natEqF_at_neq tag_ind tag_ax witness_ind_neq_ax
    in ruleTrans s1 (ruleTrans s2 s3)

  isSb_at_natCodeInd_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ind)) ->
    Deriv (eqF (ap1 isSb input) O)
  isSb_at_natCodeInd_O input tag_eq_pf =
    let s1 = isSb_unfold input
        s2 = congL natEqF (natCode tag_sb) tag_eq_pf
        s3 = natEqF_at_neq tag_ind tag_sb witness_ind_neq_sb
    in ruleTrans s1 (ruleTrans s2 s3)

  isMp_at_natCodeInd_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ind)) ->
    Deriv (eqF (ap1 isMp input) O)
  isMp_at_natCodeInd_O input tag_eq_pf =
    let s1 = isMp_unfold input
        s2 = congL natEqF (natCode tag_mp) tag_eq_pf
        s3 = natEqF_at_neq tag_ind tag_mp witness_ind_neq_mp
    in ruleTrans s1 (ruleTrans s2 s3)

  isInd_at_natCodeInd_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_ind)) ->
    Deriv (eqF (ap1 isInd input) (ap1 s O))
  isInd_at_natCodeInd_sO input tag_eq_pf =
    let s1 = isInd_unfold input
        s2 = congL natEqF (natCode tag_ind) tag_eq_pf
        s3 = natEq_eq tag_ind
    in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Cascade descents : stepBody -> sb_or_above -> mp_or_above -> ind_or_else -> ind_branch_thmT.

private
  stepBody_thmT_to_sb_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isAx input) O) ->
    Deriv (eqF (ap1 stepBody_thmT input) (ap1 sb_or_above input))
  stepBody_thmT_to_sb_or_above input isAx_O =
    let e1 = stepBody_thmT_unfold input
        sub_isAx = congR condFork (ap1 (C pi ax_branch_thmT sb_or_above) input) isAx_O
        cf_to_Snd = condFork_false (ap1 (C pi ax_branch_thmT sb_or_above) input)
        pi_eq = pi_ax_sbor_unfold input
        Snd_pi = axSnd (ap1 ax_branch_thmT input) (ap1 sb_or_above input)
    in ruleTrans e1 (ruleTrans sub_isAx
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  sb_or_above_to_mp_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input) O) ->
    Deriv (eqF (ap1 sb_or_above input) (ap1 mp_or_above input))
  sb_or_above_to_mp_or_above input isSb_O =
    let e1 = sb_or_above_unfold input
        sub_isSb = congR condFork (ap1 (C pi sb_branch_thmT mp_or_above) input) isSb_O
        cf_to_Snd = condFork_false (ap1 (C pi sb_branch_thmT mp_or_above) input)
        pi_eq = pi_sb_mpor_unfold input
        Snd_pi = axSnd (ap1 sb_branch_thmT input) (ap1 mp_or_above input)
    in ruleTrans e1 (ruleTrans sub_isSb
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  mp_or_above_to_ind_or_else :
    (input : Term) ->
    Deriv (eqF (ap1 isMp input) O) ->
    Deriv (eqF (ap1 mp_or_above input) (ap1 ind_or_else input))
  mp_or_above_to_ind_or_else input isMp_O =
    let e1 = mp_or_above_unfold input
        sub_isMp = congR condFork (ap1 (C pi mp_branch_thmT ind_or_else) input) isMp_O
        cf_to_Snd = condFork_false (ap1 (C pi mp_branch_thmT ind_or_else) input)
        pi_eq = pi_mp_indor_unfold input
        Snd_pi = axSnd (ap1 mp_branch_thmT input) (ap1 ind_or_else input)
    in ruleTrans e1 (ruleTrans sub_isMp
         (ruleTrans cf_to_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  ind_or_else_to_ind :
    (input : Term) ->
    Deriv (eqF (ap1 isInd input) (ap1 s O)) ->
    Deriv (eqF (ap1 ind_or_else input) (ap1 ind_branch_thmT input))
  ind_or_else_to_ind input isInd_sO =
    let e1 = ind_or_else_unfold input
        sub_isInd = congR condFork (ap1 (C pi ind_branch_thmT else_branch_thmT) input) isInd_sO
        cf_to_Fst = condFork_true_nc (ap1 (C pi ind_branch_thmT else_branch_thmT) input) O
        pi_eq = pi_ind_else_unfold input
        Fst_pi = axFst (ap1 ind_branch_thmT input) (ap1 else_branch_thmT input)
    in ruleTrans e1 (ruleTrans sub_isInd
         (ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

------------------------------------------------------------------------
-- HP_thmT stability bridge (local re-derivation).

private
  HP_thmT_eq_thmT_under_leq :
    (ct K : Term) ->
    Deriv (leq ct K) ->
    Deriv (eqF (HPsbt baseValue_thmT stepFun_thmT O ct K)
                (ap2 thmT_F2 O ct))
  HP_thmT_eq_thmT_under_leq ct K leq_ct_K =
    let stab = mp (stabilityP_sbt_at baseValue_thmT stepFun_thmT O ct K) leq_ct_K
        subCT_O = sub_self ct
        iter_arg = congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O ct) subCT_O
        iter_base = iter_base_univ Snd (HistP_sbt baseValue_thmT stepFun_thmT O ct)
        iter_full = ruleTrans iter_arg iter_base
        HP_at_ct = cong1 Fst iter_full
        readOff_eq = readOff_spec_eq (ap2 (cov_spec baseValue_thmT stepFun_thmT) O ct)
        thmTF2_eq_sym = ruleSym (thmT_unfold_F2 O ct)
    in ruleTrans stab
         (ruleTrans HP_at_ct (ruleTrans (ruleSym readOff_eq) thmTF2_eq_sym))

------------------------------------------------------------------------
-- Leq lemmas for sub-positions cPBaseIdx, cPStepIdx of pi cPBaseIdx cPStepIdx.

leq_cPStepIdx_P_outer_ind :
  (cPBaseIdx cPStepIdx : Term) ->
  Deriv (leq cPStepIdx
            (pi_succ_outer (natCode (suc (suc (suc zero))))
                           (ap2 pi cPBaseIdx cPStepIdx)))
leq_cPStepIdx_P_outer_ind cPBaseIdx cPStepIdx =
  let A : Term
      A = natCode (suc (suc (suc zero))) -- natCode 3
      Y : Term
      Y = ap2 pi cPBaseIdx cPStepIdx
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
      l1 = leq_pi_right cPBaseIdx cPStepIdx
      l2 = leq_sigma_right X Y
  in leq_trans cPStepIdx Y (ap2 sigma X Y) l1 l2

leq_cPBaseIdx_P_outer_ind :
  (cPBaseIdx cPStepIdx : Term) ->
  Deriv (leq cPBaseIdx
            (pi_succ_outer (natCode (suc (suc (suc zero))))
                           (ap2 pi cPBaseIdx cPStepIdx)))
leq_cPBaseIdx_P_outer_ind cPBaseIdx cPStepIdx =
  let A : Term
      A = natCode (suc (suc (suc zero)))
      Y : Term
      Y = ap2 pi cPBaseIdx cPStepIdx
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
      l1 : Deriv (leq cPBaseIdx (ap2 sigma cPBaseIdx cPStepIdx))
      l1 = leq_sigma_left cPBaseIdx cPStepIdx
      l2 : Deriv (leq (ap2 sigma cPBaseIdx cPStepIdx) (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx)))
      l2 = ruleInst 0 (ap2 sigma cPBaseIdx cPStepIdx) BRA3.ChurchT92.T92
      l3 : Deriv (leq (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx))
                       (ap2 sigma (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx)) cPStepIdx))
      l3 = leq_sigma_left (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx)) cPStepIdx
      eqPi = ruleSym (BRA4.LeqMono.T114_at cPBaseIdx cPStepIdx)
      cong_sub = congR sub (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx)) eqPi
      cong_sub_sym = ruleSym cong_sub
      l3_pi = ruleTrans cong_sub_sym l3
      l12 = leq_trans cPBaseIdx (ap2 sigma cPBaseIdx cPStepIdx)
                       (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx)) l1 l2
      l123 = leq_trans cPBaseIdx (ap1 tau (ap2 sigma cPBaseIdx cPStepIdx))
                        (ap2 pi cPBaseIdx cPStepIdx) l12 l3_pi
      l5 = leq_sigma_right X Y
  in leq_trans cPBaseIdx Y (ap2 sigma X Y) l123 l5

------------------------------------------------------------------------
-- ind_branch_thmT unfoldings.

private
  ind_branch_thmT_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ind_branch_thmT input)
                (ap2 condFork
                  (ap1 (C pi get_motive baseValue_thmT) input)
                  (ap1 isIndStepImp input)))
  ind_branch_thmT_unfold input =
    ax_C condFork (C pi get_motive baseValue_thmT) isIndStepImp input

  pi_motive_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_motive baseValue_thmT) input)
                (ap2 pi (ap1 get_motive input) (ap1 baseValue_thmT input)))
  pi_motive_unfold input = ax_C pi get_motive baseValue_thmT input

  isIndStepImp_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isIndStepImp input)
                (ap2 natEqF (ap1 get_pStep_tag input) (natCode tag_imp)))
  isIndStepImp_unfold input =
    let s1 = ax_C natEqF get_pStep_tag (constN tag_imp) input
        s2 = constN_eq tag_imp input
    in ruleTrans s1 (congR natEqF (ap1 get_pStep_tag input) s2)

  lookupAt_unfold :
    (idx_F1 : Fun1) (input : Term) ->
    Deriv (eqF (ap1 (lookupAt idx_F1) input)
                (ap1 Fst (ap2 (iter Snd) (ap1 get_table input)
                              (ap2 sub (ap1 get_K input) (ap1 idx_F1 input)))))
  lookupAt_unfold idx_F1 input =
    let s1 = compose1U_eq Fst (C (iter Snd) get_table (C sub get_K idx_F1)) input
        s2 = ax_C (iter Snd) get_table (C sub get_K idx_F1) input
        s3 = ax_C sub get_K idx_F1 input
        s4 = congR (iter Snd) (ap1 get_table input) s3
        s23 = ruleTrans s2 s4
    in ruleTrans s1 (cong1 Fst s23)

  get_pStep_tag_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_pStep_tag input)
                (ap1 Fst (ap1 get_pStep_val input)))
  get_pStep_tag_unfold input = compose1U_eq Fst get_pStep_val input

  get_pStep_body_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_pStep_body input)
                (ap1 Snd (ap1 get_pStep_val input)))
  get_pStep_body_unfold input = compose1U_eq Snd get_pStep_val input

  get_motive_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 get_motive input)
                (ap1 Fst (ap1 get_pStep_body input)))
  get_motive_unfold input = compose1U_eq Fst get_pStep_body input

------------------------------------------------------------------------
-- The main UNIVERSAL closure proof.

thmT_at_ind :
  (cPBaseIdx cPStepIdx : Term)
  (cBaseVal cStepVal : Term)
  (ih_base : Deriv (eqF (ap1 thmT cPBaseIdx) cBaseVal))
  (ih_step : Deriv (eqF (ap1 thmT cPStepIdx) cStepVal))
  (wf_step_tag : Deriv (eqF (ap1 Fst cStepVal) (natCode tag_imp))) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ind) (ap2 pi cPBaseIdx cPStepIdx)))
              (ap1 Fst (ap1 Snd cStepVal)))
thmT_at_ind cPBaseIdx cPStepIdx cBaseVal cStepVal ih_base ih_step wf_step_tag =
  let input : Term
      input = ap2 pi (natCode tag_ind) (ap2 pi cPBaseIdx cPStepIdx)

      Y_body : Term
      Y_body = ap2 pi cPBaseIdx cPStepIdx

      A_outer : Term
      A_outer = natCode (suc (suc (suc zero)))

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      -- (1) Standard cov_spec_step_univ + readOff + Post chain.
      step0 = thmT_unfold input
      step1 = thmT_unfold_F2 O input
      input_eq_sP_outer = pi_at_succ A_outer Y_body
      cov_lift = congR (cov_spec baseValue_thmT stepFun_thmT) O input_eq_sP_outer
      cov_step = cov_spec_step_univ baseValue_thmT stepFun_thmT O P_outer
      thmTState_eq = ruleTrans cov_lift cov_step
      readOff_lift = cong1 readOff_spec thmTState_eq
      readOff_eval = readOff_state_step_univ stepFun_thmT prev
      Fst_prev_eq = fst_cov_spec_eq baseValue_thmT stepFun_thmT O P_outer
      stepFun_lift = congL stepFun_thmT (ap1 Snd prev) Fst_prev_eq
      Post_eq = axPost stepBody_thmT pi P_outer (ap1 Snd prev)

      -- (2) Tag dispatch -> ind branch.
      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_ind))
      Fst_input = axFst (natCode tag_ind) Y_body

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_ind))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isAx_value = isAx_at_natCodeInd_O input_pkg' get_tag_value
      isSb_value = isSb_at_natCodeInd_O input_pkg' get_tag_value
      isMp_value = isMp_at_natCodeInd_O input_pkg' get_tag_value
      isInd_value = isInd_at_natCodeInd_sO input_pkg' get_tag_value

      stepBody_to_sbor = stepBody_thmT_to_sb_or_above input_pkg' isAx_value
      sbor_to_mpor    = sb_or_above_to_mp_or_above   input_pkg' isSb_value
      mpor_to_indor   = mp_or_above_to_ind_or_else   input_pkg' isMp_value
      indor_to_ind    = ind_or_else_to_ind            input_pkg' isInd_value

      stepBody_to_ind :
        Deriv (eqF (ap1 stepBody_thmT input_pkg') (ap1 ind_branch_thmT input_pkg'))
      stepBody_to_ind =
        ruleTrans stepBody_to_sbor
          (ruleTrans sbor_to_mpor
            (ruleTrans mpor_to_indor indor_to_ind))

      -- (3) Snd input_pkg' chain.
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)
      Snd_input_eq_Yb = axSnd (natCode tag_ind) Y_body
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

      get_ind_pBase_idx_value :
        Deriv (eqF (ap1 get_ind_pBase_idx input_pkg') cPBaseIdx)
      get_ind_pBase_idx_value =
        let s1 = get_ind_pBase_idx_at_pi P_outer (ap1 Snd prev)
            Fst_Y = axFst cPBaseIdx cPStepIdx
        in ruleTrans s1 (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ind_pStep_idx_value :
        Deriv (eqF (ap1 get_ind_pStep_idx input_pkg') cPStepIdx)
      get_ind_pStep_idx_value =
        let s1 = get_ind_pStep_idx_at_pi P_outer (ap1 Snd prev)
            Snd_Y = axSnd cPBaseIdx cPStepIdx
        in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- (4) pStep_val lookup = cStepVal (via ih_step + stability).
      pStep_val_unfold = lookupAt_unfold get_ind_pStep_idx input_pkg'
      pStep_iter_arg = ruleTrans (congL sub (ap1 get_ind_pStep_idx input_pkg') get_K_value)
                                  (congR sub P_outer get_ind_pStep_idx_value)
      pStep_iter_full =
        ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                                (ap1 get_ind_pStep_idx input_pkg'))
                          get_table_value)
                  (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                          pStep_iter_arg)
      pStep_val_to_HP = ruleTrans pStep_val_unfold (cong1 Fst pStep_iter_full)
      leq_pStep = leq_cPStepIdx_P_outer_ind cPBaseIdx cPStepIdx
      pStep_val_value =
        ruleTrans pStep_val_to_HP
                  (HP_thmT_eq_thmT_under_leq cPStepIdx P_outer leq_pStep)
      pStep_val_to_thmT = ruleTrans pStep_val_value (ruleSym (thmT_unfold cPStepIdx))

      get_pStep_val_eq :
        Deriv (eqF (ap1 get_pStep_val input_pkg') cStepVal)
      get_pStep_val_eq = ruleTrans pStep_val_to_thmT ih_step

      -- (5) pBase_val lookup -- computed for symmetry / future use ;
      --     currently UNUSED in the proof (ind_branch_thmT doesn't read it).
      --     We omit the leq+HP-bridge chain here to keep the file lean,
      --     since the value isn't consumed.  ih_base is therefore also
      --     unused (kept in the signature for downstream consistency).

      -- (6) isIndStepImp = sO via wf_step_tag + IH-substitution.
      -- get_pStep_tag input_pkg' = Fst (get_pStep_val input_pkg') = Fst cStepVal = natCode tag_imp.
      get_pStep_tag_step1 :
        Deriv (eqF (ap1 get_pStep_tag input_pkg')
                    (ap1 Fst (ap1 get_pStep_val input_pkg')))
      get_pStep_tag_step1 = get_pStep_tag_unfold input_pkg'

      get_pStep_tag_step2 :
        Deriv (eqF (ap1 Fst (ap1 get_pStep_val input_pkg')) (ap1 Fst cStepVal))
      get_pStep_tag_step2 = cong1 Fst get_pStep_val_eq

      get_pStep_tag_value :
        Deriv (eqF (ap1 get_pStep_tag input_pkg') (natCode tag_imp))
      get_pStep_tag_value =
        ruleTrans get_pStep_tag_step1 (ruleTrans get_pStep_tag_step2 wf_step_tag)

      isIndStepImp_step1 :
        Deriv (eqF (ap1 isIndStepImp input_pkg')
                    (ap2 natEqF (ap1 get_pStep_tag input_pkg') (natCode tag_imp)))
      isIndStepImp_step1 = isIndStepImp_unfold input_pkg'

      isIndStepImp_step2 :
        Deriv (eqF (ap2 natEqF (ap1 get_pStep_tag input_pkg') (natCode tag_imp))
                    (ap2 natEqF (natCode tag_imp) (natCode tag_imp)))
      isIndStepImp_step2 = congL natEqF (natCode tag_imp) get_pStep_tag_value

      isIndStepImp_step3 :
        Deriv (eqF (ap2 natEqF (natCode tag_imp) (natCode tag_imp)) (ap1 s O))
      isIndStepImp_step3 = natEq_eq tag_imp

      isIndStepImp_value :
        Deriv (eqF (ap1 isIndStepImp input_pkg') (ap1 s O))
      isIndStepImp_value =
        ruleTrans isIndStepImp_step1
          (ruleTrans isIndStepImp_step2 isIndStepImp_step3)

      -- (7) ind_branch_thmT -> get_motive.
      ind_branch_to_motive :
        Deriv (eqF (ap1 ind_branch_thmT input_pkg') (ap1 get_motive input_pkg'))
      ind_branch_to_motive =
        let e1 = ind_branch_thmT_unfold input_pkg'
            sub_isStep = congR condFork (ap1 (C pi get_motive baseValue_thmT) input_pkg')
                                        isIndStepImp_value
            cf_to_Fst = condFork_true_nc (ap1 (C pi get_motive baseValue_thmT) input_pkg') O
            pi_eq = pi_motive_unfold input_pkg'
            Fst_pi = axFst (ap1 get_motive input_pkg') (ap1 baseValue_thmT input_pkg')
        in ruleTrans e1 (ruleTrans sub_isStep
             (ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

      -- (8) get_motive input_pkg' = Fst (Snd cStepVal).
      get_motive_value :
        Deriv (eqF (ap1 get_motive input_pkg') (ap1 Fst (ap1 Snd cStepVal)))
      get_motive_value =
        let s1 : Deriv (eqF (ap1 get_motive input_pkg')
                             (ap1 Fst (ap1 get_pStep_body input_pkg')))
            s1 = get_motive_unfold input_pkg'
            s2 : Deriv (eqF (ap1 get_pStep_body input_pkg')
                             (ap1 Snd (ap1 get_pStep_val input_pkg')))
            s2 = get_pStep_body_unfold input_pkg'
            s3 : Deriv (eqF (ap1 Snd (ap1 get_pStep_val input_pkg'))
                             (ap1 Snd cStepVal))
            s3 = cong1 Snd get_pStep_val_eq
            s4 : Deriv (eqF (ap1 Fst (ap1 get_pStep_body input_pkg'))
                             (ap1 Fst (ap1 Snd cStepVal)))
            s4 = cong1 Fst (ruleTrans s2 s3)
        in ruleTrans s1 s4

      -- (9) Final assembly.
      chain_to_stepBody :
        Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
      chain_to_stepBody =
        ruleTrans step0
          (ruleTrans step1
            (ruleTrans readOff_lift
              (ruleTrans readOff_eval
                (ruleTrans stepFun_lift Post_eq))))

      chain_to_ind_branch :
        Deriv (eqF (ap1 thmT input) (ap1 ind_branch_thmT input_pkg'))
      chain_to_ind_branch = ruleTrans chain_to_stepBody stepBody_to_ind

      chain_to_motive :
        Deriv (eqF (ap1 thmT input) (ap1 get_motive input_pkg'))
      chain_to_motive = ruleTrans chain_to_ind_branch ind_branch_to_motive
  in ruleTrans chain_to_motive get_motive_value

------------------------------------------------------------------------
-- Corollary :  thmT_at_ind_codeF  -- specialised to a Formula motive.
--
-- Given that  ih_step  says  thmT cPStepIdx = codeFormula (imp P_motive cStepCons) ,
-- derive  wf_step_tag  via axFst and conclude that the output equals
--  codeFormula P_motive .

thmT_at_ind_codeF :
  (cPBaseIdx cPStepIdx : Term)
  (P_motive cBaseVal cStepCons : Term)
  (ih_base : Deriv (eqF (ap1 thmT cPBaseIdx) cBaseVal))
  (ih_step : Deriv (eqF (ap1 thmT cPStepIdx)
                         (ap2 pi (natCode tag_imp) (ap2 pi P_motive cStepCons)))) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ind) (ap2 pi cPBaseIdx cPStepIdx)))
              P_motive)
thmT_at_ind_codeF cPBaseIdx cPStepIdx P_motive cBaseVal cStepCons ih_base ih_step =
  let cStepVal : Term
      cStepVal = ap2 pi (natCode tag_imp) (ap2 pi P_motive cStepCons)

      -- wf_step_tag : Fst cStepVal = natCode tag_imp.
      wf_step_tag : Deriv (eqF (ap1 Fst cStepVal) (natCode tag_imp))
      wf_step_tag = axFst (natCode tag_imp) (ap2 pi P_motive cStepCons)

      -- Output : Fst (Snd cStepVal) = Fst (pi P_motive cStepCons) = P_motive.
      Snd_step :
        Deriv (eqF (ap1 Snd cStepVal) (ap2 pi P_motive cStepCons))
      Snd_step = axSnd (natCode tag_imp) (ap2 pi P_motive cStepCons)

      Fst_Snd_step :
        Deriv (eqF (ap1 Fst (ap1 Snd cStepVal)) P_motive)
      Fst_Snd_step = ruleTrans (cong1 Fst Snd_step) (axFst P_motive cStepCons)

      raw : Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ind) (ap2 pi cPBaseIdx cPStepIdx)))
                        (ap1 Fst (ap1 Snd cStepVal)))
      raw = thmT_at_ind cPBaseIdx cPStepIdx cBaseVal cStepVal
                        ih_base ih_step wf_step_tag
  in ruleTrans raw Fst_Snd_step
