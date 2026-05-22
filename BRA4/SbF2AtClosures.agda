{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbF2AtClosures -- discharge of the three formula closures of
--  SbContract :
--
--   sbf2_at_atomic :  ap2 sbf2 spec (pi (natCode tag_eq) (pi ca cb))
--                       = pi (natCode tag_eq) (pi (sbt2 spec ca) (sbt2 spec cb))
--   sbf2_at_neg    :  ap2 sbf2 spec (pi (natCode tag_neg) cP)
--                       = pi (natCode tag_neg) (sbf2 spec cP)
--   sbf2_at_imp    :  ap2 sbf2 spec (pi (natCode tag_imp) (pi cP cQ))
--                       = pi (natCode tag_imp) (pi (sbf2 spec cP) (sbf2 spec cQ))
--
-- Universal in the sub-positions  ca, cb, cP, cQ : Term -- no Closed
-- premise, no natCode hypothesis.
--
-- Architecture parallels  BRA4.SbtAtAp .  Tag dispatch + cov_spec_step_univ
-- + readOff + Post + stepBody_sbf2 cascade.  For tag_neg / tag_imp the
-- sub-positions are formulas and we use the sbf2 cov-table lookup +
-- stability bridge (HP_sbf_eq_sbf_under_leq).  For tag_eq the sub-positions
-- are TERMS and we use  C sbt2 get_spec get_ca_atom  + spec-preservation
-- (fstSnd_cov_spec_eq) -- no stability needed.

module BRA4.SbF2AtClosures where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv
open import BRA4.CoVSpecFst
open import BRA4.CoVSpecSpec
open import BRA4.SbT2          using ( sbt2 ; get_K ; get_inner ; get_spec
                                     ; get_table ; get_newK ; get_tag ; get_body
                                     ; lookupAt )
open import BRA4.SbF2
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
open import BRA3.RuleInst2       using ( natEq-refl ; true_neq_false )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; iter_base_univ )
import BRA3.ChurchT92

------------------------------------------------------------------------
-- NatNeqWitness construction for tag inequalities.

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

  witness_neg_neq_eq : NatNeqWitness tag_neg tag_eq
  witness_neg_neq_eq = natEqFalse_to_witness tag_eq tag_neg refl

  witness_imp_neq_eq : NatNeqWitness tag_imp tag_eq
  witness_imp_neq_eq = natEqFalse_to_witness tag_eq tag_imp refl

  witness_imp_neq_neg : NatNeqWitness tag_imp tag_neg
  witness_imp_neq_neg = natEqFalse_to_witness tag_neg tag_imp refl

------------------------------------------------------------------------
-- Position-extraction closed forms at a packaged input  pi A Y .
--
-- Reproduced (since SbtAtAp's are private).  These are generic in the
-- stepFun and work the same for sbf2 as for sbt.

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

  get_spec_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_spec (ap2 pi A Y)) (ap1 Fst Y))
  get_spec_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_spec (ap2 pi A Y))
                          (ap1 Fst (ap1 get_inner (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_inner (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_inner_at_pi A Y))

  get_table_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_table (ap2 pi A Y)) (ap1 Snd Y))
  get_table_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_table (ap2 pi A Y))
                          (ap1 Snd (ap1 get_inner (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_inner (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_inner_at_pi A Y))

  -- Branch-specific position closures.

  get_ca_atom_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_ca_atom (ap2 pi A Y))
                                  (ap1 Fst (ap1 Snd (ap1 s A))))
  get_ca_atom_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_ca_atom (ap2 pi A Y))
                          (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  get_cb_atom_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_cb_atom (ap2 pi A Y))
                                  (ap1 Snd (ap1 Snd (ap1 s A))))
  get_cb_atom_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_cb_atom (ap2 pi A Y))
                          (ap1 Snd (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_body_at_pi A Y))

  get_cP_imp_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_cP_imp (ap2 pi A Y))
                                  (ap1 Fst (ap1 Snd (ap1 s A))))
  get_cP_imp_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_cP_imp (ap2 pi A Y))
                          (ap1 Fst (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Fst get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

  get_cQ_imp_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_cQ_imp (ap2 pi A Y))
                                  (ap1 Snd (ap1 Snd (ap1 s A))))
  get_cQ_imp_at_pi A Y =
    let s1 : Deriv (eqF (ap1 get_cQ_imp (ap2 pi A Y))
                          (ap1 Snd (ap1 get_body (ap2 pi A Y))))
        s1 = compose1U_eq Snd get_body (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_body_at_pi A Y))

------------------------------------------------------------------------
-- Standard cascade unfoldings.

private
  stepBody_sbf2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 stepBody_sbf2 input)
                (ap2 condFork
                  (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                  (ap1 isEq input)))
  stepBody_sbf2_unfold input =
    ax_C condFork (C pi atomic_branch_sbf2 neg_or_above) isEq input

  pi_atomic_neg_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                (ap2 pi (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)))
  pi_atomic_neg_unfold input =
    ax_C pi atomic_branch_sbf2 neg_or_above input

  neg_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 neg_or_above input)
                (ap2 condFork
                  (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                  (ap1 isNeg input)))
  neg_or_above_unfold input =
    ax_C condFork (C pi neg_branch_sbf2 imp_or_else) isNeg input

  pi_neg_imp_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                (ap2 pi (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)))
  pi_neg_imp_unfold input =
    ax_C pi neg_branch_sbf2 imp_or_else input

  imp_or_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 imp_or_else input)
                (ap2 condFork
                  (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)
                  (ap1 isImp input)))
  imp_or_else_unfold input =
    ax_C condFork (C pi imp_branch_sbf2 else_branch_sbf2) isImp input

  pi_imp_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)
                (ap2 pi (ap1 imp_branch_sbf2 input) (ap1 else_branch_sbf2 input)))
  pi_imp_else_unfold input =
    ax_C pi imp_branch_sbf2 else_branch_sbf2 input

  isEq_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isEq input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_eq)))
  isEq_unfold input =
    let s1 :
          Deriv (eqF (ap1 isEq input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_eq) input)))
        s1 = ax_C natEqF get_tag (constN tag_eq) input
        s2 : Deriv (eqF (ap1 (constN tag_eq) input) (natCode tag_eq))
        s2 = constN_eq tag_eq input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isNeg_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isNeg input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_neg)))
  isNeg_unfold input =
    let s1 :
          Deriv (eqF (ap1 isNeg input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_neg) input)))
        s1 = ax_C natEqF get_tag (constN tag_neg) input
        s2 : Deriv (eqF (ap1 (constN tag_neg) input) (natCode tag_neg))
        s2 = constN_eq tag_neg input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  isImp_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isImp input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_imp)))
  isImp_unfold input =
    let s1 :
          Deriv (eqF (ap1 isImp input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_imp) input)))
        s1 = ax_C natEqF get_tag (constN tag_imp) input
        s2 : Deriv (eqF (ap1 (constN tag_imp) input) (natCode tag_imp))
        s2 = constN_eq tag_imp input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

------------------------------------------------------------------------
-- Tag-firing helpers, parametric on  get_tag input = natCode TAG  hypothesis.

private
  isEq_at_natCodeEq_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_eq)) ->
    Deriv (eqF (ap1 isEq input) (ap1 s O))
  isEq_at_natCodeEq_sO input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isEq input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_eq)))
        s1 = isEq_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_eq))
                      (ap2 natEqF (natCode tag_eq) (natCode tag_eq)))
        s2 = congL natEqF (natCode tag_eq) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_eq) (natCode tag_eq)) (ap1 s O))
        s3 = natEq_eq tag_eq
    in ruleTrans s1 (ruleTrans s2 s3)

  isEq_at_natCodeNeg_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_neg)) ->
    Deriv (eqF (ap1 isEq input) O)
  isEq_at_natCodeNeg_O input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isEq input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_eq)))
        s1 = isEq_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_eq))
                      (ap2 natEqF (natCode tag_neg) (natCode tag_eq)))
        s2 = congL natEqF (natCode tag_eq) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_neg) (natCode tag_eq)) O)
        s3 = natEqF_at_neq tag_neg tag_eq witness_neg_neq_eq
    in ruleTrans s1 (ruleTrans s2 s3)

  isEq_at_natCodeImp_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_imp)) ->
    Deriv (eqF (ap1 isEq input) O)
  isEq_at_natCodeImp_O input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isEq input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_eq)))
        s1 = isEq_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_eq))
                      (ap2 natEqF (natCode tag_imp) (natCode tag_eq)))
        s2 = congL natEqF (natCode tag_eq) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_imp) (natCode tag_eq)) O)
        s3 = natEqF_at_neq tag_imp tag_eq witness_imp_neq_eq
    in ruleTrans s1 (ruleTrans s2 s3)

  isNeg_at_natCodeNeg_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_neg)) ->
    Deriv (eqF (ap1 isNeg input) (ap1 s O))
  isNeg_at_natCodeNeg_sO input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isNeg input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_neg)))
        s1 = isNeg_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_neg))
                      (ap2 natEqF (natCode tag_neg) (natCode tag_neg)))
        s2 = congL natEqF (natCode tag_neg) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_neg) (natCode tag_neg)) (ap1 s O))
        s3 = natEq_eq tag_neg
    in ruleTrans s1 (ruleTrans s2 s3)

  isNeg_at_natCodeImp_O :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_imp)) ->
    Deriv (eqF (ap1 isNeg input) O)
  isNeg_at_natCodeImp_O input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isNeg input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_neg)))
        s1 = isNeg_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_neg))
                      (ap2 natEqF (natCode tag_imp) (natCode tag_neg)))
        s2 = congL natEqF (natCode tag_neg) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_imp) (natCode tag_neg)) O)
        s3 = natEqF_at_neq tag_imp tag_neg witness_imp_neq_neg
    in ruleTrans s1 (ruleTrans s2 s3)

  isImp_at_natCodeImp_sO :
    (input : Term) ->
    Deriv (eqF (ap1 get_tag input) (natCode tag_imp)) ->
    Deriv (eqF (ap1 isImp input) (ap1 s O))
  isImp_at_natCodeImp_sO input tag_eq_pf =
    let s1 :
          Deriv (eqF (ap1 isImp input)
                      (ap2 natEqF (ap1 get_tag input) (natCode tag_imp)))
        s1 = isImp_unfold input
        s2 :
          Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_imp))
                      (ap2 natEqF (natCode tag_imp) (natCode tag_imp)))
        s2 = congL natEqF (natCode tag_imp) tag_eq_pf
        s3 : Deriv (eqF (ap2 natEqF (natCode tag_imp) (natCode tag_imp)) (ap1 s O))
        s3 = natEq_eq tag_imp
    in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Cascade dispatches.

private
  stepBody_sbf2_to_atomic :
    (input : Term) ->
    Deriv (eqF (ap1 isEq input) (ap1 s O)) ->
    Deriv (eqF (ap1 stepBody_sbf2 input) (ap1 atomic_branch_sbf2 input))
  stepBody_sbf2_to_atomic input isEq_sO =
    let e1 :
          Deriv (eqF (ap1 stepBody_sbf2 input)
                      (ap2 condFork
                        (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                        (ap1 isEq input)))
        e1 = stepBody_sbf2_unfold input

        isEq_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                       (ap1 isEq input))
                      (ap2 condFork
                       (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                       (ap1 s O)))
        isEq_subst =
          congR condFork (ap1 (C pi atomic_branch_sbf2 neg_or_above) input) isEq_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi atomic_branch_sbf2 neg_or_above) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi atomic_branch_sbf2 neg_or_above) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                      (ap2 pi (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)))
        pi_eq = pi_atomic_neg_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)))
                      (ap1 atomic_branch_sbf2 input))
        Fst_pi = axFst (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)
    in ruleTrans e1
         (ruleTrans isEq_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  stepBody_sbf2_to_neg_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isEq input) O) ->
    Deriv (eqF (ap1 stepBody_sbf2 input) (ap1 neg_or_above input))
  stepBody_sbf2_to_neg_or_above input isEq_O =
    let e1 :
          Deriv (eqF (ap1 stepBody_sbf2 input)
                      (ap2 condFork
                        (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                        (ap1 isEq input)))
        e1 = stepBody_sbf2_unfold input

        isEq_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                       (ap1 isEq input))
                      (ap2 condFork
                       (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                       O))
        isEq_subst =
          congR condFork (ap1 (C pi atomic_branch_sbf2 neg_or_above) input) isEq_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi atomic_branch_sbf2 neg_or_above) input) O)
                      (ap1 Snd (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi atomic_branch_sbf2 neg_or_above) input)
                      (ap2 pi (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)))
        pi_eq = pi_atomic_neg_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)))
                      (ap1 neg_or_above input))
        Snd_pi = axSnd (ap1 atomic_branch_sbf2 input) (ap1 neg_or_above input)
    in ruleTrans e1
         (ruleTrans isEq_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  neg_or_above_to_neg :
    (input : Term) ->
    Deriv (eqF (ap1 isNeg input) (ap1 s O)) ->
    Deriv (eqF (ap1 neg_or_above input) (ap1 neg_branch_sbf2 input))
  neg_or_above_to_neg input isNeg_sO =
    let e1 :
          Deriv (eqF (ap1 neg_or_above input)
                      (ap2 condFork
                        (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                        (ap1 isNeg input)))
        e1 = neg_or_above_unfold input

        isNeg_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                       (ap1 isNeg input))
                      (ap2 condFork
                       (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                       (ap1 s O)))
        isNeg_subst =
          congR condFork (ap1 (C pi neg_branch_sbf2 imp_or_else) input) isNeg_sO

        condFork_to_Fst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi neg_branch_sbf2 imp_or_else) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi neg_branch_sbf2 imp_or_else) input)))
        condFork_to_Fst =
          condFork_true_nc (ap1 (C pi neg_branch_sbf2 imp_or_else) input) O

        pi_eq :
          Deriv (eqF (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                      (ap2 pi (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)))
        pi_eq = pi_neg_imp_unfold input

        Fst_pi :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)))
                      (ap1 neg_branch_sbf2 input))
        Fst_pi = axFst (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)
    in ruleTrans e1
         (ruleTrans isNeg_subst
           (ruleTrans condFork_to_Fst
             (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  neg_or_above_to_imp :
    (input : Term) ->
    Deriv (eqF (ap1 isNeg input) O) ->
    Deriv (eqF (ap1 isImp input) (ap1 s O)) ->
    Deriv (eqF (ap1 neg_or_above input) (ap1 imp_branch_sbf2 input))
  neg_or_above_to_imp input isNeg_O isImp_sO =
    let e1 :
          Deriv (eqF (ap1 neg_or_above input)
                      (ap2 condFork
                        (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                        (ap1 isNeg input)))
        e1 = neg_or_above_unfold input

        isNeg_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                       (ap1 isNeg input))
                      (ap2 condFork
                       (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                       O))
        isNeg_subst =
          congR condFork (ap1 (C pi neg_branch_sbf2 imp_or_else) input) isNeg_O

        condFork_to_Snd :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi neg_branch_sbf2 imp_or_else) input) O)
                      (ap1 Snd (ap1 (C pi neg_branch_sbf2 imp_or_else) input)))
        condFork_to_Snd =
          condFork_false (ap1 (C pi neg_branch_sbf2 imp_or_else) input)

        pi_eq :
          Deriv (eqF (ap1 (C pi neg_branch_sbf2 imp_or_else) input)
                      (ap2 pi (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)))
        pi_eq = pi_neg_imp_unfold input

        Snd_pi :
          Deriv (eqF (ap1 Snd (ap2 pi (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)))
                      (ap1 imp_or_else input))
        Snd_pi = axSnd (ap1 neg_branch_sbf2 input) (ap1 imp_or_else input)

        -- imp_or_else -> imp_branch.
        e2 :
          Deriv (eqF (ap1 imp_or_else input)
                      (ap2 condFork
                        (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)
                        (ap1 isImp input)))
        e2 = imp_or_else_unfold input

        isImp_subst :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)
                       (ap1 isImp input))
                      (ap2 condFork
                       (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)
                       (ap1 s O)))
        isImp_subst =
          congR condFork (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input) isImp_sO

        condFork_to_Fst_imp :
          Deriv (eqF (ap2 condFork
                       (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input) (ap1 s O))
                      (ap1 Fst (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)))
        condFork_to_Fst_imp =
          condFork_true_nc (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input) O

        pi_eq_imp :
          Deriv (eqF (ap1 (C pi imp_branch_sbf2 else_branch_sbf2) input)
                      (ap2 pi (ap1 imp_branch_sbf2 input) (ap1 else_branch_sbf2 input)))
        pi_eq_imp = pi_imp_else_unfold input

        Fst_pi_imp :
          Deriv (eqF (ap1 Fst (ap2 pi (ap1 imp_branch_sbf2 input) (ap1 else_branch_sbf2 input)))
                      (ap1 imp_branch_sbf2 input))
        Fst_pi_imp = axFst (ap1 imp_branch_sbf2 input) (ap1 else_branch_sbf2 input)

        imp_or_else_to_imp :
          Deriv (eqF (ap1 imp_or_else input) (ap1 imp_branch_sbf2 input))
        imp_or_else_to_imp =
          ruleTrans e2
            (ruleTrans isImp_subst
              (ruleTrans condFork_to_Fst_imp
                (ruleTrans (cong1 Fst pi_eq_imp) Fst_pi_imp)))
    in ruleTrans e1
         (ruleTrans isNeg_subst
           (ruleTrans condFork_to_Snd
             (ruleTrans (cong1 Snd pi_eq)
               (ruleTrans Snd_pi imp_or_else_to_imp))))

------------------------------------------------------------------------
-- Branch body unfoldings.

private
  neg_branch_sbf2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 neg_branch_sbf2 input)
                (ap2 pi (ap1 (constN tag_neg) input) (ap1 (lookupAt get_body) input)))
  neg_branch_sbf2_unfold input =
    ax_C pi (constN tag_neg) (lookupAt get_body) input

  atomic_branch_sbf2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 atomic_branch_sbf2 input)
                (ap2 pi (ap1 (constN tag_eq) input)
                        (ap1 (C pi (C sbt2 get_spec get_ca_atom)
                                    (C sbt2 get_spec get_cb_atom)) input)))
  atomic_branch_sbf2_unfold input =
    ax_C pi (constN tag_eq)
            (C pi (C sbt2 get_spec get_ca_atom) (C sbt2 get_spec get_cb_atom)) input

  atomic_pair_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi (C sbt2 get_spec get_ca_atom) (C sbt2 get_spec get_cb_atom)) input)
                (ap2 pi (ap1 (C sbt2 get_spec get_ca_atom) input)
                        (ap1 (C sbt2 get_spec get_cb_atom) input)))
  atomic_pair_unfold input =
    ax_C pi (C sbt2 get_spec get_ca_atom) (C sbt2 get_spec get_cb_atom) input

  C_sbt_ca_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C sbt2 get_spec get_ca_atom) input)
                (ap2 sbt2 (ap1 get_spec input) (ap1 get_ca_atom input)))
  C_sbt_ca_unfold input = ax_C sbt2 get_spec get_ca_atom input

  C_sbt_cb_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C sbt2 get_spec get_cb_atom) input)
                (ap2 sbt2 (ap1 get_spec input) (ap1 get_cb_atom input)))
  C_sbt_cb_unfold input = ax_C sbt2 get_spec get_cb_atom input

  imp_branch_sbf2_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 imp_branch_sbf2 input)
                (ap2 pi (ap1 (constN tag_imp) input)
                        (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input)))
  imp_branch_sbf2_unfold input =
    ax_C pi (constN tag_imp)
            (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input

  imp_pair_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input)
                (ap2 pi (ap1 (lookupAt get_cP_imp) input)
                        (ap1 (lookupAt get_cQ_imp) input)))
  imp_pair_unfold input =
    ax_C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp) input

------------------------------------------------------------------------
-- lookupAt unfolding (re-derived locally).

private
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
-- HP_sbf stability bridge (mirrors HP_sbt_eq_sbt_under_leq).

private
  HP_sbf_eq_sbf_under_leq :
    (spec ct K : Term) ->
    Deriv (leq ct K) ->
    Deriv (eqF (HPsbt baseValue_sbf2 stepFun_sbf2 spec ct K) (ap2 sbf2 spec ct))
  HP_sbf_eq_sbf_under_leq spec ct K leq_ct_K =
    let stab :
          Deriv (eqF (HPsbt baseValue_sbf2 stepFun_sbf2 spec ct K)
                      (HPsbt baseValue_sbf2 stepFun_sbf2 spec ct ct))
        stab = mp (stabilityP_sbt_at baseValue_sbf2 stepFun_sbf2 spec ct K) leq_ct_K

        subCT_O : Deriv (eqF (ap2 sub ct ct) O)
        subCT_O = sub_self ct

        iter_arg :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct) (ap2 sub ct ct))
                      (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct) O))
        iter_arg = congR (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct) subCT_O

        iter_base :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct) O)
                      (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct))
        iter_base = iter_base_univ Snd (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct)

        iter_full :
          Deriv (eqF (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct) (ap2 sub ct ct))
                      (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct))
        iter_full = ruleTrans iter_arg iter_base

        HP_at_ct :
          Deriv (eqF (HPsbt baseValue_sbf2 stepFun_sbf2 spec ct ct)
                      (ap1 Fst (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct)))
        HP_at_ct = cong1 Fst iter_full

        readOff_eq :
          Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec ct))
                      (ap1 Fst (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct)))
        readOff_eq = readOff_spec_eq (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec ct)

        readOff_eq_sym :
          Deriv (eqF (ap1 Fst (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec ct))
                      (ap1 readOff_spec (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec ct)))
        readOff_eq_sym = ruleSym readOff_eq

        sbf_eq :
          Deriv (eqF (ap2 sbf2 spec ct) (ap1 readOff_spec (ap2 sbf2State spec ct)))
        sbf_eq = sbf2_unfold spec ct

        sbf_eq_sym :
          Deriv (eqF (ap1 readOff_spec (ap2 sbf2State spec ct)) (ap2 sbf2 spec ct))
        sbf_eq_sym = ruleSym sbf_eq

    in ruleTrans stab (ruleTrans HP_at_ct (ruleTrans readOff_eq_sym sbf_eq_sym))

------------------------------------------------------------------------
-- Leq lemmas at the specific shapes.

-- For neg: leq cP (pi_succ_outer (natCode 10) cP).

leq_cP_P_outer_neg :
  (cP : Term) ->
  Deriv (leq cP (pi_succ_outer (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                                cP))
leq_cP_P_outer_neg cP =
  let A : Term
      A = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
      Y : Term
      Y = cP
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
  in leq_sigma_right X Y

-- For imp: leq cP and leq cQ to (pi_succ_outer (natCode 11) (pi cP cQ)).

leq_cQ_P_outer_imp :
  (cP cQ : Term) ->
  Deriv (leq cQ (pi_succ_outer (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
                                (ap2 pi cP cQ)))
leq_cQ_P_outer_imp cP cQ =
  let A : Term
      A = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
      Y : Term
      Y = ap2 pi cP cQ
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
      l1 : Deriv (leq cQ Y)
      l1 = leq_pi_right cP cQ
      l2 : Deriv (leq Y (ap2 sigma X Y))
      l2 = leq_sigma_right X Y
  in leq_trans cQ Y (ap2 sigma X Y) l1 l2

leq_cP_P_outer_imp :
  (cP cQ : Term) ->
  Deriv (leq cP (pi_succ_outer (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
                                (ap2 pi cP cQ)))
leq_cP_P_outer_imp cP cQ =
  let A : Term
      A = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
      Y : Term
      Y = ap2 pi cP cQ
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))

      -- Mirror leq_ca_P_outer_ap2 's chain.
      l1 : Deriv (leq cP (ap2 sigma cP cQ))
      l1 = leq_sigma_left cP cQ

      l2 : Deriv (leq (ap2 sigma cP cQ) (ap1 tau (ap2 sigma cP cQ)))
      l2 = ruleInst 0 (ap2 sigma cP cQ) BRA3.ChurchT92.T92

      l3 : Deriv (leq (ap1 tau (ap2 sigma cP cQ)) (ap2 sigma (ap1 tau (ap2 sigma cP cQ)) cQ))
      l3 = leq_sigma_left (ap1 tau (ap2 sigma cP cQ)) cQ

      eqPi : Deriv (eqF (ap2 sigma (ap1 tau (ap2 sigma cP cQ)) cQ) (ap2 pi cP cQ))
      eqPi = ruleSym (BRA4.LeqMono.T114_at cP cQ)

      cong_sub :
        Deriv (eqF (ap2 sub (ap1 tau (ap2 sigma cP cQ)) (ap2 sigma (ap1 tau (ap2 sigma cP cQ)) cQ))
                    (ap2 sub (ap1 tau (ap2 sigma cP cQ)) (ap2 pi cP cQ)))
      cong_sub = congR sub (ap1 tau (ap2 sigma cP cQ)) eqPi

      cong_sub_sym :
        Deriv (eqF (ap2 sub (ap1 tau (ap2 sigma cP cQ)) (ap2 pi cP cQ))
                    (ap2 sub (ap1 tau (ap2 sigma cP cQ)) (ap2 sigma (ap1 tau (ap2 sigma cP cQ)) cQ)))
      cong_sub_sym = ruleSym cong_sub

      l3_pi : Deriv (leq (ap1 tau (ap2 sigma cP cQ)) (ap2 pi cP cQ))
      l3_pi = ruleTrans cong_sub_sym l3

      l12 : Deriv (leq cP (ap1 tau (ap2 sigma cP cQ)))
      l12 = leq_trans cP (ap2 sigma cP cQ) (ap1 tau (ap2 sigma cP cQ)) l1 l2

      l123 : Deriv (leq cP (ap2 pi cP cQ))
      l123 = leq_trans cP (ap1 tau (ap2 sigma cP cQ)) (ap2 pi cP cQ) l12 l3_pi

      l5 : Deriv (leq Y (ap2 sigma X Y))
      l5 = leq_sigma_right X Y
  in leq_trans cP Y (ap2 sigma X Y) l123 l5

-- For atomic: leq ca and leq cb to (pi_succ_outer (natCode 9) (pi ca cb)).

leq_cb_P_outer_atom :
  (ca cb : Term) ->
  Deriv (leq cb (pi_succ_outer (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (ap2 pi ca cb)))
leq_cb_P_outer_atom ca cb =
  let A : Term
      A = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) -- 9
      Y : Term
      Y = ap2 pi ca cb
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))
      l1 : Deriv (leq cb Y)
      l1 = leq_pi_right ca cb
      l2 : Deriv (leq Y (ap2 sigma X Y))
      l2 = leq_sigma_right X Y
  in leq_trans cb Y (ap2 sigma X Y) l1 l2

leq_ca_P_outer_atom :
  (ca cb : Term) ->
  Deriv (leq ca (pi_succ_outer (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) (ap2 pi ca cb)))
leq_ca_P_outer_atom ca cb =
  let A : Term
      A = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      Y : Term
      Y = ap2 pi ca cb
      X : Term
      X = ap2 sigma (ap2 sigma A Y) (ap1 tau (ap2 sigma A Y))

      l1 : Deriv (leq ca (ap2 sigma ca cb))
      l1 = leq_sigma_left ca cb

      l2 : Deriv (leq (ap2 sigma ca cb) (ap1 tau (ap2 sigma ca cb)))
      l2 = ruleInst 0 (ap2 sigma ca cb) BRA3.ChurchT92.T92

      l3 : Deriv (leq (ap1 tau (ap2 sigma ca cb)) (ap2 sigma (ap1 tau (ap2 sigma ca cb)) cb))
      l3 = leq_sigma_left (ap1 tau (ap2 sigma ca cb)) cb

      eqPi : Deriv (eqF (ap2 sigma (ap1 tau (ap2 sigma ca cb)) cb) (ap2 pi ca cb))
      eqPi = ruleSym (BRA4.LeqMono.T114_at ca cb)

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

      l5 : Deriv (leq Y (ap2 sigma X Y))
      l5 = leq_sigma_right X Y
  in leq_trans ca Y (ap2 sigma X Y) l123 l5

------------------------------------------------------------------------
-- sbf2_at_neg :  the SbContract closure for neg.

sbf2_at_neg :
  (k1 k2 : Nat) (S1 S2 cP : Term) ->
  Deriv (eqF (ap2 sbf2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2))
               (ap2 pi (natCode tag_neg) cP))
              (ap2 pi (natCode tag_neg)
                (ap2 sbf2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)) cP)))
sbf2_at_neg k1 k2 S1 S2 cP =
  let spec : Term
      spec = ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)

      input : Term
      input = ap2 pi (natCode tag_neg) cP

      -- tag_neg = 11; natCode tag_neg = s (natCode 10).
      A_outer : Term
      A_outer = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) -- natCode 10

      P_outer : Term
      P_outer = pi_succ_outer A_outer cP

      prev : Term
      prev = ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      step1 :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 readOff_spec (ap2 sbf2State spec input)))
      step1 = sbf2_unfold spec input

      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ A_outer cP

      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec input)
                    (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec (ap1 s P_outer)))
      cov_lift = congR (cov_spec baseValue_sbf2 stepFun_sbf2) spec input_eq_sP_outer

      cov_step :
        Deriv (eqF (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec (ap1 s P_outer))
                    (ap1 (state_step_spec stepFun_sbf2) prev))
      cov_step = cov_spec_step_univ baseValue_sbf2 stepFun_sbf2 spec P_outer

      sbf2State_eq :
        Deriv (eqF (ap2 sbf2State spec input) (ap1 (state_step_spec stepFun_sbf2) prev))
      sbf2State_eq = ruleTrans cov_lift cov_step

      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 sbf2State spec input))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbf2) prev)))
      readOff_lift = cong1 readOff_spec sbf2State_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbf2) prev))
                    (ap2 stepFun_sbf2 (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ stepFun_sbf2 prev

      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq baseValue_sbf2 stepFun_sbf2 spec P_outer

      stepFun_lift :
        Deriv (eqF (ap2 stepFun_sbf2 (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun_sbf2 P_outer (ap1 Snd prev)))
      stepFun_lift = congL stepFun_sbf2 (ap1 Snd prev) Fst_prev_eq

      Post_eq :
        Deriv (eqF (ap2 stepFun_sbf2 P_outer (ap1 Snd prev))
                    (ap1 stepBody_sbf2 (ap2 pi P_outer (ap1 Snd prev))))
      Post_eq = axPost stepBody_sbf2 pi P_outer (ap1 Snd prev)

      -- Tag dispatch.
      get_newK_eq :
        Deriv (eqF (ap1 get_newK input_pkg') (ap1 s P_outer))
      get_newK_eq = get_newK_at_pi P_outer (ap1 Snd prev)

      newK_eq_input :
        Deriv (eqF (ap1 get_newK input_pkg') input)
      newK_eq_input = ruleTrans get_newK_eq (ruleSym input_eq_sP_outer)

      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_neg))
      Fst_input = axFst (natCode tag_neg) cP

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_neg))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      -- isEq = O, isNeg = sO.
      isEq_value : Deriv (eqF (ap1 isEq input_pkg') O)
      isEq_value = isEq_at_natCodeNeg_O input_pkg' get_tag_value

      isNeg_value : Deriv (eqF (ap1 isNeg input_pkg') (ap1 s O))
      isNeg_value = isNeg_at_natCodeNeg_sO input_pkg' get_tag_value

      stepBody_to_neg_or :
        Deriv (eqF (ap1 stepBody_sbf2 input_pkg') (ap1 neg_or_above input_pkg'))
      stepBody_to_neg_or = stepBody_sbf2_to_neg_or_above input_pkg' isEq_value

      negor_to_neg :
        Deriv (eqF (ap1 neg_or_above input_pkg') (ap1 neg_branch_sbf2 input_pkg'))
      negor_to_neg = neg_or_above_to_neg input_pkg' isNeg_value

      stepBody_to_neg :
        Deriv (eqF (ap1 stepBody_sbf2 input_pkg') (ap1 neg_branch_sbf2 input_pkg'))
      stepBody_to_neg = ruleTrans stepBody_to_neg_or negor_to_neg

      -- neg_branch unfolding.
      negbr_unfold :
        Deriv (eqF (ap1 neg_branch_sbf2 input_pkg')
                    (ap2 pi (ap1 (constN tag_neg) input_pkg')
                            (ap1 (lookupAt get_body) input_pkg')))
      negbr_unfold = neg_branch_sbf2_unfold input_pkg'

      constN_at :
        Deriv (eqF (ap1 (constN tag_neg) input_pkg') (natCode tag_neg))
      constN_at = constN_eq tag_neg input_pkg'

      negbr_step1 :
        Deriv (eqF (ap1 neg_branch_sbf2 input_pkg')
                    (ap2 pi (natCode tag_neg) (ap1 (lookupAt get_body) input_pkg')))
      negbr_step1 = ruleTrans negbr_unfold
                      (congL pi (ap1 (lookupAt get_body) input_pkg') constN_at)

      -- lookupAt get_body input_pkg' = HPsbf spec cP P_outer = sbf2 spec cP.

      lookup_unfold :
        Deriv (eqF (ap1 (lookupAt get_body) input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg') (ap1 get_body input_pkg')))))
      lookup_unfold = lookupAt_unfold get_body input_pkg'

      get_K_value :
        Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      -- get_body input_pkg' = Snd (Snd (s P_outer)) ... wait, get_body input_pkg' = Snd (s P_outer)
      -- Then Snd (s P_outer) = Snd input = cP.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_cP :
        Deriv (eqF (ap1 Snd input) cP)
      Snd_input_eq_cP = axSnd (natCode tag_neg) cP

      get_body_value : Deriv (eqF (ap1 get_body input_pkg') cP)
      get_body_value =
        let s1 :
              Deriv (eqF (ap1 get_body input_pkg') (ap1 Snd (ap1 s P_outer)))
            s1 = get_body_at_pi P_outer (ap1 Snd prev)
        in ruleTrans s1 (ruleTrans Snd_sP_eq Snd_input_eq_cP)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg') (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      iter_arg :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_body input_pkg'))
                    (ap2 sub P_outer cP))
      iter_arg = ruleTrans (congL sub (ap1 get_body input_pkg') get_K_value)
                  (congR sub P_outer get_body_value)

      iter_full :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                          (ap2 sub (ap1 get_K input_pkg') (ap1 get_body input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer)
                          (ap2 sub P_outer cP)))
      iter_full = ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_body input_pkg')) get_table_value)
                   (congR (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer) iter_arg)

      val_cP_unfold :
        Deriv (eqF (ap1 (lookupAt get_body) input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer)
                              (ap2 sub P_outer cP))))
      val_cP_unfold = ruleTrans lookup_unfold (cong1 Fst iter_full)

      leq_cP_P : Deriv (leq cP P_outer)
      leq_cP_P = leq_cP_P_outer_neg cP

      HP_to_sbf :
        Deriv (eqF (HPsbt baseValue_sbf2 stepFun_sbf2 spec cP P_outer) (ap2 sbf2 spec cP))
      HP_to_sbf = HP_sbf_eq_sbf_under_leq spec cP P_outer leq_cP_P

      val_cP_value :
        Deriv (eqF (ap1 (lookupAt get_body) input_pkg') (ap2 sbf2 spec cP))
      val_cP_value = ruleTrans val_cP_unfold HP_to_sbf

      -- Assemble pi (natCode tag_neg) (sbf2 spec cP).
      negbr_value :
        Deriv (eqF (ap1 neg_branch_sbf2 input_pkg')
                    (ap2 pi (natCode tag_neg) (ap2 sbf2 spec cP)))
      negbr_value =
        ruleTrans negbr_step1 (congR pi (natCode tag_neg) val_cP_value)

      chain_to_stepBody :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 stepBody_sbf2 input_pkg'))
      chain_to_stepBody =
        ruleTrans step1
          (ruleTrans readOff_lift
            (ruleTrans readOff_eval
              (ruleTrans stepFun_lift Post_eq)))

      chain_to_negbr :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 neg_branch_sbf2 input_pkg'))
      chain_to_negbr = ruleTrans chain_to_stepBody stepBody_to_neg
  in ruleTrans chain_to_negbr negbr_value

------------------------------------------------------------------------
-- sbf2_at_imp :  the SbContract closure for imp.
--
-- Mirrors sbt_at_ap2: two formula sub-positions (cP, cQ), two sbf-table
-- lookups.

sbf2_at_imp :
  (k1 k2 : Nat) (S1 S2 cP cQ : Term) ->
  Deriv (eqF (ap2 sbf2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2))
               (ap2 pi (natCode tag_imp) (ap2 pi cP cQ)))
              (ap2 pi (natCode tag_imp)
                (ap2 pi
                  (ap2 sbf2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)) cP)
                  (ap2 sbf2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)) cQ))))
sbf2_at_imp k1 k2 S1 S2 cP cQ =
  let spec : Term
      spec = ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)

      Y_body : Term
      Y_body = ap2 pi cP cQ

      input : Term
      input = ap2 pi (natCode tag_imp) Y_body

      -- tag_imp = 12, natCode tag_imp = s (natCode 11).
      A_outer : Term
      A_outer = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      step1 :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 readOff_spec (ap2 sbf2State spec input)))
      step1 = sbf2_unfold spec input

      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ A_outer Y_body

      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec input)
                    (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec (ap1 s P_outer)))
      cov_lift = congR (cov_spec baseValue_sbf2 stepFun_sbf2) spec input_eq_sP_outer

      cov_step :
        Deriv (eqF (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec (ap1 s P_outer))
                    (ap1 (state_step_spec stepFun_sbf2) prev))
      cov_step = cov_spec_step_univ baseValue_sbf2 stepFun_sbf2 spec P_outer

      sbf2State_eq :
        Deriv (eqF (ap2 sbf2State spec input) (ap1 (state_step_spec stepFun_sbf2) prev))
      sbf2State_eq = ruleTrans cov_lift cov_step

      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 sbf2State spec input))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbf2) prev)))
      readOff_lift = cong1 readOff_spec sbf2State_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbf2) prev))
                    (ap2 stepFun_sbf2 (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ stepFun_sbf2 prev

      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq baseValue_sbf2 stepFun_sbf2 spec P_outer

      stepFun_lift :
        Deriv (eqF (ap2 stepFun_sbf2 (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun_sbf2 P_outer (ap1 Snd prev)))
      stepFun_lift = congL stepFun_sbf2 (ap1 Snd prev) Fst_prev_eq

      Post_eq :
        Deriv (eqF (ap2 stepFun_sbf2 P_outer (ap1 Snd prev))
                    (ap1 stepBody_sbf2 (ap2 pi P_outer (ap1 Snd prev))))
      Post_eq = axPost stepBody_sbf2 pi P_outer (ap1 Snd prev)

      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_imp))
      Fst_input = axFst (natCode tag_imp) Y_body

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_imp))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isEq_value : Deriv (eqF (ap1 isEq input_pkg') O)
      isEq_value = isEq_at_natCodeImp_O input_pkg' get_tag_value

      isNeg_value : Deriv (eqF (ap1 isNeg input_pkg') O)
      isNeg_value = isNeg_at_natCodeImp_O input_pkg' get_tag_value

      isImp_value : Deriv (eqF (ap1 isImp input_pkg') (ap1 s O))
      isImp_value = isImp_at_natCodeImp_sO input_pkg' get_tag_value

      stepBody_to_neg_or :
        Deriv (eqF (ap1 stepBody_sbf2 input_pkg') (ap1 neg_or_above input_pkg'))
      stepBody_to_neg_or = stepBody_sbf2_to_neg_or_above input_pkg' isEq_value

      negor_to_imp :
        Deriv (eqF (ap1 neg_or_above input_pkg') (ap1 imp_branch_sbf2 input_pkg'))
      negor_to_imp = neg_or_above_to_imp input_pkg' isNeg_value isImp_value

      stepBody_to_imp :
        Deriv (eqF (ap1 stepBody_sbf2 input_pkg') (ap1 imp_branch_sbf2 input_pkg'))
      stepBody_to_imp = ruleTrans stepBody_to_neg_or negor_to_imp

      -- imp_branch unfolding.
      impbr_unfold :
        Deriv (eqF (ap1 imp_branch_sbf2 input_pkg')
                    (ap2 pi (ap1 (constN tag_imp) input_pkg')
                            (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input_pkg')))
      impbr_unfold = imp_branch_sbf2_unfold input_pkg'

      constN_at :
        Deriv (eqF (ap1 (constN tag_imp) input_pkg') (natCode tag_imp))
      constN_at = constN_eq tag_imp input_pkg'

      impbr_step1 :
        Deriv (eqF (ap1 imp_branch_sbf2 input_pkg')
                    (ap2 pi (natCode tag_imp)
                            (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input_pkg')))
      impbr_step1 = ruleTrans impbr_unfold
                      (congL pi (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input_pkg') constN_at)

      inner_C_unfold :
        Deriv (eqF (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input_pkg')
                    (ap2 pi (ap1 (lookupAt get_cP_imp) input_pkg')
                            (ap1 (lookupAt get_cQ_imp) input_pkg')))
      inner_C_unfold = imp_pair_unfold input_pkg'

      -- Snd (s P_outer) = Y_body.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_Yb :
        Deriv (eqF (ap1 Snd input) Y_body)
      Snd_input_eq_Yb = axSnd (natCode tag_imp) Y_body

      Snd_sP_to_Y :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y_body)
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

      -- get_cP_imp input_pkg' = cP.
      get_cP_value : Deriv (eqF (ap1 get_cP_imp input_pkg') cP)
      get_cP_value =
        let s1 : Deriv (eqF (ap1 get_cP_imp input_pkg') (ap1 Fst (ap1 Snd (ap1 s P_outer))))
            s1 = get_cP_imp_at_pi P_outer (ap1 Snd prev)
            Fst_Y : Deriv (eqF (ap1 Fst Y_body) cP)
            Fst_Y = axFst cP cQ
        in ruleTrans s1 (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_cQ_value : Deriv (eqF (ap1 get_cQ_imp input_pkg') cQ)
      get_cQ_value =
        let s1 : Deriv (eqF (ap1 get_cQ_imp input_pkg') (ap1 Snd (ap1 Snd (ap1 s P_outer))))
            s1 = get_cQ_imp_at_pi P_outer (ap1 Snd prev)
            Snd_Y : Deriv (eqF (ap1 Snd Y_body) cQ)
            Snd_Y = axSnd cP cQ
        in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      get_K_value :
        Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg') (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- val_cP via lookupAt get_cP_imp.
      val_cP_unfold :
        Deriv (eqF (ap1 (lookupAt get_cP_imp) input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg') (ap1 get_cP_imp input_pkg')))))
      val_cP_unfold = lookupAt_unfold get_cP_imp input_pkg'

      iter_arg_cP :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_cP_imp input_pkg'))
                    (ap2 sub P_outer cP))
      iter_arg_cP = ruleTrans (congL sub (ap1 get_cP_imp input_pkg') get_K_value)
                     (congR sub P_outer get_cP_value)

      iter_full_cP :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                          (ap2 sub (ap1 get_K input_pkg') (ap1 get_cP_imp input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer)
                          (ap2 sub P_outer cP)))
      iter_full_cP = ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_cP_imp input_pkg')) get_table_value)
                      (congR (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer) iter_arg_cP)

      val_cP_to_HP :
        Deriv (eqF (ap1 (lookupAt get_cP_imp) input_pkg')
                    (HPsbt baseValue_sbf2 stepFun_sbf2 spec cP P_outer))
      val_cP_to_HP = ruleTrans val_cP_unfold (cong1 Fst iter_full_cP)

      leq_cP_P : Deriv (leq cP P_outer)
      leq_cP_P = leq_cP_P_outer_imp cP cQ

      val_cP_value :
        Deriv (eqF (ap1 (lookupAt get_cP_imp) input_pkg') (ap2 sbf2 spec cP))
      val_cP_value = ruleTrans val_cP_to_HP
                       (HP_sbf_eq_sbf_under_leq spec cP P_outer leq_cP_P)

      -- val_cQ via lookupAt get_cQ_imp.
      val_cQ_unfold :
        Deriv (eqF (ap1 (lookupAt get_cQ_imp) input_pkg')
                    (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg')
                              (ap2 sub (ap1 get_K input_pkg') (ap1 get_cQ_imp input_pkg')))))
      val_cQ_unfold = lookupAt_unfold get_cQ_imp input_pkg'

      iter_arg_cQ :
        Deriv (eqF (ap2 sub (ap1 get_K input_pkg') (ap1 get_cQ_imp input_pkg'))
                    (ap2 sub P_outer cQ))
      iter_arg_cQ = ruleTrans (congL sub (ap1 get_cQ_imp input_pkg') get_K_value)
                     (congR sub P_outer get_cQ_value)

      iter_full_cQ :
        Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg')
                          (ap2 sub (ap1 get_K input_pkg') (ap1 get_cQ_imp input_pkg')))
                    (ap2 (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer)
                          (ap2 sub P_outer cQ)))
      iter_full_cQ = ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg') (ap1 get_cQ_imp input_pkg')) get_table_value)
                      (congR (iter Snd) (HistP_sbt baseValue_sbf2 stepFun_sbf2 spec P_outer) iter_arg_cQ)

      val_cQ_to_HP :
        Deriv (eqF (ap1 (lookupAt get_cQ_imp) input_pkg')
                    (HPsbt baseValue_sbf2 stepFun_sbf2 spec cQ P_outer))
      val_cQ_to_HP = ruleTrans val_cQ_unfold (cong1 Fst iter_full_cQ)

      leq_cQ_P : Deriv (leq cQ P_outer)
      leq_cQ_P = leq_cQ_P_outer_imp cP cQ

      val_cQ_value :
        Deriv (eqF (ap1 (lookupAt get_cQ_imp) input_pkg') (ap2 sbf2 spec cQ))
      val_cQ_value = ruleTrans val_cQ_to_HP
                       (HP_sbf_eq_sbf_under_leq spec cQ P_outer leq_cQ_P)

      -- Assemble pi (sbf2 spec cP) (sbf2 spec cQ).
      pair_val_value :
        Deriv (eqF (ap1 (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp)) input_pkg')
                    (ap2 pi (ap2 sbf2 spec cP) (ap2 sbf2 spec cQ)))
      pair_val_value =
        ruleTrans inner_C_unfold
          (ruleTrans (congL pi (ap1 (lookupAt get_cQ_imp) input_pkg') val_cP_value)
                      (congR pi (ap2 sbf2 spec cP) val_cQ_value))

      impbr_value :
        Deriv (eqF (ap1 imp_branch_sbf2 input_pkg')
                    (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 sbf2 spec cP) (ap2 sbf2 spec cQ))))
      impbr_value =
        ruleTrans impbr_step1 (congR pi (natCode tag_imp) pair_val_value)

      chain_to_stepBody :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 stepBody_sbf2 input_pkg'))
      chain_to_stepBody =
        ruleTrans step1
          (ruleTrans readOff_lift
            (ruleTrans readOff_eval
              (ruleTrans stepFun_lift Post_eq)))

      chain_to_impbr :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 imp_branch_sbf2 input_pkg'))
      chain_to_impbr = ruleTrans chain_to_stepBody stepBody_to_imp
  in ruleTrans chain_to_impbr impbr_value

------------------------------------------------------------------------
-- sbf2_at_atomic :  the SbContract closure for atomic.
--
-- Direct sbt2 invocation in sub-positions via  C sbt2 get_spec get_ca_atom .
-- No stability/lookup; instead uses  fstSnd_cov_spec_eq  (spec preservation)
-- to bridge  get_spec input_pkg' = spec .

sbf2_at_atomic :
  (k1 k2 : Nat) (S1 S2 ca cb : Term) ->
  Deriv (eqF (ap2 sbf2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2))
               (ap2 pi (natCode tag_eq) (ap2 pi ca cb)))
              (ap2 pi (natCode tag_eq)
                (ap2 pi
                  (ap2 sbt2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)) ca)
                  (ap2 sbt2 (ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)) cb))))
sbf2_at_atomic k1 k2 S1 S2 ca cb =
  let spec : Term
      spec = ap2 pi (ap2 pi (natCode k1) S1) (ap2 pi (natCode k2) S2)

      Y_body : Term
      Y_body = ap2 pi ca cb

      input : Term
      input = ap2 pi (natCode tag_eq) Y_body

      -- tag_eq = 10, natCode tag_eq = s (natCode 9).
      A_outer : Term
      A_outer = natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) -- 9

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec P_outer

      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      step1 :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 readOff_spec (ap2 sbf2State spec input)))
      step1 = sbf2_unfold spec input

      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ A_outer Y_body

      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec input)
                    (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec (ap1 s P_outer)))
      cov_lift = congR (cov_spec baseValue_sbf2 stepFun_sbf2) spec input_eq_sP_outer

      cov_step :
        Deriv (eqF (ap2 (cov_spec baseValue_sbf2 stepFun_sbf2) spec (ap1 s P_outer))
                    (ap1 (state_step_spec stepFun_sbf2) prev))
      cov_step = cov_spec_step_univ baseValue_sbf2 stepFun_sbf2 spec P_outer

      sbf2State_eq :
        Deriv (eqF (ap2 sbf2State spec input) (ap1 (state_step_spec stepFun_sbf2) prev))
      sbf2State_eq = ruleTrans cov_lift cov_step

      readOff_lift :
        Deriv (eqF (ap1 readOff_spec (ap2 sbf2State spec input))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbf2) prev)))
      readOff_lift = cong1 readOff_spec sbf2State_eq

      readOff_eval :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun_sbf2) prev))
                    (ap2 stepFun_sbf2 (ap1 Fst prev) (ap1 Snd prev)))
      readOff_eval = readOff_state_step_univ stepFun_sbf2 prev

      Fst_prev_eq :
        Deriv (eqF (ap1 Fst prev) P_outer)
      Fst_prev_eq = fst_cov_spec_eq baseValue_sbf2 stepFun_sbf2 spec P_outer

      stepFun_lift :
        Deriv (eqF (ap2 stepFun_sbf2 (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun_sbf2 P_outer (ap1 Snd prev)))
      stepFun_lift = congL stepFun_sbf2 (ap1 Snd prev) Fst_prev_eq

      Post_eq :
        Deriv (eqF (ap2 stepFun_sbf2 P_outer (ap1 Snd prev))
                    (ap1 stepBody_sbf2 (ap2 pi P_outer (ap1 Snd prev))))
      Post_eq = axPost stepBody_sbf2 pi P_outer (ap1 Snd prev)

      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag input_pkg') (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_eq))
      Fst_input = axFst (natCode tag_eq) Y_body

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_eq))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                       (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isEq_value : Deriv (eqF (ap1 isEq input_pkg') (ap1 s O))
      isEq_value = isEq_at_natCodeEq_sO input_pkg' get_tag_value

      stepBody_to_atom :
        Deriv (eqF (ap1 stepBody_sbf2 input_pkg') (ap1 atomic_branch_sbf2 input_pkg'))
      stepBody_to_atom = stepBody_sbf2_to_atomic input_pkg' isEq_value

      -- atomic_branch unfolding.
      atombr_unfold :
        Deriv (eqF (ap1 atomic_branch_sbf2 input_pkg')
                    (ap2 pi (ap1 (constN tag_eq) input_pkg')
                            (ap1 (C pi (C sbt2 get_spec get_ca_atom)
                                       (C sbt2 get_spec get_cb_atom)) input_pkg')))
      atombr_unfold = atomic_branch_sbf2_unfold input_pkg'

      constN_at :
        Deriv (eqF (ap1 (constN tag_eq) input_pkg') (natCode tag_eq))
      constN_at = constN_eq tag_eq input_pkg'

      atombr_step1 :
        Deriv (eqF (ap1 atomic_branch_sbf2 input_pkg')
                    (ap2 pi (natCode tag_eq)
                            (ap1 (C pi (C sbt2 get_spec get_ca_atom)
                                       (C sbt2 get_spec get_cb_atom)) input_pkg')))
      atombr_step1 = ruleTrans atombr_unfold
                       (congL pi (ap1 (C pi (C sbt2 get_spec get_ca_atom)
                                                (C sbt2 get_spec get_cb_atom)) input_pkg') constN_at)

      inner_C_unfold :
        Deriv (eqF (ap1 (C pi (C sbt2 get_spec get_ca_atom)
                              (C sbt2 get_spec get_cb_atom)) input_pkg')
                    (ap2 pi (ap1 (C sbt2 get_spec get_ca_atom) input_pkg')
                            (ap1 (C sbt2 get_spec get_cb_atom) input_pkg')))
      inner_C_unfold = atomic_pair_unfold input_pkg'

      -- C sbt2 get_spec get_ca_atom input_pkg' = sbt2 (get_spec input_pkg') (get_ca_atom input_pkg').
      sbt_ca_unfold :
        Deriv (eqF (ap1 (C sbt2 get_spec get_ca_atom) input_pkg')
                    (ap2 sbt2 (ap1 get_spec input_pkg') (ap1 get_ca_atom input_pkg')))
      sbt_ca_unfold = C_sbt_ca_unfold input_pkg'

      sbt_cb_unfold :
        Deriv (eqF (ap1 (C sbt2 get_spec get_cb_atom) input_pkg')
                    (ap2 sbt2 (ap1 get_spec input_pkg') (ap1 get_cb_atom input_pkg')))
      sbt_cb_unfold = C_sbt_cb_unfold input_pkg'

      -- get_spec input_pkg' = Fst (Snd input_pkg') = Fst (Snd prev) = spec
      -- via spec preservation.
      get_spec_at :
        Deriv (eqF (ap1 get_spec input_pkg') (ap1 Fst (ap1 Snd prev)))
      get_spec_at = get_spec_at_pi P_outer (ap1 Snd prev)

      fstSnd_prev :
        Deriv (eqF (ap1 Fst (ap1 Snd prev)) spec)
      fstSnd_prev = fstSnd_cov_spec_eq baseValue_sbf2 stepFun_sbf2 spec P_outer

      get_spec_value :
        Deriv (eqF (ap1 get_spec input_pkg') spec)
      get_spec_value = ruleTrans get_spec_at fstSnd_prev

      -- get_ca_atom input_pkg' = ca, get_cb_atom input_pkg' = cb.
      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_Yb :
        Deriv (eqF (ap1 Snd input) Y_body)
      Snd_input_eq_Yb = axSnd (natCode tag_eq) Y_body

      Snd_sP_to_Y :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y_body)
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

      get_ca_value : Deriv (eqF (ap1 get_ca_atom input_pkg') ca)
      get_ca_value =
        let s1 : Deriv (eqF (ap1 get_ca_atom input_pkg') (ap1 Fst (ap1 Snd (ap1 s P_outer))))
            s1 = get_ca_atom_at_pi P_outer (ap1 Snd prev)
            Fst_Y : Deriv (eqF (ap1 Fst Y_body) ca)
            Fst_Y = axFst ca cb
        in ruleTrans s1 (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_cb_value : Deriv (eqF (ap1 get_cb_atom input_pkg') cb)
      get_cb_value =
        let s1 : Deriv (eqF (ap1 get_cb_atom input_pkg') (ap1 Snd (ap1 Snd (ap1 s P_outer))))
            s1 = get_cb_atom_at_pi P_outer (ap1 Snd prev)
            Snd_Y : Deriv (eqF (ap1 Snd Y_body) cb)
            Snd_Y = axSnd ca cb
        in ruleTrans s1 (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      -- sbt2 (get_spec ipkg) (get_ca_atom ipkg) = sbt2 spec ca.
      sbt_ca_value :
        Deriv (eqF (ap1 (C sbt2 get_spec get_ca_atom) input_pkg') (ap2 sbt2 spec ca))
      sbt_ca_value =
        ruleTrans sbt_ca_unfold
          (ruleTrans (congL sbt2 (ap1 get_ca_atom input_pkg') get_spec_value)
                      (congR sbt2 spec get_ca_value))

      sbt_cb_value :
        Deriv (eqF (ap1 (C sbt2 get_spec get_cb_atom) input_pkg') (ap2 sbt2 spec cb))
      sbt_cb_value =
        ruleTrans sbt_cb_unfold
          (ruleTrans (congL sbt2 (ap1 get_cb_atom input_pkg') get_spec_value)
                      (congR sbt2 spec get_cb_value))

      pair_val_value :
        Deriv (eqF (ap1 (C pi (C sbt2 get_spec get_ca_atom)
                              (C sbt2 get_spec get_cb_atom)) input_pkg')
                    (ap2 pi (ap2 sbt2 spec ca) (ap2 sbt2 spec cb)))
      pair_val_value =
        ruleTrans inner_C_unfold
          (ruleTrans (congL pi (ap1 (C sbt2 get_spec get_cb_atom) input_pkg') sbt_ca_value)
                      (congR pi (ap2 sbt2 spec ca) sbt_cb_value))

      atombr_value :
        Deriv (eqF (ap1 atomic_branch_sbf2 input_pkg')
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (ap2 sbt2 spec ca) (ap2 sbt2 spec cb))))
      atombr_value =
        ruleTrans atombr_step1 (congR pi (natCode tag_eq) pair_val_value)

      chain_to_stepBody :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 stepBody_sbf2 input_pkg'))
      chain_to_stepBody =
        ruleTrans step1
          (ruleTrans readOff_lift
            (ruleTrans readOff_eval
              (ruleTrans stepFun_lift Post_eq)))

      chain_to_atombr :
        Deriv (eqF (ap2 sbf2 spec input) (ap1 atomic_branch_sbf2 input_pkg'))
      chain_to_atombr = ruleTrans chain_to_stepBody stepBody_to_atom
  in ruleTrans chain_to_atombr atombr_value

------------------------------------------------------------------------
-- SbContract2 record assembly lives in BRA4.SbContract2.
