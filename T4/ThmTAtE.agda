{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ThmTAtE -- discharge of the  E_intro / E_elim  closures of  thmT .
--
-- Both E rules are CLOSED-conclusion formers (a  Fun1  carries no
-- term-variable, so  E f  is a closed Sigma-0-1 sentence).  The thmT
-- branches therefore read the conclusion code DIRECTLY off the encoded
-- body -- no sub-proof table lookup, no stability bridge, no leq lemmas
-- (the ax-branch construction style ; cf.  ind_branch_thmT  which also
-- ships only a minimal check).  Consequently these closures take NO
-- IH-equation premises : the output is a pure function of the body.
--
--   thmT_at_eintro :
--     (cFcode cTcode cInnerIdx : Term) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_eintro)
--                            (ap2 pi (ap2 pi cFcode cTcode) cInnerIdx)))
--                 (ap2 pi (natCode tag_exists) cFcode))
--
--   thmT_at_eelim :
--     (cFcode cNa cAcode cMinorIdx cEIdx : Term) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_eelim)
--                            (ap2 pi (ap2 pi cFcode (ap2 pi cNa cAcode))
--                                    (ap2 pi cMinorIdx cEIdx))))
--                 cAcode)
--
-- (For  E_intro  cFcode = codeFun1 f , so the output is exactly
--  codeFormula (E f) ; for  E_elim  cAcode = codeFormula A , the output.)

module T4.ThmTAtE where

open import T4.Base
open import T4.Tags
open import T4.Code
open import T4.CoVSpec
open import T4.CoVSpecUniv
open import T4.CoVSpecFst
open import T4.SbT          using ( get_K ; get_inner ; get_table ; get_newK
                                     ; get_tag ; get_body ; lookupAt ; sbt )
open import T4.SbF          using ( sbf )
open import T4.SbContract   using ( SbContract )
open import T4.SbfAtClosures using ( sbContract )
open import T4.SbDerived    using ( module Derive )
open import T4.CodeCantorCollapse using ( natEqF_codeF_refl )
open import T4.ThmT
open import T4.StabilityNatFuel
open import T4.Stability
open import T4.LeqMono
open import T4.PiPositivity

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
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq ; Not )
open import BRA3.RuleInst2       using ( natEq-refl ; true_neq_false )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; iter_base_univ )
import BRA3.ChurchT92

-- Specialise  sbfEq_codeFormula  to T4's concrete  sbt , sbf .
open Derive sbt sbf sbContract using ( sbfEq_codeFormula )

------------------------------------------------------------------------
-- NatNeqWitnesses : tag_eintro / tag_eelim distinct from all lower tags.

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

  witness_eintro_neq_ax : NatNeqWitness tag_eintro tag_ax
  witness_eintro_neq_ax = natEqFalse_to_witness tag_ax tag_eintro refl
  witness_eintro_neq_sb : NatNeqWitness tag_eintro tag_sb
  witness_eintro_neq_sb = natEqFalse_to_witness tag_sb tag_eintro refl
  witness_eintro_neq_mp : NatNeqWitness tag_eintro tag_mp
  witness_eintro_neq_mp = natEqFalse_to_witness tag_mp tag_eintro refl
  witness_eintro_neq_ind : NatNeqWitness tag_eintro tag_ind
  witness_eintro_neq_ind = natEqFalse_to_witness tag_ind tag_eintro refl

  witness_eelim_neq_ax : NatNeqWitness tag_eelim tag_ax
  witness_eelim_neq_ax = natEqFalse_to_witness tag_ax tag_eelim refl
  witness_eelim_neq_sb : NatNeqWitness tag_eelim tag_sb
  witness_eelim_neq_sb = natEqFalse_to_witness tag_sb tag_eelim refl
  witness_eelim_neq_mp : NatNeqWitness tag_eelim tag_mp
  witness_eelim_neq_mp = natEqFalse_to_witness tag_mp tag_eelim refl
  witness_eelim_neq_ind : NatNeqWitness tag_eelim tag_ind
  witness_eelim_neq_ind = natEqFalse_to_witness tag_ind tag_eelim refl
  witness_eelim_neq_eintro : NatNeqWitness tag_eelim tag_eintro
  witness_eelim_neq_eintro = natEqFalse_to_witness tag_eintro tag_eelim refl

  witness_eia_neq_ax : NatNeqWitness tag_eintroax tag_ax
  witness_eia_neq_ax = natEqFalse_to_witness tag_ax tag_eintroax refl
  witness_eia_neq_sb : NatNeqWitness tag_eintroax tag_sb
  witness_eia_neq_sb = natEqFalse_to_witness tag_sb tag_eintroax refl
  witness_eia_neq_mp : NatNeqWitness tag_eintroax tag_mp
  witness_eia_neq_mp = natEqFalse_to_witness tag_mp tag_eintroax refl
  witness_eia_neq_ind : NatNeqWitness tag_eintroax tag_ind
  witness_eia_neq_ind = natEqFalse_to_witness tag_ind tag_eintroax refl
  witness_eia_neq_eintro : NatNeqWitness tag_eintroax tag_eintro
  witness_eia_neq_eintro = natEqFalse_to_witness tag_eintro tag_eintroax refl
  witness_eia_neq_eelim : NatNeqWitness tag_eintroax tag_eelim
  witness_eia_neq_eelim = natEqFalse_to_witness tag_eelim tag_eintroax refl

------------------------------------------------------------------------
-- Position-extraction at packaged input  pi A Y  (copied from ThmTAtInd).

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
    let s1 = compose1U_eq s get_K (ap2 pi A Y)
    in ruleTrans s1 (cong1 s (get_K_at_pi A Y))

  get_tag_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (ap1 Fst (ap1 s A)))
  get_tag_at_pi A Y =
    let s1 = compose1U_eq Fst get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Fst (get_newK_at_pi A Y))

  get_body_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_body (ap2 pi A Y)) (ap1 Snd (ap1 s A)))
  get_body_at_pi A Y =
    let s1 = compose1U_eq Snd get_newK (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_newK_at_pi A Y))

  get_table_at_pi :
    (A Y : Term) -> Deriv (eqF (ap1 get_table (ap2 pi A Y)) (ap1 Snd Y))
  get_table_at_pi A Y =
    let s1 = compose1U_eq Snd get_inner (ap2 pi A Y)
    in ruleTrans s1 (cong1 Snd (get_inner_at_pi A Y))

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

  sb_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 sb_or_above input)
                (ap2 condFork
                  (ap1 (C pi sb_branch_thmT mp_or_above) input)
                  (ap1 isSb input)))
  sb_or_above_unfold input =
    ax_C condFork (C pi sb_branch_thmT mp_or_above) isSb input

  mp_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 mp_or_above input)
                (ap2 condFork
                  (ap1 (C pi mp_branch_thmT ind_or_else) input)
                  (ap1 isMp input)))
  mp_or_above_unfold input =
    ax_C condFork (C pi mp_branch_thmT ind_or_else) isMp input

  ind_or_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 ind_or_else input)
                (ap2 condFork
                  (ap1 (C pi ind_branch_thmT eintro_or_above) input)
                  (ap1 isInd input)))
  ind_or_else_unfold input =
    ax_C condFork (C pi ind_branch_thmT eintro_or_above) isInd input

  eintro_or_above_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 eintro_or_above input)
                (ap2 condFork
                  (ap1 (C pi eintro_branch_thmT eelim_or_else) input)
                  (ap1 isEIntro input)))
  eintro_or_above_unfold input =
    ax_C condFork (C pi eintro_branch_thmT eelim_or_else) isEIntro input

  eelim_or_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 eelim_or_else input)
                (ap2 condFork
                  (ap1 (C pi eelim_branch_thmT eintroax_or_else) input)
                  (ap1 isEElim input)))
  eelim_or_else_unfold input =
    ax_C condFork (C pi eelim_branch_thmT eintroax_or_else) isEElim input

  eintroax_or_else_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 eintroax_or_else input)
                (ap2 condFork
                  (ap1 (C pi eintroax_branch_thmT else_branch_thmT) input)
                  (ap1 isEIntroAx input)))
  eintroax_or_else_unfold input =
    ax_C condFork (C pi eintroax_branch_thmT else_branch_thmT) isEIntroAx input

  -- Generic  is<Tag>_unfold : is<Tag> input = natEqF (get_tag input) (natCode tag).
  isAx_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isAx input) (ap2 natEqF (ap1 get_tag input) (natCode tag_ax)))
  isAx_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_ax) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_ax input))

  isSb_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input) (ap2 natEqF (ap1 get_tag input) (natCode tag_sb)))
  isSb_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_sb) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_sb input))

  isMp_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isMp input) (ap2 natEqF (ap1 get_tag input) (natCode tag_mp)))
  isMp_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_mp) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_mp input))

  isInd_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isInd input) (ap2 natEqF (ap1 get_tag input) (natCode tag_ind)))
  isInd_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_ind) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_ind input))

  isEIntro_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isEIntro input) (ap2 natEqF (ap1 get_tag input) (natCode tag_eintro)))
  isEIntro_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_eintro) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_eintro input))

  isEElim_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isEElim input) (ap2 natEqF (ap1 get_tag input) (natCode tag_eelim)))
  isEElim_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_eelim) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_eelim input))

  isEIntroAx_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isEIntroAx input) (ap2 natEqF (ap1 get_tag input) (natCode tag_eintroax)))
  isEIntroAx_unfold input =
    ruleTrans (ax_C natEqF get_tag (constN tag_eintroax) input)
              (congR natEqF (ap1 get_tag input) (constN_eq tag_eintroax input))

------------------------------------------------------------------------
-- Tag-firing helpers (generic : take the get_tag value, produce is<X> value).

-- Firing helpers : take the proof that  get_tag input = natCode <thisTag>
-- and produce the value of the relevant  natEqF  comparison.

private
  -- get_tag = natCode k , k /= j  =>  isJ = O .
  is_neq_O :
    (input : Term) (k j : Nat) ->
    NatNeqWitness k j ->
    Deriv (eqF (ap1 get_tag input) (natCode k)) ->
    Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode j)) O)
  is_neq_O input k j w tag_eq =
    ruleTrans (congL natEqF (natCode j) tag_eq)
              (natEqF_at_neq k j w)

  -- get_tag = natCode k  =>  isK = sO .
  is_eq_sO :
    (input : Term) (k : Nat) ->
    Deriv (eqF (ap1 get_tag input) (natCode k)) ->
    Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode k)) (ap1 s O))
  is_eq_sO input k tag_eq =
    ruleTrans (congL natEqF (natCode k) tag_eq) (natEq_eq k)

------------------------------------------------------------------------
-- Cascade descents (tag-agnostic ; take the relevant is<X> value).

private
  -- FALSE descent : condFork _ O  ->  Snd  ->  next level.
  stepBody_to_sb_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isAx input) O) ->
    Deriv (eqF (ap1 stepBody_thmT input) (ap1 sb_or_above input))
  stepBody_to_sb_or_above input isAx_O =
    let e1 = stepBody_thmT_unfold input
        sub = congR condFork (ap1 (C pi ax_branch_thmT sb_or_above) input) isAx_O
        cf = condFork_false (ap1 (C pi ax_branch_thmT sb_or_above) input)
        pe = ax_C pi ax_branch_thmT sb_or_above input
        sp = axSnd (ap1 ax_branch_thmT input) (ap1 sb_or_above input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Snd pe) sp)))

  sb_or_above_to_mp_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isSb input) O) ->
    Deriv (eqF (ap1 sb_or_above input) (ap1 mp_or_above input))
  sb_or_above_to_mp_or_above input isSb_O =
    let e1 = sb_or_above_unfold input
        sub = congR condFork (ap1 (C pi sb_branch_thmT mp_or_above) input) isSb_O
        cf = condFork_false (ap1 (C pi sb_branch_thmT mp_or_above) input)
        pe = ax_C pi sb_branch_thmT mp_or_above input
        sp = axSnd (ap1 sb_branch_thmT input) (ap1 mp_or_above input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Snd pe) sp)))

  mp_or_above_to_ind_or_else :
    (input : Term) ->
    Deriv (eqF (ap1 isMp input) O) ->
    Deriv (eqF (ap1 mp_or_above input) (ap1 ind_or_else input))
  mp_or_above_to_ind_or_else input isMp_O =
    let e1 = mp_or_above_unfold input
        sub = congR condFork (ap1 (C pi mp_branch_thmT ind_or_else) input) isMp_O
        cf = condFork_false (ap1 (C pi mp_branch_thmT ind_or_else) input)
        pe = ax_C pi mp_branch_thmT ind_or_else input
        sp = axSnd (ap1 mp_branch_thmT input) (ap1 ind_or_else input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Snd pe) sp)))

  ind_or_else_to_eintro_or_above :
    (input : Term) ->
    Deriv (eqF (ap1 isInd input) O) ->
    Deriv (eqF (ap1 ind_or_else input) (ap1 eintro_or_above input))
  ind_or_else_to_eintro_or_above input isInd_O =
    let e1 = ind_or_else_unfold input
        sub = congR condFork (ap1 (C pi ind_branch_thmT eintro_or_above) input) isInd_O
        cf = condFork_false (ap1 (C pi ind_branch_thmT eintro_or_above) input)
        pe = ax_C pi ind_branch_thmT eintro_or_above input
        sp = axSnd (ap1 ind_branch_thmT input) (ap1 eintro_or_above input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Snd pe) sp)))

  -- TRUE descent : condFork _ (sO)  ->  Fst  ->  this branch.
  eintro_or_above_to_eintro :
    (input : Term) ->
    Deriv (eqF (ap1 isEIntro input) (ap1 s O)) ->
    Deriv (eqF (ap1 eintro_or_above input) (ap1 eintro_branch_thmT input))
  eintro_or_above_to_eintro input isEIntro_sO =
    let e1 = eintro_or_above_unfold input
        sub = congR condFork (ap1 (C pi eintro_branch_thmT eelim_or_else) input) isEIntro_sO
        cf = condFork_true_nc (ap1 (C pi eintro_branch_thmT eelim_or_else) input) O
        pe = ax_C pi eintro_branch_thmT eelim_or_else input
        fp = axFst (ap1 eintro_branch_thmT input) (ap1 eelim_or_else input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Fst pe) fp)))

  -- FALSE descent for the eelim path : eintro_or_above _ O  ->  Snd  ->  eelim_or_else.
  eintro_or_above_to_eelim_or_else :
    (input : Term) ->
    Deriv (eqF (ap1 isEIntro input) O) ->
    Deriv (eqF (ap1 eintro_or_above input) (ap1 eelim_or_else input))
  eintro_or_above_to_eelim_or_else input isEIntro_O =
    let e1 = eintro_or_above_unfold input
        sub = congR condFork (ap1 (C pi eintro_branch_thmT eelim_or_else) input) isEIntro_O
        cf = condFork_false (ap1 (C pi eintro_branch_thmT eelim_or_else) input)
        pe = ax_C pi eintro_branch_thmT eelim_or_else input
        sp = axSnd (ap1 eintro_branch_thmT input) (ap1 eelim_or_else input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Snd pe) sp)))

  eelim_or_else_to_eelim :
    (input : Term) ->
    Deriv (eqF (ap1 isEElim input) (ap1 s O)) ->
    Deriv (eqF (ap1 eelim_or_else input) (ap1 eelim_branch_thmT input))
  eelim_or_else_to_eelim input isEElim_sO =
    let e1 = eelim_or_else_unfold input
        sub = congR condFork (ap1 (C pi eelim_branch_thmT eintroax_or_else) input) isEElim_sO
        cf = condFork_true_nc (ap1 (C pi eelim_branch_thmT eintroax_or_else) input) O
        pe = ax_C pi eelim_branch_thmT eintroax_or_else input
        fp = axFst (ap1 eelim_branch_thmT input) (ap1 eintroax_or_else input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Fst pe) fp)))

  -- FALSE descent : eelim_or_else _ O  ->  Snd  ->  eintroax_or_else.
  eelim_or_else_to_eintroax_or_else :
    (input : Term) ->
    Deriv (eqF (ap1 isEElim input) O) ->
    Deriv (eqF (ap1 eelim_or_else input) (ap1 eintroax_or_else input))
  eelim_or_else_to_eintroax_or_else input isEElim_O =
    let e1 = eelim_or_else_unfold input
        sub = congR condFork (ap1 (C pi eelim_branch_thmT eintroax_or_else) input) isEElim_O
        cf = condFork_false (ap1 (C pi eelim_branch_thmT eintroax_or_else) input)
        pe = ax_C pi eelim_branch_thmT eintroax_or_else input
        sp = axSnd (ap1 eelim_branch_thmT input) (ap1 eintroax_or_else input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Snd pe) sp)))

  -- TRUE descent : eintroax_or_else _ (sO)  ->  Fst  ->  eintroax_branch.
  eintroax_or_else_to_eintroax :
    (input : Term) ->
    Deriv (eqF (ap1 isEIntroAx input) (ap1 s O)) ->
    Deriv (eqF (ap1 eintroax_or_else input) (ap1 eintroax_branch_thmT input))
  eintroax_or_else_to_eintroax input isEIntroAx_sO =
    let e1 = eintroax_or_else_unfold input
        sub = congR condFork (ap1 (C pi eintroax_branch_thmT else_branch_thmT) input) isEIntroAx_sO
        cf = condFork_true_nc (ap1 (C pi eintroax_branch_thmT else_branch_thmT) input) O
        pe = ax_C pi eintroax_branch_thmT else_branch_thmT input
        fp = axFst (ap1 eintroax_branch_thmT input) (ap1 else_branch_thmT input)
    in ruleTrans e1 (ruleTrans sub (ruleTrans cf (ruleTrans (cong1 Fst pe) fp)))

------------------------------------------------------------------------
-- Shared preamble :  thmT input = stepBody_thmT input_pkg'  where
--   input      = pi (natCode tag) Y_body  ,  tag = s A_outer's nat ,
--   P_outer    = pi_succ_outer A_outer Y_body ,
--   prev       = cov_spec baseValue_thmT stepFun_thmT O P_outer ,
--   input_pkg' = pi P_outer (Snd prev) .

private
  preamble_to_stepBody :
    (A_outer Y_body : Term) ->
    Deriv (eqF (ap1 thmT (ap2 pi (ap1 s A_outer) Y_body))
                (ap1 stepBody_thmT
                  (ap2 pi (pi_succ_outer A_outer Y_body)
                          (ap1 Snd (ap2 (cov_spec baseValue_thmT stepFun_thmT) O
                                          (pi_succ_outer A_outer Y_body))))))
  preamble_to_stepBody A_outer Y_body =
    let input : Term
        input = ap2 pi (ap1 s A_outer) Y_body
        P_outer : Term
        P_outer = pi_succ_outer A_outer Y_body
        prev : Term
        prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
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
    in ruleTrans step0
         (ruleTrans step1
           (ruleTrans readOff_lift
             (ruleTrans readOff_eval
               (ruleTrans stepFun_lift Post_eq))))

  -- get_tag input_pkg' = natCode tag, where tag's numeral = s A_outer.
  get_tag_value_gen :
    (A_outer Y_body tagN : Term) ->
    Deriv (eqF (ap1 s A_outer) tagN) ->
    Deriv (eqF (ap1 get_tag
                 (ap2 pi (pi_succ_outer A_outer Y_body)
                         (ap1 Snd (ap2 (cov_spec baseValue_thmT stepFun_thmT) O
                                         (pi_succ_outer A_outer Y_body)))))
                tagN)
  get_tag_value_gen A_outer Y_body tagN sA_eq =
    let input : Term
        input = ap2 pi (ap1 s A_outer) Y_body
        P_outer : Term
        P_outer = pi_succ_outer A_outer Y_body
        prev : Term
        prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
        input_eq_sP_outer = pi_at_succ A_outer Y_body
        get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)
        Fst_input = axFst (ap1 s A_outer) Y_body
        Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)
    in ruleTrans get_tag_eq_Fst_sP
         (ruleTrans Fst_sP_to_Fst_input (ruleTrans Fst_input sA_eq))

  -- Snd (s P_outer) = Y_body  (the body), via Snd input.
  Snd_sP_to_body_gen :
    (A_outer Y_body : Term) ->
    Deriv (eqF (ap1 Snd (ap1 s (pi_succ_outer A_outer Y_body))) Y_body)
  Snd_sP_to_body_gen A_outer Y_body =
    let input_eq_sP_outer = pi_at_succ A_outer Y_body
        Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)
        Snd_input_eq = axSnd (ap1 s A_outer) Y_body
    in ruleTrans Snd_sP_eq Snd_input_eq

------------------------------------------------------------------------
-- E_intro closure.

thmT_at_eintro :
  (cFcode cTcode cInnerIdx : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_eintro)
                         (ap2 pi (ap2 pi cFcode cTcode) cInnerIdx)))
              (ap2 pi (natCode tag_exists) cFcode))
thmT_at_eintro cFcode cTcode cInnerIdx =
  let A_outer : Term
      A_outer = natCode (suc (suc (suc (suc zero))))   -- natCode 4 ; s A_outer = natCode 5 = tag_eintro
      Y_body : Term
      Y_body = ap2 pi (ap2 pi cFcode cTcode) cInnerIdx
      input : Term
      input = ap2 pi (natCode tag_eintro) Y_body
      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body
      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      -- s A_outer = natCode tag_eintro  (definitional).
      sA_eq : Deriv (eqF (ap1 s A_outer) (natCode tag_eintro))
      sA_eq = axRefl (natCode tag_eintro)

      -- (1) thmT input = stepBody_thmT input_pkg' .
      to_stepBody :
        Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
      to_stepBody = preamble_to_stepBody A_outer Y_body

      -- (2) tag dispatch to the eintro branch.
      tag_value : Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_eintro))
      tag_value = get_tag_value_gen A_outer Y_body (natCode tag_eintro) sA_eq

      isAx_O = is_neq_O input_pkg' tag_eintro tag_ax witness_eintro_neq_ax tag_value
      isSb_O = is_neq_O input_pkg' tag_eintro tag_sb witness_eintro_neq_sb tag_value
      isMp_O = is_neq_O input_pkg' tag_eintro tag_mp witness_eintro_neq_mp tag_value
      isInd_O = is_neq_O input_pkg' tag_eintro tag_ind witness_eintro_neq_ind tag_value
      isEIntro_sO = is_eq_sO input_pkg' tag_eintro tag_value

      d1 = stepBody_to_sb_or_above input_pkg' (ruleTrans (isAx_unfold input_pkg') isAx_O)
      d2 = sb_or_above_to_mp_or_above input_pkg' (ruleTrans (isSb_unfold input_pkg') isSb_O)
      d3 = mp_or_above_to_ind_or_else input_pkg' (ruleTrans (isMp_unfold input_pkg') isMp_O)
      d4 = ind_or_else_to_eintro_or_above input_pkg' (ruleTrans (isInd_unfold input_pkg') isInd_O)
      d5 = eintro_or_above_to_eintro input_pkg' (ruleTrans (isEIntro_unfold input_pkg') isEIntro_sO)

      to_eintro_branch :
        Deriv (eqF (ap1 thmT input) (ap1 eintro_branch_thmT input_pkg'))
      to_eintro_branch =
        ruleTrans to_stepBody
          (ruleTrans d1 (ruleTrans d2 (ruleTrans d3 (ruleTrans d4 d5))))

      -- (3) eintro_branch_thmT input_pkg' = pi (natCode tag_exists) cFcode .
      get_body_value : Deriv (eqF (ap1 get_body input_pkg') Y_body)
      get_body_value =
        ruleTrans (get_body_at_pi P_outer (ap1 Snd prev))
                  (Snd_sP_to_body_gen A_outer Y_body)

      -- fcode : ap1 get_eintro_fcode input_pkg' = cFcode .
      fcode_eq : Deriv (eqF (ap1 get_eintro_fcode input_pkg') cFcode)
      fcode_eq =
        let s1 = compose1U_eq Fst (compose1U Fst get_body) input_pkg'
            s2 = compose1U_eq Fst get_body input_pkg'
            -- ap1 (compose1U Fst get_body) input_pkg' = Fst (get_body input_pkg') = Fst Y_body
            inner : Deriv (eqF (ap1 (compose1U Fst get_body) input_pkg')
                                (ap1 Fst Y_body))
            inner = ruleTrans s2 (cong1 Fst get_body_value)
            -- Fst Y_body = pi cFcode cTcode ; Fst (pi cFcode cTcode) = cFcode
            FstYb : Deriv (eqF (ap1 Fst Y_body) (ap2 pi cFcode cTcode))
            FstYb = axFst (ap2 pi cFcode cTcode) cInnerIdx
            FstFstYb : Deriv (eqF (ap1 Fst (ap2 pi cFcode cTcode)) cFcode)
            FstFstYb = axFst cFcode cTcode
        in ruleTrans s1
             (ruleTrans (cong1 Fst inner)
               (ruleTrans (cong1 Fst FstYb) FstFstYb))

      eintro_branch_value :
        Deriv (eqF (ap1 eintro_branch_thmT input_pkg')
                    (ap2 pi (natCode tag_exists) cFcode))
      eintro_branch_value =
        let e1 = ax_C pi (constN tag_exists) get_eintro_fcode input_pkg'
            tag_e = constN_eq tag_exists input_pkg'
            picong = ruleTrans
                       (congL pi (ap1 get_eintro_fcode input_pkg') tag_e)
                       (congR pi (natCode tag_exists) fcode_eq)
        in ruleTrans e1 picong
  in ruleTrans to_eintro_branch eintro_branch_value

------------------------------------------------------------------------
-- E_elim closure.

-- Lookup / stability / leq machinery for the E_elim sub-proof checks.
private
  HP_thmT_eq_thmT_under_leq :
    (ct K : Term) ->
    Deriv (leq ct K) ->
    Deriv (eqF (HPsbt baseValue_thmT stepFun_thmT O ct K) (ap2 thmT_F2 O ct))
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

  eelim_A5 : Term
  eelim_A5 = natCode (suc (suc (suc (suc (suc zero)))))

  leq_eelim_minorIdx :
    (header cMinorIdx cEIdx : Term) ->
    Deriv (leq cMinorIdx
              (pi_succ_outer eelim_A5 (ap2 pi header (ap2 pi cMinorIdx cEIdx))))
  leq_eelim_minorIdx header cMinorIdx cEIdx =
    let rest : Term
        rest = ap2 pi cMinorIdx cEIdx
        Y : Term
        Y = ap2 pi header rest
        X : Term
        X = ap2 sigma (ap2 sigma eelim_A5 Y) (ap1 tau (ap2 sigma eelim_A5 Y))
        l1 : Deriv (leq cMinorIdx (ap2 sigma cMinorIdx cEIdx))
        l1 = leq_sigma_left cMinorIdx cEIdx
        l2 : Deriv (leq (ap2 sigma cMinorIdx cEIdx) (ap1 tau (ap2 sigma cMinorIdx cEIdx)))
        l2 = ruleInst 0 (ap2 sigma cMinorIdx cEIdx) BRA3.ChurchT92.T92
        l3 : Deriv (leq (ap1 tau (ap2 sigma cMinorIdx cEIdx))
                         (ap2 sigma (ap1 tau (ap2 sigma cMinorIdx cEIdx)) cEIdx))
        l3 = leq_sigma_left (ap1 tau (ap2 sigma cMinorIdx cEIdx)) cEIdx
        eqPi = ruleSym (T4.LeqMono.T114_at cMinorIdx cEIdx)
        cong_sub = congR sub (ap1 tau (ap2 sigma cMinorIdx cEIdx)) eqPi
        l3_pi = ruleTrans (ruleSym cong_sub) l3
        l12 = leq_trans cMinorIdx (ap2 sigma cMinorIdx cEIdx)
                         (ap1 tau (ap2 sigma cMinorIdx cEIdx)) l1 l2
        l123 = leq_trans cMinorIdx (ap1 tau (ap2 sigma cMinorIdx cEIdx)) rest l12 l3_pi
        lR : Deriv (leq rest Y)
        lR = leq_pi_right header rest
        l1234 = leq_trans cMinorIdx rest Y l123 lR
        l5 = leq_sigma_right X Y
    in leq_trans cMinorIdx Y (ap2 sigma X Y) l1234 l5

  leq_eelim_eIdx :
    (header cMinorIdx cEIdx : Term) ->
    Deriv (leq cEIdx
              (pi_succ_outer eelim_A5 (ap2 pi header (ap2 pi cMinorIdx cEIdx))))
  leq_eelim_eIdx header cMinorIdx cEIdx =
    let rest : Term
        rest = ap2 pi cMinorIdx cEIdx
        Y : Term
        Y = ap2 pi header rest
        X : Term
        X = ap2 sigma (ap2 sigma eelim_A5 Y) (ap1 tau (ap2 sigma eelim_A5 Y))
        l0 : Deriv (leq cEIdx rest)
        l0 = leq_pi_right cMinorIdx cEIdx
        lR : Deriv (leq rest Y)
        lR = leq_pi_right header rest
        l01 = leq_trans cEIdx rest Y l0 lR
        l5 = leq_sigma_right X Y
    in leq_trans cEIdx Y (ap2 sigma X Y) l01 l5

thmT_at_eelim :
  (cFcode cNa cAcode cMinorIdx cEIdx : Term)
  (cMinorVal cEVal : Term)
  (ih_minor : Deriv (eqF (ap1 thmT cMinorIdx) cMinorVal))
  (ih_e     : Deriv (eqF (ap1 thmT cEIdx) cEVal))
  (wf_minor : Deriv (eqF (ap2 natEqF cMinorVal
                           (ap2 pi (natCode tag_imp)
                             (ap2 pi
                               (ap2 pi (natCode tag_eq)
                                 (ap2 pi (ap2 pi (natCode tag_ap1)
                                           (ap2 pi cFcode (ap2 pi (natCode tag_var) cNa))) O))
                               cAcode)))
                         (ap1 s O)))
  (wf_major : Deriv (eqF (ap2 natEqF cEVal (ap2 pi (natCode tag_exists) cFcode)) (ap1 s O)))
  (wf_fresh : Deriv (eqF (ap2 natEqF (ap2 sbf (ap2 pi cNa O) cAcode) cAcode) (ap1 s O))) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_eelim)
                         (ap2 pi (ap2 pi cFcode (ap2 pi cNa cAcode))
                                 (ap2 pi cMinorIdx cEIdx))))
              cAcode)
thmT_at_eelim cFcode cNa cAcode cMinorIdx cEIdx cMinorVal cEVal
              ih_minor ih_e wf_minor wf_major wf_fresh =
  let A_outer : Term
      A_outer = natCode (suc (suc (suc (suc (suc zero)))))
      header : Term
      header = ap2 pi cFcode (ap2 pi cNa cAcode)
      rest : Term
      rest = ap2 pi cMinorIdx cEIdx
      Y_body : Term
      Y_body = ap2 pi header rest
      input : Term
      input = ap2 pi (natCode tag_eelim) Y_body
      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body
      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      sA_eq : Deriv (eqF (ap1 s A_outer) (natCode tag_eelim))
      sA_eq = axRefl (natCode tag_eelim)

      to_stepBody : Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
      to_stepBody = preamble_to_stepBody A_outer Y_body

      tag_value : Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_eelim))
      tag_value = get_tag_value_gen A_outer Y_body (natCode tag_eelim) sA_eq

      isAx_O = is_neq_O input_pkg' tag_eelim tag_ax witness_eelim_neq_ax tag_value
      isSb_O = is_neq_O input_pkg' tag_eelim tag_sb witness_eelim_neq_sb tag_value
      isMp_O = is_neq_O input_pkg' tag_eelim tag_mp witness_eelim_neq_mp tag_value
      isInd_O = is_neq_O input_pkg' tag_eelim tag_ind witness_eelim_neq_ind tag_value
      isEIntro_O = is_neq_O input_pkg' tag_eelim tag_eintro witness_eelim_neq_eintro tag_value
      isEElim_sO = is_eq_sO input_pkg' tag_eelim tag_value

      d1 = stepBody_to_sb_or_above input_pkg' (ruleTrans (isAx_unfold input_pkg') isAx_O)
      d2 = sb_or_above_to_mp_or_above input_pkg' (ruleTrans (isSb_unfold input_pkg') isSb_O)
      d3 = mp_or_above_to_ind_or_else input_pkg' (ruleTrans (isMp_unfold input_pkg') isMp_O)
      d4 = ind_or_else_to_eintro_or_above input_pkg' (ruleTrans (isInd_unfold input_pkg') isInd_O)
      d5 = eintro_or_above_to_eelim_or_else input_pkg' (ruleTrans (isEIntro_unfold input_pkg') isEIntro_O)
      d6 = eelim_or_else_to_eelim input_pkg' (ruleTrans (isEElim_unfold input_pkg') isEElim_sO)

      to_eelim_branch : Deriv (eqF (ap1 thmT input) (ap1 eelim_branch_thmT input_pkg'))
      to_eelim_branch =
        ruleTrans to_stepBody
          (ruleTrans d1 (ruleTrans d2 (ruleTrans d3 (ruleTrans d4 (ruleTrans d5 d6)))))

      get_body_value : Deriv (eqF (ap1 get_body input_pkg') Y_body)
      get_body_value =
        ruleTrans (get_body_at_pi P_outer (ap1 Snd prev))
                  (Snd_sP_to_body_gen A_outer Y_body)

      get_K_value : Deriv (eqF (ap1 get_K input_pkg') P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value : Deriv (eqF (ap1 get_table input_pkg') (ap1 Snd (ap1 Snd prev)))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      get_eelim_header_value : Deriv (eqF (ap1 get_eelim_header input_pkg') header)
      get_eelim_header_value =
        ruleTrans (compose1U_eq Fst get_body input_pkg')
                  (ruleTrans (cong1 Fst get_body_value) (axFst header rest))

      get_eelim_fcode_value : Deriv (eqF (ap1 get_eelim_fcode input_pkg') cFcode)
      get_eelim_fcode_value =
        ruleTrans (compose1U_eq Fst get_eelim_header input_pkg')
                  (ruleTrans (cong1 Fst get_eelim_header_value)
                             (axFst cFcode (ap2 pi cNa cAcode)))

      get_eelim_naA_value : Deriv (eqF (ap1 get_eelim_naA input_pkg') (ap2 pi cNa cAcode))
      get_eelim_naA_value =
        ruleTrans (compose1U_eq Snd get_eelim_header input_pkg')
                  (ruleTrans (cong1 Snd get_eelim_header_value)
                             (axSnd cFcode (ap2 pi cNa cAcode)))

      get_eelim_na_value : Deriv (eqF (ap1 get_eelim_na input_pkg') cNa)
      get_eelim_na_value =
        ruleTrans (compose1U_eq Fst get_eelim_naA input_pkg')
                  (ruleTrans (cong1 Fst get_eelim_naA_value) (axFst cNa cAcode))

      get_eelim_Acode_value : Deriv (eqF (ap1 get_eelim_Acode input_pkg') cAcode)
      get_eelim_Acode_value =
        ruleTrans (compose1U_eq Snd get_eelim_naA input_pkg')
                  (ruleTrans (cong1 Snd get_eelim_naA_value) (axSnd cNa cAcode))

      get_eelim_rest_value : Deriv (eqF (ap1 get_eelim_rest input_pkg') rest)
      get_eelim_rest_value =
        ruleTrans (compose1U_eq Snd get_body input_pkg')
                  (ruleTrans (cong1 Snd get_body_value) (axSnd header rest))

      get_eelim_minorIdx_value : Deriv (eqF (ap1 get_eelim_minorIdx input_pkg') cMinorIdx)
      get_eelim_minorIdx_value =
        ruleTrans (compose1U_eq Fst get_eelim_rest input_pkg')
                  (ruleTrans (cong1 Fst get_eelim_rest_value) (axFst cMinorIdx cEIdx))

      get_eelim_eIdx_value : Deriv (eqF (ap1 get_eelim_eIdx input_pkg') cEIdx)
      get_eelim_eIdx_value =
        ruleTrans (compose1U_eq Snd get_eelim_rest input_pkg')
                  (ruleTrans (cong1 Snd get_eelim_rest_value) (axSnd cMinorIdx cEIdx))

      minor_val_value : Deriv (eqF (ap1 get_eelim_minor_val input_pkg') cMinorVal)
      minor_val_value =
        let unfold = lookupAt_unfold get_eelim_minorIdx input_pkg'
            iter_arg = ruleTrans (congL sub (ap1 get_eelim_minorIdx input_pkg') get_K_value)
                                  (congR sub P_outer get_eelim_minorIdx_value)
            iter_full =
              ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                                  (ap1 get_eelim_minorIdx input_pkg'))
                                get_table_value)
                        (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                                iter_arg)
            val_to_HP = ruleTrans unfold (cong1 Fst iter_full)
            leq_m = leq_eelim_minorIdx header cMinorIdx cEIdx
            val_value = ruleTrans val_to_HP (HP_thmT_eq_thmT_under_leq cMinorIdx P_outer leq_m)
            val_to_thmT = ruleTrans val_value (ruleSym (thmT_unfold cMinorIdx))
        in ruleTrans val_to_thmT ih_minor

      e_val_value : Deriv (eqF (ap1 get_eelim_e_val input_pkg') cEVal)
      e_val_value =
        let unfold = lookupAt_unfold get_eelim_eIdx input_pkg'
            iter_arg = ruleTrans (congL sub (ap1 get_eelim_eIdx input_pkg') get_K_value)
                                  (congR sub P_outer get_eelim_eIdx_value)
            iter_full =
              ruleTrans (congL (iter Snd) (ap2 sub (ap1 get_K input_pkg')
                                                  (ap1 get_eelim_eIdx input_pkg'))
                                get_table_value)
                        (congR (iter Snd) (HistP_sbt baseValue_thmT stepFun_thmT O P_outer)
                                iter_arg)
            val_to_HP = ruleTrans unfold (cong1 Fst iter_full)
            leq_e = leq_eelim_eIdx header cMinorIdx cEIdx
            val_value = ruleTrans val_to_HP (HP_thmT_eq_thmT_under_leq cEIdx P_outer leq_e)
            val_to_thmT = ruleTrans val_value (ruleSym (thmT_unfold cEIdx))
        in ruleTrans val_to_thmT ih_e

      cVarA_built : Term
      cVarA_built = ap2 pi (natCode tag_var) cNa
      cApp_built : Term
      cApp_built = ap2 pi (natCode tag_ap1) (ap2 pi cFcode cVarA_built)
      cEqAt_built : Term
      cEqAt_built = ap2 pi (natCode tag_eq) (ap2 pi cApp_built O)
      cMinor_built : Term
      cMinor_built = ap2 pi (natCode tag_imp) (ap2 pi cEqAt_built cAcode)
      cMajor_built : Term
      cMajor_built = ap2 pi (natCode tag_exists) cFcode
      freshLHS_built : Term
      freshLHS_built = ap2 sbf (ap2 pi cNa O) cAcode

      cVarA_value : Deriv (eqF (ap1 eelim_cVarA input_pkg') cVarA_built)
      cVarA_value =
        ruleTrans (ax_C pi (constN tag_var) get_eelim_na input_pkg')
          (ruleTrans (congL pi (ap1 get_eelim_na input_pkg') (constN_eq tag_var input_pkg'))
                     (congR pi (natCode tag_var) get_eelim_na_value))

      cApp_value : Deriv (eqF (ap1 eelim_cApp input_pkg') cApp_built)
      cApp_value =
        let innerF = C pi get_eelim_fcode eelim_cVarA
            inner_val : Deriv (eqF (ap1 innerF input_pkg') (ap2 pi cFcode cVarA_built))
            inner_val =
              ruleTrans (ax_C pi get_eelim_fcode eelim_cVarA input_pkg')
                (ruleTrans (congL pi (ap1 eelim_cVarA input_pkg') get_eelim_fcode_value)
                           (congR pi cFcode cVarA_value))
        in ruleTrans (ax_C pi (constN tag_ap1) innerF input_pkg')
             (ruleTrans (congL pi (ap1 innerF input_pkg') (constN_eq tag_ap1 input_pkg'))
                        (congR pi (natCode tag_ap1) inner_val))

      cEqAt_value : Deriv (eqF (ap1 eelim_cEqAt input_pkg') cEqAt_built)
      cEqAt_value =
        let innerF = C pi eelim_cApp o
            inner_val : Deriv (eqF (ap1 innerF input_pkg') (ap2 pi cApp_built O))
            inner_val =
              ruleTrans (ax_C pi eelim_cApp o input_pkg')
                (ruleTrans (congL pi (ap1 o input_pkg') cApp_value)
                           (congR pi cApp_built (ax_o input_pkg')))
        in ruleTrans (ax_C pi (constN tag_eq) innerF input_pkg')
             (ruleTrans (congL pi (ap1 innerF input_pkg') (constN_eq tag_eq input_pkg'))
                        (congR pi (natCode tag_eq) inner_val))

      cMinor_value : Deriv (eqF (ap1 eelim_cMinor input_pkg') cMinor_built)
      cMinor_value =
        let innerF = C pi eelim_cEqAt get_eelim_Acode
            inner_val : Deriv (eqF (ap1 innerF input_pkg') (ap2 pi cEqAt_built cAcode))
            inner_val =
              ruleTrans (ax_C pi eelim_cEqAt get_eelim_Acode input_pkg')
                (ruleTrans (congL pi (ap1 get_eelim_Acode input_pkg') cEqAt_value)
                           (congR pi cEqAt_built get_eelim_Acode_value))
        in ruleTrans (ax_C pi (constN tag_imp) innerF input_pkg')
             (ruleTrans (congL pi (ap1 innerF input_pkg') (constN_eq tag_imp input_pkg'))
                        (congR pi (natCode tag_imp) inner_val))

      cMajor_value : Deriv (eqF (ap1 eelim_cMajor input_pkg') cMajor_built)
      cMajor_value =
        ruleTrans (ax_C pi (constN tag_exists) get_eelim_fcode input_pkg')
          (ruleTrans (congL pi (ap1 get_eelim_fcode input_pkg') (constN_eq tag_exists input_pkg'))
                     (congR pi (natCode tag_exists) get_eelim_fcode_value))

      freshLHS_value : Deriv (eqF (ap1 eelim_freshLHS input_pkg') freshLHS_built)
      freshLHS_value =
        let spec_val : Deriv (eqF (ap1 eelim_freshSpec input_pkg') (ap2 pi cNa O))
            spec_val =
              ruleTrans (ax_C pi get_eelim_na o input_pkg')
                (ruleTrans (congL pi (ap1 o input_pkg') get_eelim_na_value)
                           (congR pi cNa (ax_o input_pkg')))
        in ruleTrans (ax_C sbf eelim_freshSpec get_eelim_Acode input_pkg')
             (ruleTrans (congL sbf (ap1 get_eelim_Acode input_pkg') spec_val)
                        (congR sbf (ap2 pi cNa O) get_eelim_Acode_value))

      isMinorOk_value : Deriv (eqF (ap1 isMinorOk input_pkg') (ap1 s O))
      isMinorOk_value =
        ruleTrans (ax_C natEqF get_eelim_minor_val eelim_cMinor input_pkg')
          (ruleTrans (congL natEqF (ap1 eelim_cMinor input_pkg') minor_val_value)
            (ruleTrans (congR natEqF cMinorVal cMinor_value) wf_minor))

      isMajorOk_value : Deriv (eqF (ap1 isMajorOk input_pkg') (ap1 s O))
      isMajorOk_value =
        ruleTrans (ax_C natEqF get_eelim_e_val eelim_cMajor input_pkg')
          (ruleTrans (congL natEqF (ap1 eelim_cMajor input_pkg') e_val_value)
            (ruleTrans (congR natEqF cEVal cMajor_value) wf_major))

      isFreshOk_value : Deriv (eqF (ap1 isFreshOk input_pkg') (ap1 s O))
      isFreshOk_value =
        ruleTrans (ax_C natEqF eelim_freshLHS get_eelim_Acode input_pkg')
          (ruleTrans (congL natEqF (ap1 get_eelim_Acode input_pkg') freshLHS_value)
            (ruleTrans (congR natEqF freshLHS_built get_eelim_Acode_value) wf_fresh))

      descent_minor : Deriv (eqF (ap1 eelim_branch_thmT input_pkg') (ap1 eelim_inner_major input_pkg'))
      descent_minor =
        let e1 = ax_C condFork (C pi eelim_inner_major baseValue_thmT) isMinorOk input_pkg'
            sub1 = congR condFork (ap1 (C pi eelim_inner_major baseValue_thmT) input_pkg') isMinorOk_value
            cf1 = condFork_true_nc (ap1 (C pi eelim_inner_major baseValue_thmT) input_pkg') O
            pe1 = ax_C pi eelim_inner_major baseValue_thmT input_pkg'
            fp1 = axFst (ap1 eelim_inner_major input_pkg') (ap1 baseValue_thmT input_pkg')
        in ruleTrans e1 (ruleTrans sub1 (ruleTrans cf1 (ruleTrans (cong1 Fst pe1) fp1)))

      descent_major : Deriv (eqF (ap1 eelim_inner_major input_pkg') (ap1 eelim_inner_fresh input_pkg'))
      descent_major =
        let e1 = ax_C condFork (C pi eelim_inner_fresh baseValue_thmT) isMajorOk input_pkg'
            sub1 = congR condFork (ap1 (C pi eelim_inner_fresh baseValue_thmT) input_pkg') isMajorOk_value
            cf1 = condFork_true_nc (ap1 (C pi eelim_inner_fresh baseValue_thmT) input_pkg') O
            pe1 = ax_C pi eelim_inner_fresh baseValue_thmT input_pkg'
            fp1 = axFst (ap1 eelim_inner_fresh input_pkg') (ap1 baseValue_thmT input_pkg')
        in ruleTrans e1 (ruleTrans sub1 (ruleTrans cf1 (ruleTrans (cong1 Fst pe1) fp1)))

      descent_fresh : Deriv (eqF (ap1 eelim_inner_fresh input_pkg') (ap1 get_eelim_Acode input_pkg'))
      descent_fresh =
        let e1 = ax_C condFork (C pi get_eelim_Acode baseValue_thmT) isFreshOk input_pkg'
            sub1 = congR condFork (ap1 (C pi get_eelim_Acode baseValue_thmT) input_pkg') isFreshOk_value
            cf1 = condFork_true_nc (ap1 (C pi get_eelim_Acode baseValue_thmT) input_pkg') O
            pe1 = ax_C pi get_eelim_Acode baseValue_thmT input_pkg'
            fp1 = axFst (ap1 get_eelim_Acode input_pkg') (ap1 baseValue_thmT input_pkg')
        in ruleTrans e1 (ruleTrans sub1 (ruleTrans cf1 (ruleTrans (cong1 Fst pe1) fp1)))

      to_Acode : Deriv (eqF (ap1 eelim_branch_thmT input_pkg') (ap1 get_eelim_Acode input_pkg'))
      to_Acode = ruleTrans descent_minor (ruleTrans descent_major descent_fresh)

      eelim_branch_value : Deriv (eqF (ap1 eelim_branch_thmT input_pkg') cAcode)
      eelim_branch_value = ruleTrans to_Acode get_eelim_Acode_value
  in ruleTrans to_eelim_branch eelim_branch_value

------------------------------------------------------------------------
-- Corollary :  thmT_at_eelim_codeF  -- the genuine soundness wrapper.

thmT_at_eelim_codeF :
  (f : Fun1) (a : Nat) (A : Formula)
  (nf : (t : Term) -> Eq (substF a t A) A)
  (cMinorIdx cEIdx : Term)
  (ih_minor : Deriv (eqF (ap1 thmT cMinorIdx)
                          (codeFormula (imp (eqF (ap1 f (var a)) O) A))))
  (ih_e : Deriv (eqF (ap1 thmT cEIdx) (codeFormula (E f)))) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_eelim)
                         (ap2 pi (ap2 pi (codeFun1 f) (ap2 pi (natCode a) (codeFormula A)))
                                 (ap2 pi cMinorIdx cEIdx))))
              (codeFormula A))
thmT_at_eelim_codeF f a A nf cMinorIdx cEIdx ih_minor ih_e =
  let cAcode : Term
      cAcode = codeFormula A

      wf_minor :
        Deriv (eqF (ap2 natEqF (codeFormula (imp (eqF (ap1 f (var a)) O) A))
                     (ap2 pi (natCode tag_imp)
                       (ap2 pi
                         (ap2 pi (natCode tag_eq)
                           (ap2 pi (ap2 pi (natCode tag_ap1)
                                     (ap2 pi (codeFun1 f) (ap2 pi (natCode tag_var) (natCode a)))) O))
                         cAcode)))
                   (ap1 s O))
      wf_minor = natEqF_codeF_refl (imp (eqF (ap1 f (var a)) O) A)

      wf_major :
        Deriv (eqF (ap2 natEqF (codeFormula (E f))
                     (ap2 pi (natCode tag_exists) (codeFun1 f)))
                   (ap1 s O))
      wf_major = natEqF_codeF_refl (E f)

      sbfEq_fresh : Deriv (eqF (ap2 sbf (ap2 pi (natCode a) O) cAcode)
                               (codeFormula (substF a O A)))
      sbfEq_fresh = sbfEq_codeFormula a O A

      subst_eq : Deriv (eqF (codeFormula (substF a O A)) cAcode)
      subst_eq = eqSubst (\ z -> Deriv (eqF (codeFormula (substF a O A)) (codeFormula z)))
                         (nf O) (axRefl (codeFormula (substF a O A)))

      fresh_eq : Deriv (eqF (ap2 sbf (ap2 pi (natCode a) O) cAcode) cAcode)
      fresh_eq = ruleTrans sbfEq_fresh subst_eq

      wf_fresh : Deriv (eqF (ap2 natEqF (ap2 sbf (ap2 pi (natCode a) O) cAcode) cAcode) (ap1 s O))
      wf_fresh = ruleTrans (congL natEqF cAcode fresh_eq) (natEqF_codeF_refl A)
  in thmT_at_eelim (codeFun1 f) (natCode a) cAcode cMinorIdx cEIdx
       (codeFormula (imp (eqF (ap1 f (var a)) O) A)) (codeFormula (E f))
       ih_minor ih_e wf_minor wf_major wf_fresh


------------------------------------------------------------------------
-- eIntroAx closure (exists-intro AXIOM ; pure construction, SOUND).
--   input body = pi cG cT  (cG = codeFun1 f , cT = codeTerm t) ;
--   output = codeFormula (imp (eqF (ap1 f t) O) (E f)) .

thmT_at_eintroax :
  (cG cT : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_eintroax) (ap2 pi cG cT)))
              (ap2 pi (natCode tag_imp)
                (ap2 pi
                  (ap2 pi (natCode tag_eq)
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi cG cT)) O))
                  (ap2 pi (natCode tag_exists) cG))))
thmT_at_eintroax cG cT =
  let A_outer : Term
      A_outer = natCode (suc (suc (suc (suc (suc (suc zero))))))  -- natCode 6 ; s A_outer = 7 = tag_eintroax
      Y_body : Term
      Y_body = ap2 pi cG cT
      input : Term
      input = ap2 pi (natCode tag_eintroax) Y_body
      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body
      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
      input_pkg' : Term
      input_pkg' = ap2 pi P_outer (ap1 Snd prev)

      sA_eq : Deriv (eqF (ap1 s A_outer) (natCode tag_eintroax))
      sA_eq = axRefl (natCode tag_eintroax)

      to_stepBody : Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT input_pkg'))
      to_stepBody = preamble_to_stepBody A_outer Y_body

      tag_value : Deriv (eqF (ap1 get_tag input_pkg') (natCode tag_eintroax))
      tag_value = get_tag_value_gen A_outer Y_body (natCode tag_eintroax) sA_eq

      isAx_O = is_neq_O input_pkg' tag_eintroax tag_ax witness_eia_neq_ax tag_value
      isSb_O = is_neq_O input_pkg' tag_eintroax tag_sb witness_eia_neq_sb tag_value
      isMp_O = is_neq_O input_pkg' tag_eintroax tag_mp witness_eia_neq_mp tag_value
      isInd_O = is_neq_O input_pkg' tag_eintroax tag_ind witness_eia_neq_ind tag_value
      isEIntro_O = is_neq_O input_pkg' tag_eintroax tag_eintro witness_eia_neq_eintro tag_value
      isEElim_O = is_neq_O input_pkg' tag_eintroax tag_eelim witness_eia_neq_eelim tag_value
      isEIntroAx_sO = is_eq_sO input_pkg' tag_eintroax tag_value

      d1 = stepBody_to_sb_or_above input_pkg' (ruleTrans (isAx_unfold input_pkg') isAx_O)
      d2 = sb_or_above_to_mp_or_above input_pkg' (ruleTrans (isSb_unfold input_pkg') isSb_O)
      d3 = mp_or_above_to_ind_or_else input_pkg' (ruleTrans (isMp_unfold input_pkg') isMp_O)
      d4 = ind_or_else_to_eintro_or_above input_pkg' (ruleTrans (isInd_unfold input_pkg') isInd_O)
      d5 = eintro_or_above_to_eelim_or_else input_pkg' (ruleTrans (isEIntro_unfold input_pkg') isEIntro_O)
      d6 = eelim_or_else_to_eintroax_or_else input_pkg' (ruleTrans (isEElim_unfold input_pkg') isEElim_O)
      d7 = eintroax_or_else_to_eintroax input_pkg' (ruleTrans (isEIntroAx_unfold input_pkg') isEIntroAx_sO)

      to_branch : Deriv (eqF (ap1 thmT input) (ap1 eintroax_branch_thmT input_pkg'))
      to_branch =
        ruleTrans to_stepBody
          (ruleTrans d1 (ruleTrans d2 (ruleTrans d3 (ruleTrans d4
            (ruleTrans d5 (ruleTrans d6 d7))))))

      get_body_value : Deriv (eqF (ap1 get_body input_pkg') Y_body)
      get_body_value =
        ruleTrans (get_body_at_pi P_outer (ap1 Snd prev))
                  (Snd_sP_to_body_gen A_outer Y_body)

      g_val : Deriv (eqF (ap1 get_eia_g input_pkg') cG)
      g_val =
        ruleTrans (compose1U_eq Fst get_body input_pkg')
          (ruleTrans (cong1 Fst get_body_value) (axFst cG cT))
      t_val : Deriv (eqF (ap1 get_eia_t input_pkg') cT)
      t_val =
        ruleTrans (compose1U_eq Snd get_body input_pkg')
          (ruleTrans (cong1 Snd get_body_value) (axSnd cG cT))

      -- inner  (C pi get_eia_g get_eia_t) input = pi cG cT .
      gt_val : Deriv (eqF (ap1 (C pi get_eia_g get_eia_t) input_pkg') (ap2 pi cG cT))
      gt_val =
        ruleTrans (ax_C pi get_eia_g get_eia_t input_pkg')
          (ruleTrans (congL pi (ap1 get_eia_t input_pkg') g_val)
                     (congR pi cG t_val))

      apnode_val :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) input_pkg')
                    (ap2 pi (natCode tag_ap1) (ap2 pi cG cT)))
      apnode_val =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_eia_g get_eia_t) input_pkg')
          (ruleTrans (congL pi (ap1 (C pi get_eia_g get_eia_t) input_pkg')
                              (constN_eq tag_ap1 input_pkg'))
                     (congR pi (natCode tag_ap1) gt_val))

      eqbody_val :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) o) input_pkg')
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi cG cT)) O))
      eqbody_val =
        ruleTrans (ax_C pi (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) o input_pkg')
          (ruleTrans (congL pi (ap1 o input_pkg') apnode_val)
                     (congR pi (ap2 pi (natCode tag_ap1) (ap2 pi cG cT)) (ax_o input_pkg')))

      mid1_target : Term
      mid1_target =
        ap2 pi (natCode tag_eq)
          (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi cG cT)) O)

      mid1_val :
        Deriv (eqF (ap1 (C pi (constN tag_eq)
                          (C pi (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) o)) input_pkg')
                    mid1_target)
      mid1_val =
        ruleTrans (ax_C pi (constN tag_eq)
                        (C pi (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) o) input_pkg')
          (ruleTrans (congL pi (ap1 (C pi (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) o) input_pkg')
                              (constN_eq tag_eq input_pkg'))
                     (congR pi (natCode tag_eq) eqbody_val))

      mid2_target : Term
      mid2_target = ap2 pi (natCode tag_exists) cG

      mid2_val :
        Deriv (eqF (ap1 (C pi (constN tag_exists) get_eia_g) input_pkg') mid2_target)
      mid2_val =
        ruleTrans (ax_C pi (constN tag_exists) get_eia_g input_pkg')
          (ruleTrans (congL pi (ap1 get_eia_g input_pkg') (constN_eq tag_exists input_pkg'))
                     (congR pi (natCode tag_exists) g_val))

      -- OUTER = C pi MID1 MID2 .
      MID1F : Fun1
      MID1F = C pi (constN tag_eq) (C pi (C pi (constN tag_ap1) (C pi get_eia_g get_eia_t)) o)
      MID2F : Fun1
      MID2F = C pi (constN tag_exists) get_eia_g

      outer_val :
        Deriv (eqF (ap1 (C pi MID1F MID2F) input_pkg') (ap2 pi mid1_target mid2_target))
      outer_val =
        ruleTrans (ax_C pi MID1F MID2F input_pkg')
          (ruleTrans (congL pi (ap1 MID2F input_pkg') mid1_val)
                     (congR pi mid1_target mid2_val))

      branch_val :
        Deriv (eqF (ap1 eintroax_branch_thmT input_pkg')
                    (ap2 pi (natCode tag_imp) (ap2 pi mid1_target mid2_target)))
      branch_val =
        ruleTrans (ax_C pi (constN tag_imp) (C pi MID1F MID2F) input_pkg')
          (ruleTrans (congL pi (ap1 (C pi MID1F MID2F) input_pkg') (constN_eq tag_imp input_pkg'))
                     (congR pi (natCode tag_imp) outer_val))
  in ruleTrans to_branch branch_val
