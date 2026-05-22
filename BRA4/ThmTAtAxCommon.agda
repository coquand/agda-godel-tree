{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAxCommon -- shared infrastructure for the 14  thmT_at_ax_N
-- closures.
--
-- Provides :
--   * NatNeqWitnesses for OUTER tag dispatch (tag_sb / tag_mp / tag_ind vs tag_ax)
--     and for ax SUB-dispatch (axiom indices 0..13, pairwise).
--   * Position-extraction closed forms  get_X_at_pi  (re-derived locally).
--   * Cascade unfolds + tag-firing helpers for the OUTER ax/sb/mp/ind dispatch.
--   * Cascade unfolds + tag-firing helpers for the 14-way ax SUB-dispatch
--     (isAxN parametric over N : Nat).
--   * Factored cov_spec/Post chain helper  thmT_at_pi_succ_to_stepBody .

module BRA4.ThmTAtAxCommon where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv
open import BRA4.CoVSpecFst
open import BRA4.SbT          using ( get_K ; get_inner ; get_table ; get_newK ; get_tag ; get_body
                                     ; lookupAt )
open import BRA4.ThmT
open import BRA4.PiPositivity

open import BRA3.Church          using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost ; I ; axI )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( condFork ; condFork_true_nc ; condFork_false
  ; constN ; constN_eq )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq ; Not )
open import BRA3.RuleInst2       using ( natEq-refl ; true_neq_false )

------------------------------------------------------------------------
-- NatNeqWitness builder.

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

------------------------------------------------------------------------
-- Outer tag dispatch witnesses.
-- Convention: witness_X_neq_Y : NatNeqWitness X Y (X /= Y as Nats).
-- natEqF_at_neq X Y w proves natEqF (natCode X) (natCode Y) = O.

witness_ax_neq_sb : NatNeqWitness tag_ax tag_sb
witness_ax_neq_sb = natEqFalse_to_witness tag_sb tag_ax refl

witness_ax_neq_mp : NatNeqWitness tag_ax tag_mp
witness_ax_neq_mp = natEqFalse_to_witness tag_mp tag_ax refl

witness_ax_neq_ind : NatNeqWitness tag_ax tag_ind
witness_ax_neq_ind = natEqFalse_to_witness tag_ind tag_ax refl

------------------------------------------------------------------------
-- Position-extraction closed forms at  pi A Y .

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

-- get_ax_index at pi A Y.
get_ax_index_at_pi :
  (A Y : Term) -> Deriv (eqF (ap1 get_ax_index (ap2 pi A Y))
                                (ap1 Fst (ap1 Snd (ap1 s A))))
get_ax_index_at_pi A Y =
  let s1 = compose1U_eq Fst get_body (ap2 pi A Y)
  in ruleTrans s1 (cong1 Fst (get_body_at_pi A Y))

get_ax_extra_at_pi :
  (A Y : Term) -> Deriv (eqF (ap1 get_ax_extra (ap2 pi A Y))
                                (ap1 Snd (ap1 Snd (ap1 s A))))
get_ax_extra_at_pi A Y =
  let s1 = compose1U_eq Snd get_body (ap2 pi A Y)
  in ruleTrans s1 (cong1 Snd (get_body_at_pi A Y))

------------------------------------------------------------------------
-- Outer tag dispatch unfoldings.

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
-- Outer tag firing : when  get_tag input = natCode tag_ax .

isAx_at_natCodeAx_sO :
  (input : Term) ->
  Deriv (eqF (ap1 get_tag input) (natCode tag_ax)) ->
  Deriv (eqF (ap1 isAx input) (ap1 s O))
isAx_at_natCodeAx_sO input tag_eq_pf =
  let s1 = isAx_unfold input
      s2 = congL natEqF (natCode tag_ax) tag_eq_pf
      s3 = natEq_eq tag_ax
  in ruleTrans s1 (ruleTrans s2 s3)

isSb_at_natCodeAx_O :
  (input : Term) ->
  Deriv (eqF (ap1 get_tag input) (natCode tag_ax)) ->
  Deriv (eqF (ap1 isSb input) O)
isSb_at_natCodeAx_O input tag_eq_pf =
  let s1 = isSb_unfold input
      s2 = congL natEqF (natCode tag_sb) tag_eq_pf
      s3 = natEqF_at_neq tag_ax tag_sb witness_ax_neq_sb
  in ruleTrans s1 (ruleTrans s2 s3)

isMp_at_natCodeAx_O :
  (input : Term) ->
  Deriv (eqF (ap1 get_tag input) (natCode tag_ax)) ->
  Deriv (eqF (ap1 isMp input) O)
isMp_at_natCodeAx_O input tag_eq_pf =
  let s1 = isMp_unfold input
      s2 = congL natEqF (natCode tag_mp) tag_eq_pf
      s3 = natEqF_at_neq tag_ax tag_mp witness_ax_neq_mp
  in ruleTrans s1 (ruleTrans s2 s3)

isInd_at_natCodeAx_O :
  (input : Term) ->
  Deriv (eqF (ap1 get_tag input) (natCode tag_ax)) ->
  Deriv (eqF (ap1 isInd input) O)
isInd_at_natCodeAx_O input tag_eq_pf =
  let s1 = isInd_unfold input
      s2 = congL natEqF (natCode tag_ind) tag_eq_pf
      s3 = natEqF_at_neq tag_ax tag_ind witness_ax_neq_ind
  in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Outer cascade descents (when tag = tag_ax).
-- stepBody_thmT -> ax_branch_thmT (4 fires : isAx=sO).

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

stepBody_thmT_to_ax_branch :
  (input : Term) ->
  Deriv (eqF (ap1 isAx input) (ap1 s O)) ->
  Deriv (eqF (ap1 stepBody_thmT input) (ap1 ax_branch_thmT input))
stepBody_thmT_to_ax_branch input isAx_sO =
  let e1 = stepBody_thmT_unfold input
      sub_isAx = congR condFork (ap1 (C pi ax_branch_thmT sb_or_above) input) isAx_sO
      cf_to_Fst = condFork_true_nc (ap1 (C pi ax_branch_thmT sb_or_above) input) O
      pi_eq = pi_ax_sbor_unfold input
      Fst_pi = axFst (ap1 ax_branch_thmT input) (ap1 sb_or_above input)
  in ruleTrans e1 (ruleTrans sub_isAx
       (ruleTrans cf_to_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

------------------------------------------------------------------------
-- Parametric isAxOf (= isAxN for the specific N).
--
-- The naming  isAxOf N  is definitionally equal to  isAxN  (both reduce to
--  C natEqF get_ax_index (constN N) ).  Lemmas stated parametrically.

isAxOf : Nat -> Fun1
isAxOf N = C natEqF get_ax_index (constN N)

isAxOf_unfold :
  (N : Nat) (input : Term) ->
  Deriv (eqF (ap1 (isAxOf N) input)
              (ap2 natEqF (ap1 get_ax_index input) (natCode N)))
isAxOf_unfold N input =
  let s1 = ax_C natEqF get_ax_index (constN N) input
      s2 = constN_eq N input
  in ruleTrans s1 (congR natEqF (ap1 get_ax_index input) s2)

isAxOf_at_eq_sO :
  (N : Nat) (input : Term) ->
  Deriv (eqF (ap1 get_ax_index input) (natCode N)) ->
  Deriv (eqF (ap1 (isAxOf N) input) (ap1 s O))
isAxOf_at_eq_sO N input idx_eq =
  let s1 = isAxOf_unfold N input
      s2 = congL natEqF (natCode N) idx_eq
      s3 = natEq_eq N
  in ruleTrans s1 (ruleTrans s2 s3)

-- Witness convention: NatNeqWitness N M means "N /= M as Nats" ;
-- natEqF_at_neq N M w proves natEqF (natCode N) (natCode M) = O.
-- For isAxOf at level M with input encoding axiom N (M /= N), we need
-- natEqF (natCode N) (natCode M) = O via natEqF_at_neq N M with
-- witness NatNeqWitness N M.

isAxOf_at_neq_O :
  (M N : Nat) (w : NatNeqWitness N M) (input : Term) ->
  Deriv (eqF (ap1 get_ax_index input) (natCode N)) ->
  Deriv (eqF (ap1 (isAxOf M) input) O)
isAxOf_at_neq_O M N w input idx_eq =
  let s1 = isAxOf_unfold M input
      s2 = congL natEqF (natCode M) idx_eq
      s3 = natEqF_at_neq N M w
  in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Cov_spec/Post chain helper.  Factors out the chain that goes from
--  ap1 thmT input  to  ap1 stepBody_thmT input_pkg' .  Used by ALL
--  thmT_at_X  closures (sb/mp/ind/ax) -- though sb/mp/ind already
-- inlined it ; only ax closures import this.

thmT_at_pi_succ_to_stepBody :
  (input P_outer : Term) ->
  Deriv (eqF input (ap1 s P_outer)) ->
  Deriv (eqF (ap1 thmT input)
              (ap1 stepBody_thmT
                (ap2 pi P_outer
                  (ap1 Snd (ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer)))))
thmT_at_pi_succ_to_stepBody input P_outer input_eq_sP_outer =
  let prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
      step0 = thmT_unfold input
      step1 = thmT_unfold_F2 O input
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

------------------------------------------------------------------------
-- AX SUB-DISPATCH cascade unfoldings.
--
-- ax_branch_thmT = condFork (pi axBranch0 axDispatch1) isAx0  -- N=0 dispatch
-- axDispatch1    = condFork (pi axBranch1 axDispatch2) isAx1  -- N=1
-- axDispatch2    = condFork (pi axBranch2 axDispatch3) isAx2  -- N=2
-- ...
-- axDispatch13   = condFork (pi axBranch13 ax_fallthrough) isAx13  -- N=13

axBranchThmT_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 ax_branch_thmT input)
              (ap2 condFork (ap1 (C pi axBranch0 axDispatch1) input) (ap1 isAx0 input)))
axBranchThmT_unfold input = ax_C condFork (C pi axBranch0 axDispatch1) isAx0 input

axDispatch1_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch1 input)
              (ap2 condFork (ap1 (C pi axBranch1 axDispatch2) input) (ap1 isAx1 input)))
axDispatch1_unfold input = ax_C condFork (C pi axBranch1 axDispatch2) isAx1 input

axDispatch2_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch2 input)
              (ap2 condFork (ap1 (C pi axBranch2 axDispatch3) input) (ap1 isAx2 input)))
axDispatch2_unfold input = ax_C condFork (C pi axBranch2 axDispatch3) isAx2 input

axDispatch3_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch3 input)
              (ap2 condFork (ap1 (C pi axBranch3 axDispatch4) input) (ap1 isAx3 input)))
axDispatch3_unfold input = ax_C condFork (C pi axBranch3 axDispatch4) isAx3 input

axDispatch4_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch4 input)
              (ap2 condFork (ap1 (C pi axBranch4 axDispatch5) input) (ap1 isAx4 input)))
axDispatch4_unfold input = ax_C condFork (C pi axBranch4 axDispatch5) isAx4 input

axDispatch5_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch5 input)
              (ap2 condFork (ap1 (C pi axBranch5 axDispatch6) input) (ap1 isAx5 input)))
axDispatch5_unfold input = ax_C condFork (C pi axBranch5 axDispatch6) isAx5 input

axDispatch6_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch6 input)
              (ap2 condFork (ap1 (C pi axBranch6 axDispatch7) input) (ap1 isAx6 input)))
axDispatch6_unfold input = ax_C condFork (C pi axBranch6 axDispatch7) isAx6 input

axDispatch7_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch7 input)
              (ap2 condFork (ap1 (C pi axBranch7 axDispatch8) input) (ap1 isAx7 input)))
axDispatch7_unfold input = ax_C condFork (C pi axBranch7 axDispatch8) isAx7 input

axDispatch8_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch8 input)
              (ap2 condFork (ap1 (C pi axBranch8 axDispatch9) input) (ap1 isAx8 input)))
axDispatch8_unfold input = ax_C condFork (C pi axBranch8 axDispatch9) isAx8 input

axDispatch9_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch9 input)
              (ap2 condFork (ap1 (C pi axBranch9 axDispatch10) input) (ap1 isAx9 input)))
axDispatch9_unfold input = ax_C condFork (C pi axBranch9 axDispatch10) isAx9 input

axDispatch10_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch10 input)
              (ap2 condFork (ap1 (C pi axBranch10 axDispatch11) input) (ap1 isAx10 input)))
axDispatch10_unfold input = ax_C condFork (C pi axBranch10 axDispatch11) isAx10 input

axDispatch11_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch11 input)
              (ap2 condFork (ap1 (C pi axBranch11 axDispatch12) input) (ap1 isAx11 input)))
axDispatch11_unfold input = ax_C condFork (C pi axBranch11 axDispatch12) isAx11 input

axDispatch12_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch12 input)
              (ap2 condFork (ap1 (C pi axBranch12 axDispatch13) input) (ap1 isAx12 input)))
axDispatch12_unfold input = ax_C condFork (C pi axBranch12 axDispatch13) isAx12 input

axDispatch13_unfold :
  (input : Term) ->
  Deriv (eqF (ap1 axDispatch13 input)
              (ap2 condFork (ap1 (C pi axBranch13 ax_fallthrough) input) (ap1 isAx13 input)))
axDispatch13_unfold input = ax_C condFork (C pi axBranch13 ax_fallthrough) isAx13 input

------------------------------------------------------------------------
-- Cascade descent helpers.
--
-- For each level M = 0..13 :
--   * land_at_M :  given isAxM = sO, dispatch fires Fst -> axBranchM.
--   * skip_at_M (M < 13) :  given isAxM = O, dispatch fires Snd -> next dispatch.

-- Land helpers.

landAt0 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx0 input) (ap1 s O)) ->
  Deriv (eqF (ap1 ax_branch_thmT input) (ap1 axBranch0 input))
landAt0 input isAx0_sO =
  let e1 = axBranchThmT_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch0 axDispatch1) input) isAx0_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch0 axDispatch1) input) O
      pi_eq = ax_C pi axBranch0 axDispatch1 input
      Fst_pi = axFst (ap1 axBranch0 input) (ap1 axDispatch1 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt1 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx1 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch1 input) (ap1 axBranch1 input))
landAt1 input isAx_sO =
  let e1 = axDispatch1_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch1 axDispatch2) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch1 axDispatch2) input) O
      pi_eq = ax_C pi axBranch1 axDispatch2 input
      Fst_pi = axFst (ap1 axBranch1 input) (ap1 axDispatch2 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt2 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx2 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch2 input) (ap1 axBranch2 input))
landAt2 input isAx_sO =
  let e1 = axDispatch2_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch2 axDispatch3) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch2 axDispatch3) input) O
      pi_eq = ax_C pi axBranch2 axDispatch3 input
      Fst_pi = axFst (ap1 axBranch2 input) (ap1 axDispatch3 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt3 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx3 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch3 input) (ap1 axBranch3 input))
landAt3 input isAx_sO =
  let e1 = axDispatch3_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch3 axDispatch4) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch3 axDispatch4) input) O
      pi_eq = ax_C pi axBranch3 axDispatch4 input
      Fst_pi = axFst (ap1 axBranch3 input) (ap1 axDispatch4 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt4 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx4 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch4 input) (ap1 axBranch4 input))
landAt4 input isAx_sO =
  let e1 = axDispatch4_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch4 axDispatch5) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch4 axDispatch5) input) O
      pi_eq = ax_C pi axBranch4 axDispatch5 input
      Fst_pi = axFst (ap1 axBranch4 input) (ap1 axDispatch5 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt5 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx5 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch5 input) (ap1 axBranch5 input))
landAt5 input isAx_sO =
  let e1 = axDispatch5_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch5 axDispatch6) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch5 axDispatch6) input) O
      pi_eq = ax_C pi axBranch5 axDispatch6 input
      Fst_pi = axFst (ap1 axBranch5 input) (ap1 axDispatch6 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt6 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx6 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch6 input) (ap1 axBranch6 input))
landAt6 input isAx_sO =
  let e1 = axDispatch6_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch6 axDispatch7) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch6 axDispatch7) input) O
      pi_eq = ax_C pi axBranch6 axDispatch7 input
      Fst_pi = axFst (ap1 axBranch6 input) (ap1 axDispatch7 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt7 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx7 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch7 input) (ap1 axBranch7 input))
landAt7 input isAx_sO =
  let e1 = axDispatch7_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch7 axDispatch8) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch7 axDispatch8) input) O
      pi_eq = ax_C pi axBranch7 axDispatch8 input
      Fst_pi = axFst (ap1 axBranch7 input) (ap1 axDispatch8 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt8 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx8 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch8 input) (ap1 axBranch8 input))
landAt8 input isAx_sO =
  let e1 = axDispatch8_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch8 axDispatch9) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch8 axDispatch9) input) O
      pi_eq = ax_C pi axBranch8 axDispatch9 input
      Fst_pi = axFst (ap1 axBranch8 input) (ap1 axDispatch9 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt9 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx9 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch9 input) (ap1 axBranch9 input))
landAt9 input isAx_sO =
  let e1 = axDispatch9_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch9 axDispatch10) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch9 axDispatch10) input) O
      pi_eq = ax_C pi axBranch9 axDispatch10 input
      Fst_pi = axFst (ap1 axBranch9 input) (ap1 axDispatch10 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt10 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx10 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch10 input) (ap1 axBranch10 input))
landAt10 input isAx_sO =
  let e1 = axDispatch10_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch10 axDispatch11) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch10 axDispatch11) input) O
      pi_eq = ax_C pi axBranch10 axDispatch11 input
      Fst_pi = axFst (ap1 axBranch10 input) (ap1 axDispatch11 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt11 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx11 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch11 input) (ap1 axBranch11 input))
landAt11 input isAx_sO =
  let e1 = axDispatch11_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch11 axDispatch12) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch11 axDispatch12) input) O
      pi_eq = ax_C pi axBranch11 axDispatch12 input
      Fst_pi = axFst (ap1 axBranch11 input) (ap1 axDispatch12 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt12 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx12 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch12 input) (ap1 axBranch12 input))
landAt12 input isAx_sO =
  let e1 = axDispatch12_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch12 axDispatch13) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch12 axDispatch13) input) O
      pi_eq = ax_C pi axBranch12 axDispatch13 input
      Fst_pi = axFst (ap1 axBranch12 input) (ap1 axDispatch13 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

landAt13 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx13 input) (ap1 s O)) ->
  Deriv (eqF (ap1 axDispatch13 input) (ap1 axBranch13 input))
landAt13 input isAx_sO =
  let e1 = axDispatch13_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch13 ax_fallthrough) input) isAx_sO
      cf_Fst = condFork_true_nc (ap1 (C pi axBranch13 ax_fallthrough) input) O
      pi_eq = ax_C pi axBranch13 ax_fallthrough input
      Fst_pi = axFst (ap1 axBranch13 input) (ap1 ax_fallthrough input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Fst (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

-- Skip helpers : at level M, isAxM = O, descend to level M+1.

skipAt0 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx0 input) O) ->
  Deriv (eqF (ap1 ax_branch_thmT input) (ap1 axDispatch1 input))
skipAt0 input isAx0_O =
  let e1 = axBranchThmT_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch0 axDispatch1) input) isAx0_O
      cf_Snd = condFork_false (ap1 (C pi axBranch0 axDispatch1) input)
      pi_eq = ax_C pi axBranch0 axDispatch1 input
      Snd_pi = axSnd (ap1 axBranch0 input) (ap1 axDispatch1 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt1 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx1 input) O) ->
  Deriv (eqF (ap1 axDispatch1 input) (ap1 axDispatch2 input))
skipAt1 input isAx_O =
  let e1 = axDispatch1_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch1 axDispatch2) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch1 axDispatch2) input)
      pi_eq = ax_C pi axBranch1 axDispatch2 input
      Snd_pi = axSnd (ap1 axBranch1 input) (ap1 axDispatch2 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt2 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx2 input) O) ->
  Deriv (eqF (ap1 axDispatch2 input) (ap1 axDispatch3 input))
skipAt2 input isAx_O =
  let e1 = axDispatch2_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch2 axDispatch3) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch2 axDispatch3) input)
      pi_eq = ax_C pi axBranch2 axDispatch3 input
      Snd_pi = axSnd (ap1 axBranch2 input) (ap1 axDispatch3 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt3 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx3 input) O) ->
  Deriv (eqF (ap1 axDispatch3 input) (ap1 axDispatch4 input))
skipAt3 input isAx_O =
  let e1 = axDispatch3_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch3 axDispatch4) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch3 axDispatch4) input)
      pi_eq = ax_C pi axBranch3 axDispatch4 input
      Snd_pi = axSnd (ap1 axBranch3 input) (ap1 axDispatch4 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt4 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx4 input) O) ->
  Deriv (eqF (ap1 axDispatch4 input) (ap1 axDispatch5 input))
skipAt4 input isAx_O =
  let e1 = axDispatch4_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch4 axDispatch5) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch4 axDispatch5) input)
      pi_eq = ax_C pi axBranch4 axDispatch5 input
      Snd_pi = axSnd (ap1 axBranch4 input) (ap1 axDispatch5 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt5 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx5 input) O) ->
  Deriv (eqF (ap1 axDispatch5 input) (ap1 axDispatch6 input))
skipAt5 input isAx_O =
  let e1 = axDispatch5_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch5 axDispatch6) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch5 axDispatch6) input)
      pi_eq = ax_C pi axBranch5 axDispatch6 input
      Snd_pi = axSnd (ap1 axBranch5 input) (ap1 axDispatch6 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt6 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx6 input) O) ->
  Deriv (eqF (ap1 axDispatch6 input) (ap1 axDispatch7 input))
skipAt6 input isAx_O =
  let e1 = axDispatch6_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch6 axDispatch7) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch6 axDispatch7) input)
      pi_eq = ax_C pi axBranch6 axDispatch7 input
      Snd_pi = axSnd (ap1 axBranch6 input) (ap1 axDispatch7 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt7 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx7 input) O) ->
  Deriv (eqF (ap1 axDispatch7 input) (ap1 axDispatch8 input))
skipAt7 input isAx_O =
  let e1 = axDispatch7_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch7 axDispatch8) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch7 axDispatch8) input)
      pi_eq = ax_C pi axBranch7 axDispatch8 input
      Snd_pi = axSnd (ap1 axBranch7 input) (ap1 axDispatch8 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt8 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx8 input) O) ->
  Deriv (eqF (ap1 axDispatch8 input) (ap1 axDispatch9 input))
skipAt8 input isAx_O =
  let e1 = axDispatch8_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch8 axDispatch9) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch8 axDispatch9) input)
      pi_eq = ax_C pi axBranch8 axDispatch9 input
      Snd_pi = axSnd (ap1 axBranch8 input) (ap1 axDispatch9 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt9 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx9 input) O) ->
  Deriv (eqF (ap1 axDispatch9 input) (ap1 axDispatch10 input))
skipAt9 input isAx_O =
  let e1 = axDispatch9_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch9 axDispatch10) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch9 axDispatch10) input)
      pi_eq = ax_C pi axBranch9 axDispatch10 input
      Snd_pi = axSnd (ap1 axBranch9 input) (ap1 axDispatch10 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt10 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx10 input) O) ->
  Deriv (eqF (ap1 axDispatch10 input) (ap1 axDispatch11 input))
skipAt10 input isAx_O =
  let e1 = axDispatch10_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch10 axDispatch11) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch10 axDispatch11) input)
      pi_eq = ax_C pi axBranch10 axDispatch11 input
      Snd_pi = axSnd (ap1 axBranch10 input) (ap1 axDispatch11 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt11 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx11 input) O) ->
  Deriv (eqF (ap1 axDispatch11 input) (ap1 axDispatch12 input))
skipAt11 input isAx_O =
  let e1 = axDispatch11_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch11 axDispatch12) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch11 axDispatch12) input)
      pi_eq = ax_C pi axBranch11 axDispatch12 input
      Snd_pi = axSnd (ap1 axBranch11 input) (ap1 axDispatch12 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

skipAt12 :
  (input : Term) ->
  Deriv (eqF (ap1 isAx12 input) O) ->
  Deriv (eqF (ap1 axDispatch12 input) (ap1 axDispatch13 input))
skipAt12 input isAx_O =
  let e1 = axDispatch12_unfold input
      sub_eq = congR condFork (ap1 (C pi axBranch12 axDispatch13) input) isAx_O
      cf_Snd = condFork_false (ap1 (C pi axBranch12 axDispatch13) input)
      pi_eq = ax_C pi axBranch12 axDispatch13 input
      Snd_pi = axSnd (ap1 axBranch12 input) (ap1 axDispatch13 input)
  in ruleTrans e1 (ruleTrans sub_eq
       (ruleTrans cf_Snd (ruleTrans (cong1 Snd pi_eq) Snd_pi)))
