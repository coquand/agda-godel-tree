{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefRecogImp -- Carneiro-lifted (imp P) variants of the three
-- KdefRecog lemmas:
--   outKdef_correct  ==>  imp_outKdef_correct
--   hitKdef_fires    ==>  imp_hitKdef_fires
--   dNeg_from_hitKdef ==> imp_dNeg_from_hitKdef
--
-- The original lemmas are Hilbert chains over closed primitives.  The
-- lift maps each ruleTrans/cong*/ruleSym to its impEqTrans/impCong*/
-- impRuleSym analog (T4.Thm12.ImpHelpers); closed Derivs are wrapped
-- via impLift.  We also Carneiro-lift  eqInd_sound  inline (it is the
-- only KdefRecog dependency that has its own h-dependent inner chain).

module T4.KdefRecogImp where

open import T4.Base
open import T4.Code        using ( falseF )
open import T4.ThmT        using ( thmT )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.Num         using ( num )
open import T4.Kdef        using ( Kcode ; Kcode_eval ; kdefSkel ; kdefConsts )
open import T4.KOut        using ( skelOf_proj )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_at_neq_imp
                                   ; negToImpFalse ; impFalseToNeg_imp )
open import T4.KFire       using ( eqInd_at_eq )
open import T4.KdefRecog   using ( projKdef ; outKdef ; hitKdef
                                   ; hitKdef_eval )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impEqTrans ; impCong1 ; impCongL ; impCongR )
open import T4.ImpExtras
  using ( imp_eqTrans_imp )

open import BRA3.Logic           using ( impTrans )
open import BRA3.Contrapositive  using ( DNE )
open import BRA3.PairAlgebra     using ( compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- Local helper:  imp-lifted composition of two implications.
-- Given F : imp P (imp X Y)  and  G : imp P (imp Y W) , produce
--      H : imp P (imp X W) .
-- Derived from axK + axS.

imp_compI :
  {P X Y W : Formula} ->
  Deriv (imp P (imp X Y)) -> Deriv (imp P (imp Y W)) ->
  Deriv (imp P (imp X W))
imp_compI {P} {X} {Y} {W} F G =
  let G' : Deriv (imp P (imp X (imp Y W)))
      G' = impTrans G (axK (imp Y W) X)
      G'' : Deriv (imp P (imp (imp X Y) (imp X W)))
      G'' = impTrans G' (axS X Y W)
  in impMp {P} G'' F

------------------------------------------------------------------------
-- imp_eqInd_sound -- Carneiro-lifted  T4.Bridge.eqInd_sound .
--
-- Original (T4/Bridge.agda):
--   eqInd_sound a b h =
--     let nq      = neg (eqF a b)                              -- closed
--         d_O     = eqInd_at_neq_imp a b                       -- closed
--         rw      = prependEqLeft (s O) (eqInd a b) O (ruleSym h)
--                 = mp (ax_eqTrans (eqInd a b) (s O) O) h      -- DEPENDS on h
--         d_soO   = compI d_O rw
--         d_false = compI d_soO (negToImpFalse (s O = O) ax_succ_nonzero)
--         dnn     = mp (impFalseToNeg_imp nq) d_false
--     in mp (DNE (eqF a b)) dnn
--
-- Carneiro lift:  only  rw  has h-content;  rw_imp  is the only thing
-- that needs imp-wrapping, and is built from h_imp via impMp +
-- impLift (axiom ax_eqTrans).   The rest threads through  imp_compI .

imp_eqInd_sound :
  (P : Formula) (a b : Term) ->
  Deriv (imp P (eqF (eqInd a b) (ap1 s O))) ->
  Deriv (imp P (eqF a b))
imp_eqInd_sound P a b h_imp =
  let nq : Formula
      nq = neg (eqF a b)

      d_O : Deriv (imp nq (eqF (eqInd a b) O))
      d_O = eqInd_at_neq_imp a b

      d_O_imp : Deriv (imp P (imp nq (eqF (eqInd a b) O)))
      d_O_imp = impLift {P} d_O

      ax_eqT_inst :
        Deriv (imp (eqF (eqInd a b) (ap1 s O))
                   (imp (eqF (eqInd a b) O) (eqF (ap1 s O) O)))
      ax_eqT_inst = ax_eqTrans (eqInd a b) (ap1 s O) O

      rw_imp : Deriv (imp P (imp (eqF (eqInd a b) O) (eqF (ap1 s O) O)))
      rw_imp = impMp {P} (impLift {P} ax_eqT_inst) h_imp

      d_soO_imp : Deriv (imp P (imp nq (eqF (ap1 s O) O)))
      d_soO_imp = imp_compI {P} d_O_imp rw_imp

      closed_neg_succ : Deriv (imp (eqF (ap1 s O) O) falseF)
      closed_neg_succ = negToImpFalse (eqF (ap1 s O) O) ax_succ_nonzero

      d_false_imp : Deriv (imp P (imp nq falseF))
      d_false_imp = imp_compI {P} d_soO_imp (impLift {P} closed_neg_succ)

      i2n_axiom : Deriv (imp (imp nq falseF) (neg nq))
      i2n_axiom = impFalseToNeg_imp nq

      dnn_imp : Deriv (imp P (neg nq))
      dnn_imp = impMp {P} (impLift {P} i2n_axiom) d_false_imp

      dne_axiom : Deriv (imp (neg nq) (eqF a b))
      dne_axiom = DNE (eqF a b)

  in impMp {P} (impLift {P} dne_axiom) dnn_imp

------------------------------------------------------------------------
-- imp_outKdef_correct -- Carneiro-lifted  outKdef_correct .

imp_outKdef_correct :
  (P : Formula) (L w x' : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 (Kcode L) x'))) ->
  Deriv (imp P (eqF (ap1 (outKdef L) w) x'))
imp_outKdef_correct P L w x' matched_imp =
  let e1 = compose1U_eq decode (compose1U (projKdef L) thmT) w
      e2 = compose1U_eq (projKdef L) thmT w
      kcode_eval = Kcode_eval L x'
      step_to_skel =
        imp_eqTrans_imp matched_imp (impLift {P} kcode_eval)
      cong_step = impCong1 (projKdef L) (ap1 thmT w)
                    (kdefSkel L (ap1 num x')) step_to_skel
      -- EXPLICIT kdefConsts L:  avoids the slow NVList unfolding
      -- (see feedback_slow_typecheck_means_abstract_constants).
      skel_final = skelOf_proj (kdefConsts L) (ap1 num x')
      e3_imp = imp_eqTrans_imp cong_step (impLift {P} skel_final)
      e4 = decode_num_id_at x'
      e2_to_e3 = imp_eqTrans_imp (impLift {P} e2) e3_imp
      cong_decode = impCong1 decode (ap1 (compose1U (projKdef L) thmT) w)
                      (ap1 num x') e2_to_e3
      step_decode_to_x' =
        imp_eqTrans_imp cong_decode (impLift {P} e4)
  in imp_eqTrans_imp (impLift {P} e1) step_decode_to_x'

------------------------------------------------------------------------
-- imp_hitKdef_fires -- Carneiro-lifted  hitKdef_fires .

imp_hitKdef_fires :
  (P : Formula) (L w x : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 (Kcode L) x))) ->
  Deriv (imp P (eqF (ap1 (hitKdef L (outKdef L)) w) (ap1 s O)))
imp_hitKdef_fires P L w x hyp_imp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 (Kcode L) (ap1 (outKdef L) w)

      out_ok : Deriv (imp P (eqF (ap1 (outKdef L) w) x))
      out_ok = imp_outKdef_correct P L w x hyp_imp

      bIsKx : Deriv (imp P (eqF B (ap1 (Kcode L) x)))
      bIsKx = impCong1 (Kcode L) (ap1 (outKdef L) w) x out_ok

      hk_eval :
        Deriv (eqF (ap1 (hitKdef L (outKdef L)) w) (eqInd A B))
      hk_eval = hitKdef_eval L (outKdef L) w

      eqIndF_eq_AB : Deriv (eqF (ap2 eqIndF A B) (eqInd A B))
      eqIndF_eq_AB = eqIndF_eq A B

      eqIndF_eq_AB_rev : Deriv (eqF (eqInd A B) (ap2 eqIndF A B))
      eqIndF_eq_AB_rev = ruleSym eqIndF_eq_AB

      congL_step :
        Deriv (imp P (eqF (ap2 eqIndF A B) (ap2 eqIndF (ap1 (Kcode L) x) B)))
      congL_step = impCongL eqIndF A (ap1 (Kcode L) x) B hyp_imp

      congR_step :
        Deriv (imp P (eqF (ap2 eqIndF (ap1 (Kcode L) x) B)
                           (ap2 eqIndF (ap1 (Kcode L) x) (ap1 (Kcode L) x))))
      congR_step = impCongR eqIndF B (ap1 (Kcode L) x) (ap1 (Kcode L) x) bIsKx

      eqIndF_eq_KxKx :
        Deriv (eqF (ap2 eqIndF (ap1 (Kcode L) x) (ap1 (Kcode L) x))
                    (eqInd (ap1 (Kcode L) x) (ap1 (Kcode L) x)))
      eqIndF_eq_KxKx = eqIndF_eq (ap1 (Kcode L) x) (ap1 (Kcode L) x)

      eqInd_diag :
        Deriv (eqF (eqInd (ap1 (Kcode L) x) (ap1 (Kcode L) x)) (ap1 s O))
      eqInd_diag = eqInd_at_eq (ap1 (Kcode L) x)

      chain1 : Deriv (imp P (eqF (ap1 (hitKdef L (outKdef L)) w) (eqInd A B)))
      chain1 = impLift {P} hk_eval

      chain2 :
        Deriv (imp P (eqF (ap1 (hitKdef L (outKdef L)) w) (ap2 eqIndF A B)))
      chain2 = impEqTrans (ap1 (hitKdef L (outKdef L)) w) (eqInd A B)
                 (ap2 eqIndF A B) chain1 (impLift {P} eqIndF_eq_AB_rev)

      chain3 :
        Deriv (imp P (eqF (ap1 (hitKdef L (outKdef L)) w)
                           (ap2 eqIndF (ap1 (Kcode L) x) B)))
      chain3 = impEqTrans (ap1 (hitKdef L (outKdef L)) w) (ap2 eqIndF A B)
                 (ap2 eqIndF (ap1 (Kcode L) x) B) chain2 congL_step

      chain4 :
        Deriv (imp P (eqF (ap1 (hitKdef L (outKdef L)) w)
                           (ap2 eqIndF (ap1 (Kcode L) x) (ap1 (Kcode L) x))))
      chain4 = impEqTrans (ap1 (hitKdef L (outKdef L)) w)
                 (ap2 eqIndF (ap1 (Kcode L) x) B)
                 (ap2 eqIndF (ap1 (Kcode L) x) (ap1 (Kcode L) x))
                 chain3 congR_step

      chain5 :
        Deriv (imp P (eqF (ap1 (hitKdef L (outKdef L)) w)
                           (eqInd (ap1 (Kcode L) x) (ap1 (Kcode L) x))))
      chain5 = impEqTrans (ap1 (hitKdef L (outKdef L)) w)
                 (ap2 eqIndF (ap1 (Kcode L) x) (ap1 (Kcode L) x))
                 (eqInd (ap1 (Kcode L) x) (ap1 (Kcode L) x))
                 chain4 (impLift {P} eqIndF_eq_KxKx)
  in impEqTrans (ap1 (hitKdef L (outKdef L)) w)
       (eqInd (ap1 (Kcode L) x) (ap1 (Kcode L) x)) (ap1 s O)
       chain5 (impLift {P} eqInd_diag)

------------------------------------------------------------------------
-- imp_dNeg_from_hitKdef -- Carneiro-lifted  dNeg_from_hitKdef .
--
-- Original:
--   dNeg_from_hitKdef L out w0 h =
--     let match = ruleTrans (ruleSym (hitKdef_eval L out w0)) h
--     in eqInd_sound (thmT w0) (Kcode L (out w0)) match

imp_dNeg_from_hitKdef :
  (P : Formula) (L : Term) (out : Fun1) (w0 : Term) ->
  Deriv (imp P (eqF (ap1 (hitKdef L out) w0) (ap1 s O))) ->
  Deriv (imp P (eqF (ap1 thmT w0) (ap1 (Kcode L) (ap1 out w0))))
imp_dNeg_from_hitKdef P L out w0 h_imp =
  let A : Term
      A = ap1 thmT w0
      B : Term
      B = ap1 (Kcode L) (ap1 out w0)

      hk_eval_sym :
        Deriv (eqF (eqInd A B) (ap1 (hitKdef L out) w0))
      hk_eval_sym = ruleSym (hitKdef_eval L out w0)

      match_imp :
        Deriv (imp P (eqF (eqInd A B) (ap1 s O)))
      match_imp =
        impEqTrans (eqInd A B) (ap1 (hitKdef L out) w0) (ap1 s O)
          (impLift {P} hk_eval_sym) h_imp
  in imp_eqInd_sound P A B match_imp
