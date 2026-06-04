{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefRecogImpAlph -- Carneiro-lifted (imp P) variants of KdefRecogAlph,
-- the  checkAlphN -guard analog of  T4.KdefRecogImp .   The guard-independent
-- helper  imp_eqInd_sound  is reused verbatim from  T4.KdefRecogImp .

open import T4.Base

module T4.KdefRecogImpAlph (Lstar_meta : Nat) where

open import T4.ThmT        using ( thmT )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.Num         using ( num )
open import T4.KdefAlph Lstar_meta
  using ( KcodeAlph ; KcodeAlph_eval ; kdefAlphSkel ; kdefAlphConsts )
open import T4.KOut        using ( skelOf_proj )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd )
open import T4.KFire       using ( eqInd_at_eq )
open import T4.KdefRecogAlph Lstar_meta
  using ( projKdefAlph ; outKdefAlph ; hitKdefAlph ; hitKdefAlph_eval )
open import T4.KdefRecogImp using ( imp_eqInd_sound )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impEqTrans ; impCong1 ; impCongL ; impCongR )
open import T4.ImpExtras
  using ( imp_eqTrans_imp )

open import BRA3.PairAlgebra     using ( compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- imp_outKdefAlph_correct .

imp_outKdefAlph_correct :
  (P : Formula) (w x' : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 KcodeAlph x'))) ->
  Deriv (imp P (eqF (ap1 outKdefAlph w) x'))
imp_outKdefAlph_correct P w x' matched_imp =
  let e1 = compose1U_eq decode (compose1U projKdefAlph thmT) w
      e2 = compose1U_eq projKdefAlph thmT w
      kcode_eval = KcodeAlph_eval x'
      step_to_skel =
        imp_eqTrans_imp matched_imp (impLift {P} kcode_eval)
      cong_step = impCong1 projKdefAlph (ap1 thmT w)
                    (kdefAlphSkel (ap1 num x')) step_to_skel
      skel_final = skelOf_proj kdefAlphConsts (ap1 num x')
      e3_imp = imp_eqTrans_imp cong_step (impLift {P} skel_final)
      e4 = decode_num_id_at x'
      e2_to_e3 = imp_eqTrans_imp (impLift {P} e2) e3_imp
      cong_decode = impCong1 decode (ap1 (compose1U projKdefAlph thmT) w)
                      (ap1 num x') e2_to_e3
      step_decode_to_x' =
        imp_eqTrans_imp cong_decode (impLift {P} e4)
  in imp_eqTrans_imp (impLift {P} e1) step_decode_to_x'

------------------------------------------------------------------------
-- imp_hitKdefAlph_fires .

imp_hitKdefAlph_fires :
  (P : Formula) (w x : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 KcodeAlph x))) ->
  Deriv (imp P (eqF (ap1 (hitKdefAlph outKdefAlph) w) (ap1 s O)))
imp_hitKdefAlph_fires P w x hyp_imp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 KcodeAlph (ap1 outKdefAlph w)

      out_ok : Deriv (imp P (eqF (ap1 outKdefAlph w) x))
      out_ok = imp_outKdefAlph_correct P w x hyp_imp

      bIsKx : Deriv (imp P (eqF B (ap1 KcodeAlph x)))
      bIsKx = impCong1 KcodeAlph (ap1 outKdefAlph w) x out_ok

      hk_eval :
        Deriv (eqF (ap1 (hitKdefAlph outKdefAlph) w) (eqInd A B))
      hk_eval = hitKdefAlph_eval outKdefAlph w

      eqIndF_eq_AB : Deriv (eqF (ap2 eqIndF A B) (eqInd A B))
      eqIndF_eq_AB = eqIndF_eq A B

      eqIndF_eq_AB_rev : Deriv (eqF (eqInd A B) (ap2 eqIndF A B))
      eqIndF_eq_AB_rev = ruleSym eqIndF_eq_AB

      congL_step :
        Deriv (imp P (eqF (ap2 eqIndF A B) (ap2 eqIndF (ap1 KcodeAlph x) B)))
      congL_step = impCongL eqIndF A (ap1 KcodeAlph x) B hyp_imp

      congR_step :
        Deriv (imp P (eqF (ap2 eqIndF (ap1 KcodeAlph x) B)
                           (ap2 eqIndF (ap1 KcodeAlph x) (ap1 KcodeAlph x))))
      congR_step = impCongR eqIndF B (ap1 KcodeAlph x) (ap1 KcodeAlph x) bIsKx

      eqIndF_eq_KxKx :
        Deriv (eqF (ap2 eqIndF (ap1 KcodeAlph x) (ap1 KcodeAlph x))
                    (eqInd (ap1 KcodeAlph x) (ap1 KcodeAlph x)))
      eqIndF_eq_KxKx = eqIndF_eq (ap1 KcodeAlph x) (ap1 KcodeAlph x)

      eqInd_diag :
        Deriv (eqF (eqInd (ap1 KcodeAlph x) (ap1 KcodeAlph x)) (ap1 s O))
      eqInd_diag = eqInd_at_eq (ap1 KcodeAlph x)

      chain1 : Deriv (imp P (eqF (ap1 (hitKdefAlph outKdefAlph) w) (eqInd A B)))
      chain1 = impLift {P} hk_eval

      chain2 :
        Deriv (imp P (eqF (ap1 (hitKdefAlph outKdefAlph) w) (ap2 eqIndF A B)))
      chain2 = impEqTrans (ap1 (hitKdefAlph outKdefAlph) w) (eqInd A B)
                 (ap2 eqIndF A B) chain1 (impLift {P} eqIndF_eq_AB_rev)

      chain3 :
        Deriv (imp P (eqF (ap1 (hitKdefAlph outKdefAlph) w)
                           (ap2 eqIndF (ap1 KcodeAlph x) B)))
      chain3 = impEqTrans (ap1 (hitKdefAlph outKdefAlph) w) (ap2 eqIndF A B)
                 (ap2 eqIndF (ap1 KcodeAlph x) B) chain2 congL_step

      chain4 :
        Deriv (imp P (eqF (ap1 (hitKdefAlph outKdefAlph) w)
                           (ap2 eqIndF (ap1 KcodeAlph x) (ap1 KcodeAlph x))))
      chain4 = impEqTrans (ap1 (hitKdefAlph outKdefAlph) w)
                 (ap2 eqIndF (ap1 KcodeAlph x) B)
                 (ap2 eqIndF (ap1 KcodeAlph x) (ap1 KcodeAlph x))
                 chain3 congR_step

      chain5 :
        Deriv (imp P (eqF (ap1 (hitKdefAlph outKdefAlph) w)
                           (eqInd (ap1 KcodeAlph x) (ap1 KcodeAlph x))))
      chain5 = impEqTrans (ap1 (hitKdefAlph outKdefAlph) w)
                 (ap2 eqIndF (ap1 KcodeAlph x) (ap1 KcodeAlph x))
                 (eqInd (ap1 KcodeAlph x) (ap1 KcodeAlph x))
                 chain4 (impLift {P} eqIndF_eq_KxKx)
  in impEqTrans (ap1 (hitKdefAlph outKdefAlph) w)
       (eqInd (ap1 KcodeAlph x) (ap1 KcodeAlph x)) (ap1 s O)
       chain5 (impLift {P} eqInd_diag)

------------------------------------------------------------------------
-- imp_dNeg_from_hitKdefAlph .

imp_dNeg_from_hitKdefAlph :
  (P : Formula) (out : Fun1) (w0 : Term) ->
  Deriv (imp P (eqF (ap1 (hitKdefAlph out) w0) (ap1 s O))) ->
  Deriv (imp P (eqF (ap1 thmT w0) (ap1 KcodeAlph (ap1 out w0))))
imp_dNeg_from_hitKdefAlph P out w0 h_imp =
  let A : Term
      A = ap1 thmT w0
      B : Term
      B = ap1 KcodeAlph (ap1 out w0)

      hk_eval_sym :
        Deriv (eqF (eqInd A B) (ap1 (hitKdefAlph out) w0))
      hk_eval_sym = ruleSym (hitKdefAlph_eval out w0)

      match_imp :
        Deriv (imp P (eqF (eqInd A B) (ap1 s O)))
      match_imp =
        impEqTrans (eqInd A B) (ap1 (hitKdefAlph out) w0) (ap1 s O)
          (impLift {P} hk_eval_sym) h_imp
  in imp_eqInd_sound P A B match_imp
