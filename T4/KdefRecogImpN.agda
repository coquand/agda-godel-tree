{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefRecogImpN -- the number-code re-pointing of T4.KdefRecogImp : the
-- Carneiro-lifted (imp P) recogniser lemmas over the honest KdefN K-formula.
-- Verbatim mirror ( KdefRecogImp is generic in the K-formula's code/skeleton ),
-- with Kdef* -> Kdef*N , L absorbed into predN .  imp_eqInd_sound is GENERIC and
-- reused from T4.KdefRecogImp.

open import T4.Base

module T4.KdefRecogImpN (predN : Term) where

open import T4.ThmT        using ( thmT )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.Num         using ( num )
open import T4.KdefN  predN using ( KcodeN ; KcodeN_eval ; kdefSkelN ; kdefConstsN )
open import T4.KOut        using ( skelOf_proj )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd )
open import T4.KFire       using ( eqInd_at_eq )
open import T4.KdefRecogN predN using ( projKdefN ; outKdefN ; hitKdefN ; hitKdefN_eval )
open import T4.KdefRecogImp using ( imp_eqInd_sound )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impEqTrans ; impCong1 ; impCongL ; impCongR )
open import T4.ImpExtras using ( imp_eqTrans_imp )

open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- imp_outKdefN_correct -- Carneiro-lifted  outKdefN_correct .

imp_outKdefN_correct :
  (P : Formula) (w x' : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 KcodeN x'))) ->
  Deriv (imp P (eqF (ap1 outKdefN w) x'))
imp_outKdefN_correct P w x' matched_imp =
  let e1 = compose1U_eq decode (compose1U projKdefN thmT) w
      e2 = compose1U_eq projKdefN thmT w
      kcode_eval = KcodeN_eval x'
      step_to_skel =
        imp_eqTrans_imp matched_imp (impLift {P} kcode_eval)
      cong_step = impCong1 projKdefN (ap1 thmT w)
                    (kdefSkelN (ap1 num x')) step_to_skel
      skel_final = skelOf_proj kdefConstsN (ap1 num x')
      e3_imp = imp_eqTrans_imp cong_step (impLift {P} skel_final)
      e4 = decode_num_id_at x'
      e2_to_e3 = imp_eqTrans_imp (impLift {P} e2) e3_imp
      cong_decode = impCong1 decode (ap1 (compose1U projKdefN thmT) w)
                      (ap1 num x') e2_to_e3
      step_decode_to_x' =
        imp_eqTrans_imp cong_decode (impLift {P} e4)
  in imp_eqTrans_imp (impLift {P} e1) step_decode_to_x'

------------------------------------------------------------------------
-- imp_hitKdefN_fires -- Carneiro-lifted  hitKdefN_fires .

imp_hitKdefN_fires :
  (P : Formula) (w x : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 KcodeN x))) ->
  Deriv (imp P (eqF (ap1 (hitKdefN outKdefN) w) (ap1 s O)))
imp_hitKdefN_fires P w x hyp_imp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 KcodeN (ap1 outKdefN w)

      out_ok : Deriv (imp P (eqF (ap1 outKdefN w) x))
      out_ok = imp_outKdefN_correct P w x hyp_imp

      bIsKx : Deriv (imp P (eqF B (ap1 KcodeN x)))
      bIsKx = impCong1 KcodeN (ap1 outKdefN w) x out_ok

      hk_eval : Deriv (eqF (ap1 (hitKdefN outKdefN) w) (eqInd A B))
      hk_eval = hitKdefN_eval outKdefN w

      eqIndF_eq_AB : Deriv (eqF (ap2 eqIndF A B) (eqInd A B))
      eqIndF_eq_AB = eqIndF_eq A B

      eqIndF_eq_AB_rev : Deriv (eqF (eqInd A B) (ap2 eqIndF A B))
      eqIndF_eq_AB_rev = ruleSym eqIndF_eq_AB

      congL_step :
        Deriv (imp P (eqF (ap2 eqIndF A B) (ap2 eqIndF (ap1 KcodeN x) B)))
      congL_step = impCongL eqIndF A (ap1 KcodeN x) B hyp_imp

      congR_step :
        Deriv (imp P (eqF (ap2 eqIndF (ap1 KcodeN x) B)
                           (ap2 eqIndF (ap1 KcodeN x) (ap1 KcodeN x))))
      congR_step = impCongR eqIndF B (ap1 KcodeN x) (ap1 KcodeN x) bIsKx

      eqIndF_eq_KxKx :
        Deriv (eqF (ap2 eqIndF (ap1 KcodeN x) (ap1 KcodeN x))
                    (eqInd (ap1 KcodeN x) (ap1 KcodeN x)))
      eqIndF_eq_KxKx = eqIndF_eq (ap1 KcodeN x) (ap1 KcodeN x)

      eqInd_diag :
        Deriv (eqF (eqInd (ap1 KcodeN x) (ap1 KcodeN x)) (ap1 s O))
      eqInd_diag = eqInd_at_eq (ap1 KcodeN x)

      chain1 : Deriv (imp P (eqF (ap1 (hitKdefN outKdefN) w) (eqInd A B)))
      chain1 = impLift {P} hk_eval

      chain2 :
        Deriv (imp P (eqF (ap1 (hitKdefN outKdefN) w) (ap2 eqIndF A B)))
      chain2 = impEqTrans (ap1 (hitKdefN outKdefN) w) (eqInd A B)
                 (ap2 eqIndF A B) chain1 (impLift {P} eqIndF_eq_AB_rev)

      chain3 :
        Deriv (imp P (eqF (ap1 (hitKdefN outKdefN) w)
                           (ap2 eqIndF (ap1 KcodeN x) B)))
      chain3 = impEqTrans (ap1 (hitKdefN outKdefN) w) (ap2 eqIndF A B)
                 (ap2 eqIndF (ap1 KcodeN x) B) chain2 congL_step

      chain4 :
        Deriv (imp P (eqF (ap1 (hitKdefN outKdefN) w)
                           (ap2 eqIndF (ap1 KcodeN x) (ap1 KcodeN x))))
      chain4 = impEqTrans (ap1 (hitKdefN outKdefN) w)
                 (ap2 eqIndF (ap1 KcodeN x) B)
                 (ap2 eqIndF (ap1 KcodeN x) (ap1 KcodeN x))
                 chain3 congR_step

      chain5 :
        Deriv (imp P (eqF (ap1 (hitKdefN outKdefN) w)
                           (eqInd (ap1 KcodeN x) (ap1 KcodeN x))))
      chain5 = impEqTrans (ap1 (hitKdefN outKdefN) w)
                 (ap2 eqIndF (ap1 KcodeN x) (ap1 KcodeN x))
                 (eqInd (ap1 KcodeN x) (ap1 KcodeN x))
                 chain4 (impLift {P} eqIndF_eq_KxKx)
  in impEqTrans (ap1 (hitKdefN outKdefN) w)
       (eqInd (ap1 KcodeN x) (ap1 KcodeN x)) (ap1 s O)
       chain5 (impLift {P} eqInd_diag)

------------------------------------------------------------------------
-- imp_dNeg_from_hitKdefN -- Carneiro-lifted  dNeg_from_hitKdefN .

imp_dNeg_from_hitKdefN :
  (P : Formula) (out : Fun1) (w0 : Term) ->
  Deriv (imp P (eqF (ap1 (hitKdefN out) w0) (ap1 s O))) ->
  Deriv (imp P (eqF (ap1 thmT w0) (ap1 KcodeN (ap1 out w0))))
imp_dNeg_from_hitKdefN P out w0 h_imp =
  let A : Term
      A = ap1 thmT w0
      B : Term
      B = ap1 KcodeN (ap1 out w0)

      hk_eval_sym : Deriv (eqF (eqInd A B) (ap1 (hitKdefN out) w0))
      hk_eval_sym = ruleSym (hitKdefN_eval out w0)

      match_imp : Deriv (imp P (eqF (eqInd A B) (ap1 s O)))
      match_imp =
        impEqTrans (eqInd A B) (ap1 (hitKdefN out) w0) (ap1 s O)
          (impLift {P} hk_eval_sym) h_imp
  in imp_eqInd_sound P A B match_imp
