{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriPresGlue -- the per-tag GLUE terms of the object tag dispatch, for the
-- four non-Ad tags.  Each glue is  imp htag (imp PA B)  where
--   sK   = s (var 0)                  (the code = the bound's successor)
--   PA   = (sigma bigK (wfRedSized sK) = O)   (combined PhiK + validity)
--   B    = (wfRedSized (triFSized sK) = O)
-- plugging directly into the X-branch of caseElim (htag = X hypothesis).
--
-- Recipe: PA=>PhiK (sigmaZeroL) + PA=>A (sigmaZeroR); child validity via
-- extractChild_X_H; child triF-validity via QofChild; build_X_ctx for the cell;
-- op-eq rewrite via triFSized_op_X_imp .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriPresGlue where

open import T4.Base

open import T4.DerCodeS using ( szDerZe ; szDerSu ; szDerAd ; dtag ; pArg ; pL ; pR )
open import T4.DerCode using ( dgZe ; dgSu ; dgRO ; dgRS )
open import T4.WfRedSized using ( wfRedSized ; wfRedSized_Ze )
open import T4.DerTriS using ( triFSized )

open import T4.WfRedExtract using ( argValueBound ; pLValueBound ; pRValueBound )
open import T4.WfRedExtractHtag
  using ( extractChild_Su_H ; extractChild_RO_H ; extractChild_RS_L_H ; extractChild_RS_R_H )
open import T4.WfRedBuildCtx using ( build_Su_ctx ; build_RO_ctx ; build_Ad_ctx )
open import T4.DerTriSOpaqueImp
  using ( triFSized_op_Ze_imp ; triFSized_op_Su_imp
        ; triFSized_op_RO_imp ; triFSized_op_RS_imp )
open import T4.QCheck using ( qcheck )
open import T4.BoundedConj using ( bigC )
open import T4.QCheckProj using ( PhiK ; QofChild )

open import T4.DescSnd using ( posNeqO )
open import BRA3.Church      using ( sigma ; sub ; predecessor ; T_p_S_v0 )
open import BRA3.ChurchLeq   using ( leq ; T76 )
open import BRA3.ChurchT78   using ( T78 )
open import BRA3.RuleInst2   using ( ruleInst2 )
open import T4.SigmaZeroN    using ( sigmaZeroL ; sigmaZeroR )
open import BRA3.Contrapositive using ( compI ; liftP )
open import T4.CtxKit using ( lift2 ; ap2c ; trans2c )
open import T4.Thm12.ImpHelpers using ( impLift ; impCong1 )

------------------------------------------------------------------------
-- Shared definitions for the code  sK = s (var 0) .

sK : Term
sK = ap1 s (var 0)

bigK : Term
bigK = ap2 (bigC qcheck) O (var 0)

Aform : Formula                            -- validity of sK
Aform = eqF (ap1 wfRedSized sK) O

PA : Formula                               -- combined PhiK + validity
PA = eqF (ap2 sigma bigK (ap1 wfRedSized sK)) O

Bform : Formula                            -- the goal
Bform = eqF (ap1 wfRedSized (ap1 triFSized sK)) O

ne_sK : Deriv (neg (eqF sK O))
ne_sK = posNeqO sK (mp (ruleInst2 0 O 1 (var 0) refl T78) (ruleInst 0 (var 0) T76))

pa2a : Deriv (imp PA Aform)
pa2a = sigmaZeroR bigK (ap1 wfRedSized sK)

pa2phik : Deriv (imp PA PhiK)
pa2phik = sigmaZeroL bigK (ap1 wfRedSized sK)

-- rewrite a child bound  leq c (pred (s var0))  to  leq c (var 0) .
rebound : (c : Term) ->
  Deriv (leq c (ap1 predecessor sK)) -> Deriv (leq c (var 0))
rebound c d =
  ruleTrans (congR sub c (ruleSym (ruleInst 0 (var 0) T_p_S_v0))) d

------------------------------------------------------------------------
-- triF-validity of a child  c  under [htag, PA], given its extractChild and
-- its (bare) leq bound: imp htag (imp PA (wfRedSized (triFSized c) = O)) .

triFvalidChild : (Hf : Formula) (c : Term) ->
  Deriv (imp Hf (imp Aform (eqF (ap1 wfRedSized c) O))) ->
  Deriv (leq c (var 0)) ->
  Deriv (imp Hf (imp PA (eqF (ap1 wfRedSized (ap1 triFSized c)) O)))
triFvalidChild Hf c extr leqc =
  let CV : Formula
      CV = eqF (ap1 wfRedSized c) O
      TV : Formula
      TV = eqF (ap1 wfRedSized (ap1 triFSized c)) O
      f : Deriv (imp Hf (imp PA (imp Aform CV)))
      f = compI extr (axK (imp Aform CV) PA)
      x : Deriv (imp Hf (imp PA Aform))
      x = liftP Hf pa2a
      childvalid : Deriv (imp Hf (imp PA CV))
      childvalid = ap2c f x
      q_ctx : Deriv (imp Hf (imp PA (imp CV TV)))
      q_ctx = liftP Hf (compI pa2phik (QofChild c leqc))
  in ap2c q_ctx childvalid

------------------------------------------------------------------------
-- Ze :  triFSized sK = szDerZe ,  wfRedSized szDerZe = O .

glue_Ze : Deriv (imp (eqF (dtag sK) dgZe) (imp PA Bform))
glue_Ze =
  let H : Formula
      H = eqF (dtag sK) dgZe
      Z1 : Formula
      Z1 = eqF (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized szDerZe)
      opRw : Deriv (imp H Z1)
      opRw = impCong1 wfRedSized (ap1 triFSized sK) szDerZe
               (triFSized_op_Ze_imp sK ne_sK)
      opRw_ctx : Deriv (imp H (imp PA Z1))
      opRw_ctx = compI opRw (axK Z1 PA)
      zeVal_ctx : Deriv (imp H (imp PA (eqF (ap1 wfRedSized szDerZe) O)))
      zeVal_ctx = lift2 H PA wfRedSized_Ze
  in trans2c (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized szDerZe) O
       opRw_ctx zeVal_ctx

------------------------------------------------------------------------
-- RO :  triFSized sK = triFSized (pArg sK) .

glue_RO : Deriv (imp (eqF (dtag sK) dgRO) (imp PA Bform))
glue_RO =
  let H : Formula
      H = eqF (dtag sK) dgRO
      child : Term
      child = pArg sK
      tv : Deriv (imp H (imp PA (eqF (ap1 wfRedSized (ap1 triFSized child)) O)))
      tv = triFvalidChild H child (extractChild_RO_H sK ne_sK)
             (rebound child (argValueBound sK ne_sK))
      Z1 : Formula
      Z1 = eqF (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized (ap1 triFSized child))
      opRw : Deriv (imp H Z1)
      opRw = impCong1 wfRedSized (ap1 triFSized sK) (ap1 triFSized child)
               (triFSized_op_RO_imp sK ne_sK)
      opRw_ctx : Deriv (imp H (imp PA Z1))
      opRw_ctx = compI opRw (axK Z1 PA)
  in trans2c (ap1 wfRedSized (ap1 triFSized sK))
             (ap1 wfRedSized (ap1 triFSized child)) O opRw_ctx tv

------------------------------------------------------------------------
-- Su :  triFSized sK = szDerSu (triFSized (pArg sK)) .

glue_Su : Deriv (imp (eqF (dtag sK) dgSu) (imp PA Bform))
glue_Su =
  let H : Formula
      H = eqF (dtag sK) dgSu
      child : Term
      child = pArg sK
      tv : Deriv (imp H (imp PA (eqF (ap1 wfRedSized (ap1 triFSized child)) O)))
      tv = triFvalidChild H child (extractChild_Su_H sK ne_sK)
             (rebound child (argValueBound sK ne_sK))
      bld : Deriv (imp H (imp PA (eqF (ap1 wfRedSized (szDerSu (ap1 triFSized child))) O)))
      bld = build_Su_ctx H PA (ap1 triFSized child) tv
      Z1 : Formula
      Z1 = eqF (ap1 wfRedSized (ap1 triFSized sK))
               (ap1 wfRedSized (szDerSu (ap1 triFSized child)))
      opRw : Deriv (imp H Z1)
      opRw = impCong1 wfRedSized (ap1 triFSized sK) (szDerSu (ap1 triFSized child))
               (triFSized_op_Su_imp sK ne_sK)
      opRw_ctx : Deriv (imp H (imp PA Z1))
      opRw_ctx = compI opRw (axK Z1 PA)
  in trans2c (ap1 wfRedSized (ap1 triFSized sK))
             (ap1 wfRedSized (szDerSu (ap1 triFSized child))) O opRw_ctx bld

------------------------------------------------------------------------
-- RS :  triFSized sK = szDerSu (szDerAd (triFSized (pL sK)) (triFSized (pR sK))) .

glue_RS : Deriv (imp (eqF (dtag sK) dgRS) (imp PA Bform))
glue_RS =
  let H : Formula
      H = eqF (dtag sK) dgRS
      cl : Term
      cl = ap1 triFSized (pL sK)
      cr : Term
      cr = ap1 triFSized (pR sK)
      tvL : Deriv (imp H (imp PA (eqF (ap1 wfRedSized cl) O)))
      tvL = triFvalidChild H (pL sK) (extractChild_RS_L_H sK ne_sK)
              (rebound (pL sK) (pLValueBound sK ne_sK))
      tvR : Deriv (imp H (imp PA (eqF (ap1 wfRedSized cr) O)))
      tvR = triFvalidChild H (pR sK) (extractChild_RS_R_H sK ne_sK)
              (rebound (pR sK) (pRValueBound sK ne_sK))
      bldAd : Deriv (imp H (imp PA (eqF (ap1 wfRedSized (szDerAd cl cr)) O)))
      bldAd = build_Ad_ctx H PA cl cr tvL tvR
      bld : Deriv (imp H (imp PA (eqF (ap1 wfRedSized (szDerSu (szDerAd cl cr))) O)))
      bld = build_Su_ctx H PA (szDerAd cl cr) bldAd
      Z1 : Formula
      Z1 = eqF (ap1 wfRedSized (ap1 triFSized sK))
               (ap1 wfRedSized (szDerSu (szDerAd cl cr)))
      opRw : Deriv (imp H Z1)
      opRw = impCong1 wfRedSized (ap1 triFSized sK) (szDerSu (szDerAd cl cr))
               (triFSized_op_RS_imp sK ne_sK)
      opRw_ctx : Deriv (imp H (imp PA Z1))
      opRw_ctx = compI opRw (axK Z1 PA)
  in trans2c (ap1 wfRedSized (ap1 triFSized sK))
             (ap1 wfRedSized (szDerSu (szDerAd cl cr))) O opRw_ctx bld
