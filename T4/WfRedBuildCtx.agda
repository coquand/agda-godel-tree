{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedBuildCtx -- depth-2 (context [Ga,Gb]) versions of the wfRedSized BUILD
-- steps: from child validity under the context, rebuild the constructor's
-- validity.  Needed because the per-tag dispatch threads BOTH htag and PA
-- (T4.WfRedBuildImp is single-phi).  Immediate from the wfRedSized defining
-- equations + ax_eqCongL/R sigma + T33, via the CtxKit depth-2 transitivity.
--
-- Also exports  sigBoth_ctx  (depth-2 sigma-of-two-zeros), reused to assemble PA.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedBuildCtx where

open import T4.Base

open import T4.DerCodeS using ( szDerSu ; szDerRO ; szDerAd ; szDerRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfRedSized_Su ; wfRedSized_RO ; wfRedSized_Ad ; wfRedSized_RS )

open import BRA3.Church  using ( sigma ; T33 )
open import T4.CtxKit    using ( lift2 ; ap2c ; trans2c )

------------------------------------------------------------------------
-- sigma X Y = O  under [Ga,Gb], from  X = O  and  Y = O  under [Ga,Gb].

sigBoth_ctx : (Ga Gb : Formula) (X Y : Term) ->
  Deriv (imp Ga (imp Gb (eqF X O))) ->
  Deriv (imp Ga (imp Gb (eqF Y O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap2 sigma X Y) O)))
sigBoth_ctx Ga Gb X Y hX hY =
  let r1 : Deriv (imp Ga (imp Gb (eqF (ap2 sigma X Y) (ap2 sigma O Y))))
      r1 = ap2c (lift2 Ga Gb (ax_eqCongL sigma X O Y)) hX
      r2 : Deriv (imp Ga (imp Gb (eqF (ap2 sigma O Y) (ap2 sigma O O))))
      r2 = ap2c (lift2 Ga Gb (ax_eqCongR sigma Y O O)) hY
      r3 : Deriv (imp Ga (imp Gb (eqF (ap2 sigma O O) O)))
      r3 = lift2 Ga Gb (T33 O)
  in trans2c (ap2 sigma X Y) (ap2 sigma O Y) O r1
       (trans2c (ap2 sigma O Y) (ap2 sigma O O) O r2 r3)

------------------------------------------------------------------------
-- sigma O Y = O  under [Ga,Gb], from  Y = O .

private
  sigOY_ctx : (Ga Gb : Formula) (Y : Term) ->
    Deriv (imp Ga (imp Gb (eqF Y O))) ->
    Deriv (imp Ga (imp Gb (eqF (ap2 sigma O Y) O)))
  sigOY_ctx Ga Gb Y hY =
    let r2 : Deriv (imp Ga (imp Gb (eqF (ap2 sigma O Y) (ap2 sigma O O))))
        r2 = ap2c (lift2 Ga Gb (ax_eqCongR sigma Y O O)) hY
        r3 : Deriv (imp Ga (imp Gb (eqF (ap2 sigma O O) O)))
        r3 = lift2 Ga Gb (T33 O)
    in trans2c (ap2 sigma O Y) (ap2 sigma O O) O r2 r3

------------------------------------------------------------------------
-- The four build steps.

build_Su_ctx : (Ga Gb : Formula) (X : Term) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized X) O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized (szDerSu X)) O)))
build_Su_ctx Ga Gb X h =
  trans2c (ap1 wfRedSized (szDerSu X)) (ap2 sigma O (ap1 wfRedSized X)) O
    (lift2 Ga Gb (wfRedSized_Su X))
    (sigOY_ctx Ga Gb (ap1 wfRedSized X) h)

build_RO_ctx : (Ga Gb : Formula) (X : Term) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized X) O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized (szDerRO X)) O)))
build_RO_ctx Ga Gb X h =
  trans2c (ap1 wfRedSized (szDerRO X)) (ap2 sigma O (ap1 wfRedSized X)) O
    (lift2 Ga Gb (wfRedSized_RO X))
    (sigOY_ctx Ga Gb (ap1 wfRedSized X) h)

build_Ad_ctx : (Ga Gb : Formula) (X1 X2 : Term) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized X1) O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized X2) O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized (szDerAd X1 X2)) O)))
build_Ad_ctx Ga Gb X1 X2 h1 h2 =
  let inner : Deriv (imp Ga (imp Gb
                (eqF (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) O)))
      inner = sigBoth_ctx Ga Gb (ap1 wfRedSized X1) (ap1 wfRedSized X2) h1 h2
  in trans2c (ap1 wfRedSized (szDerAd X1 X2))
       (ap2 sigma O (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2))) O
       (lift2 Ga Gb (wfRedSized_Ad X1 X2))
       (sigOY_ctx Ga Gb (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) inner)

build_RS_ctx : (Ga Gb : Formula) (X1 X2 : Term) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized X1) O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized X2) O))) ->
  Deriv (imp Ga (imp Gb (eqF (ap1 wfRedSized (szDerRS X1 X2)) O)))
build_RS_ctx Ga Gb X1 X2 h1 h2 =
  let inner : Deriv (imp Ga (imp Gb
                (eqF (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) O)))
      inner = sigBoth_ctx Ga Gb (ap1 wfRedSized X1) (ap1 wfRedSized X2) h1 h2
  in trans2c (ap1 wfRedSized (szDerRS X1 X2))
       (ap2 sigma O (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2))) O
       (lift2 Ga Gb (wfRedSized_RS X1 X2))
       (sigOY_ctx Ga Gb (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) inner)
