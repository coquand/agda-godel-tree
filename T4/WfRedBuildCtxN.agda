{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedBuildCtxN -- depth-3 and depth-4 versions of the wfRedSized BUILD
-- steps, needed by the Ad sub-dispatch glues (which thread htag, the left-tag
-- hypothesis/hypotheses, and PA together).  Same content as T4.WfRedBuildCtx but
-- in the deeper CtxKit contexts.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedBuildCtxN where

open import T4.Base

open import T4.DerCodeS using ( szDerRO ; szDerAd ; szDerRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfRedSized_RO ; wfRedSized_Ad ; wfRedSized_RS )

open import BRA3.Church  using ( sigma ; T33 )
open import T4.CtxKit
  using ( lift3 ; ap3c ; trans3c ; lift4 ; ap4c ; trans4c )

------------------------------------------------------------------------
-- Depth-3 helpers.

sigOY_ctx3 : (Ga Gb Gc : Formula) (Y : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (eqF Y O)))) ->
  Deriv (imp Ga (imp Gb (imp Gc (eqF (ap2 sigma O Y) O))))
sigOY_ctx3 Ga Gb Gc Y hY =
  trans3c (ap2 sigma O Y) (ap2 sigma O O) O
    (ap3c (lift3 Ga Gb Gc (ax_eqCongR sigma Y O O)) hY)
    (lift3 Ga Gb Gc (T33 O))

build_RO_ctx3 : (Ga Gb Gc : Formula) (X : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (eqF (ap1 wfRedSized X) O)))) ->
  Deriv (imp Ga (imp Gb (imp Gc (eqF (ap1 wfRedSized (szDerRO X)) O))))
build_RO_ctx3 Ga Gb Gc X h =
  trans3c (ap1 wfRedSized (szDerRO X)) (ap2 sigma O (ap1 wfRedSized X)) O
    (lift3 Ga Gb Gc (wfRedSized_RO X))
    (sigOY_ctx3 Ga Gb Gc (ap1 wfRedSized X) h)

------------------------------------------------------------------------
-- Depth-4 helpers.

sigBoth_ctx4 : (Ga Gb Gc Gd : Formula) (X Y : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF X O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF Y O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap2 sigma X Y) O)))))
sigBoth_ctx4 Ga Gb Gc Gd X Y hX hY =
  trans4c (ap2 sigma X Y) (ap2 sigma O Y) O
    (ap4c (lift4 Ga Gb Gc Gd (ax_eqCongL sigma X O Y)) hX)
    (trans4c (ap2 sigma O Y) (ap2 sigma O O) O
      (ap4c (lift4 Ga Gb Gc Gd (ax_eqCongR sigma Y O O)) hY)
      (lift4 Ga Gb Gc Gd (T33 O)))

sigOY_ctx4 : (Ga Gb Gc Gd : Formula) (Y : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF Y O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap2 sigma O Y) O)))))
sigOY_ctx4 Ga Gb Gc Gd Y hY =
  trans4c (ap2 sigma O Y) (ap2 sigma O O) O
    (ap4c (lift4 Ga Gb Gc Gd (ax_eqCongR sigma Y O O)) hY)
    (lift4 Ga Gb Gc Gd (T33 O))

build_Ad_ctx4 : (Ga Gb Gc Gd : Formula) (X1 X2 : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap1 wfRedSized X1) O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap1 wfRedSized X2) O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap1 wfRedSized (szDerAd X1 X2)) O)))))
build_Ad_ctx4 Ga Gb Gc Gd X1 X2 h1 h2 =
  let inner = sigBoth_ctx4 Ga Gb Gc Gd (ap1 wfRedSized X1) (ap1 wfRedSized X2) h1 h2
  in trans4c (ap1 wfRedSized (szDerAd X1 X2))
       (ap2 sigma O (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2))) O
       (lift4 Ga Gb Gc Gd (wfRedSized_Ad X1 X2))
       (sigOY_ctx4 Ga Gb Gc Gd (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) inner)

build_RS_ctx4 : (Ga Gb Gc Gd : Formula) (X1 X2 : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap1 wfRedSized X1) O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap1 wfRedSized X2) O))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF (ap1 wfRedSized (szDerRS X1 X2)) O)))))
build_RS_ctx4 Ga Gb Gc Gd X1 X2 h1 h2 =
  let inner = sigBoth_ctx4 Ga Gb Gc Gd (ap1 wfRedSized X1) (ap1 wfRedSized X2) h1 h2
  in trans4c (ap1 wfRedSized (szDerRS X1 X2))
       (ap2 sigma O (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2))) O
       (lift4 Ga Gb Gc Gd (wfRedSized_RS X1 X2))
       (sigOY_ctx4 Ga Gb Gc Gd (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) inner)
