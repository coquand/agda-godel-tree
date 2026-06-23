{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepDispatch -- the validity-free DISPATCH core for object head-stability
-- (the last arrow,  objJoinClash ).  The src step-body cascade
--
--   stepBody_src = condFork (pi cellSu inner1) test1
--   inner1       = condFork (pi cellAd inner2) test2
--   inner2       = condFork (pi cellRO cellRS) test3
--
-- is unfolded ONE level at a time, driven only by whether the test is O:
--   test_k pkg != O  -> the FIRST cell fires   (via succForm + condFork_true_nc)
--   test_k pkg  = O  -> the REST fires          (via condFork_false)
-- NO validity, NO num_eq_code, NO Closed (condFork_true_nc).  `byCases` on
-- (test_k pkg = O) supplies the two hypotheses; each leaf is then a cell whose
-- head is a successor (T4.CellHead), so  hd (src d) = tagZe  is impossible for
-- d != O -- the object "only cZe is ze-headed".
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.StepDispatch where

open import T4.Base

open import T4.ParEnds using
  ( stepBody_src ; inner1 ; inner2
  ; cellSu ; cellAd ; cellRO ; cellRS ; test1 ; test2 ; test3 )
open import T4.SizedPres using ( succForm )

open import BRA3.Church   using ( predecessor ; pi )
open import BRA3.Dispatch using ( condFork ; condFork_true_nc ; condFork_false )

------------------------------------------------------------------------
-- A generic one-level unfold, instantiated three times.
-- (fires : test != O -> first cell ;  rest : test = O -> rest)

private
  firesTo : (body fstCell sndCell test : Fun1) (pkg : Term) ->
            Deriv (eqF (ap1 body pkg)
                       (ap2 condFork (ap1 (C pi fstCell sndCell) pkg) (ap1 test pkg))) ->
            Deriv (neg (eqF (ap1 test pkg) O)) ->
            Deriv (eqF (ap1 body pkg) (ap1 fstCell pkg))
  firesTo body fstCell sndCell test pkg unf ne =
    let z : Term
        z = ap1 (C pi fstCell sndCell) pkg
        e2 : Deriv (eqF (ap2 condFork z (ap1 test pkg))
                        (ap2 condFork z (ap1 s (ap1 predecessor (ap1 test pkg)))))
        e2 = congR condFork z (ruleSym (succForm (ap1 test pkg) ne))
        e3 : Deriv (eqF (ap2 condFork z (ap1 s (ap1 predecessor (ap1 test pkg))))
                        (ap1 Fst z))
        e3 = condFork_true_nc z (ap1 predecessor (ap1 test pkg))
        e4 : Deriv (eqF (ap1 Fst z) (ap1 fstCell pkg))
        e4 = ruleTrans (cong1 Fst (ax_C pi fstCell sndCell pkg))
                       (axFst (ap1 fstCell pkg) (ap1 sndCell pkg))
    in ruleTrans unf (ruleTrans e2 (ruleTrans e3 e4))

  restTo : (body fstCell sndCell test : Fun1) (pkg : Term) ->
           Deriv (eqF (ap1 body pkg)
                      (ap2 condFork (ap1 (C pi fstCell sndCell) pkg) (ap1 test pkg))) ->
           Deriv (eqF (ap1 test pkg) O) ->
           Deriv (eqF (ap1 body pkg) (ap1 sndCell pkg))
  restTo body fstCell sndCell test pkg unf eq =
    let z : Term
        z = ap1 (C pi fstCell sndCell) pkg
        e2 : Deriv (eqF (ap2 condFork z (ap1 test pkg)) (ap2 condFork z O))
        e2 = congR condFork z eq
        e3 : Deriv (eqF (ap2 condFork z O) (ap1 Snd z))
        e3 = condFork_false z
        e4 : Deriv (eqF (ap1 Snd z) (ap1 sndCell pkg))
        e4 = ruleTrans (cong1 Snd (ax_C pi fstCell sndCell pkg))
                       (axSnd (ap1 fstCell pkg) (ap1 sndCell pkg))
    in ruleTrans unf (ruleTrans e2 (ruleTrans e3 e4))

------------------------------------------------------------------------
-- Level 1:  stepBody_src .

to_cellSu : (pkg : Term) -> Deriv (neg (eqF (ap1 test1 pkg) O)) ->
  Deriv (eqF (ap1 stepBody_src pkg) (ap1 cellSu pkg))
to_cellSu pkg ne =
  firesTo stepBody_src cellSu inner1 test1 pkg
    (ax_C condFork (C pi cellSu inner1) test1 pkg) ne

to_inner1 : (pkg : Term) -> Deriv (eqF (ap1 test1 pkg) O) ->
  Deriv (eqF (ap1 stepBody_src pkg) (ap1 inner1 pkg))
to_inner1 pkg eq =
  restTo stepBody_src cellSu inner1 test1 pkg
    (ax_C condFork (C pi cellSu inner1) test1 pkg) eq

------------------------------------------------------------------------
-- Level 2:  inner1 .

to_cellAd : (pkg : Term) -> Deriv (neg (eqF (ap1 test2 pkg) O)) ->
  Deriv (eqF (ap1 inner1 pkg) (ap1 cellAd pkg))
to_cellAd pkg ne =
  firesTo inner1 cellAd inner2 test2 pkg
    (ax_C condFork (C pi cellAd inner2) test2 pkg) ne

to_inner2 : (pkg : Term) -> Deriv (eqF (ap1 test2 pkg) O) ->
  Deriv (eqF (ap1 inner1 pkg) (ap1 inner2 pkg))
to_inner2 pkg eq =
  restTo inner1 cellAd inner2 test2 pkg
    (ax_C condFork (C pi cellAd inner2) test2 pkg) eq

------------------------------------------------------------------------
-- Level 3:  inner2 .

to_cellRO : (pkg : Term) -> Deriv (neg (eqF (ap1 test3 pkg) O)) ->
  Deriv (eqF (ap1 inner2 pkg) (ap1 cellRO pkg))
to_cellRO pkg ne =
  firesTo inner2 cellRO cellRS test3 pkg
    (ax_C condFork (C pi cellRO cellRS) test3 pkg) ne

to_cellRS : (pkg : Term) -> Deriv (eqF (ap1 test3 pkg) O) ->
  Deriv (eqF (ap1 inner2 pkg) (ap1 cellRS pkg))
to_cellRS pkg eq =
  restTo inner2 cellRO cellRS test3 pkg
    (ax_C condFork (C pi cellRO cellRS) test3 pkg) eq
