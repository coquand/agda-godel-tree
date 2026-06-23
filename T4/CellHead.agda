{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CellHead -- the reusable core of OBJECT head-stability (target-(2) step 3,
-- the all-object BRA |- Con(T0)): every source step-body cell rebuilds a
-- SUCCESSOR-tagged node, so  hd (cellX pkg) = natCode 1 or 2  -- never  tagZe = O.
--
-- T4.ParEnds' cells are all  C pi (constN k) (...)  with  k in {1,2}:
--   cellSu = C pi (constN 1) (...)        -- su#  head = natCode 1
--   cellAd = C pi (constN 2) (...)        -- ad#  head = natCode 2
--   cellRO = C pi (constN 2) (...)        -- ad#  head = natCode 2
--   cellRS = C pi (constN 2) (...)        -- ad#  head = natCode 2
-- so  Fst (cellX pkg) = ap1 (constN k) pkg = natCode k  (ax_C pi + axFst +
-- constN_eq), independent of the recursive payload.  Since  stepBody_src pkg  is
-- always one of these cells (for d != O), this is exactly why  hd (src d) = tagZe
-- forces  d = O  (the base) -- the OBJECT analog of "only cZe has a ze-head", with
-- NO validity hypothesis and NO recursion (only the head is touched).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CellHead where

open import T4.Base

open import T4.ParEnds  using ( cellSu ; cellAd ; cellRO ; cellRS ; lcIdx ; rcIdx ; ze#F )
open import T4.LenR     using ( get_rc )
open import T4.FoldRec  using ( lookupAt )

open import BRA3.Church   using ( pi )
open import BRA3.Dispatch using ( constN ; constN_eq )

------------------------------------------------------------------------
-- The four cell heads (Fst of the rebuilt node = the constN tag = a successor).

hd_cellSu : (pkg : Term) ->
  Deriv (eqF (ap1 Fst (ap1 cellSu pkg)) (natCode 1))
hd_cellSu pkg =
  ruleTrans (cong1 Fst (ax_C pi (constN 1) (lookupAt get_rc) pkg))
    (ruleTrans (axFst (ap1 (constN 1) pkg) (ap1 (lookupAt get_rc) pkg))
               (constN_eq 1 pkg))

hd_cellAd : (pkg : Term) ->
  Deriv (eqF (ap1 Fst (ap1 cellAd pkg)) (natCode 2))
hd_cellAd pkg =
  ruleTrans (cong1 Fst (ax_C pi (constN 2)
                          (C pi (lookupAt lcIdx) (lookupAt rcIdx)) pkg))
    (ruleTrans (axFst (ap1 (constN 2) pkg)
                      (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) pkg))
               (constN_eq 2 pkg))

hd_cellRO : (pkg : Term) ->
  Deriv (eqF (ap1 Fst (ap1 cellRO pkg)) (natCode 2))
hd_cellRO pkg =
  ruleTrans (cong1 Fst (ax_C pi (constN 2)
                          (C pi ze#F (lookupAt get_rc)) pkg))
    (ruleTrans (axFst (ap1 (constN 2) pkg)
                      (ap1 (C pi ze#F (lookupAt get_rc)) pkg))
               (constN_eq 2 pkg))

hd_cellRS : (pkg : Term) ->
  Deriv (eqF (ap1 Fst (ap1 cellRS pkg)) (natCode 2))
hd_cellRS pkg =
  ruleTrans (cong1 Fst (ax_C pi (constN 2)
                          (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) pkg))
    (ruleTrans (axFst (ap1 (constN 2) pkg)
                      (ap1 (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) pkg))
               (constN_eq 2 pkg))
