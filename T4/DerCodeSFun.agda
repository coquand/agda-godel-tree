{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerCodeSFun -- the size-prefixed derivation constructors of T4.DerCodeS
-- packaged as OBJECT Fun1 / Fun2 CODES, with their build equations.  These are
-- the "triangle output constructors" the triFSized cells apply to folded child
-- values; the size field is recomputed automatically (= s of the children's
-- Fst), so no separate size arithmetic is needed in the cells.
--
--   ap1 szDerSuF d      = szDerSu d
--   ap1 szDerROF d      = szDerRO d
--   ap2 szDerAdF d1 d2  = szDerAd d1 d2
--   ap2 szDerRSF d1 d2  = szDerRS d1 d2
--
-- Built from C / Fan / Lift1 / Lift2 / Post / compose1U + the tag numerals.
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerCodeSFun where

open import T4.Base

open import T4.DerCodeS using ( szDerSu ; szDerRO ; szDerAd ; szDerRS )

open import BRA3.Church      using ( pi ; sigma )
open import BRA3.PairAlgebra using ( axPost )

------------------------------------------------------------------------
-- SECTION 1.  The constructor codes.

-- size field of a UNARY output:  s (Fst d) .
sizeUF : Fun1
sizeUF = compose1U s Fst

-- size field of a BINARY output:  s (sigma (Fst d1) (Fst d2)) .
sizeBF : Fun2
sizeBF = Post s (Fan (Lift1 Fst) (Lift2 Fst) sigma)

szDerSuF : Fun1
szDerSuF = C pi sizeUF (C pi (constN 1) I)

szDerROF : Fun1
szDerROF = C pi sizeUF (C pi (constN 3) I)

szDerAdF : Fun2
szDerAdF = Fan sizeBF (Fan (Lift1 (constN 2)) pi pi) pi

szDerRSF : Fun2
szDerRSF = Fan sizeBF (Fan (Lift1 (constN 4)) pi pi) pi

------------------------------------------------------------------------
-- SECTION 2.  Shared sub-equations.

-- the binary size field reduces to  s (sigma (Fst d1) (Fst d2)) .
sizeBF_eq : (d1 d2 : Term) ->
  Deriv (eqF (ap2 sizeBF d1 d2) (ap1 s (ap2 sigma (ap1 Fst d1) (ap1 Fst d2))))
sizeBF_eq d1 d2 =
  ruleTrans (axPost s (Fan (Lift1 Fst) (Lift2 Fst) sigma) d1 d2)
    (cong1 s
      (ruleTrans (axFan (Lift1 Fst) (Lift2 Fst) sigma d1 d2)
        (ruleTrans (congL sigma (ap2 (Lift2 Fst) d1 d2) (axLift Fst d1 d2))
                   (congR sigma (ap1 Fst d1) (axLift2 Fst d1 d2)))))

-- a UNARY payload  pi (natCode k) d .
payUF_eq : (k : Nat) (d : Term) ->
  Deriv (eqF (ap1 (C pi (constN k) I) d) (ap2 pi (natCode k) d))
payUF_eq k d =
  ruleTrans (ax_C pi (constN k) I d)
    (ruleTrans (congL pi (ap1 I d) (constN_eq k d))
               (congR pi (natCode k) (axI d)))

-- a BINARY payload  pi (natCode k) (pi d1 d2) .
payBF_eq : (k : Nat) (d1 d2 : Term) ->
  Deriv (eqF (ap2 (Fan (Lift1 (constN k)) pi pi) d1 d2)
             (ap2 pi (natCode k) (ap2 pi d1 d2)))
payBF_eq k d1 d2 =
  ruleTrans (axFan (Lift1 (constN k)) pi pi d1 d2)
    (congL pi (ap2 pi d1 d2)
      (ruleTrans (axLift (constN k) d1 d2) (constN_eq k d1)))

------------------------------------------------------------------------
-- SECTION 3.  The four build equations.

szDerSuF_eq : (d : Term) -> Deriv (eqF (ap1 szDerSuF d) (szDerSu d))
szDerSuF_eq d =
  ruleTrans (ax_C pi sizeUF (C pi (constN 1) I) d)
    (ruleTrans (congL pi (ap1 (C pi (constN 1) I) d) (axComp s Fst d))
               (congR pi (ap1 s (ap1 Fst d)) (payUF_eq 1 d)))

szDerROF_eq : (d : Term) -> Deriv (eqF (ap1 szDerROF d) (szDerRO d))
szDerROF_eq d =
  ruleTrans (ax_C pi sizeUF (C pi (constN 3) I) d)
    (ruleTrans (congL pi (ap1 (C pi (constN 3) I) d) (axComp s Fst d))
               (congR pi (ap1 s (ap1 Fst d)) (payUF_eq 3 d)))

szDerAdF_eq : (d1 d2 : Term) -> Deriv (eqF (ap2 szDerAdF d1 d2) (szDerAd d1 d2))
szDerAdF_eq d1 d2 =
  ruleTrans (axFan sizeBF (Fan (Lift1 (constN 2)) pi pi) pi d1 d2)
    (ruleTrans (congL pi (ap2 (Fan (Lift1 (constN 2)) pi pi) d1 d2) (sizeBF_eq d1 d2))
               (congR pi (ap1 s (ap2 sigma (ap1 Fst d1) (ap1 Fst d2))) (payBF_eq 2 d1 d2)))

szDerRSF_eq : (d1 d2 : Term) -> Deriv (eqF (ap2 szDerRSF d1 d2) (szDerRS d1 d2))
szDerRSF_eq d1 d2 =
  ruleTrans (axFan sizeBF (Fan (Lift1 (constN 4)) pi pi) pi d1 d2)
    (ruleTrans (congL pi (ap2 (Fan (Lift1 (constN 4)) pi pi) d1 d2) (sizeBF_eq d1 d2))
               (congR pi (ap1 s (ap2 sigma (ap1 Fst d1) (ap1 Fst d2))) (payBF_eq 4 d1 d2)))
