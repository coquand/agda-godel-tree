{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ObjCert -- the STRICT, tag-pinning object validity primitive for the
-- OBJECT route (target-(2) BRA |- Con(T0)).  External-LLM-confirmed principle:
-- "object validity must be STRONGER than meta validity", because the object
-- proof must extract constructor information from OPAQUE codes -- the weak
-- T4.ParEnds.isCert (junk tags >=5 pass as cRS, tag NOT pinned) cannot drive an
-- opaque dispatch.
--
-- This file delivers the strict TOP-TAG check (enough for object head-stability
-- / objJoinClash; full recursive ObjCert for the CR phase extends it):
--
--   objTagOk d  =  pi (sub (natCode 1) (Fst d)) (sub (Fst d) (natCode 4))
--               =  O   iff   1 <= Fst d <= 4   (a valid constructor tag)
--
-- since  sub a b = O  iff  a <= b  (leq is  eqF (sub a b) O).  With this,
-- the opaque dispatch in  certHeadZe_obj  works: classical `byCases` on
-- (Fst d = natCode k) for k=1..4 (no natEqF evaluation needed on the opaque
-- head -- the branch HYPOTHESIS supplies the tag equation), and the
-- none-of-1..4 branch is closed by  objTagOk d = O  (1<=Fst d<=4 exhausts
-- {1,2,3,4}).  Each tag branch unfolds its cell and applies T4.CellHead.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ObjCert where

open import T4.Base

open import BRA3.Church       using ( pi ; sub )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.ChurchSubSucc using ( T_sub_O )
open import BRA3.Dispatch     using ( constN ; constN_eq )
open import T4.LeqPiLeft      using ( leq_pi_left )
open import T4.LeqMono        using ( leq_pi_right )

------------------------------------------------------------------------
-- The strict top-tag validity check and its application law.

objTagOk : Fun1
objTagOk = C pi (C sub (constN 1) Fst) (C sub Fst (constN 4))

objTagOk_app : (d : Term) ->
  Deriv (eqF (ap1 objTagOk d)
             (ap2 pi (ap2 sub (natCode 1) (ap1 Fst d))
                     (ap2 sub (ap1 Fst d) (natCode 4))))
objTagOk_app d =
  let loEq : Deriv (eqF (ap1 (C sub (constN 1) Fst) d)
                        (ap2 sub (natCode 1) (ap1 Fst d)))
      loEq = ruleTrans (ax_C sub (constN 1) Fst d)
                       (congL sub (ap1 Fst d) (constN_eq 1 d))
      hiEq : Deriv (eqF (ap1 (C sub Fst (constN 4)) d)
                        (ap2 sub (ap1 Fst d) (natCode 4)))
      hiEq = ruleTrans (ax_C sub Fst (constN 4) d)
                       (congR sub (ap1 Fst d) (constN_eq 4 d))
  in ruleTrans (ax_C pi (C sub (constN 1) Fst) (C sub Fst (constN 4)) d)
       (ruleTrans (congL pi (ap1 (C sub Fst (constN 4)) d) loEq)
                  (congR pi (ap2 sub (natCode 1) (ap1 Fst d)) hiEq))

------------------------------------------------------------------------
-- Range extraction:  objTagOk d = O  gives  1 <= Fst d  and  Fst d <= 4
-- (the bounded-nat facts the opaque tag dispatch needs).

objTagOk_lo : (d : Term) -> Deriv (eqF (ap1 objTagOk d) O) ->
  Deriv (leq (natCode 1) (ap1 Fst d))
objTagOk_lo d hyp =
  let lo : Term
      lo = ap2 sub (natCode 1) (ap1 Fst d)
      hi : Term
      hi = ap2 sub (ap1 Fst d) (natCode 4)
      piO : Deriv (eqF (ap2 pi lo hi) O)
      piO = ruleTrans (ruleSym (objTagOk_app d)) hyp
  in ruleTrans (ruleSym (T_sub_O lo))
       (ruleTrans (ruleSym (congR sub lo piO)) (leq_pi_left lo hi))

objTagOk_hi : (d : Term) -> Deriv (eqF (ap1 objTagOk d) O) ->
  Deriv (leq (ap1 Fst d) (natCode 4))
objTagOk_hi d hyp =
  let lo : Term
      lo = ap2 sub (natCode 1) (ap1 Fst d)
      hi : Term
      hi = ap2 sub (ap1 Fst d) (natCode 4)
      piO : Deriv (eqF (ap2 pi lo hi) O)
      piO = ruleTrans (ruleSym (objTagOk_app d)) hyp
  in ruleTrans (ruleSym (T_sub_O hi))
       (ruleTrans (ruleSym (congR sub hi piO)) (leq_pi_right lo hi))
