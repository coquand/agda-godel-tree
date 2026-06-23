{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.OpaqueTag -- BRICK 2 of the opaque local diamond: the TAG-DISPATCH layer.
--
-- After T4.TriFUnfold exposes a fold at an opaque nonzero code  d  as
--   stepBody (pi (pred d) STATE)
-- the step body dispatches on the cert tag via the natEqF cascade
-- test1 / test2 / test3  (= "is  get_tag  equal to  1 / 2 / 3 ?").  The
-- structure-carrying proofs (T4.ParEnds, module DispatchIC) read the tag from
-- a BUILT node code  Pair (s A) child  via  np_head : get_tag input_pkg = s A .
--
-- For an OPAQUE  d  the same tag is recovered with NO surjective pairing,
-- fold-independently (it does not look at STATE):
--
--   get_tag (pi (pred d) Y)
--     = Fst (get_newK (pi (pred d) Y))      (get_tag = compose1U Fst get_newK)
--     = Fst (s (pred d))                    (get_newK_at_pi)
--     = Fst d                               (succForm: s (pred d) = d, d != O)
--
-- so the cascade tests reduce to comparing the ORIGINAL head tag  Fst d
-- against the constant  k :
--
--   test_k (pi (pred d) Y) = natEqF (Fst d) (natCode k) .
--
-- Combined with  byCases  on  (Fst d = natCode k)  + natEq_eq / natEqF_at_neq,
-- this drives the opaque per-constructor dispatch.  No holes, no postulates,
-- no termination warnings; --safe --without-K --exact-split.

module T4.OpaqueTag where

open import T4.Base

open import T4.ProgParse using ( get_tag )
open import T4.FoldRec   using ( get_newK ; get_newK_at_pi )
open import T4.SizedPres using ( succForm )
open import T4.ParEnds   using ( test1 ; test2 ; test3 )
open import T4.LenR      using ( get_rc )

open import BRA3.Church       using ( predecessor ; pi )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.Dispatch     using ( constN ; constN_eq )
open import BRA3.SubT.NatEq    using ( natEqF )

------------------------------------------------------------------------
-- SECTION 1.  The opaque tag linchpin:  get_tag (pi (pred d) Y) = Fst d .
--   Fold-independent: Y (the recovery STATE) is arbitrary.

get_tag_op : (d Y : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 get_tag (ap2 pi (ap1 predecessor d) Y)) (ap1 Fst d))
get_tag_op d Y ne =
  ruleTrans (compose1U_eq Fst get_newK (ap2 pi (ap1 predecessor d) Y))
    (ruleTrans (cong1 Fst (get_newK_at_pi (ap1 predecessor d) Y))
               (cong1 Fst (succForm d ne)))

-- The right-child index reads  Snd d  from the opaque package (same
-- get_newK_at_pi + succForm pattern; get_rc = compose1U Snd get_newK).  This
-- is the  idx_eq  that T4.OpaqueLookup.lookup_op consumes for the unary
-- (cSu / cRO) child and -- composed with Fst/Snd of the payload -- the binary
-- (cAd / cRS) children.

get_rc_op : (d Y : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 get_rc (ap2 pi (ap1 predecessor d) Y)) (ap1 Snd d))
get_rc_op d Y ne =
  ruleTrans (compose1U_eq Snd get_newK (ap2 pi (ap1 predecessor d) Y))
    (ruleTrans (cong1 Snd (get_newK_at_pi (ap1 predecessor d) Y))
               (cong1 Snd (succForm d ne)))

------------------------------------------------------------------------
-- SECTION 2.  The opaque cascade decisions:  test_k pkg = natEqF (Fst d) k .
--   (Mirror of ParEnds.DispatchIC.test_k_val for the opaque package.)

test1_op : (d Y : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 test1 (ap2 pi (ap1 predecessor d) Y))
             (ap2 natEqF (ap1 Fst d) (natCode 1)))
test1_op d Y ne =
  let pkg : Term
      pkg = ap2 pi (ap1 predecessor d) Y
  in ruleTrans (ax_C natEqF get_tag (constN 1) pkg)
       (ruleTrans (congL natEqF (ap1 (constN 1) pkg) (get_tag_op d Y ne))
                  (congR natEqF (ap1 Fst d) (constN_eq 1 pkg)))

test2_op : (d Y : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 test2 (ap2 pi (ap1 predecessor d) Y))
             (ap2 natEqF (ap1 Fst d) (natCode 2)))
test2_op d Y ne =
  let pkg : Term
      pkg = ap2 pi (ap1 predecessor d) Y
  in ruleTrans (ax_C natEqF get_tag (constN 2) pkg)
       (ruleTrans (congL natEqF (ap1 (constN 2) pkg) (get_tag_op d Y ne))
                  (congR natEqF (ap1 Fst d) (constN_eq 2 pkg)))

test3_op : (d Y : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 test3 (ap2 pi (ap1 predecessor d) Y))
             (ap2 natEqF (ap1 Fst d) (natCode 3)))
test3_op d Y ne =
  let pkg : Term
      pkg = ap2 pi (ap1 predecessor d) Y
  in ruleTrans (ax_C natEqF get_tag (constN 3) pkg)
       (ruleTrans (congL natEqF (ap1 (constN 3) pkg) (get_tag_op d Y ne))
                  (congR natEqF (ap1 Fst d) (constN_eq 3 pkg)))
