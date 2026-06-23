{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SrcHeadStab -- foundational piece of the OPAQUE single-step head
-- preservation (toward object head-stability / object Con(T0)).
--
-- The eta-free OPAQUE unfold of the  src  fold at a nonzero code: for d != O,
--   src d = stepBody_src (pi (pred d) (Snd (cov_spec srcBase stepFun_src O (pred d))))
-- via  T4.SizedPres.foldOpaque (= foldStepRaw + succForm, no surjective pairing)
-- + axPost (Post stepBody_src pi).  The step body  stepBody_src  then dispatches
-- on  get_tag = Fst d = chd d  (the 4-way natEqF cascade), so an opaque cert's
-- tag is reachable with NO eta -- the foundation for the opaque  certHeadZe
-- (which case-splits the tag UNDER the d != O assumption via T4.ImpExtras.
-- imp_byCases and refutes every non-cZe head against tagZe by
-- succEqO_to_anything).
--
-- This file delivers the opaque unfold (src + tgt) GREEN; the tag-dispatch
-- assembly is the next step.  No holes, no postulates.

module T4.SrcHeadStab where

open import T4.Base

open import T4.ParEnds  using
  ( src ; tgt ; stepBody_src ; stepFun_src ; stepBody_tgt ; stepFun_tgt ; srcBase )
open import T4.SizedPres using ( foldOpaque )
open import T4.CoVSpec   using ( cov_spec )

open import BRA3.Church      using ( predecessor ; pi )
open import BRA3.PairAlgebra using ( Post ; axPost )

------------------------------------------------------------------------
-- src  opaque unfold.

srcUnfold : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 src d)
             (ap1 stepBody_src
               (ap2 pi (ap1 predecessor d)
                       (ap1 Snd (ap2 (cov_spec srcBase stepFun_src) O
                                     (ap1 predecessor d))))))
srcUnfold d ne =
  ruleTrans (foldOpaque srcBase stepFun_src d ne)
            (axPost stepBody_src pi
              (ap1 predecessor d)
              (ap1 Snd (ap2 (cov_spec srcBase stepFun_src) O (ap1 predecessor d))))

------------------------------------------------------------------------
-- tgt  opaque unfold (same base srcBase, step body stepBody_tgt).

tgtUnfold : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 tgt d)
             (ap1 stepBody_tgt
               (ap2 pi (ap1 predecessor d)
                       (ap1 Snd (ap2 (cov_spec srcBase stepFun_tgt) O
                                     (ap1 predecessor d))))))
tgtUnfold d ne =
  ruleTrans (foldOpaque srcBase stepFun_tgt d ne)
            (axPost stepBody_tgt pi
              (ap1 predecessor d)
              (ap1 Snd (ap2 (cov_spec srcBase stepFun_tgt) O (ap1 predecessor d))))
