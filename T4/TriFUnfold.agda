{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriFUnfold -- the OPAQUE-UNFOLD atoms for the diamond's folds, the first
-- move of every case of the OPAQUE local diamond (toward BRA |- Con(T0)).
--
-- The structure-carrying local diamond (T4.DiamondF.localDiamond) consumes
-- proof trees built as  codeC c .  For  BRA |- Con(T0)  the proof code  p  is
-- OPAQUE (an E-witness from the consistency hypothesis), so the verifier
-- equations  isCert (triF p) = O ,  src (triF p) = tgt p ,  tgt (triF p) =
-- devF (src p)  must be proved by COURSE-OF-VALUES on  p  (the syntax-directed
-- recursion on the proof TREE, with  descSnd  giving sub-code < code).
--
-- Every such case begins by UNFOLDING a fold at the opaque nonzero code.  All
-- three folds (triF, isCert, devF) have the uniform shape  fold base
-- (Post stepBody pi) , so -- exactly as T4.SrcHeadStab does for src / tgt --
-- foldOpaque + axPost exposes the step body applied to the recovery package:
--
--     fold base (Post stepBody pi) d
--       =  stepBody (pi (pred d) (Snd (cov_spec base (Post stepBody pi) O (pred d))))
--                                                                       (for d != O)
--
-- The step body then dispatches on  Fst d  (the cert tag) via condFork; that
-- tag-dispatch + descSnd child-recovery + the covFuel assembly is the
-- remaining BULK.  This file delivers the unfold layer GREEN.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriFUnfold where

open import T4.Base

open import T4.TriF    using ( triF ; triBase ; stepFun_tri ; stepBody_tri )
open import T4.DevF    using ( devF ; devBase ; stepFun_dev ; stepBody_dev )
open import T4.ParEnds using ( isCert ; stepFun_ic ; stepBody_ic )
open import T4.SizedPres using ( foldOpaque )
open import T4.CoVSpec   using ( cov_spec )

open import BRA3.Church      using ( predecessor ; pi )
open import BRA3.PairAlgebra using ( Z ; Post ; axPost )

------------------------------------------------------------------------
-- triF  opaque unfold.

triFUnfold : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 triF d)
             (ap1 stepBody_tri
               (ap2 pi (ap1 predecessor d)
                       (ap1 Snd (ap2 (cov_spec triBase stepFun_tri) O
                                     (ap1 predecessor d))))))
triFUnfold d ne =
  ruleTrans (foldOpaque triBase stepFun_tri d ne)
            (axPost stepBody_tri pi
              (ap1 predecessor d)
              (ap1 Snd (ap2 (cov_spec triBase stepFun_tri) O (ap1 predecessor d))))

------------------------------------------------------------------------
-- isCert  opaque unfold (base Z, step body stepBody_ic).

isCertUnfold : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 isCert d)
             (ap1 stepBody_ic
               (ap2 pi (ap1 predecessor d)
                       (ap1 Snd (ap2 (cov_spec Z stepFun_ic) O
                                     (ap1 predecessor d))))))
isCertUnfold d ne =
  ruleTrans (foldOpaque Z stepFun_ic d ne)
            (axPost stepBody_ic pi
              (ap1 predecessor d)
              (ap1 Snd (ap2 (cov_spec Z stepFun_ic) O (ap1 predecessor d))))

------------------------------------------------------------------------
-- devF  opaque unfold (base devBase, step body stepBody_dev).

devFUnfold : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 devF d)
             (ap1 stepBody_dev
               (ap2 pi (ap1 predecessor d)
                       (ap1 Snd (ap2 (cov_spec devBase stepFun_dev) O
                                     (ap1 predecessor d))))))
devFUnfold d ne =
  ruleTrans (foldOpaque devBase stepFun_dev d ne)
            (axPost stepBody_dev pi
              (ap1 predecessor d)
              (ap1 Snd (ap2 (cov_spec devBase stepFun_dev) O (ap1 predecessor d))))
