{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.OpaqueHarness -- the OPAQUE recovery harness for an ARBITRARY sized
-- course-of-values step body  sbf , abstracted from T4.WfRedExtract (which is
-- the  sbf = wfStep  instance).  For  p != O  the fold  szRunF sbf = fold Z
-- (Post sbf pi)  fires eta-free (foldOpaque) onto the package
--
--     opkg p = pi (predecessor p) (Snd (cov_spec Z (Post sbf pi) O (predecessor p)))
--
-- whose accessors recover the structure of  p  (sbf-independent in value):
--
--     get_newK (opkg p) = p          nIdx (opkg p) = dtag p
--     get_rc   (opkg p) = Snd p      argIdx (opkg p) = pArg p
--     lIdx (opkg p) = pL p           rIdx (opkg p) = pR p
--
-- and  opUnfold : szRunF sbf p = sbf (opkg p) .  Instantiated at  sbf = triStep
-- this drives the OPAQUE triFSized equations (T4.DerTriSOpaque).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.OpaqueHarness where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg ; pL ; pR )
open import T4.SizedPres using ( foldOpaque ; succForm )
open import T4.CoVSpec using ( cov_spec )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( fold ; get_newK ; get_newK_at_pi )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import BRA3.Church      using ( pi ; predecessor )
open import BRA3.PairAlgebra using ( Post ; axPost ; compose1U ; compose1U_eq )

-- Generalised over the fold BASE  g  (the value at O).  The accessors are
-- base-independent in value (they recover the structure of  p  itself); only
-- prevS / opkg / opUnfold thread  g  via  cov_spec g / fold g .  The original
-- single-argument  H  is recovered below as  HBase Z .  This lets the strict
-- validity fold  wfRed = binRec (constN 1) Z wfCellNode  (base = reject, so
-- wfRed O = s O , i.e. O is NOT a valid derivation) reuse the same harness.
module HBase (g sbf : Fun1) where

  -- The opaque package and its eta-free unfold.
  prevS : Term -> Term
  prevS p = ap1 Snd (ap2 (cov_spec g (Post sbf pi)) O (ap1 predecessor p))

  opkg : Term -> Term
  opkg p = ap2 pi (ap1 predecessor p) (prevS p)

  opUnfold : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (fold g (Post sbf pi)) p) (ap1 sbf (opkg p)))
  opUnfold p ne =
    ruleTrans (foldOpaque g (Post sbf pi) p ne)
              (axPost sbf pi (ap1 predecessor p) (prevS p))

  -- Accessors.
  op_newK : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 get_newK (opkg p)) p)
  op_newK p ne =
    ruleTrans (get_newK_at_pi (ap1 predecessor p) (prevS p)) (succForm p ne)

  op_rc : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 get_rc (opkg p)) (ap1 Snd p))
  op_rc p ne =
    ruleTrans (compose1U_eq Snd get_newK (opkg p)) (cong1 Snd (op_newK p ne))

  op_nIdx : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 nIdx (opkg p)) (dtag p))
  op_nIdx p ne =
    ruleTrans (compose1U_eq Fst get_rc (opkg p)) (cong1 Fst (op_rc p ne))

  argIdx : Fun1
  argIdx = compose1U Snd get_rc

  op_argIdx : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 argIdx (opkg p)) (pArg p))
  op_argIdx p ne =
    ruleTrans (compose1U_eq Snd get_rc (opkg p)) (cong1 Snd (op_rc p ne))

  op_pL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 lIdx (opkg p)) (pL p))
  op_pL p ne =
    ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) (opkg p))
              (cong1 Fst (op_argIdx p ne))

  op_pR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 rIdx (opkg p)) (pR p))
  op_pR p ne =
    ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) (opkg p))
              (cong1 Snd (op_argIdx p ne))

-- The original harness:  fold base = Z  (used by triF / srcF / tgtF).
module H (sbf : Fun1) where
  open HBase Z sbf public
