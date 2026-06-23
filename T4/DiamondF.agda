{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DiamondF -- the DIAMOND as a genuine object PRIMITIVE-RECURSIVE FUNCTION
-- on reduction-proof CODES (the relational Church-Rosser route: NO eval, NO
-- normal forms -- only codes of reductions and a completion function).
--
-- Following Takahashi: the diamond is built from the triangle.  Given two
-- parallel-reduction proof codes  p : t => u  and  q : t => v  (same source),
-- the completion is
--
--     diamondF p q  =  < w , p' , q' >        ( w = devF (src p) )
--                   =  Pair (devF (src p)) (Pair (triF p) (triF q))
--
-- with  w  the COMPLETE DEVELOPMENT of the common source  t ,  p' = triF p
-- ( u => w ),  q' = triF q ( v => w ).  Note  w  is CONSTRUCTED (by  devF ),
-- never searched -- this is the whole point of the parallel-reduction proof:
-- confluence WITHOUT normalization, the apex is a primitive-recursive function
-- of the source.
--
-- The LOCAL DIAMOND verifier equation (structure-carrying form): for proof
-- trees built as  codeC c1 , codeC c2  with a COMMON source, both legs of
-- diamondF are VALID certs ending at the common apex  w :
--
--     isCert (diaL D) = O , src (diaL D) = tgt(codeC c1) , tgt (diaL D) = w
--     isCert (diaR D) = O , src (diaR D) = tgt(codeC c2) , tgt (diaR D) = w
--
-- (D = diamondF (codeC c1)(codeC c2)).  This is exactly the triangle facts
-- isCert_triF_M / src_triF / tgt_triF (T4.TriFPres / T4.TriFEnds) repackaged
-- into diamond shape -- no new induction, no eval.  It is the SPEC the opaque
-- version (diamondF on an opaque proof code, verifier equation by
-- course-of-values on the code) must match.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DiamondF where

open import T4.Base

open import T4.CertTree using ( CertM ; codeC )
open import T4.TriF     using ( triF )
open import T4.DevF     using ( devF )
open import T4.ParEnds  using ( src ; tgt ; isCert )
open import T4.TriFPres using ( isCert_triF_M )
open import T4.TriFEnds using ( src_triF ; tgt_triF )

------------------------------------------------------------------------
-- SECTION 1.  The completion function and its projections (Pair algebra).

diamondF : Term -> Term -> Term
diamondF p q =
  ap2 Pair (ap1 devF (ap1 src p)) (ap2 Pair (ap1 triF p) (ap1 triF q))

diaW : Term -> Term            -- the apex  w
diaW D = ap1 Fst D

diaL : Term -> Term            -- the left leg  p' : u => w
diaL D = ap1 Fst (ap1 Snd D)

diaR : Term -> Term            -- the right leg  q' : v => w
diaR D = ap1 Snd (ap1 Snd D)

-- Projection equations (axFst / axSnd only).

diaW_eq : (p q : Term) ->
  Deriv (eqF (diaW (diamondF p q)) (ap1 devF (ap1 src p)))
diaW_eq p q =
  axFst (ap1 devF (ap1 src p)) (ap2 Pair (ap1 triF p) (ap1 triF q))

diaL_eq : (p q : Term) -> Deriv (eqF (diaL (diamondF p q)) (ap1 triF p))
diaL_eq p q =
  ruleTrans
    (cong1 Fst (axSnd (ap1 devF (ap1 src p)) (ap2 Pair (ap1 triF p) (ap1 triF q))))
    (axFst (ap1 triF p) (ap1 triF q))

diaR_eq : (p q : Term) -> Deriv (eqF (diaR (diamondF p q)) (ap1 triF q))
diaR_eq p q =
  ruleTrans
    (cong1 Snd (axSnd (ap1 devF (ap1 src p)) (ap2 Pair (ap1 triF p) (ap1 triF q))))
    (axSnd (ap1 triF p) (ap1 triF q))

------------------------------------------------------------------------
-- SECTION 2.  The local-diamond verifier obligations (one per leg per fact).
-- Independent Deriv fields (no field references another) -- safe record.

record LocalDiamond (u1 u2 w pL pR : Term) : Set where
  field
    okL_cert : Deriv (eqF (ap1 isCert pL) O)
    okL_src  : Deriv (eqF (ap1 src pL) u1)
    okL_tgt  : Deriv (eqF (ap1 tgt pL) w)
    okR_cert : Deriv (eqF (ap1 isCert pR) O)
    okR_src  : Deriv (eqF (ap1 src pR) u2)
    okR_tgt  : Deriv (eqF (ap1 tgt pR) w)
open LocalDiamond public

------------------------------------------------------------------------
-- SECTION 3.  The LOCAL DIAMOND (structure-carrying).
--   Two proofs with a COMMON source close to the common apex  devF (src) .

localDiamond :
  (c1 c2 : CertM) ->
  Deriv (eqF (ap1 src (codeC c1)) (ap1 src (codeC c2))) ->
  LocalDiamond (ap1 tgt (codeC c1)) (ap1 tgt (codeC c2))
               (diaW (diamondF (codeC c1) (codeC c2)))
               (diaL (diamondF (codeC c1) (codeC c2)))
               (diaR (diamondF (codeC c1) (codeC c2)))
localDiamond c1 c2 srcEq = record
  { okL_cert = ruleTrans (cong1 isCert (diaL_eq (codeC c1) (codeC c2)))
                         (isCert_triF_M c1)
  ; okL_src  = ruleTrans (cong1 src (diaL_eq (codeC c1) (codeC c2)))
                         (src_triF c1)
  ; okL_tgt  = ruleTrans (cong1 tgt (diaL_eq (codeC c1) (codeC c2)))
                 (ruleTrans (tgt_triF c1)
                            (ruleSym (diaW_eq (codeC c1) (codeC c2))))
  ; okR_cert = ruleTrans (cong1 isCert (diaR_eq (codeC c1) (codeC c2)))
                         (isCert_triF_M c2)
  ; okR_src  = ruleTrans (cong1 src (diaR_eq (codeC c1) (codeC c2)))
                         (src_triF c2)
  ; okR_tgt  = ruleTrans (cong1 tgt (diaR_eq (codeC c1) (codeC c2)))
                 (ruleTrans (tgt_triF c2)
                   (ruleTrans (cong1 devF (ruleSym srcEq))
                              (ruleSym (diaW_eq (codeC c1) (codeC c2)))))
  }
