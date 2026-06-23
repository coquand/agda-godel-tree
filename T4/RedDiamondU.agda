{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RedDiamondU -- STEP 1 of the OPAQUE confluence: the one-step relation and
-- the local diamond driven by the genuine opaque diamond  diamondU
-- (T4.TriUDiamond), over the UNSIZED coding, with GENUINE  srcF / tgtF
-- endpoints and the strict-validity side-condition  wfRed p = O .
--
--   RedU p a b : the code  p  is a VALID derivation (wfRed p = O) whose source
--   is  a  (srcF p = a) and whose target is  b  (tgtF p = b) -- a one-step
--   parallel reduction  a => b  witnessed by the opaque derivation code  p .
--
-- The triangle leg comes straight out of  diamondU :  under  wfRed p = O ,
-- diamondU gives  conj3 p = O , which T4.CRGlueU.childV/S/T decompose into
--   (V) wfRed (triF p) = O          -- validity preserved
--   (S) srcF (triF p) = tgtF p      -- source endpoint
--   (T) tgtF (triF p) = devF (srcF p)
-- so  triF p  is a VALID step  b => devF a , and two steps out of a common
-- source  a  join at  devF a .  This mirrors T4.DerTriShadow.objDiamondU but
-- with opaque codes  p : Term  (no meta shadow) and genuine validity.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.RedDiamondU where

open import T4.Base

open import T4.WfRed  using ( wfRed )
open import T4.DerTri using ( triF )
open import T4.DerSrc using ( srcF )
open import T4.DerTgt using ( tgtF )
open import T4.DerDev using ( devF )
open import T4.QCheckU using ( conj3 )
open import T4.TriUDiamond using ( diamondU )
open import T4.CRGlueU using ( childV ; childS ; childT )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

------------------------------------------------------------------------
-- SECTION 1.  The opaque one-step relation.

-- RedU p a b : opaque code  p  is a valid one-step  a => b .
RedU : Term -> Term -> Term -> Set
RedU p a b =
  And (Deriv (eqF (ap1 wfRed p) O))
      (And (Deriv (eqF (ap1 srcF p) a))
           (Deriv (eqF (ap1 tgtF p) b)))

-- projections
redV : {p a b : Term} -> RedU p a b -> Deriv (eqF (ap1 wfRed p) O)
redV r = andL r

redS : {p a b : Term} -> RedU p a b -> Deriv (eqF (ap1 srcF p) a)
redS r = andL (andR r)

redT : {p a b : Term} -> RedU p a b -> Deriv (eqF (ap1 tgtF p) b)
redT r = andR (andR r)

mkRed : {p a b : Term} ->
  Deriv (eqF (ap1 wfRed p) O) ->
  Deriv (eqF (ap1 srcF p) a) ->
  Deriv (eqF (ap1 tgtF p) b) ->
  RedU p a b
mkRed hV hS hT = mkAnd hV (mkAnd hS hT)

------------------------------------------------------------------------
-- SECTION 2.  The triangle leg out of the opaque diamond.
--
-- triLeg p (rp : RedU p a b) : RedU (triF p) b (devF a)
--   srcF (triF p) = tgtF p = b ,  tgtF (triF p) = devF (srcF p) = devF a ,
--   wfRed (triF p) = O .

triLeg : (p : Term) {a b : Term} ->
  RedU p a b -> RedU (ap1 triF p) b (ap1 devF a)
triLeg p {a} {b} r =
  let hV : Deriv (eqF (ap1 wfRed p) O)
      hV = redV r
      hS : Deriv (eqF (ap1 srcF p) a)
      hS = redS r
      hT : Deriv (eqF (ap1 tgtF p) b)
      hT = redT r
      cj : Deriv (eqF (ap1 conj3 p) O)
      cj = mp (diamondU p) hV
  in mkRed (childV p cj)
           (ruleTrans (childS p cj) hT)          -- srcF (triF p) = tgtF p = b
           (ruleTrans (childT p cj) (cong1 devF hS))  -- tgtF(triF p) = devF(srcF p) = devF a

------------------------------------------------------------------------
-- SECTION 3.  Local diamond:  two valid steps out of a common source join.

-- Join1U u1 u2 : a common reduct  w  with a valid step from each of u1, u2.
Join1U : Term -> Term -> Set
Join1U u1 u2 =
  Sigma Term (\ w -> And (Sigma Term (\ p -> RedU p u1 w))
                         (Sigma Term (\ q -> RedU q u2 w)))

objDiamondU : {p q : Term} {a u1 u2 : Term} ->
  RedU p a u1 -> RedU q a u2 -> Join1U u1 u2
objDiamondU {p} {q} {a} rp rq =
  mkSigma (ap1 devF a)
    (mkAnd (mkSigma (ap1 triF p) (triLeg p rp))
           (mkSigma (ap1 triF q) (triLeg q rq)))
