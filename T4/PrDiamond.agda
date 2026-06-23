{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrDiamond -- the OBJECT DIAMOND for parallel reduction of the FULL
-- closed-term p.r. calculus, on the PrTriShadow derivation shadow, mirroring
-- T4.DerTriShadow §3.  Two parallel steps  p : a => u1 ,  q : a => u2  out of a
-- common source  a  join at the object development  devF a , with a derivation-
-- shadow leg on each side (legs = triMeta p , triMeta q); endpoints discharged
-- by src_tri / tgt_tri + triShadowU (all green object Derivs).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrDiamond where

open import T4.Base

open import T4.PrTriShadow using ( DerM ; triMeta ; triShadowU ; codeDer )
open import T4.PrSrc using ( srcF )
open import T4.PrTgt using ( tgtF )
open import T4.PrDev using ( devF )
open import T4.PrTriPres using ( src_tri ; tgt_tri )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

------------------------------------------------------------------------
-- SECTION 1.  Object reduction at the term-code level.
--
-- RedU d a b : the derivation shadow  d  codes a parallel step  a => b , i.e.
-- srcF (codeDer d) = a  and  tgtF (codeDer d) = b  (object equations).

RedU : DerM -> Term -> Term -> Set
RedU d a b =
  And (Deriv (eqF (ap1 srcF (codeDer d)) a))
      (Deriv (eqF (ap1 tgtF (codeDer d)) b))

Join1U : Term -> Term -> Set
Join1U u1 u2 =
  Sigma Term (\ w -> And (Sigma DerM (\ p -> RedU p u1 w))
                         (Sigma DerM (\ q -> RedU q u2 w)))

------------------------------------------------------------------------
-- SECTION 2.  The triangle legs and the diamond.

-- triMeta p : u => devF a , with both endpoints discharged.
triLeg : (p : DerM) {a u : Term} -> RedU p a u -> RedU (triMeta p) u (ap1 devF a)
triLeg p (mkAnd sp tp) =
  mkAnd
    (ruleTrans (cong1 srcF (ruleSym (triShadowU p)))
       (ruleTrans (src_tri p) tp))
    (ruleTrans (cong1 tgtF (ruleSym (triShadowU p)))
       (ruleTrans (tgt_tri p) (cong1 devF sp)))

objDiamondU : {p q : DerM} {a u1 u2 : Term} ->
  RedU p a u1 -> RedU q a u2 -> Join1U u1 u2
objDiamondU {p} {q} {a} {u1} {u2} rp rq =
  mkSigma (ap1 devF a)
    (mkAnd (mkSigma (triMeta p) (triLeg p rp))
           (mkSigma (triMeta q) (triLeg q rq)))
