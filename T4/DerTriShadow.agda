{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriShadow -- STEP 2: the OBJECT DIAMOND for parallel reduction, on the
-- DerCode derivation shadow.
--
-- The endpoint equations of the triangle are already green as OBJECT Derivs in
-- T4.DerTriPres (over the unsized DerCode coding, which carries full object
-- srcF / tgtF / triF / devF):
--
--   src_tri : srcF (triF (codeDer d)) = tgtF (codeDer d)
--   tgt_tri : tgtF (triF (codeDer d)) = devF (srcF (codeDer d))
--
-- The one structural brick still missing for the diamond is the analogue of
-- T4.TriPresShadow.triShadow on this coding: that the object triangle map triF
-- sends a derivation code to a derivation code,
--
--   triShadowU : triF (codeDer d) = codeDer (triMeta d)
--
-- with triMeta : DerM -> DerM the meta triangle on shadows (clause-for-clause
-- ObjCR.tri).  Proved by structural recursion using the BUILT triF equations
-- (DerTri / DerTri2) + constructor congruences -- exactly the Escardo-style
-- structural diamond, no measure / fuel / ne.
--
-- Then the object diamond:  two parallel steps  p : a => u1 ,  q : a => u2
-- out of a common source  a  join at the object development  devF a , with a
-- derivation-shadow leg on each side (legs = triMeta p , triMeta q ; endpoints
-- discharged by src_tri / tgt_tri + triShadowU).  This mirrors ObjCR.objDiamond
-- but every endpoint is a genuine object Deriv.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriShadow where

open import T4.Base

open import T4.DerCode
  using ( DerM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeDer
        ; derZe ; derSu ; derAd ; derRO ; derRS ; filler )
open import T4.DerCode using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.DerSrc using ( srcF )
open import T4.DerTgt using ( tgtF )
open import T4.DerDev using ( devF )
open import T4.DerTri
  using ( triF ; triF_derZe ; triF_derSu ; triF_derRO ; triF_derRS )
open import T4.DerTri2
  using ( triF_derAd_Ze ; triF_derAd_Su ; triF_derAd_Ad ; triF_derAd_RO ; triF_derAd_RS )
open import T4.DerTriPres using ( src_tri ; tgt_tri )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

open import BRA3.Church using ( pi )  -- (Pair is in scope from T4.Base)

------------------------------------------------------------------------
-- SECTION 0.  Constructor congruences over  codeDer  (X = Y  =>  der.. X = der.. Y).
-- der.. d = binNode tag.. = Pair (natCode 2) (Pair tag.. (Pair l r)) ; cong on the
-- child slot(s) via congL / congR over the binary  Pair .

derSuCong : {X Y : Term} -> Deriv (eqF X Y) -> Deriv (eqF (derSu X) (derSu Y))
derSuCong {X} {Y} eq =
  congR Pair (natCode 2) (congR Pair dgSu (congL Pair filler eq))

derROCong : {X Y : Term} -> Deriv (eqF X Y) -> Deriv (eqF (derRO X) (derRO Y))
derROCong {X} {Y} eq =
  congR Pair (natCode 2) (congR Pair dgRO (congL Pair filler eq))

derAdCong : {X1 Y1 X2 Y2 : Term} ->
  Deriv (eqF X1 Y1) -> Deriv (eqF X2 Y2) ->
  Deriv (eqF (derAd X1 X2) (derAd Y1 Y2))
derAdCong {X1} {Y1} {X2} {Y2} e1 e2 =
  congR Pair (natCode 2)
    (congR Pair dgAd (ruleTrans (congL Pair X2 e1) (congR Pair Y1 e2)))

derRSCong : {X1 Y1 X2 Y2 : Term} ->
  Deriv (eqF X1 Y1) -> Deriv (eqF X2 Y2) ->
  Deriv (eqF (derRS X1 X2) (derRS Y1 Y2))
derRSCong {X1} {Y1} {X2} {Y2} e1 e2 =
  congR Pair (natCode 2)
    (congR Pair dgRS (ruleTrans (congL Pair X2 e1) (congR Pair Y1 e2)))

------------------------------------------------------------------------
-- SECTION 1.  The meta triangle map on shadows (clause-for-clause ObjCR.tri).

triMeta : DerM -> DerM
triMeta mZe                  = mZe
triMeta (mSu p)              = mSu (triMeta p)
triMeta (mAd mZe q)          = mRO (triMeta q)
triMeta (mAd (mSu p) q)      = mRS (triMeta p) (triMeta q)
triMeta (mAd (mAd p1 p2) q)  = mAd (triMeta (mAd p1 p2)) (triMeta q)
triMeta (mAd (mRO p) q)      = mAd (triMeta (mRO p)) (triMeta q)
triMeta (mAd (mRS p1 p2) q)  = mAd (triMeta (mRS p1 p2)) (triMeta q)
triMeta (mRO p)              = triMeta p
triMeta (mRS p q)            = mSu (mAd (triMeta p) (triMeta q))

------------------------------------------------------------------------
-- SECTION 2.  triF preserves the shadow:  triF (codeDer d) = codeDer (triMeta d).
-- Structural recursion; each case = BUILT triF equation then constructor cong on
-- the recursive results.  Ad dispatches on the LEFT child shadow.

triShadowU : (d : DerM) ->
  Deriv (eqF (ap1 triF (codeDer d)) (codeDer (triMeta d)))
triShadowU mZe       = triF_derZe
triShadowU (mSu p)   =
  ruleTrans (triF_derSu (codeDer p)) (derSuCong (triShadowU p))
triShadowU (mRO p)   =
  ruleTrans (triF_derRO (codeDer p)) (triShadowU p)
triShadowU (mRS p q) =
  ruleTrans (triF_derRS (codeDer p) (codeDer q))
            (derSuCong (derAdCong (triShadowU p) (triShadowU q)))
triShadowU (mAd mZe q) =
  ruleTrans (triF_derAd_Ze (codeDer q)) (derROCong (triShadowU q))
triShadowU (mAd (mSu p) q) =
  ruleTrans (triF_derAd_Su (codeDer p) (codeDer q))
            (derRSCong (triShadowU p) (triShadowU q))
triShadowU (mAd (mAd p1 p2) q) =
  ruleTrans (triF_derAd_Ad (codeDer p1) (codeDer p2) (codeDer q))
            (derAdCong (triShadowU (mAd p1 p2)) (triShadowU q))
triShadowU (mAd (mRO p) q) =
  ruleTrans (triF_derAd_RO (codeDer p) (codeDer q))
            (derAdCong (triShadowU (mRO p)) (triShadowU q))
triShadowU (mAd (mRS p1 p2) q) =
  ruleTrans (triF_derAd_RS (codeDer p1) (codeDer p2) (codeDer q))
            (derAdCong (triShadowU (mRS p1 p2)) (triShadowU q))

------------------------------------------------------------------------
-- SECTION 3.  Object reduction at the term-code level, and the diamond.
--
-- RedU d a b : the derivation shadow  d  codes a parallel step  a => b , i.e.
-- srcF (codeDer d) = a  and  tgtF (codeDer d) = b  (object equations).

RedU : DerM -> Term -> Term -> Set
RedU d a b =
  And (Deriv (eqF (ap1 srcF (codeDer d)) a))
      (Deriv (eqF (ap1 tgtF (codeDer d)) b))

-- Join1U u1 u2 : a common reduct  w  with a derivation-shadow leg from each of
-- u1 and u2.

Join1U : Term -> Term -> Set
Join1U u1 u2 =
  Sigma Term (\ w -> And (Sigma DerM (\ p -> RedU p u1 w))
                         (Sigma DerM (\ q -> RedU q u2 w)))

-- the two legs of the triangle of a single derivation  p : a => u .
-- triMeta p : u => devF a , with both endpoints discharged.

triLeg : (p : DerM) {a u : Term} -> RedU p a u -> RedU (triMeta p) u (ap1 devF a)
triLeg p (mkAnd sp tp) =
  mkAnd
    -- srcF (codeDer (triMeta p)) = u
    (ruleTrans (cong1 srcF (ruleSym (triShadowU p)))
       (ruleTrans (src_tri p) tp))
    -- tgtF (codeDer (triMeta p)) = devF a
    (ruleTrans (cong1 tgtF (ruleSym (triShadowU p)))
       (ruleTrans (tgt_tri p) (cong1 devF sp)))

objDiamondU : {p q : DerM} {a u1 u2 : Term} ->
  RedU p a u1 -> RedU q a u2 -> Join1U u1 u2
objDiamondU {p} {q} {a} {u1} {u2} rp rq =
  mkSigma (ap1 devF a)
    (mkAnd (mkSigma (triMeta p) (triLeg p rp))
           (mkSigma (triMeta q) (triLeg q rq)))
