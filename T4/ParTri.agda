{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParTri -- STAGE 4b (deliverable 2b): the TRIANGLE LEMMA (Takahashi
-- complete development), the CRUX of the internal Church-Rosser proof.
-- Object analog of  tri : Par t u -> Par u (dev t)  (T4.ChurchRosserProto).
--
-- ★ KEY SIMPLIFICATION.  For the RELATIONAL / ParCert formulation no object
-- devF : Fun1 is needed.  The complete development  dev  is a META function
-- dev : Tm -> Tm  (Agda computes it structurally), and the triangle is built
-- by META induction on a meta parallel-reduction  ParM  (mirroring the proto's
-- Par), using the reusable cert-constructor combinators of T4.ParBuild
-- (parSuC/parAdC/parROC/parRSC) and the diagonal cert T4.ParReflPres.parRefl.
-- Each case is EXACTLY the proto's  tri  clause with the Par constructors
-- replaced by their ParCert combinators; the endpoints  code u  and
-- code (dev t)  match definitionally because  dev  reduces in the meta layer.
--
-- Result:   tri : ParM t u -> ParCert (code u) (code (dev t)) .
-- The diamond (next, 2c) is immediate:  given  ParM t u1 ,  ParM t u2 , both
-- u1 , u2  reduce (as certs) to the common  code (dev t) .

module T4.ParTri where

open import T4.Base

open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code ; ParCert ; parRefl )
open import T4.ParBuild    using ( parSuC ; parAdC ; parROC ; parRSC )

------------------------------------------------------------------------
-- Meta parallel reduction (the proto's  Par , over the meta terms  Tm ).

data ParM : Tm -> Tm -> Set where
  pZe : ParM ze ze
  pSu : {t t' : Tm}      -> ParM t t' -> ParM (su t) (su t')
  pAd : {a a' b b' : Tm} -> ParM a a' -> ParM b b' -> ParM (ad a b) (ad a' b')
  pRO : {y y' : Tm}      -> ParM y y' -> ParM (ad ze y) y'
  pRS : {x x' y y' : Tm} -> ParM x x' -> ParM y y' ->
                            ParM (ad (su x) y) (su (ad x' y'))

------------------------------------------------------------------------
-- Complete development (Takahashi), as a META function on  Tm .

dev : Tm -> Tm
dev ze              = ze
dev (su t)          = su (dev t)
dev (ad ze y)       = dev y
dev (ad (su x) y)   = su (ad (dev x) (dev y))
dev (ad (ad p q) y) = ad (dev (ad p q)) (dev y)

------------------------------------------------------------------------
-- The triangle:  for every parallel step  ParM t u ,  u  parallel-reduces
-- (as a certificate) to the complete development  dev t .
--
-- Mirrors  ChurchRosserProto.tri  clause-for-clause (Par ctor -> ParCert
-- combinator); the recursion is on structural sub-derivations.

tri : {t u : Tm} -> ParM t u -> ParCert (code u) (code (dev t))
tri pZe                    = parRefl ze
tri (pSu p)                = parSuC (tri p)
tri (pAd pZe pb)           = parROC (tri pb)
tri (pAd (pSu px) pb)      = parRSC (tri px) (tri pb)
tri (pAd (pAd pa1 pa2) pb) = parAdC (tri (pAd pa1 pa2)) (tri pb)
tri (pAd (pRO p) pb)       = parAdC (tri (pRO p)) (tri pb)
tri (pAd (pRS px py) pb)   = parAdC (tri (pRS px py)) (tri pb)
tri (pRO p)                = tri p
tri (pRS px py)            = parSuC (parAdC (tri px) (tri py))

------------------------------------------------------------------------
-- Diamond for parallel reduction, immediate from the triangle:  any two
-- parallel reducts of  t  both reduce (as object certificates) to the
-- common complete development  dev t .

record Diamond (u1 u2 : Tm) : Set where
  constructor mkDiamond
  field
    apex : Tm
    legL : ParCert (code u1) (code apex)
    legR : ParCert (code u2) (code apex)
open Diamond public

diamond : {t u1 u2 : Tm} -> ParM t u1 -> ParM t u2 -> Diamond u1 u2
diamond {t} p1 p2 = mkDiamond (dev t) (tri p1) (tri p2)
