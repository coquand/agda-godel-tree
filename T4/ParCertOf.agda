{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParCertOf -- the OBJECT CONTENT of the meta confluence (T4.ParConfl):
-- a homomorphism turning EVERY meta parallel-reduction derivation into an
-- object Par-CERTIFICATE with the matching coded endpoints.
--
--     certOf : ParM t u -> ParCert (code t) (code u)
--
-- Built by meta induction on  ParM  (T4.ParTri), one clause per constructor,
-- using the diagonal cert (T4.ParReflPres.parRefl) and the cert-constructor
-- combinators (T4.ParBuild).  This is the bridge from the (proto-isomorphic)
-- meta combinatorics to genuine object certificates: the apex of every
-- diamond / strip / confl step is object-certified by applying certOf at the
-- leaves.  (T4.ParTri.tri is the triangle instance  certOf o triM .)

module T4.ParCertOf where

open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code ; ParCert ; parRefl )
open import T4.ParTri      using ( ParM ; pZe ; pSu ; pAd ; pRO ; pRS )
open import T4.ParBuild    using ( parSuC ; parAdC ; parROC ; parRSC )

certOf : {t u : Tm} -> ParM t u -> ParCert (code t) (code u)
certOf pZe          = parRefl ze
certOf (pSu p)      = parSuC (certOf p)
certOf (pAd pa pb)  = parAdC (certOf pa) (certOf pb)
certOf (pRO p)      = parROC (certOf p)
certOf (pRS px py)  = parRSC (certOf px) (certOf py)
