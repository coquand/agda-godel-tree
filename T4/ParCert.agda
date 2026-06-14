{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParCert -- the RELATIONAL route to internal Church-Rosser
-- (attempt3 §8-§11), encoding layer for PARALLEL REDUCTION.
--
-- We represent the parallel-reduction relation  Par  of
-- T4.ChurchRosserProto INTENSIONALLY, by its derivation CERTIFICATES
-- (coded derivation trees).  The five Par constructors
--     pZe : Par ze ze
--     pSu : Par t t' -> Par (su t) (su t')
--     pAd : Par a a' -> Par b b' -> Par (ad a b) (ad a' b')
--     pRO : Par y y' -> Par (ad ze y) y'
--     pRS : Par x x' -> Par y y' -> Par (ad (su x) y) (su (ad x' y'))
-- become tagged-pair certificate constructors.  A certificate carries NO
-- terms: its source and target are DETERMINED structurally (src/tgt,
-- T4.ParEnds, next file), and every well-tagged certificate is valid, so
--     Par t u  :=  E (\ d -> And (isCert d = O) (And (src d = t) (tgt d = u)))
-- (the object existential with a certificate witness; the Carneiro
-- deduction-theorem lift turns the meta certificate constructions of the
-- CR lemmas -- parRefl, stepPar, tri, ... -- into object implications).
--
-- This file: the constructors + tag/sub-certificate projection equations
-- (all  axFst / axSnd ).  No induction, no postulates, no holes.

module T4.ParCert where

open import T4.Base

------------------------------------------------------------------------
-- Certificate constructor tags.

ptZe : Term
ptZe = natCode 0

ptSu : Term
ptSu = natCode 1

ptAd : Term
ptAd = natCode 2

ptRO : Term
ptRO = natCode 3

ptRS : Term
ptRS = natCode 4

------------------------------------------------------------------------
-- Certificate constructors (coded derivation trees).
--   cZe          -- pZe
--   cSu d        -- pSu d
--   cAd d1 d2    -- pAd d1 d2
--   cRO d        -- pRO d
--   cRS d1 d2    -- pRS d1 d2

cZe : Term
cZe = ap2 Pair ptZe O

cSu : Term -> Term
cSu d = ap2 Pair ptSu d

cAd : Term -> Term -> Term
cAd d1 d2 = ap2 Pair ptAd (ap2 Pair d1 d2)

cRO : Term -> Term
cRO d = ap2 Pair ptRO d

cRS : Term -> Term -> Term
cRS d1 d2 = ap2 Pair ptRS (ap2 Pair d1 d2)

------------------------------------------------------------------------
-- Projectors:  chd = Fst (constructor tag),  cdat = Snd (payload).

chd : Term -> Term
chd d = ap1 Fst d

cdat : Term -> Term
cdat d = ap1 Snd d

------------------------------------------------------------------------
-- Tag projection equations.

chd_cZe : Deriv (eqF (chd cZe) ptZe)
chd_cZe = axFst ptZe O

chd_cSu : (d : Term) -> Deriv (eqF (chd (cSu d)) ptSu)
chd_cSu d = axFst ptSu d

chd_cAd : (d1 d2 : Term) -> Deriv (eqF (chd (cAd d1 d2)) ptAd)
chd_cAd d1 d2 = axFst ptAd (ap2 Pair d1 d2)

chd_cRO : (d : Term) -> Deriv (eqF (chd (cRO d)) ptRO)
chd_cRO d = axFst ptRO d

chd_cRS : (d1 d2 : Term) -> Deriv (eqF (chd (cRS d1 d2)) ptRS)
chd_cRS d1 d2 = axFst ptRS (ap2 Pair d1 d2)

------------------------------------------------------------------------
-- Sub-certificate projection equations.

-- cSu / cRO carry a single sub-certificate in  Snd .
cSu_sub : (d : Term) -> Deriv (eqF (cdat (cSu d)) d)
cSu_sub d = axSnd ptSu d

cRO_sub : (d : Term) -> Deriv (eqF (cdat (cRO d)) d)
cRO_sub d = axSnd ptRO d

-- cAd / cRS carry a pair  Pair d1 d2  in  Snd .
cAd_dat : (d1 d2 : Term) -> Deriv (eqF (cdat (cAd d1 d2)) (ap2 Pair d1 d2))
cAd_dat d1 d2 = axSnd ptAd (ap2 Pair d1 d2)

cRS_dat : (d1 d2 : Term) -> Deriv (eqF (cdat (cRS d1 d2)) (ap2 Pair d1 d2))
cRS_dat d1 d2 = axSnd ptRS (ap2 Pair d1 d2)

-- First / second sub-certificate of a binary node.
cAdL : (d1 d2 : Term) -> Deriv (eqF (ap1 Fst (cdat (cAd d1 d2))) d1)
cAdL d1 d2 = ruleTrans (cong1 Fst (cAd_dat d1 d2)) (axFst d1 d2)

cAdR : (d1 d2 : Term) -> Deriv (eqF (ap1 Snd (cdat (cAd d1 d2))) d2)
cAdR d1 d2 = ruleTrans (cong1 Snd (cAd_dat d1 d2)) (axSnd d1 d2)

cRSL : (d1 d2 : Term) -> Deriv (eqF (ap1 Fst (cdat (cRS d1 d2))) d1)
cRSL d1 d2 = ruleTrans (cong1 Fst (cRS_dat d1 d2)) (axFst d1 d2)

cRSR : (d1 d2 : Term) -> Deriv (eqF (ap1 Snd (cdat (cRS d1 d2))) d2)
cRSR d1 d2 = ruleTrans (cong1 Snd (cRS_dat d1 d2)) (axSnd d1 d2)
