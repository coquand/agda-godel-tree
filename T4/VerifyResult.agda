{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.VerifyResult -- the OUTPUT coding of the trace-producing verifier
-- verifyPar (the "do not throw away evidence" design): verifyPar p t u returns
-- a STRUCTURED RESULT, either  fail  or  ok d  with  d  a canonically BUILT
-- trace (a size-prefixed proof code, T4.SizedProof's pcZe/pcSu/pcAd/pcRO/pcRS)
-- witnessing  p : t => u .  The diamond then recurses on the built trace  d  --
-- back in the STRUCTURE-CARRYING regime (where T4.DiamondF.localDiamond /
-- T4.TriFEnds apply) -- NOT on the opaque input  p ; the verifier is the single
-- opaque->structure bridge (it BUILDS d, so d decomposes by cheap projection).
--
--   okR d  = Pair O d            -- ok flag O, payload = trace d
--   failR  = Pair (s O) O        -- reject flag s O
--   isOk r = Fst r               -- O  iff  ok
--   okTrace r = Snd r            -- the built trace (when ok)
--   checkPar p t u := isOk (verifyPar p t u)        -- boolean projection
--
-- This file delivers the wrapper + accessors + their Deriv equations
-- (axFst / axSnd only).  No holes, no postulates, no termination warnings;
-- --safe --without-K --exact-split.

module T4.VerifyResult where

open import T4.Base

------------------------------------------------------------------------
-- SECTION 1.  The result wrapper.

okR : Term -> Term
okR d = ap2 Pair O d

failR : Term
failR = ap2 Pair (ap1 s O) O

isOk : Term -> Term
isOk r = ap1 Fst r

okTrace : Term -> Term
okTrace r = ap1 Snd r

------------------------------------------------------------------------
-- SECTION 2.  Accessor equations.

isOk_ok : (d : Term) -> Deriv (eqF (isOk (okR d)) O)
isOk_ok d = axFst O d

okTrace_ok : (d : Term) -> Deriv (eqF (okTrace (okR d)) d)
okTrace_ok d = axSnd O d

isOk_fail : Deriv (eqF (isOk failR) (ap1 s O))
isOk_fail = axFst (ap1 s O) O
