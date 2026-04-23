{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Prov -- provability predicate and combinators.
--
-- Per UNIFIED-DESIGN-REV2-5C.md step 2.  Prov packages an encoded
-- proof tree with its thmT-correctness witness:
--
--   Prov P = Sigma (e : Term)
--     (Deriv (atomic (eqn (ap1 thmT e) (reify (codeFormula P)))))
--
-- Combinators provMp, provInst, provRefl, provTrans, provSym,
-- provCongL, provCongR wrap the existing encoders from
-- Guard.ProofEncUnify / Guard.ProofEncFormula.  Each combinator
-- bundles a Term (the encoded proof tree) with a Deriv witness.
--
-- This file covers the simplest combinators.  The ones requiring
-- the "thmT respects Pair" adapter (provMp, provRuleInst via
-- the encoded sub-proof pairing in encMpCorr) are deferred to a
-- later commit.

module Guard.Prov where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForHF using (thmT)
open import Guard.ThFun using (codeEqn)
open import Guard.ProofEncUnify using (encAxRefl ; encAxReflCorr)

------------------------------------------------------------------------
-- The provability predicate.
--
-- Prov P witnesses "BRA proves P" by exhibiting a specific encoded
-- proof tree  e : Term  together with a Deriv proof that thmT(e)
-- evaluates to the Godel code of P.

Prov : Formula -> Set
Prov P = Sigma Term
  (\ e -> Deriv (eqF (ap1 thmT e) (reify (codeFormula P))))

------------------------------------------------------------------------
-- Destructor convenience accessors.

provTerm : (P : Formula) -> Prov P -> Term
provTerm P p = fst p

provDeriv : (P : Formula) -> (p : Prov P) ->
  Deriv (eqF (ap1 thmT (provTerm P p)) (reify (codeFormula P)))
provDeriv P p = snd p

------------------------------------------------------------------------
-- provRefl: reflexivity.  For any Term t,  t = t  is provable.
--
-- Uses encAxRefl / encAxReflCorr from Guard.ProofEncUnify.
--
-- encAxReflCorr gives  thmT (encAxRefl tC) = Pair tC tC .
-- We want   thmT (encAxRefl (reify (code t))) = reify (codeFormula (atomic (eqn t t))) .
-- By definition: codeFormula (atomic (eqn t t)) = codeEqn (eqn t t) = nd (code t) (code t),
-- so reify (codeFormula (atomic (eqn t t))) = ap2 Pair (reify (code t)) (reify (code t)).
-- Setting tC = reify (code t) gives the result definitionally.

provRefl : (t : Term) -> Prov (atomic (eqn t t))
provRefl t = mkSigma (encAxRefl (reify (code t)))
                     (encAxReflCorr (reify (code t)))
