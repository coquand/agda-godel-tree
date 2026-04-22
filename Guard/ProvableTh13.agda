{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvableTh13 -- meta-Th-13 lift to the Provable layer.
--
-- Guard 1963 BRA, Theorem 13 states: for any singulary functor f and
-- terms x, y, the implication  f(x) = y ⊃ th(Df(x)) = "fx = y"  is
-- provable in BRA, where Df(x) is a constructed singulary functor.
--
-- In our system, the analog of "th" is  thmT trivCT  and the analog of
-- the encoded equation "fx = y" is  reify (codeEqn (eqn (ap1 f x) y)) .
--
-- The internal-Provable form of Th 13 (with Df constructed as a Term
-- combinator) requires substantial machinery (see GUARD-BRA-TEMPLATE.md
-- step 6, ~200 lines).  This file provides the META form: given a
-- meta-level Deriv  Triv ⊢ eq , the corresponding ProofE3-encoded proof
-- enc satisfies  thmT(trivCT)(enc) = reify(codeEqn eq) , and we lift
-- this fact polymorphically to the Provable layer via fromDeriv.
--
-- The meta-Th-13 form is sufficient for a META-LEVEL Gödel II argument:
-- once we have a meta Deriv, we can lift it through the propositional
-- chain and combine via mp.  The "fully internal" Provable-only chain
-- (where the hypothesis  f(x) = y  is itself a Provable assumption,
-- not a meta Deriv) requires the constructed Df combinator and is
-- deferred.
--
-- Provided lemmas:
--
--   provThm14E      : From  Deriv Triv eq , build a Provable atomic
--                     stating  thmT(trivCT)(enc(d)) = reify(codeEqn eq) .
--                     Where enc(d) = encT (thm14EV3 d).
--
--   provThm14EFor   : Convenience for constructed encodings: given a
--                     specific Term enc and a polymorphic-in-h Deriv
--                     showing thmT(trivCT)(enc) = reify(codeEqn eq),
--                     produce the Provable atomic.
--
--   provNec         : Necessitation for ProofE3 Triv eq (any concrete
--                     ProofE3 lifts to a Provable atomic).
--
-- No postulates, no holes.

module Guard.ProvableTh13 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical using (Triv ; trivCT ; trivCTDef)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; encT ; corr)
open import Guard.Formula
open import Guard.Provable

------------------------------------------------------------------------
-- provNec : necessitation lift of a concrete ProofE3 Triv eq.
--
-- ProofE3.corr is polymorphic in its ambient Deriv hypothesis, so the
-- atomic equation it asserts can be wrapped via fromDeriv at any
-- Provable-level hyp.
--
-- We bridge  reify(codeEqn Triv)  to  trivCT  using trivCTDef (since
-- trivCT is abstract in SubstTForPrecompClassical).

provNec : {hyp : Formula} {eq : Equation} ->
          (pe : ProofE3 Triv eq) ->
          Provable hyp
            (atomic (eqn (ap1 (thmT trivCT) (encT pe))
                         (reify (codeEqn eq))))
provNec {hyp} {eq} pe =
  fromDeriv corrTrivCT
  where
  -- corr pe is polymorphic in the ambient Deriv hyp; bridge the
  -- abstract trivCT to reify(codeEqn Triv) using trivCTDef.
  corrTrivCT : {h : Equation} ->
               Deriv h (eqn (ap1 (thmT trivCT) (encT pe))
                            (reify (codeEqn eq)))
  corrTrivCT {h} =
    eqSubst (\t -> Deriv h (eqn (ap1 (thmT t) (encT pe)) (reify (codeEqn eq))))
            (eqSym trivCTDef)
            (corr pe {h})

------------------------------------------------------------------------
-- provThm14E : meta-Th-13.  From a Triv-level Deriv, build the lifted
-- atomic asserting that the encoded proof's thmT-image is the encoded
-- conclusion.

provThm14E : {hyp : Formula} {eq : Equation} ->
             (d : Deriv Triv eq) ->
             Provable hyp
               (atomic (eqn (ap1 (thmT trivCT) (encT (thm14EV3 d)))
                            (reify (codeEqn eq))))
provThm14E d = provNec (thm14EV3 d)

------------------------------------------------------------------------
-- provThm14EFor : convenience for users who already have a polymorphic
-- Deriv.  Identical pattern, no thm14EV3 call.

provThm14EFor : {hyp : Formula} (enc : Term) (eq : Equation) ->
                ({h : Equation} ->
                  Deriv h (eqn (ap1 (thmT trivCT) enc)
                               (reify (codeEqn eq)))) ->
                Provable hyp
                  (atomic (eqn (ap1 (thmT trivCT) enc)
                               (reify (codeEqn eq))))
provThm14EFor enc eq d = fromDeriv d
