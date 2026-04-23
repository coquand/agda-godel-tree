{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Prov -- provability predicate and combinators.
--
-- Per UNIFIED-DESIGN-REV2-5C.md step 2.  Prov packages an encoded
-- proof tree with its thmT-correctness witness.
--
-- Design note.  The spec signature for Prov is a plain Sigma:
--
--   Prov P = Sigma (e : Term) (Deriv (atomic (eqn (ap1 thmT e)
--                                             (reify (codeFormula P)))))
--
-- In order to compose proofs via the encoders from
-- Guard.ProofEncUnify / Guard.ProofEncFormula, each combinator needs
-- (i) a Pair decomposition of the encoded Term  e , and (ii) a
-- tag-opacity witness ("Pass") on  e  -- the fact that  e  is a
-- valid outer encoding, not a raw natCode.  Both pieces are
-- standard (every existing encoder satisfies them), so we bundle
-- them in the record  Prov  itself.  A plain Sigma view is
-- recovered via  provToSigma  for consumers who only need the
-- bare correctness witness.
--
-- Combinators exposed in this module:
--   provRefl   -- reflexivity             axRefl t.
--   provSym    -- symmetry                encRuleSym.
--   (more to come in a subsequent commit: provTrans, provCongL,
--    provCongR, provMp, provInst.)

module Guard.Prov where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForHF using (thmT ; ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3DefsUnify using (intermediateGenericV3)
open import Guard.ProofEncUnify using
  ( encAxRefl ; encAxReflCorr ; encAxReflPass
  ; encRuleSym ; encRuleSymCorr ; encRuleSymPass
  )

------------------------------------------------------------------------
-- The provability predicate (rich form).
--
-- Prov P packages:
--   * prov1, prov2      : the outer Pair components of the encoded
--                         proof tree.  (We always compose encoded
--                         proofs as  ap2 Pair prov1 prov2 .)
--   * provCorr          : thmT applied to the encoded tree yields
--                         the Gödel code of the formula being proved.
--   * provPass          : tag-opacity.  When used as the tag of a
--                         larger Pair, this encoding's head does not
--                         match any ndDispatchV3 branch, so dispatch
--                         falls through to sndArg2.

record Prov (P : Formula) : Set where
  constructor mkProv
  field
    prov1    : Term
    prov2    : Term
    provCorr : Deriv (eqF (ap1 thmT (ap2 Pair prov1 prov2))
                          (reify (codeFormula P)))
    provPass : (x rcs : Term) ->
      Deriv (eqF (ap2 ndDispatchV3
                       (ap2 Pair (ap2 Pair prov1 prov2) x) rcs)
                 (ap2 sndArg2
                       (ap2 Pair (ap2 Pair prov1 prov2) x) rcs))
open Prov public

------------------------------------------------------------------------
-- Full encoded Term of a proof.

provTerm : {P : Formula} -> Prov P -> Term
provTerm p = ap2 Pair (prov1 p) (prov2 p)

------------------------------------------------------------------------
-- Spec-level Sigma projection.

provToSigma : {P : Formula} -> Prov P ->
  Sigma Term (\ e -> Deriv (eqF (ap1 thmT e) (reify (codeFormula P))))
provToSigma p = mkSigma (provTerm p) (provCorr p)

------------------------------------------------------------------------
-- provRefl: reflexivity.  For any Term t, t = t is provable.
--
-- Uses encAxRefl / encAxReflCorr / encAxReflPass from
-- Guard.ProofEncUnify.
--
--   encAxRefl tC = ap2 Pair (reify (natCode n17)) (ap2 Pair tC O)
--
-- where tC = reify (code t).
-- Target codeFormula (atomic (eqn t t))
--      = codeEqn (eqn t t)
--      = nd (code t) (code t).
-- reify of that = ap2 Pair tC tC, which encAxReflCorr delivers.

provRefl : (t : Term) -> Prov (atomic (eqn t t))
provRefl t =
  let tC : Term ; tC = reify (code t) in
  mkProv
    (reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))
    (ap2 Pair tC O)
    (encAxReflCorr tC)
    (\ x rcs -> encAxReflPass t x rcs)

------------------------------------------------------------------------
-- provSym: symmetry.  From  t = u  conclude  u = t .
--
-- Wraps encRuleSym.  The input's  prov1 , prov2  become the
-- sub-encoding's  paR , pbR  for encRuleSymCorr; tC , uC  are the
-- reified codes of the equation's sides.
--
--   encRuleSym enc = ap2 Pair (reify (natCode n18))
--                             (ap2 Pair (reify tagVar) enc)
--
-- so the output's outer Pair decomposition is
--   prov1_out = reify (natCode n18)
--   prov2_out = ap2 Pair (reify tagVar) enc_in .

provSym : (t u : Term) -> Prov (atomic (eqn t u)) ->
          Prov (atomic (eqn u t))
provSym t u p =
  let paR : Term ; paR = prov1 p
      pbR : Term ; pbR = prov2 p
      tC  : Term ; tC  = reify (code t)
      uC  : Term ; uC  = reify (code u)
  in mkProv
       (reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))
       (ap2 Pair (reify tagVar) (ap2 Pair paR pbR))
       (encRuleSymCorr paR pbR tC uC (provCorr p))
       (\ x rcs -> encRuleSymPass paR pbR x rcs)
