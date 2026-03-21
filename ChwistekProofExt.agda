{-# OPTIONS --without-K --exact-split #-}

module ChwistekProofExt where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness

------------------------------------------------------------------------
-- A. Extended proof system
------------------------------------------------------------------------

-- ProofExt extends Proof with:
-- - ax-eval: reflect evalCExp results into fceq proofs
-- - mpE, genE, cgenE: structural rules (needed to combine with ax-eval)
-- - base: embed old proofs

data ProofExt : Formula -> Set where
  base    : {A : Formula} -> Proof A -> ProofExt A
  ax-eval : (e : CExp) -> (c : Code) ->
            Eq (evalCExp e) (just c) ->
            ProofExt (fceq e (clit c))
  mpE     : {A B : Formula} -> ProofExt (fimp A B) -> ProofExt A -> ProofExt B
  genE    : {A : Formula} -> ProofExt A -> ProofExt (fall A)
  cgenE   : {A : Formula} -> ProofExt A -> ProofExt (fcAll A)

------------------------------------------------------------------------
-- B. Soundness of the extended system
------------------------------------------------------------------------

-- evalCExp-env-closed: for closed CExps (where evalCExp succeeds),
-- evalCExpEnv gives the same result as evalCExp.
-- We prove this for the specific patterns used by ax-eval.

-- Key observation: evalCExpEnv cenv (clit c) = just c = evalCExp (clit c).
-- For ccheck (clit p): both reduce to maybeBind (checkProof p) (...).
-- For csub (clit c1) (clit c2): both reduce identically since clit
-- doesn't depend on the environment.

-- For soundness, we prove the general case by transport.

soundProofExt : {A : Formula} -> ProofExt A -> TrueFormula A

soundProofExt (base prf) = soundProof prf

soundProofExt (ax-eval e c eq) tenv cenv =
  mkSigma c (mkProd (evalCExpEnv-closed e c cenv eq) refl)
  where
  -- evalCExpEnv agrees with evalCExp for closed expressions.
  -- If evalCExp e' = just c', then evalCExpEnv cv e' = just c'.
  -- Proof by structural induction on CExp.
  evalCExpEnv-closed :
    (e' : CExp) -> (c' : Code) -> (cv : CEnv) ->
    Eq (evalCExp e') (just c') ->
    Eq (evalCExpEnv cv e') (just c')
  evalCExpEnv-closed (cvar _) _ _ ()
  evalCExpEnv-closed (clit _) c' cv eq' = eq'
  evalCExpEnv-closed (ccheck e') c' cv eq' =
    chkH (evalCExp e') refl eq'
    where
    cont : Code -> Maybe Code
    cont p = maybeBind (checkProof p) (\ a -> just (encFormula a))
    chkH : (r : Maybe Code) -> Eq (evalCExp e') r ->
           Eq (maybeBind r cont) (just c') ->
           Eq (maybeBind (evalCExpEnv cv e') cont) (just c')
    chkH nothing  er ()
    chkH (just v) er h =
      eqTrans
        (eqCong (\ s -> maybeBind s cont)
                (evalCExpEnv-closed e' v cv er))
        h
  evalCExpEnv-closed (csub e1 e2) c' cv eq' =
    subH (evalCExp e1) refl eq'
    where
    subH : (r1 : Maybe Code) -> Eq (evalCExp e1) r1 ->
           Eq (maybeBind r1 (\ c1 ->
               maybeBind (evalCExp e2) (\ c2 ->
               maybeBind (decFormula c1) (\ a ->
               just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c') ->
           Eq (maybeBind (evalCExpEnv cv e1) (\ c1 ->
               maybeBind (evalCExpEnv cv e2) (\ c2 ->
               maybeBind (decFormula c1) (\ a ->
               just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c')
    subH nothing  er1 ()
    subH (just v1) er1 h1 =
      eqTrans
        (eqCong (\ s -> maybeBind s (\ c1 ->
                  maybeBind (evalCExpEnv cv e2) (\ c2 ->
                  maybeBind (decFormula c1) (\ a ->
                  just (encFormula (substFormulaCode0 (clit c2) a))))))
                (evalCExpEnv-closed e1 v1 cv er1))
        (subH2 (evalCExp e2) refl h1)
      where
      subH2 : (r2 : Maybe Code) -> Eq (evalCExp e2) r2 ->
              Eq (maybeBind r2 (\ c2 ->
                  maybeBind (decFormula v1) (\ a ->
                  just (encFormula (substFormulaCode0 (clit c2) a))))) (just c') ->
              Eq (maybeBind (evalCExpEnv cv e2) (\ c2 ->
                  maybeBind (decFormula v1) (\ a ->
                  just (encFormula (substFormulaCode0 (clit c2) a))))) (just c')
      subH2 nothing  er2 ()
      subH2 (just v2) er2 h2 =
        eqTrans
          (eqCong (\ s -> maybeBind s (\ c2 ->
                    maybeBind (decFormula v1) (\ a ->
                    just (encFormula (substFormulaCode0 (clit c2) a)))))
                  (evalCExpEnv-closed e2 v2 cv er2))
          h2

soundProofExt (mpE pf1 pf2) tenv cenv =
  soundProofExt pf1 tenv cenv (soundProofExt pf2 tenv cenv)

soundProofExt (genE pf) tenv cenv =
  \ t -> soundProofExt pf (extendTEnv tenv t) cenv

soundProofExt (cgenE pf) tenv cenv =
  \ c -> soundProofExt pf tenv (extendCEnv cenv c)

------------------------------------------------------------------------
-- C. First derivability condition (representability)
------------------------------------------------------------------------

-- From a Proof A (old system), we can derive a ProofExt stating that
-- the encoded proof checks to A. This is the first Hilbert-Bernays
-- derivability condition.

represent-check :
  {A : Formula} ->
  (prf : Proof A) ->
  ProofExt (fceq (ccheck (clit (encodeProof prf))) (clit (encFormula A)))
represent-check prf =
  ax-eval
    (ccheck (clit (encodeProof prf)))
    (encFormula A)
    (eqCong (\ r -> maybeBind r (\ a -> just (encFormula a)))
            (encodeProof-correct prf))
  where
  A : Formula
  A = proofFormula prf
    where
    proofFormula : {X : Formula} -> Proof X -> Formula
    proofFormula {X} _ = X

------------------------------------------------------------------------
-- D. Self-reference as a ProofExt fact
------------------------------------------------------------------------

-- The csub self-reference can now be internalized as a ProofExt:

self-ref-proof :
  ProofExt (fceq (csub (clit phiCode) (clit phiCode))
                 (clit (encFormula GoedelSentence)))
self-ref-proof =
  ax-eval
    (csub (clit phiCode) (clit phiCode))
    (encFormula GoedelSentence)
    GoedelSentence-self-ref

------------------------------------------------------------------------
-- E. Consistency formula
------------------------------------------------------------------------

-- Con says: no proof code (in the old system) proves fbot
Con : Formula
Con =
  fcAll
    (fimp
      (fceq (ccheck (cvar cvz)) (clit (encFormula fbot)))
      fbot)

------------------------------------------------------------------------
-- F. Goedel I for the extended system
------------------------------------------------------------------------

-- GoedelSentence talks about the OLD checkProof (via evalCExp/ccheck).
-- soundProofExt gives: ProofExt GoedelSentence -> TrueFormula GoedelSentence.
-- TrueFormula GoedelSentence means: for all c, if OLD checkProof c = just GoedelSentence,
-- then Empty.
--
-- For goedel1-ext, we need: ProofExt GoedelSentence -> Empty.
-- This requires finding a specific c where checkProof c = just GoedelSentence.
-- For proofs built ONLY from base, encodeProof gives such a c.
-- For proofs using ax-eval, the encoded proof might use tag 36 which
-- the old checkProof doesn't handle.
--
-- However, we can prove a slightly weaker but still valuable result:
-- any ProofExt GoedelSentence gives TrueFormula GoedelSentence,
-- which is "no old code proves GoedelSentence." This is the semantic
-- content of GoedelSentence being true.

goedelSentence-true-if-provable :
  ProofExt GoedelSentence -> TrueFormula GoedelSentence
goedelSentence-true-if-provable = soundProofExt

-- For proofs built only from base constructors (old system):

-- goedel1-final from ChwistekSoundness already gives:
--   MetaNot (Proof GoedelSentence)
-- where MetaNot A = A -> Empty (from ChwistekSoundness)

------------------------------------------------------------------------
-- G. Analysis: what is needed for Goedel II
------------------------------------------------------------------------

-- STATUS: The extended system has the first derivability condition
-- (represent-check) and the self-reference internalized as a proof
-- (self-ref-proof).
--
-- For Goedel II (MetaNot (ProofExt Con)), the classical argument
-- requires:
--
--   1. ProofExt (fimp Con GoedelSentence)  [Con implies G internally]
--   2. ProofExt (fimp GoedelSentence fbot) [G implies false internally]
--   3. From ProofExt Con: by mpE twice, ProofExt fbot
--   4. But soundProofExt (ProofExt fbot) gives TrueF ... fbot = Empty
--   5. Contradiction.
--
-- Step 2 is the INTERNAL formalization of Goedel I. It requires the
-- proof system to reason about its own soundness:
--   "if GoedelSentence is provable, then fbot is provable"
-- This needs the proof system to:
--   a. Verify that a proof code checks to GoedelSentence
--   b. Instantiate GoedelSentence's universal quantifier at that code
--   c. Derive the code equality (via self-reference)
--   d. Apply modus ponens to get fbot
--
-- Steps (a) and (c) are covered by ax-eval / represent-check.
-- Step (b) requires cinst (universal elimination for fcAll).
-- Step (d) requires mpE.
--
-- But the full argument also requires INTERNALIZING soundness itself:
-- the system must prove that every provable formula is true, which
-- is a second-order property the system cannot prove about itself
-- (this is exactly what Goedel II says).
--
-- Step 1 (Con → G) requires the system to formalize:
--   "if no code proves fbot, then no code proves G"
-- This is the CONTRAPOSITIVE of:
--   "if some code proves G, then some code proves fbot"
-- Which is the internal Goedel I argument — again requiring internal
-- soundness.
--
-- CONCLUSION:
--   The current extended system has the REPRESENTABILITY infrastructure
--   (first derivability condition) but lacks the means to internalize
--   the full soundness argument. This is the known fundamental barrier
--   for Goedel II: the system cannot prove its own soundness.
--
--   Adding cinst (fcAll elimination) and fceq transitivity would give
--   more proof-theoretic power but would NOT overcome this barrier,
--   because the barrier is about INTERNALIZING INDUCTION over proof
--   codes, not about specific proof rules.
--
--   This confirms the classical situation: Goedel I is a theorem,
--   Goedel II requires strictly more (the derivability conditions
--   D2 and D3, which amount to the system proving facts about its
--   own proof predicate).
