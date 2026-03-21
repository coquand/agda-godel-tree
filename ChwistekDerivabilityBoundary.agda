{-# OPTIONS --without-K --exact-split #-}

module ChwistekDerivabilityBoundary where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekProofExt

------------------------------------------------------------------------
-- A. Achieved meta-level derivability principles
------------------------------------------------------------------------

-- D1 (representability): from a Proof A, derive a ProofExt stating
-- that the encoded proof code checks to A.

D1-check :
  {A : Formula} ->
  (prf : Proof A) ->
  ProofExt (fceq (ccheck (clit (encodeProof prf))) (clit (encFormula A)))
D1-check = represent-check

-- D1 for the self-reference: the csub quine evaluates to the Goedel
-- sentence's own code.

D1-self :
  ProofExt (fceq (csub (clit phiCode) (clit phiCode))
                 (clit (encFormula GoedelSentence)))
D1-self = self-ref-proof

-- D2 (closure under mp): if p proves fimp A B and q proves A,
-- then the mp code proves B. This IS derivable from ax-eval.

mpCode : Code -> Code -> Code
mpCode p q = cnode (catom n33) (cnode p q)

-- Helper: checkProof of an mp code gives the consequent
mp-code-correct :
  (p q : Code) -> (A B : Formula) ->
  Eq (checkProof p) (just (fimp A B)) ->
  Eq (checkProof q) (just A) ->
  Eq (checkProof (mpCode p q)) (just B)
mp-code-correct p q A B hp hq =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ pf ->
              maybeBind (checkProof q) (\ qf ->
              matchMP pf qf)))
            hp)
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
              hq)
      (guardEq-self A B))

D2-mp :
  (p q : Code) -> (A B : Formula) ->
  Eq (checkProof p) (just (fimp A B)) ->
  Eq (checkProof q) (just A) ->
  ProofExt (fceq (ccheck (clit (mpCode p q))) (clit (encFormula B)))
D2-mp p q A B hp hq =
  ax-eval
    (ccheck (clit (mpCode p q)))
    (encFormula B)
    (eqCong (\ r -> maybeBind r (\ a -> just (encFormula a)))
            (mp-code-correct p q A B hp hq))

-- D2 from Proof witnesses (more convenient form)
D2-mp-proof :
  {A B : Formula} ->
  (pf1 : Proof (fimp A B)) ->
  (pf2 : Proof A) ->
  ProofExt (fceq (ccheck (clit (mpCode (encodeProof pf1) (encodeProof pf2))))
                 (clit (encFormula B)))
D2-mp-proof pf1 pf2 =
  D2-mp (encodeProof pf1) (encodeProof pf2) _ _
        (encodeProof-correct pf1) (encodeProof-correct pf2)

-- Soundness of the extended system (clean restatement)
soundness-ext : {A : Formula} -> ProofExt A -> TrueFormula A
soundness-ext = soundProofExt

------------------------------------------------------------------------
-- B. Internal provability formula (negated form)
------------------------------------------------------------------------

-- "A is not provable" = "for all proof codes p, checkProof(p) != encFormula(A)"
-- Since we lack existential quantification, this is the natural encoding.

NotProvForm : Formula -> Formula
NotProvForm A =
  fcAll (fimp (fceq (ccheck (cvar cvz)) (clit (encFormula A))) fbot)

-- GoedelSentence IS NotProvForm GoedelSentence (up to the csub quine).
-- More precisely:
-- GoedelSentence = fcAll (fimp (fceq (ccheck (cvar cvz))
--                                    (csub (clit phiCode) (clit phiCode)))
--                              fbot)
-- And csub (clit phiCode) (clit phiCode) evaluates to encFormula GoedelSentence.
-- So GoedelSentence is SEMANTICALLY equivalent to NotProvForm GoedelSentence,
-- but SYNTACTICALLY different (csub vs clit).

-- Consistency formula (reuse Con from ChwistekProofExt)
-- Con = fcAll (fimp (fceq (ccheck (cvar cvz)) (clit (encFormula fbot))) fbot)
-- Note: Con = NotProvForm fbot

------------------------------------------------------------------------
-- C. Candidate D3 statement (not derivable)
------------------------------------------------------------------------

-- D3 would say: from a proof code p proving A, derive a ProofExt
-- stating that the REPRESENTATION of "p proves A" is itself provable.
--
-- In code form: from Eq (checkProof p) (just A), derive
--   ProofExt (fceq (ccheck (clit q)) (clit (encFormula (fceq (ccheck (clit p)) (clit (encFormula A))))))
-- for some code q.
--
-- This requires q to be a proof code that the checker accepts for
-- the fceq formula. In the extended system, q would be the encoding
-- of the ax-eval proof. But the OLD checkProof doesn't handle ax-eval
-- codes (tag 36). And we don't have a checkProofExt.
--
-- So D3 at the meta-level would be:

D3Candidate : Set
D3Candidate =
  (p : Code) -> (A : Formula) ->
  Eq (checkProof p) (just A) ->
  Sigma Code (\ q ->
    Eq (checkProof q)
       (just (fceq (ccheck (clit p)) (clit (encFormula A)))))

-- D3Candidate is NOT derivable because:
-- The needed q would encode an ax-eval proof (tag 36).
-- But checkProof doesn't handle tag 36.
-- The old proof system has no rule that produces fceq formulas.

------------------------------------------------------------------------
-- D. Meta-level consequences of D1 + D2
------------------------------------------------------------------------

-- D1 applied to mp: if pf1 proves fimp A B and pf2 proves A,
-- then the encoded mp proof checks to B.

D1-D2-mp-result :
  {A B : Formula} ->
  (pf1 : Proof (fimp A B)) ->
  (pf2 : Proof A) ->
  ProofExt (fceq (ccheck (clit (encodeProof (mp pf1 pf2))))
                 (clit (encFormula B)))
D1-D2-mp-result pf1 pf2 = D1-check (mp pf1 pf2)

------------------------------------------------------------------------
-- E. Explicit boundary: what cannot be derived
------------------------------------------------------------------------

-- ACHIEVED:
--
-- 1. D1 (meta-level): Proof A → ProofExt (fceq (ccheck ...) (clit ...))
--    Given an old proof, the extended system can state that the
--    encoded proof code checks to the formula.
--
-- 2. D2 (meta-level): given OLD proof codes for fimp A B and A,
--    the extended system can state that the mp code checks to B.
--
-- 3. Self-reference (internal): ProofExt can prove the quine equality
--    csub(phiCode, phiCode) = encFormula(GoedelSentence).
--
-- 4. Soundness (meta-level): ProofExt A → TrueFormula A for all A.
--
-- 5. Goedel I (meta-level): MetaNot (Proof GoedelSentence).
--
-- NOT ACHIEVED:
--
-- 1. D3 (meta-level): cannot show that the PROOF of "p proves A"
--    is itself verifiable by checkProof. The ax-eval proof uses
--    tag 36, which checkProof doesn't handle.
--
-- 2. Internal D1/D2: the derivability conditions are META-LEVEL
--    rules (given Agda witnesses, produce ProofExt terms). They
--    are NOT internal theorems (formulas provable inside ProofExt).
--    For Goedel II, they must be internal.
--
-- 3. Con → GoedelSentence (internal): requires internalizing the
--    Goedel I proof. Even with D1 + D2, the argument needs D3.
--
-- 4. Goedel II: MetaNot (ProofExt Con) or ProofExt (fimp Con fbot).
--    Blocked by the above.
--
-- WHY D3 IS THE KEY BLOCKER:
--
-- The Goedel II proof (standard version) requires:
--   step 1: ⊢ G → ¬Prov(⌜G⌝)    (from the diagonal, available)
--   step 2: ⊢ Prov(⌜step 1⌝)     (by D1, available)
--   step 3: ⊢ Prov(⌜G⌝) → Prov(⌜¬Prov(⌜G⌝)⌝)  (by D2, available)
--   step 4: ⊢ Prov(⌜G⌝) → Prov(⌜Prov(⌜G⌝)⌝)   (by D3, NOT available)
--   step 5: combine to get ⊢ Prov(⌜G⌝) → Prov(⌜⊥⌝)
--   step 6: contrapositive: ⊢ Con → ¬Prov(⌜G⌝) = Con → G
--
-- D3 is needed at step 4 to show that provability of G implies
-- provability of the fact that G is provable. This is the
-- self-reflection principle that requires the system to verify
-- its own proofs of provability.
--
-- WHAT WOULD UNLOCK D3:
--
-- Option A: Define checkProofExt (handling tag 36) and define
--   evalCExpExt and GoedelSentenceExt using the extended checker.
--   Then D3 becomes derivable via ax-eval in the extended system.
--   But this requires redefining the Goedel sentence and all
--   self-reference machinery for the extended system.
--
-- Option B: Add a proof rule that allows the system to verify
--   its own ax-eval proofs. E.g., a rule that if evalCExp e = just c
--   (verified at the meta level), then checkProof (encode-ax-eval e c) = just (fceq e (clit c)).
--   This adds tag 36 to checkProof, making it checkProofExt.
--
-- Option C: Add an internal induction principle over proof codes
--   that lets the system reason about checkProof universally.
--
-- All options require extending the proof checker, which breaks
-- the separation between the stable Goedel I development and
-- the extended system.
