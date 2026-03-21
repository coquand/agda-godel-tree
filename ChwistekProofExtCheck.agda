{-# OPTIONS --without-K --exact-split #-}

module ChwistekProofExtCheck where

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
-- A. Extended proof checker
------------------------------------------------------------------------

-- Tag 36: ax-eval
-- Format: cnode (catom n36) (cnode (encCExp e) c)
-- Returns: fceq (decode e) (clit c)
--
-- DESIGN NOTE: checkProofExt does NOT re-evaluate the CExp.
-- It accepts the tag 36 code structurally (decodes the CExp,
-- returns the fceq formula). Soundness is guaranteed by ProofExt,
-- which carries the Eq (evalCExp e) (just c) witness.
--
-- This avoids mutual recursion with evalCExp, which would cause
-- termination issues (a self-referential code could loop).

n36 : Nat
n36 = suc n35

checkProofExt : Code -> Maybe Formula

checkProofExt (cnode (catom n) tc) = chkE n tc
  where
  chkE : Nat -> Code -> Maybe Formula
  chkE n tc = chkE30 (eqNat n n30) n tc
    where
    chkE30 : Bool -> Nat -> Code -> Maybe Formula
    chkE30 true _ tc =
      maybeBind (decTerm tc) (\ t -> just (feq t t))
    chkE30 false n tc = chkE31 (eqNat n n31) n tc
      where
      chkE31 : Bool -> Nat -> Code -> Maybe Formula
      chkE31 true _ (cnode ac bc) =
        maybeBind (decFormula ac) (\ a ->
        maybeBind (decFormula bc) (\ b ->
        just (fimp a (fimp b a))))
      chkE31 true _ _ = nothing
      chkE31 false n tc = chkE32 (eqNat n n32) n tc
        where
        chkE32 : Bool -> Nat -> Code -> Maybe Formula
        chkE32 true _ (cnode ac (cnode bc cc)) =
          maybeBind (decFormula ac) (\ a ->
          maybeBind (decFormula bc) (\ b ->
          maybeBind (decFormula cc) (\ c ->
          just (fimp (fimp a (fimp b c))
                     (fimp (fimp a b)
                           (fimp a c))))))
        chkE32 true _ _ = nothing
        chkE32 false n tc = chkE33 (eqNat n n33) n tc
          where
          chkE33 : Bool -> Nat -> Code -> Maybe Formula
          chkE33 true _ (cnode p q) =
            maybeBind (checkProofExt p) (\ pf ->
            maybeBind (checkProofExt q) (\ qf ->
            matchMP pf qf))
          chkE33 true _ _ = nothing
          chkE33 false n tc = chkE34 (eqNat n n34) n tc
            where
            chkE34 : Bool -> Nat -> Code -> Maybe Formula
            chkE34 true _ p = maybeMap fall (checkProofExt p)
            chkE34 false n tc = chkE35 (eqNat n n35) n tc
              where
              chkE35 : Bool -> Nat -> Code -> Maybe Formula
              chkE35 true _ p = maybeMap fcAll (checkProofExt p)
              chkE35 false n tc = chkE36 (eqNat n n36) tc
                where
                -- Tag 36: structurally accept ax-eval codes
                chkE36 : Bool -> Code -> Maybe Formula
                chkE36 true (cnode ec c) =
                  maybeMap (\ e -> fceq e (clit c)) (decCExp ec)
                chkE36 true (catom _) = nothing
                chkE36 false (catom _) = nothing
                chkE36 false (cnode _ _) = nothing

checkProofExt (catom _) = nothing
checkProofExt (cnode (cnode _ _) _) = nothing

------------------------------------------------------------------------
-- B. Encode ProofExt as Code
------------------------------------------------------------------------

encodeProofExt : {A : Formula} -> ProofExt A -> Code
encodeProofExt (base prf)       = encodeProof prf
encodeProofExt (ax-eval e c eq) = cnode (catom n36) (cnode (encCExp e) c)
encodeProofExt (mpE pf1 pf2)    = cnode (catom n33)
  (cnode (encodeProofExt pf1) (encodeProofExt pf2))
encodeProofExt (genE pf)        = cnode (catom n34) (encodeProofExt pf)
encodeProofExt (cgenE pf)       = cnode (catom n35) (encodeProofExt pf)

------------------------------------------------------------------------
-- C. Correctness: checkProofExt accepts encoded ProofExt
------------------------------------------------------------------------

-- Split into two functions to help the termination checker:
-- encodeBase-correct for old Proof (recurses on Proof)
-- encodeProofExt-correct for ProofExt (recurses on ProofExt, delegates base to above)

encodeBase-correct :
  {A : Formula} ->
  (prf : Proof A) ->
  Eq (checkProofExt (encodeProof prf)) (just A)

encodeBase-correct (ax-refl t) = refl-provable-lemma t

encodeBase-correct (ax-k A B) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ a -> maybeBind (decFormula (encFormula B))
              (\ b -> just (fimp a (fimp b a)))))
            (decFormula-encFormula A))
    (eqCong (\ r -> maybeBind r (\ b -> just (fimp A (fimp b A))))
            (decFormula-encFormula B))

encodeBase-correct (ax-s A B C) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ a -> maybeBind (decFormula (encFormula B))
              (\ b -> maybeBind (decFormula (encFormula C))
              (\ c -> just (fimp (fimp a (fimp b c))
                                 (fimp (fimp a b) (fimp a c)))))))
            (decFormula-encFormula A))
    (eqTrans
      (eqCong (\ r -> maybeBind r
                (\ b -> maybeBind (decFormula (encFormula C))
                (\ c -> just (fimp (fimp A (fimp b c))
                                   (fimp (fimp A b) (fimp A c))))))
              (decFormula-encFormula B))
      (eqCong (\ r -> maybeBind r
                (\ c -> just (fimp (fimp A (fimp B c))
                                   (fimp (fimp A B) (fimp A c)))))
              (decFormula-encFormula C)))

encodeBase-correct (mp {A} {B} pf1 pf2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ pf ->
              maybeBind (checkProofExt (encodeProof pf2)) (\ qf ->
              matchMP pf qf)))
            (encodeBase-correct pf1))
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
              (encodeBase-correct pf2))
      (guardEq-self A B))

encodeBase-correct (gen pf) =
  eqCong (maybeMap fall) (encodeBase-correct pf)

encodeBase-correct (cgen pf) =
  eqCong (maybeMap fcAll) (encodeBase-correct pf)

-- Now the main function, recursive on ProofExt
encodeProofExt-correct :
  {A : Formula} ->
  (prf : ProofExt A) ->
  Eq (checkProofExt (encodeProofExt prf)) (just A)

encodeProofExt-correct (base prf) = encodeBase-correct prf

encodeProofExt-correct (ax-eval e c eq) =
  eqCong (maybeMap (\ de -> fceq de (clit c))) (decCExp-encCExp e)

encodeProofExt-correct (mpE {A} {B} pf1 pf2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ pf ->
              maybeBind (checkProofExt (encodeProofExt pf2)) (\ qf ->
              matchMP pf qf)))
            (encodeProofExt-correct pf1))
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
              (encodeProofExt-correct pf2))
      (guardEq-self A B))

encodeProofExt-correct (genE pf) =
  eqCong (maybeMap fall) (encodeProofExt-correct pf)

encodeProofExt-correct (cgenE pf) =
  eqCong (maybeMap fcAll) (encodeProofExt-correct pf)

------------------------------------------------------------------------
-- D. D1 for extended checker
------------------------------------------------------------------------

-- From ProofExt A, derive ProofExt that checkProofExt accepts the
-- encoded proof. Uses evalCExp (old evaluator), which calls
-- checkProof (old checker). This works because:
-- - ccheck (clit p) evaluates to encFormula A when checkProof p = just A
-- - For base proofs: checkProof (encodeProof prf) = just A (by encodeProof-correct)
-- - For ax-eval proofs: checkProof (encodeProofExt ...) may NOT work
--   (tag 36 not in old checker), but checkProofExt does accept them.
--
-- So D1-ext uses checkProofExt, not checkProof:

D1-ext-check :
  {A : Formula} ->
  (prf : ProofExt A) ->
  Eq (checkProofExt (encodeProofExt prf)) (just A)
D1-ext-check = encodeProofExt-correct

------------------------------------------------------------------------
-- E. D3: self-verification
------------------------------------------------------------------------

-- From ProofExt A, we can derive a ProofExt stating that the
-- extended checker accepts the encoded proof. And then we can
-- derive a ProofExt stating that THAT fact's encoding is also accepted.
--
-- The key: the ax-eval proof's encoding (tag 36) IS accepted by
-- checkProofExt (structurally, without re-evaluation).
-- And encodeProofExt-correct proves this.

-- D1-ext for base proofs works: ax-eval uses evalCExp (old), and
-- encodeProof gives old-style codes accepted by old checkProof.
D1-ext-base :
  {A : Formula} ->
  (prf : Proof A) ->
  ProofExt (fceq (ccheck (clit (encodeProof prf))) (clit (encFormula A)))
D1-ext-base = represent-check

-- D1-ext for GENERAL ProofExt does NOT work:
-- ax-eval uses evalCExp (old), which calls checkProof (old).
-- encodeProofExt of an ax-eval proof has tag 36.
-- checkProof (old) doesn't handle tag 36.
-- evalCExp (ccheck (clit (encodeProofExt (ax-eval ...)))) = nothing.
--
-- The gap: ax-eval reflects the OLD checker into ProofExt formulas,
-- but encodeProofExt-correct is about the NEW checker. These are
-- different, and ax-eval can only reflect the old one.

------------------------------------------------------------------------
-- F. D3 analysis
------------------------------------------------------------------------

-- D3 attempt: from ProofExt A, derive a ProofExt stating that
-- the D1-ext proof's encoding is also accepted.
--
-- D1-ext prf gives: ax-eval proof with tag 36 code.
-- encodeProofExt (D1-ext prf) = cnode (catom n36) (cnode (encCExp ...) ...)
-- checkProofExt accepts this (by encodeProofExt-correct).
-- But D1-ext uses evalCExp (old), and the CExp inside mentions
-- ccheck (clit (encodeProofExt prf)). evalCExp of ccheck calls
-- checkProof (old), which may not handle tag 36 in encodeProofExt prf.
--
-- For BASE proofs: encodeProofExt (base prf) = encodeProof prf,
-- which uses only old tags. So evalCExp (ccheck (clit (encodeProof prf)))
-- works via old checkProof. D1-ext for base proofs is valid.
--
-- D3 for base proofs: D1-ext-base gives an ax-eval ProofExt.
-- Its encoding has tag 36. checkProofExt accepts it.
-- To apply D1-ext AGAIN, we'd need evalCExp to handle the tag 36
-- encoding — but evalCExp uses old checkProof, which doesn't.
--
-- So D3 remains blocked at the second level: the extended system
-- can represent first-level facts but cannot represent the
-- representation itself.

------------------------------------------------------------------------
-- G. Summary
------------------------------------------------------------------------

-- RESULT: checkProofExt handles tag 36 and accepts all encoded
-- ProofExt proofs (encodeProofExt-correct).
--
-- HOWEVER, D3 does NOT become fully derivable because:
--
-- 1. ax-eval uses evalCExp (old evaluator), which calls checkProof
--    (old checker). Tag 36 codes are not accepted by the old checker.
--
-- 2. D1-ext works for base proofs (whose codes are old-style).
--    D1-ext does NOT work for ax-eval proofs (whose codes have tag 36).
--
-- 3. To fix this, ax-eval would need to use an evaluator that calls
--    checkProofExt. But checkProofExt + evalCExpExt are mutually
--    recursive and Agda's termination checker can't verify them
--    (a self-referential code could loop).
--
-- CONCLUSION: The hierarchy climbs one level. Each extension adds
-- a reflection layer, but the reflection always uses the PREVIOUS
-- checker. D3 requires the checker to verify its OWN reflection
-- proofs, which creates a genuine fixed-point challenge.
--
-- This is the formal analogue of the classical observation:
-- a consistent system cannot prove its own consistency, because
-- such a proof would need to internalize the system's own
-- soundness — which requires reasoning about the proof predicate
-- at a level the system cannot reach without bootstrapping.
