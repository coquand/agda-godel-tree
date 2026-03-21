{-# OPTIONS --without-K --exact-split #-}

module ChwistekFuelGodel where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekFuelChecker

------------------------------------------------------------------------
-- A. Code-level representability for the fuel checker
------------------------------------------------------------------------

-- n36 (local, matching the one inside checkProofN's where clause)
n36' : Nat
n36' = suc n35

-- The key representability lemma:
-- From checkProofN (suc n) p = just A,
-- construct a code that checkProofN (suc (suc (suc n))) accepts
-- as a proof of fceq (ccheck (clit p)) (clit (encFormula A)).
--
-- The code is: cnode (catom n36) (cnode (encCExp (ccheck (clit p))) (encFormula A))
--
-- The proof chains through:
-- 1. decCExp (encCExp ...) = just (ccheck (clit p))
-- 2. evalCExpN (suc (suc n)) (ccheck (clit p)) = just (encFormula A)
-- 3. eqCode (encFormula A) (encFormula A) = true
-- 4. boolGuard true (just X) = just X

represent-fuel :
  (p : Code) (A : Formula) (n : Nat) ->
  Eq (checkProofN (suc n) p) (just A) ->
  Eq (checkProofN (suc (suc (suc n)))
       (cnode (catom n36') (cnode (encCExp (ccheck (clit p))) (encFormula A))))
     (just (fceq (ccheck (clit p)) (clit (encFormula A))))
represent-fuel p A n hyp =
  -- Step 1: abstract over decCExp
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ e -> boolGuard (eqMaybeCode (evalCExpN (suc (suc n)) e)
                                             (encFormula A))
                       (just (fceq e (clit (encFormula A))))))
            (decCExp-encCExp (ccheck (clit p))))
    -- After decCExp: goal is about boolGuard (eqMaybeCode (evalCExpN ...) ...) (just ...)
    -- Step 2: transport through evalCExpN result
    (eqSubst (\ v -> Eq (boolGuard (eqMaybeCode v (encFormula A))
                          (just (fceq (ccheck (clit p)) (clit (encFormula A)))))
                        (just (fceq (ccheck (clit p)) (clit (encFormula A)))))
      (eqSym (eqCong (\ r -> maybeBind r (\ a -> just (encFormula a))) hyp))
      -- Step 3: transport through eqCode-refl
      (eqSubst (\ b -> Eq (boolGuard b
                             (just (fceq (ccheck (clit p)) (clit (encFormula A)))))
                           (just (fceq (ccheck (clit p)) (clit (encFormula A)))))
        (eqSym (eqCode-refl (encFormula A)))
        refl))

------------------------------------------------------------------------
-- B. D3 falls out: self-reflection by re-application
------------------------------------------------------------------------

-- D3 is just represent-fuel applied to a D1 code.
-- Given checkProofN (suc n) p = just A:
-- 1. represent-fuel gives code q with checkProofN (suc (suc (suc n))) q = just (fceq ...)
-- 2. represent-fuel AGAIN gives code q' with checkProofN (suc (suc (suc (suc (suc (suc n)))))) q' = just (fceq ...)
-- Each application costs 3 fuel.

D1-fuel :
  (p : Code) (A : Formula) (n : Nat) ->
  Eq (checkProofN (suc n) p) (just A) ->
  Sigma Code (\ q ->
    Eq (checkProofN (suc (suc (suc n))) q)
       (just (fceq (ccheck (clit p)) (clit (encFormula A)))))
D1-fuel p A n hyp =
  mkSigma (cnode (catom n36') (cnode (encCExp (ccheck (clit p))) (encFormula A)))
          (represent-fuel p A n hyp)

-- D3: from D1, re-represent
D3-fuel :
  (p : Code) (A : Formula) (n : Nat) ->
  (hyp : Eq (checkProofN (suc n) p) (just A)) ->
  Sigma Code (\ q' ->
    Eq (checkProofN (suc (suc (suc (suc (suc n))))) q')
       (just (fceq (ccheck (clit (sigFst (D1-fuel p A n hyp))))
                   (clit (encFormula (fceq (ccheck (clit p))
                                          (clit (encFormula A))))))))
D3-fuel p A n hyp =
  let d1 = D1-fuel p A n hyp in
  D1-fuel (sigFst d1)
          (fceq (ccheck (clit p)) (clit (encFormula A)))
          (suc (suc n))
          (sigSnd d1)

------------------------------------------------------------------------
-- C. Comments
------------------------------------------------------------------------

-- RESULT: D1, D2 (via mp), and D3 are all available in the fuel system.
--
-- D1-fuel: from checkProofN (suc n) p = just A, produce a code
--   accepted by checkProofN (suc (suc (suc n))) as a proof of the
--   corresponding fceq formula. Cost: 3 fuel per level.
--
-- D3-fuel: from the same hypothesis, produce a code accepted at
--   fuel (suc^6 n) as a proof that the D1 representation is itself
--   represented. Cost: 6 fuel total from the base.
--
-- The hierarchy has COLLAPSED: unlike the stratified architecture
-- (where D3 was blocked by evalCExp being blind to tag 36),
-- the fuel-based checkProofN handles tag 36 at every fuel level.
-- Self-reflection works because the checker sees its own reflected
-- proofs.
--
-- KEY COMPARISON:
--   Stratified: evalCExp blind to tag 36 -> D3 fails -> strict hierarchy
--   Fuel-based: checkProofN handles tag 36 -> D3 works -> hierarchy collapses
--
-- NEXT: bounded Goedel I and II using this infrastructure.
-- The bounded Goedel sentence talks about checkProofN N for specific N.
-- Goedel II: from a "proof" of bounded consistency, derive bounded fbot.
