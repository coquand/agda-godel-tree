{-# OPTIONS --without-K --exact-split #-}

module TreeArithC where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekSoundness using (eqSym)
open import TreeArith

private
  eqSub : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
  eqSub P refl px = px

------------------------------------------------------------------------
-- D1: if ⊢ A then Provable(A)
------------------------------------------------------------------------

-- ProvC = exists fuel and code such that checkTA accepts
ProvC : FormTA -> Set
ProvC A = SigmaTA Nat (\ n -> SigmaTA Code (\ c -> Eq (checkTA n c) (just A)))

-- D1 for axioms (using existing witnesses from TreeArith)
d1-axRefl : (c : Code) -> ProvC (feqTA c c)
d1-axRefl c = mkSigmaTA (suc zero) (mkSigmaTA (encProofTA (axReflTA c)) (encodeTA-axRefl c))

d1-axK : (A B : FormTA) -> ProvC (fimpTA A (fimpTA B A))
d1-axK A B = mkSigmaTA (suc zero) (mkSigmaTA (encProofTA (axKTA A B)) (encodeTA-axK A B))

d1-axS : (A B C : FormTA) -> ProvC (fimpTA (fimpTA A (fimpTA B C)) (fimpTA (fimpTA A B) (fimpTA A C)))
d1-axS A B C = mkSigmaTA (suc zero) (mkSigmaTA (encProofTA (axSTA A B C)) (encodeTA-axS A B C))

-- D1 STATUS: PARTIAL. Proved for axioms. mp/gen/inst need checkTA-mono (~100 lines).

------------------------------------------------------------------------
-- D2: Prov(A->B) -> Prov(A) -> Prov(B)
------------------------------------------------------------------------

-- D2 at same fuel level
private
  eqFormTA-r : (f : FormTA) -> Eq (eqFormTA f f) true
  eqFormTA-r fbotTA = refl
  eqFormTA-r (fatomTA n) = eqNat-refl n
  eqFormTA-r (fimpTA a b) = ab (eqFormTA a a) (eqFormTA b b) (eqFormTA-r a) (eqFormTA-r b)
    where ab : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          ab true true refl refl = refl
  eqFormTA-r (fallTA a) = eqFormTA-r a
  eqFormTA-r (feqTA c1 c2) = ab (eqCode c1 c1) (eqCode c2 c2) (ec c1) (ec c2)
    where
    ec : (c : Code) -> Eq (eqCode c c) true
    ec (catom n) = eqNat-refl n
    ec (cnode a b) = ab2 (eqCode a a) (eqCode b b) (ec a) (ec b)
      where ab2 : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
            ab2 true true refl refl = refl
    ab : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
    ab true true refl refl = refl

  mpSelf : (A B : FormTA) -> Eq (matchMPTA (fimpTA A B) A) (just B)
  mpSelf A B = eqSub (\ v -> Eq (boolGuardTA v (just B)) (just B)) (eqSym (eqFormTA-r A)) refl

d2-same-fuel : (n : Nat) -> (c1 c2 : Code) -> (A B : FormTA) ->
  Eq (checkTA n c1) (just (fimpTA A B)) -> Eq (checkTA n c2) (just A) ->
  Eq (checkTA (suc n) (cnode (catom n92) (cnode c1 c2))) (just B)
d2-same-fuel n c1 c2 A B h1 h2 =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ f1 ->
              maybeBind (checkTA n c2) (\ f2 -> matchMPTA f1 f2))) h1)
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ f2 -> matchMPTA (fimpTA A B) f2)) h2)
      (mpSelf A B))

-- D2 STATUS: ESSENTIALLY PROVED (same-fuel version). Full Sigma needs checkTA-mono.

------------------------------------------------------------------------
-- D3: Prov(A) -> Prov("Prov(A)")   [DECISIVE]
------------------------------------------------------------------------

-- D3 requires expressing "Prov(A)" as a FormTA formula.
-- Prov(A) = exists n c, checkTA n c = just A   (a Sigma type in Agda)
--
-- FormTA has: fbotTA, fatomTA, fimpTA, fallTA, feqTA.
-- fallTA gives UNIVERSAL quantification over codes.
-- There is NO existential quantifier in FormTA.
--
-- "Prov(A)" is an EXISTENTIAL statement. FormTA cannot express it.
--
-- Even if we encode the checker result as a Code (totalized checker):
--   checkTATotal : Nat -> Code -> Code
-- and express "checkTATotal n c = encFormTA A" via feqTA:
--   feqTA (checkTATotal n c) (encFormTA A)
-- we still need to EXISTENTIALLY quantify over n and c.
-- fallTA only gives universal quantification.
--
-- D3 requires: from Prov(A), produce Prov("Prov(A)").
-- But "Prov(A)" as a FormTA formula requires existentials.
-- FormTA has no existentials.

-- D3 STATUS: NOT FORMULABLE.
-- Missing ingredient: existential quantifier in FormTA.

------------------------------------------------------------------------
-- Classification table
------------------------------------------------------------------------

-- | Condition | Status          | Theorem proved         | Missing ingredient              |
-- |-----------|-----------------|------------------------|---------------------------------|
-- | D1        | PARTIAL         | d1-axRefl/axK/axS      | checkTA-mono for mp/gen/inst    |
-- | D2        | ESSENTIALLY YES | d2-same-fuel           | checkTA-mono for Sigma version  |
-- | D3        | NOT FORMULABLE  | (none)                 | Existential quantifier in FormTA|

------------------------------------------------------------------------
-- Relation to Goedel II
------------------------------------------------------------------------

-- D3 is NOT FORMULABLE. Standard Goedel II (D1+D2+D3 -> fixed point)
-- does NOT apply to this system in the usual way.
--
-- The model-theoretic route (GoodTA soundness) STILL blocks Con
-- independently of D3.
--
-- To make D3 formulable: add existential quantifier to FormTA.
-- Then D3 becomes a real question (can the system prove its own
-- self-awareness?). This is a precise, actionable next step.
