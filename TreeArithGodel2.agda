{-# OPTIONS --without-K --exact-split #-}

module TreeArithGodel2 where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import ChwistekProvability
  using (Bool; true; false; and; Maybe; nothing; just;
         maybeBind; maybeMap; eqNat; eqCode; eqNat-refl)
open import TreeArith
open import TreeArithTrack1
open import TreeArithInternal

------------------------------------------------------------------------
-- 1. Abstract Gödel II (Löb's theorem)
------------------------------------------------------------------------

record DerivabilityConditions : Set1 where
  field
    Form : Set
    Proof : Form -> Set
    Prov : Form -> Form
    bot : Form
    imp : Form -> Form -> Form
    axK : {A B : Form} -> Proof (imp A (imp B A))
    axS : {A B C : Form} -> Proof (imp (imp A (imp B C)) (imp (imp A B) (imp A C)))
    mp  : {A B : Form} -> Proof (imp A B) -> Proof A -> Proof B
    d1 : {A : Form} -> Proof A -> Proof (Prov A)
    d2 : {A B : Form} -> Proof (imp (Prov (imp A B)) (imp (Prov A) (Prov B)))
    d3 : {A : Form} -> Proof (imp (Prov A) (Prov (Prov A)))
    goedelSentence : Form
    goedelLeft  : Proof (imp goedelSentence (imp (Prov goedelSentence) bot))
    goedelRight : Proof (imp (imp (Prov goedelSentence) bot) goedelSentence)
    consistent : Proof bot -> EmptyTA

loeb-godel2 : (dc : DerivabilityConditions) ->
  let open DerivabilityConditions dc in
  Proof (imp (Prov bot) bot) -> EmptyTA
loeb-godel2 dc conProof = consistent proofOfBot
  where
  open DerivabilityConditions dc
  G : Form
  G = goedelSentence

  comp : {A B C : Form} -> Proof (imp A B) -> Proof (imp B C) -> Proof (imp A C)
  comp {A} {B} {C} fab fbc = mp (mp axS (mp axK fbc)) fab

  pair : {A B C D : Form} -> Proof (imp A B) -> Proof (imp A C) ->
    Proof (imp B (imp C D)) -> Proof (imp A D)
  pair {A} {B} {C} {D} fab fac fbcd = mp (mp axS (comp fab fbcd)) fac

  provGL : Proof (Prov (imp G (imp (Prov G) bot)))
  provGL = d1 goedelLeft

  step1 : Proof (imp (Prov G) (Prov (imp (Prov G) bot)))
  step1 = mp d2 provGL

  provG-to-provBot : Proof (imp (Prov G) (Prov bot))
  provG-to-provBot = pair step1 d3 d2

  provG-to-bot : Proof (imp (Prov G) bot)
  provG-to-bot = comp provG-to-provBot conProof

  proofOfG : Proof G
  proofOfG = mp goedelRight provG-to-bot

  proofOfProvG : Proof (Prov G)
  proofOfProvG = d1 proofOfG

  proofOfBot : Proof bot
  proofOfBot = mp provG-to-bot proofOfProvG

------------------------------------------------------------------------
-- 2. Abstract encoding interface
------------------------------------------------------------------------

-- Tag numbers for FormTA3 and CodeTm encodings
private
  n100t : Nat
  n100t = suc (suc (suc (suc (suc n95))))

  n110t : Nat
  n110t = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n100t)))))))))

encCodeTm : CodeTm -> Code
encCodeTm (ctVar n)      = cnode (catom n100t) (catom n)
encCodeTm (ctAtom n)     = cnode (catom (suc n100t)) (catom n)
encCodeTm (ctNode a b)   = cnode (catom (suc (suc n100t))) (cnode (encCodeTm a) (encCodeTm b))
encCodeTm (ctCase t a n) = cnode (catom (suc (suc (suc n100t)))) (cnode (encCodeTm t) (cnode (encCodeTm a) (encCodeTm n)))
encCodeTm (ctFold t a n) = cnode (catom (suc (suc (suc (suc n100t))))) (cnode (encCodeTm t) (cnode (encCodeTm a) (encCodeTm n)))
encCodeTm (ctEqNat a b)  = cnode (catom (suc (suc (suc (suc (suc n100t)))))) (cnode (encCodeTm a) (encCodeTm b))
encCodeTm (ctIf c t e)   = cnode (catom (suc (suc (suc (suc (suc (suc n100t))))))) (cnode (encCodeTm c) (cnode (encCodeTm t) (encCodeTm e)))
encCodeTm (ctEqCode a b) = cnode (catom (suc (suc (suc (suc (suc (suc (suc n100t)))))))) (cnode (encCodeTm a) (encCodeTm b))

encFormTA3 : FormTA3 -> Code
encFormTA3 fbotTA3        = catom n110t
encFormTA3 (fimpTA3 a b)  = cnode (catom (suc n110t)) (cnode (encFormTA3 a) (encFormTA3 b))
encFormTA3 (fallTA3 a)    = cnode (catom (suc (suc n110t))) (encFormTA3 a)
encFormTA3 (fexTA3 a)     = cnode (catom (suc (suc (suc n110t)))) (encFormTA3 a)
encFormTA3 (feqTA3 t1 t2) = cnode (catom (suc (suc (suc (suc n110t))))) (cnode (encCodeTm t1) (encCodeTm t2))

-- Key property: encFormTA3 is injective (different formulas get different codes).
-- This is because each constructor has a unique tag and the recursion is structural.
-- We don't prove this but note it holds by construction.

------------------------------------------------------------------------
-- 3. Internal provability predicate
------------------------------------------------------------------------

Prov3 : FormTA3 -> FormTA3
Prov3 A = fexTA3 (feqTA3 checkCT-full (liftCode (encFormTA3 A)))

-- Internal consistency statement:
Con3 : FormTA3
Con3 = fimpTA3 (Prov3 fbotTA3) fbotTA3

------------------------------------------------------------------------
-- 4. Conditional Gödel II for ProofTA3
------------------------------------------------------------------------

-- This is the concrete theorem: ProofTA3 cannot prove Con3,
-- given that the derivability conditions hold and a Gödel sentence exists.

godel2-TA3 :
  -- D1 for ProofTA3 (meta-level, as in the abstract record):
  (d1-3 : {A : FormTA3} -> ProofTA3 A -> ProofTA3 (Prov3 A)) ->
  -- D2 for ProofTA3 (internal provability compositionality):
  (d2-3 : {A B : FormTA3} -> ProofTA3 (fimpTA3 (Prov3 (fimpTA3 A B)) (fimpTA3 (Prov3 A) (Prov3 B)))) ->
  -- D3 for ProofTA3 (internal provability self-awareness):
  (d3-3 : {A : FormTA3} -> ProofTA3 (fimpTA3 (Prov3 A) (Prov3 (Prov3 A)))) ->
  -- Gödel sentence with diagonal properties:
  (G : FormTA3) ->
  (gL : ProofTA3 (fimpTA3 G (fimpTA3 (Prov3 G) fbotTA3))) ->
  (gR : ProofTA3 (fimpTA3 (fimpTA3 (Prov3 G) fbotTA3) G)) ->
  -- Consistency of ProofTA3:
  (con3 : ProofTA3 fbotTA3 -> EmptyTA) ->
  -- CONCLUSION: ProofTA3 does not prove Con3.
  ProofTA3 Con3 -> EmptyTA
godel2-TA3 d1-3 d2-3 d3-3 G gL gR con3 =
  loeb-godel2 (record
    { Form = FormTA3
    ; Proof = ProofTA3
    ; Prov = Prov3
    ; bot = fbotTA3
    ; imp = fimpTA3
    ; axK = axK3 _ _
    ; axS = axS3 _ _ _
    ; mp = mp3
    ; d1 = d1-3
    ; d2 = d2-3
    ; d3 = d3-3
    ; goedelSentence = G
    ; goedelLeft = gL
    ; goedelRight = gR
    ; consistent = con3
    })

------------------------------------------------------------------------
-- 5. Status of each condition
------------------------------------------------------------------------

-- con3 (consistency): PROVABLE.
-- All ProofTA3 axioms are sound under GoodTA3.
-- GoodTA3 f env fbotTA3 = EmptyTA (uninhabited).
-- A full soundness proof would verify each axiom constructor.
-- The axK3, axS3, mp3 cases follow GoodTA's pattern.
-- The computation axioms hold because evalCT satisfies them.
-- Here we prove a representative case:

con3-axRefl : (f : Nat) -> (env : Env3) -> (t : CodeTm) -> GoodTA3 f env (feqTA3 t t)
con3-axRefl f env t = refl

-- d1-3 (D1 for ProofTA3):
-- Given ProofTA3 A, construct ProofTA3 (Prov3 A).
-- Prov3 A = fexTA3 (feqTA3 checkCT-full (liftCode (encFormTA3 A))).
-- Need: a code c such that checkCT-full applied to c gives encFormTA3 A.
-- This requires an extended checker (checkCT3-full) that handles ProofTA3 rules.
-- The code c = encProofTA3 prf (encoding of the ProofTA3 derivation).
--
-- STATUS: requires checkCT3-full and foldCorrect3.
-- Same pattern as Track 1 but for the extended system.
-- Estimated: ~400 lines following established patterns.

-- d2-3 (D2 for ProofTA3):
-- ProofTA3 proves: Prov(A->B) -> Prov(A) -> Prov(B).
-- This is an INTERNAL proof about existentially quantified checker witnesses.
-- From witness c1 with check(c1) = enc(A->B) and c2 with check(c2) = enc(A),
-- build c3 with check(c3) = enc(B).
-- The witness c3 encodes modus ponens: cnode (catom mp-tag) (cnode c1 c2).
-- This requires internal reasoning about the checker's mp handling.
--
-- STATUS: requires ProofTA3 to prove facts about checkCT-full's behavior.
-- Uses the computation axioms (axCaseAtom, axIfTrue, etc.) to trace
-- the mp dispatch step by step inside the proof system.
-- Estimated: ~100 lines.

-- d3-3 (D3 for ProofTA3):
-- ProofTA3 proves: Prov(A) -> Prov(Prov(A)).
-- Given witness c with check(c) = enc(A), build witness c' with
-- check(c') = enc(Prov(A)) = encFormTA3 (Prov3 A).
-- The witness c' encodes the D1 derivation applied to c.
-- This is the representability/self-awareness condition.
--
-- STATUS: same as d1-3, requires checkCT3-full and internal verification.
-- Estimated: ~200 lines.

-- G + gL + gR (diagonal lemma):
-- Construct G such that G ↔ ¬Prov(G).
-- Standard diagonal construction using representable substitution.
-- The substitution function sub(enc(A), c) = enc(A[c/v0]) must be
-- expressible as a CodeTm and verified by the computation axioms.
--
-- STATUS: requires defining the substitution CodeTm (~50 lines)
-- and proving its correctness using computation axioms (~100 lines).
-- Then G = A[enc(A)/v0] for appropriate A. Standard construction.

------------------------------------------------------------------------
-- 6. Precise remaining work
------------------------------------------------------------------------

-- Total estimated remaining work for unconditional Gödel II:
--
-- 1. checkCT3-full (checker for ProofTA3): ~200 lines
--    - Add tags for each ProofTA3 constructor
--    - Extend ncFull with dispatch for new tags
--
-- 2. foldCorrect3 (correctness of extended checker): ~300 lines
--    - Same pattern as foldCorrect in TreeArithTrack1
--    - One case per ProofTA3 constructor
--
-- 3. d1-3 (D1 for ProofTA3): ~50 lines
--    - Use foldCorrect3 + existential introduction
--
-- 4. d2-3 (internal D2): ~100 lines
--    - ProofTA3 derivation using computation axioms
--    - Traces the mp dispatch of the checker
--
-- 5. d3-3 (internal D3): ~200 lines
--    - ProofTA3 derivation using computation axioms
--    - Traces the D1 encoding inside the checker
--
-- 6. Diagonal lemma: ~150 lines
--    - Substitution CodeTm + correctness
--    - Gödel sentence construction
--
-- Total: ~1000 lines, all following established patterns.
-- No new mathematical ideas. All patterns demonstrated in Track 1.
--
-- The ABSTRACT Gödel II theorem (loeb-godel2) is proved.
-- The CONDITIONAL concrete theorem (godel2-TA3) is proved.
-- The UNCONDITIONAL concrete theorem requires the bootstrap above.
