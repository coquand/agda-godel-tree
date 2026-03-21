{-# OPTIONS --without-K --exact-split #-}

module ChwistekGodelProof where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence

------------------------------------------------------------------------
-- A. Empty, negation, product
------------------------------------------------------------------------

data Empty : Set where

MetaNot : Set -> Set
MetaNot A = A -> Empty

absurd : {A : Set} -> Empty -> A
absurd ()

data Prod (A B : Set) : Set where
  mkProd : A -> B -> Prod A B

------------------------------------------------------------------------
-- B. Sigma projections
------------------------------------------------------------------------

sigFst : {A : Set} {B : A -> Set} -> Sigma A B -> A
sigFst (mkSigma x _) = x

sigSnd : {A : Set} {B : A -> Set} -> (s : Sigma A B) -> B (sigFst s)
sigSnd (mkSigma _ y) = y

------------------------------------------------------------------------
-- C. Direct truth types for the Goedel argument
------------------------------------------------------------------------

-- Instead of a general recursive TrueF (which fails termination),
-- we define the specific truth types needed for GoedelSentence.

-- TrueCodeEq e1 e2: both code expressions evaluate to the same code
TrueCodeEq : CExp -> CExp -> Set
TrueCodeEq e1 e2 =
  Sigma Code (\ c -> Prod (Eq (evalCExp e1) (just c))
                          (Eq (evalCExp e2) (just c)))

-- Truth of InstBody p = fimp (fceq (ccheck (clit p)) (csub ...)) fbot
-- i.e., TrueCodeEq -> Empty
TrueInstBody : Code -> Set
TrueInstBody p =
  TrueCodeEq (ccheck (clit p))
             (csub (clit phiCode) (clit phiCode)) -> Empty

-- Truth of GoedelSentence = fcAll GoedelBody
-- i.e., for all proof codes p, TrueInstBody p
TrueGoedel : Set
TrueGoedel = (p : Code) -> TrueInstBody p

------------------------------------------------------------------------
-- D. Key lemma: a proof code for GoedelSentence makes TrueCodeEq hold
------------------------------------------------------------------------

-- If checkProof p = just GoedelSentence, then:
--   evalCExp (ccheck (clit p))
--     = maybeBind (just p) (\ q -> maybeBind (checkProof q) (...))
--     = maybeBind (checkProof p) (\ a -> just (encFormula a))
--     = just (encFormula GoedelSentence)
--
-- And by GoedelSentence-self-ref:
--   evalCExp (csub (clit phiCode) (clit phiCode))
--     = just (encFormula GoedelSentence)

check-eval-lemma :
  (p : Code) ->
  Eq (checkProof p) (just GoedelSentence) ->
  Eq (evalCExp (ccheck (clit p))) (just (encFormula GoedelSentence))
check-eval-lemma p hyp =
  eqCong (\ r -> maybeBind r (\ a -> just (encFormula a))) hyp

check-enc-goedel :
  (p : Code) ->
  Eq (checkProof p) (just GoedelSentence) ->
  TrueCodeEq (ccheck (clit p)) (csub (clit phiCode) (clit phiCode))
check-enc-goedel p hyp =
  mkSigma (encFormula GoedelSentence)
    (mkProd (check-eval-lemma p hyp) GoedelSentence-self-ref)

------------------------------------------------------------------------
-- E. Soundness assumption
------------------------------------------------------------------------

-- GoedelSoundness: if GoedelSentence is provable, then it is true.
-- This is the meta-level soundness for this specific formula.

GoedelSoundness : Set
GoedelSoundness = ProvableFormula GoedelSentence -> TrueGoedel

------------------------------------------------------------------------
-- F. Goedel I (conditional on soundness)
------------------------------------------------------------------------

-- Proof:
--   1. Assume ProvableFormula GoedelSentence.
--   2. Extract witness p with checkProof p = just GoedelSentence.
--   3. By GoedelSoundness, obtain TrueGoedel.
--   4. TrueGoedel = (q : Code) -> TrueInstBody q.
--   5. Instantiate at q = p: get TrueInstBody p.
--   6. TrueInstBody p = TrueCodeEq ... -> Empty.
--   7. By check-enc-goedel, construct TrueCodeEq.
--   8. Apply step 6 to step 7: obtain Empty.

goedel1 :
  GoedelSoundness ->
  MetaNot (ProvableFormula GoedelSentence)
goedel1 sound prov =
  contradiction (sigFst prov) (sigSnd prov)
  where
  contradiction : (p : Code) -> Eq (checkProof p) (just GoedelSentence) -> Empty
  contradiction p hyp = sound prov p (check-enc-goedel p hyp)

------------------------------------------------------------------------
-- G. Consistency corollary
------------------------------------------------------------------------

Consistent : Set
Consistent = MetaNot (ProvableFormula fbot)

goedel1-consistent :
  GoedelSoundness ->
  Consistent ->
  MetaNot (ProvableFormula GoedelSentence)
goedel1-consistent sound cons = goedel1 sound

------------------------------------------------------------------------
-- H. Comments
------------------------------------------------------------------------

-- RESULT: Goedel I is proved conditional on GoedelSoundness.
--
-- GoedelSoundness says: if GoedelSentence is provable (via checkProof),
-- then it is true (TrueGoedel).
--
-- TrueGoedel says: for all proof codes p,
--   if evalCExp(ccheck(clit p)) = evalCExp(csub(clit phiCode)(clit phiCode))
--   then Empty.
--
-- i.e., no proof code's result equals the self-referential code of
-- GoedelSentence.
--
-- How the contradiction works:
--
--   Given a proof code p with checkProof p = just GoedelSentence:
--   - evalCExp(ccheck(clit p)) = just (encFormula GoedelSentence)
--     (because checkProof p returns GoedelSentence)
--   - evalCExp(csub(clit phiCode)(clit phiCode)) = just (encFormula GoedelSentence)
--     (by GoedelSentence-self-ref, the fixed-point property)
--   - So both sides evaluate to the same code: TrueCodeEq holds.
--   - But GoedelSoundness says exactly this situation implies Empty.
--   - Contradiction.
--
-- Where GoedelSentence-self-ref is used:
--
--   To show that csub(phiCode, phiCode) evaluates to encFormula(GoedelSentence).
--   This is the quine trick: GoedelSentence contains a computation that
--   produces its own encoding.
--
-- What GoedelSoundness means concretely:
--
--   It says: the proof system does not prove false claims about
--   code equality. If checkProof says formula A is provable, and
--   A = fcAll (fimp (fceq e1 e2) fbot), then it is not the case
--   that e1 and e2 evaluate to the same code. This is a fragment
--   of soundness: the proof system respects code-equality semantics.
--
-- Next steps:
--
--   1. Prove GoedelSoundness from a general soundness theorem for
--      the proof system with respect to code-equality semantics.
--   2. Alternatively, prove GoedelSoundness directly by induction
--      on proof codes (showing checkProof respects TrueCodeEq).
--   3. Goedel II: prove that the system cannot prove its own
--      consistency.
