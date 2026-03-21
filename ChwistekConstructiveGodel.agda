{-# OPTIONS --without-K --exact-split #-}

module ChwistekConstructiveGodel where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekFuelChecker
open import ChwistekFuelGodel
open import ChwistekFuelGodel2

------------------------------------------------------------------------
-- Extended proof system: ProofC = ProofN + cinst + fceq-trans + fceq-sym
------------------------------------------------------------------------

data ProofC (n : Nat) : Formula -> Set where
  baseC   : {A : Formula} -> Proof A -> ProofC n A
  axEvalC : (e : CExp) -> (c : Code) ->
            Eq (evalCExpN n e) (just c) -> ProofC n (fceq e (clit c))
  mpC     : {A B : Formula} -> ProofC n (fimp A B) -> ProofC n A -> ProofC n B
  genC    : {A : Formula} -> ProofC n A -> ProofC n (fall A)
  cgenC   : {A : Formula} -> ProofC n A -> ProofC n (fcAll A)
  cinstC  : {A : Formula} -> ProofC n (fcAll A) -> (c : Code) ->
            ProofC n (substFormulaCode0 (clit c) A)
  fceqTr  : {e1 e2 e3 : CExp} ->
            ProofC n (fceq e1 e2) -> ProofC n (fceq e2 e3) ->
            ProofC n (fceq e1 e3)
  fceqSy  : {e1 e2 : CExp} ->
            ProofC n (fceq e1 e2) -> ProofC n (fceq e2 e1)

------------------------------------------------------------------------
-- The GoedelSentence body
------------------------------------------------------------------------

GoedelBodyC : Formula
GoedelBodyC =
  fimp (fceq (ccheck (cvar cvz))
             (csub (clit phiCode) (clit phiCode)))
       fbot

-- GoedelSentence = fcAll GoedelBodyC (verified by refl)
goedel-is-fcAll : Eq GoedelSentence (fcAll GoedelBodyC)
goedel-is-fcAll = GoedelSentence-unfold

-- Instantiation gives the expected formula
inst-at-p : (p : Code) ->
  Eq (substFormulaCode0 (clit p) GoedelBodyC)
     (fimp (fceq (ccheck (clit p))
                 (csub (clit phiCode) (clit phiCode)))
           fbot)
inst-at-p p = refl

------------------------------------------------------------------------
-- Self-reference at arbitrary fuel >= 2
------------------------------------------------------------------------

-- evalCExpN (suc (suc n)) on csub of two clits reduces identically
-- to evalCExp, because clit doesn't consume fuel.

selfRefGen : (n : Nat) ->
  Eq (evalCExpN (suc (suc n)) (csub (clit phiCode) (clit phiCode)))
     (just (encFormula GoedelSentence))
selfRefGen n = GoedelSentence-self-ref

------------------------------------------------------------------------
-- The ccheck evaluation fact
------------------------------------------------------------------------

-- If checkProofN (suc n) p = just GoedelSentence, then
-- evalCExpN (suc (suc n)) (ccheck (clit p)) = just (encFormula GoedelSentence)

eval-ccheck-fact :
  (p : Code) (n : Nat) ->
  Eq (checkProofN (suc n) p) (just GoedelSentence) ->
  Eq (evalCExpN (suc (suc n)) (ccheck (clit p)))
     (just (encFormula GoedelSentence))
eval-ccheck-fact p n hyp =
  eqCong (\ r -> maybeBind r (\ a -> just (encFormula a))) hyp

------------------------------------------------------------------------
-- CONSTRUCTIVE GOEDEL I
------------------------------------------------------------------------

-- From a ProofC of GoedelSentence and a code p that the checker
-- accepts as a proof of GoedelSentence, construct a ProofC of fbot.
--
-- The construction:
--   1. cinstC: instantiate GoedelSentence at p
--   2. axEvalC: ccheck(clit p) evaluates to encFormula(GoedelSentence)
--   3. axEvalC: csub(...) evaluates to encFormula(GoedelSentence) (self-ref)
--   4. fceqSy(3): swap sides
--   5. fceqTr(2,4): ccheck(clit p) equals csub(...)
--   6. mpC(1,5): fbot

constructive-goedel1 :
  {n : Nat} ->
  ProofC (suc (suc n)) GoedelSentence ->
  (p : Code) ->
  Eq (checkProofN (suc n) p) (just GoedelSentence) ->
  ProofC (suc (suc n)) fbot
constructive-goedel1 {n} pG p hyp =
  let
    -- Step 1: instantiate the universal quantifier at p
    step1 : ProofC (suc (suc n))
              (fimp (fceq (ccheck (clit p))
                         (csub (clit phiCode) (clit phiCode)))
                    fbot)
    step1 = cinstC pG p

    -- Step 2: ccheck(clit p) = encFormula(GoedelSentence)
    step2 : ProofC (suc (suc n))
              (fceq (ccheck (clit p))
                    (clit (encFormula GoedelSentence)))
    step2 = axEvalC (ccheck (clit p))
                    (encFormula GoedelSentence)
                    (eval-ccheck-fact p n hyp)

    -- Step 3: csub(...) = encFormula(GoedelSentence)
    step3 : ProofC (suc (suc n))
              (fceq (csub (clit phiCode) (clit phiCode))
                    (clit (encFormula GoedelSentence)))
    step3 = axEvalC (csub (clit phiCode) (clit phiCode))
                    (encFormula GoedelSentence)
                    (selfRefGen n)

    -- Step 4: swap step 3
    step4 : ProofC (suc (suc n))
              (fceq (clit (encFormula GoedelSentence))
                    (csub (clit phiCode) (clit phiCode)))
    step4 = fceqSy step3

    -- Step 5: chain step 2 and step 4
    step5 : ProofC (suc (suc n))
              (fceq (ccheck (clit p))
                    (csub (clit phiCode) (clit phiCode)))
    step5 = fceqTr step2 step4

    -- Step 6: modus ponens
  in mpC step1 step5

------------------------------------------------------------------------
-- The key result is constructive-goedel1: an INTERNAL proof
-- transformation from GoedelSentence to fbot. The meta-level
-- corollary (GoedelSentence is unprovable) follows from any
-- sound interpretation of ProofC.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Comments
------------------------------------------------------------------------

-- RESULT: constructive-goedel1
--
-- Type:
--   ProofC (suc (suc n)) GoedelSentence ->
--   (p : Code) ->
--   Eq (checkProofN (suc n) p) (just GoedelSentence) ->
--   ProofC (suc (suc n)) fbot
--
-- This is a constructive proof transformation: given a proof of
-- the Goedel sentence and a code witnessing its checkability,
-- produce a proof of fbot.
--
-- The construction uses all three new rules:
--   cinstC  : instantiate GoedelSentence at the witness code
--   fceqTr  : chain ccheck evaluation with csub self-reference
--   fceqSy  : swap the csub direction
--
-- Combined with mpC, this gives fbot in 6 steps.
--
-- This is STRONGER than the previous goedel1-fuel (which gave Empty).
-- constructive-goedel1 produces an actual PROOF OF FBOT inside
-- the extended system.
--
-- COMPARISON:
--   goedel1-final : Proof GoedelSentence -> Empty  (meta-level, old system)
--   goedel1-fuel  : ProofN GoedelSentence -> Empty (meta-level, fuel system)
--   constructive-goedel1 : ProofC G -> Code -> ProofC fbot (INTERNAL, new)
--
-- The remaining gap for full Goedel II:
--   Con -> GoedelSentence requires showing that for ALL codes p,
--   if checkProofN p = GoedelSentence, then fbot. This needs
--   universal reasoning about code variables, which axEvalC
--   (requiring closed CExps) cannot provide.
