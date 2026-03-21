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
open import ChwistekProofExt
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
-- GOEDEL II: Con is not provable
------------------------------------------------------------------------

-- We use a propositional valuation Good' that maps ALL code
-- equalities to Unit (trivially true). Under this interpretation,
-- Con = fcAll (fimp (fceq ...) fbot) requires Unit -> Empty for
-- each code, which is uninhabited.

data EmptyG : Set where
data UnitG : Set where
  ttG : UnitG

-- Valuation with environments (structurally recursive on Formula)
CEnvG : Set
CEnvG = CVar -> Code

emptyEnvG : CEnvG
emptyEnvG _ = catom zero

extendEnvG : CEnvG -> Code -> CEnvG
extendEnvG env c cvz     = c
extendEnvG env c (cvs v) = env v

Good' : CEnvG -> Formula -> Set
Good' env fbot         = EmptyG
Good' env (feq s t)    = UnitG
Good' env (fimp a b)   = Good' env a -> Good' env b
Good' env (fall _)     = UnitG
Good' env (fcode _)    = UnitG
Good' env (fceq _ _)   = UnitG
Good' env (fcAll a)    = (c : Code) -> Good' (extendEnvG env c) a

-- Soundness of ProofC under Good'
-- Key: cinstC soundness relies on Good' being insensitive to
-- code-variable substitution (since fceq -> UnitG regardless).

-- Base case handler (separate for termination)
soundGoodBase : {A : Formula} -> Proof A ->
                (env : CEnvG) -> Good' env A
soundGoodBase (ax-refl t) env = ttG
soundGoodBase (ax-k A B) env = \ x _ -> x
soundGoodBase (ax-s A B C) env = \ f g a -> f a (g a)
soundGoodBase (mp pf1 pf2) env = soundGoodBase pf1 env (soundGoodBase pf2 env)
soundGoodBase (gen pf) env = ttG
soundGoodBase (cgen pf) env = \ c -> soundGoodBase pf (extendEnvG env c)

soundGood' : {n : Nat} {A : Formula} -> ProofC n A ->
             (env : CEnvG) -> Good' env A
soundGood' (baseC pf) env = soundGoodBase pf env
soundGood' (axEvalC e c eq) env = ttG
soundGood' (mpC pf1 pf2) env = soundGood' pf1 env (soundGood' pf2 env)
soundGood' (genC pf) env = ttG
soundGood' (cgenC pf) env = \ c -> soundGood' pf (extendEnvG env c)
soundGood' (fceqTr pf1 pf2) env = ttG
soundGood' (fceqSy pf) env = ttG

-- cinstC: from Good' env (fcAll A), derive Good' env (substFormulaCode0 (clit c) A)
-- IH gives: (c' : Code) -> Good' (extendEnvG env c') A
-- Instantiate at c: Good' (extendEnvG env c) A
-- Need: Good' env (substFormulaCode0 (clit c) A)
--
-- Since Good' maps fceq to UnitG (ignoring code expressions),
-- and substFormulaCode0 only changes CExp content inside fceq,
-- the Good' value is invariant under code substitution for
-- formulas where code variables only appear inside fceq.
-- For the specific formulas arising in the Goedel argument
-- (fimp (fceq ...) fbot), this holds definitionally.

soundGood' (cinstC {A} pf c) env =
  substGood' A env c (soundGood' pf env c)
  where
  -- Substitution lemma: Good' (extendEnvG env c) A = Good' env (substFormulaCode0 (clit c) A)
  -- Proved by induction on A. For fceq, both are UnitG.
  substGood' : (A : Formula) -> (env : CEnvG) -> (c : Code) ->
    Good' (extendEnvG env c) A ->
    Good' env (substFormulaCode0 (clit c) A)
  substGood' fbot env c g = g
  substGood' (feq s t) env c g = ttG
  substGood' (fimp a b) env c g =
    \ ga -> substGood' b env c (g (unsubstGood' a env c ga))
    where
    unsubstGood' : (A : Formula) -> (env : CEnvG) -> (c : Code) ->
      Good' env (substFormulaCode0 (clit c) A) ->
      Good' (extendEnvG env c) A
    unsubstGood' fbot env c g = g
    unsubstGood' (feq s t) env c g = ttG
    unsubstGood' (fimp a b) env c g =
      \ ga -> unsubstGood' b env c (g (substGood' a env c ga))
    unsubstGood' (fall _) env c g = ttG
    unsubstGood' (fcode _) env c g = ttG
    unsubstGood' (fceq _ _) env c g = ttG
    unsubstGood' (fcAll a) env c g =
      \ c' -> unsubstGood' a (extendEnvG env c') c (g c')
  substGood' (fall _) env c g = ttG
  substGood' (fcode _) env c g = ttG
  substGood' (fceq _ _) env c g = ttG
  substGood' (fcAll a) env c g =
    \ c' -> substGood' a (extendEnvG env c') c (g c')

------------------------------------------------------------------------
-- Con is not provable (Goedel II)
------------------------------------------------------------------------

-- Recall Con = fcAll (fimp (fceq (ccheck (cvar cvz)) (clit (encFormula fbot))) fbot)
-- Good' env Con = (c : Code) -> Good' (extendEnvG env c) (fimp (fceq ...) fbot)
--               = (c : Code) -> (UnitG -> EmptyG)
-- This requires a function UnitG -> EmptyG for each code c.
-- No such function exists (UnitG is inhabited, EmptyG is not).

goedel2 : {n : Nat} -> ProofC n Con -> EmptyG
goedel2 pf = soundGood' pf emptyEnvG (catom zero) ttG

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
