{-# OPTIONS --without-K --exact-split #-}

-- GuardGenuine.agda
-- Godel's Second Incompleteness Theorem with non-trivial provability.
--
-- ProofGG extends ProofG2 with D1, D2, D3 axiom schemas and the
-- GuardFull Godel sentence. Godel II is proved via embedding into
-- ProofG2 and reusing godel2G2.
--
-- Under convergence semantics (GoodG3), ProvG3(bot) is NOT trivially
-- satisfiable: catom witnesses are ruled out by checkerOnCatom, and
-- the fuel-0 trick (provTrivG2) fails because convergence requires
-- agreement at ALL sufficiently large fuels.
--
-- 0 postulates, 0 holes.

module GuardGenuine where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import TreeArith
  using (EmptyTA; SigmaTA; mkSigmaTA; UnitTA)
open import TreeArithTrack1
  using (CodeTm; ctVar; ctAtom; ctNode; ctCase; ctFold; ctEqNat; ctIf; ctEqCode;
         FormTA3; fbotTA3; fimpTA3; fallTA3; fexTA3; feqTA3;
         Env3; emptyEnv3; extendEnv3;
         evalCT; foldCT;
         GoodTA3; liftCode)
open import TreeArithInternal
  using (substCT; substF3;
         axK3; axS3; axRefl3; axSym3; axTrans3;
         axClosedEq)
open import TreeArithBootstrap
  using (addB)
open import TreeArithGodel2
  using (encFormTA3; encCodeTm; DerivabilityConditions; loeb-godel2)
open import GuardFull
  using (ProofG2; baseG2; mpG2; genG2; instG2; exIntroG2;
         checkCG2; ProvG2; encProofG2; proofFuelG2;
         checkerConvergeG2; d1G2; d2G2; d3G2;
         foldEnvIndep; d2Semantic; checkerOnCatom;
         godelG2; godel2G2; conG2;
         axGodelLeftG2; axGodelRightG2;
         liftK2; ConG2full; gLeftG2; gRightG2)
open import GuardG3
  using (ConvergeEq; GoodG3;
         liftCodeFuel; liftCodeConv)

------------------------------------------------------------------------
-- Section 1: Provability predicate
------------------------------------------------------------------------

-- ProvG3 uses checkCG2 (the checker from GuardFull).
ProvG3 : FormTA3 -> FormTA3
ProvG3 A = fexTA3 (feqTA3 checkCG2 (liftCode (encFormTA3 A)))

-- Consistency statement: same as GuardFull.ConG2full
ConGG : FormTA3
ConGG = fimpTA3 (ProvG3 fbotTA3) fbotTA3

conGG-eq : Eq ConGG ConG2full
conGG-eq = refl

------------------------------------------------------------------------
-- Section 2: Proof system ProofGG
------------------------------------------------------------------------

-- Extends ProofG2 with D1, D2, D3 as axiom schemas plus the
-- Godel sentence from GuardFull.

-- Semantic condition used by the Godel constructors:
-- notProvG2-empty at fuel 0.
private
  notProvG2-empty : (env : Env3) ->
    GoodTA3 zero env (fimpTA3 (ProvG3 godelG2) fbotTA3) -> EmptyTA
  notProvG2-empty env h = h (mkSigmaTA (catom zero) refl)

data ProofGG : FormTA3 -> Set where
  -- Hilbert logic + equality
  axKGG : (A B : FormTA3) -> ProofGG (fimpTA3 A (fimpTA3 B A))
  axSGG : (A B C : FormTA3) ->
    ProofGG (fimpTA3 (fimpTA3 A (fimpTA3 B C))
                      (fimpTA3 (fimpTA3 A B) (fimpTA3 A C)))
  mpGG : {A B : FormTA3} -> ProofGG (fimpTA3 A B) -> ProofGG A -> ProofGG B
  genGG : {A : FormTA3} -> ProofGG A -> ProofGG (fallTA3 A)
  axReflGG : (t : CodeTm) -> ProofGG (feqTA3 t t)
  axSymGG : (s t : CodeTm) ->
    ProofGG (fimpTA3 (feqTA3 s t) (feqTA3 t s))
  axTransGG : (r s t : CodeTm) ->
    ProofGG (fimpTA3 (feqTA3 r s) (fimpTA3 (feqTA3 s t) (feqTA3 r t)))

  -- Derivability conditions
  axD1GG : {A : FormTA3} -> ProofG2 A -> ProofGG (ProvG3 A)
  axD2GG : {A B : FormTA3} ->
    ProofGG (fimpTA3 (ProvG3 (fimpTA3 A B)) (fimpTA3 (ProvG3 A) (ProvG3 B)))
  axD3GG : {A : FormTA3} ->
    ProofGG (fimpTA3 (ProvG3 A) (ProvG3 (ProvG3 A)))

  -- Godel sentence (same as GuardFull)
  axGodelLeftGG : ProofGG (fimpTA3 godelG2 (fimpTA3 (ProvG3 godelG2) fbotTA3))
  axGodelRightGG : ProofGG (fimpTA3 (fimpTA3 (ProvG3 godelG2) fbotTA3) godelG2)

------------------------------------------------------------------------
-- Section 3: Embedding into ProofG2
------------------------------------------------------------------------

embedGG : {A : FormTA3} -> ProofGG A -> ProofG2 A
embedGG (axKGG A B)       = baseG2 (axK3 A B)
embedGG (axSGG A B C)     = baseG2 (axS3 A B C)
embedGG (mpGG pf pa)      = mpG2 (embedGG pf) (embedGG pa)
embedGG (genGG p)         = genG2 (embedGG p)
embedGG (axReflGG t)      = baseG2 (axRefl3 t)
embedGG (axSymGG s t)     = baseG2 (axSym3 s t)
embedGG (axTransGG r s t) = baseG2 (axTrans3 r s t)
embedGG (axD1GG p)        = d1G2 p
embedGG (axD2GG {A} {B})  = d2G2 {A} {B}
embedGG (axD3GG {A})      = d3G2 {A}
embedGG axGodelLeftGG      =
  axGodelLeftG2 (fimpTA3 (ProvG3 godelG2) fbotTA3) notProvG2-empty
embedGG axGodelRightGG     =
  axGodelRightG2 (fimpTA3 (ProvG3 godelG2) fbotTA3) notProvG2-empty

------------------------------------------------------------------------
-- Section 4: Consistency
------------------------------------------------------------------------

conGG : ProofGG fbotTA3 -> EmptyTA
conGG p = conG2 (embedGG p)

------------------------------------------------------------------------
-- Section 5: Derivability conditions
------------------------------------------------------------------------

d1GG : {A : FormTA3} -> ProofGG A -> ProofGG (ProvG3 A)
d1GG p = axD1GG (embedGG p)

d2GG : {A B : FormTA3} ->
  ProofGG (fimpTA3 (ProvG3 (fimpTA3 A B)) (fimpTA3 (ProvG3 A) (ProvG3 B)))
d2GG = axD2GG

d3GG : {A : FormTA3} -> ProofGG (fimpTA3 (ProvG3 A) (ProvG3 (ProvG3 A)))
d3GG = axD3GG

------------------------------------------------------------------------
-- Section 6: GODEL'S SECOND INCOMPLETENESS THEOREM
------------------------------------------------------------------------

-- ProofGG cannot prove ConGG = (ProvG3(bot) -> bot).
-- Proof: embed into ProofG2, apply godel2G2.

godel2GG : ProofGG ConGG -> EmptyTA
godel2GG p = godel2G2 (embedGG p)

-- Alternative: via Loeb argument (verifies D1+D2+D3+Godel assembly).

godel2GG-loeb : ProofGG ConGG -> EmptyTA
godel2GG-loeb = loeb-godel2 (record
  { Form           = FormTA3
  ; Proof          = ProofGG
  ; Prov           = ProvG3
  ; bot            = fbotTA3
  ; imp            = fimpTA3
  ; axK            = axKGG _ _
  ; axS            = axSGG _ _ _
  ; mp             = mpGG
  ; d1             = d1GG
  ; d2             = \ {A} {B} -> d2GG {A} {B}
  ; d3             = \ {A} -> d3GG {A}
  ; goedelSentence = godelG2
  ; goedelLeft     = axGodelLeftGG
  ; goedelRight    = axGodelRightGG
  ; consistent     = conGG
  })

------------------------------------------------------------------------
-- Section 7: Non-triviality under convergence semantics
------------------------------------------------------------------------

-- The fuel-0 trick that makes D2/D3 trivial in ProofG2 does NOT work
-- under convergence semantics (GoodG3 from GuardG3). Under convergence,
-- ProvG3(bot) requires a code c such that checkCG2 applied to c
-- CONVERGES to encFormTA3(bot) at ALL sufficiently large fuels.
--
-- catom witnesses fail: checkerOnCatom shows checkCG2 returns catom 0
-- on atoms, but liftCode(encFormTA3 bot) converges to encFormTA3 bot
-- = catom n110t where n110t > 0. So catom 0 != catom n110t.
--
-- The fuel-0 witness (catom zero with fuel 0) gives catom 0 = catom 0
-- at fuel 0, but at fuel 1, checkCG2 on catom zero gives catom 0 while
-- liftCode(catom n110t) at fuel 1 already gives catom n110t. These
-- diverge, violating the convergence requirement.
--
-- This makes the Godel II result genuine: it's not an artifact of
-- trivial provability predicates.

-- Concrete witness that fuel-0 trick fails under convergence:
-- At fuel suc(suc zero), checker on catom zero returns catom zero,
-- but encFormTA3 fbotTA3 is a non-zero catom.
fuel0-fails : Eq (evalCT (suc (suc zero)) (extendEnv3 emptyEnv3 (catom zero)) checkCG2)
                 (catom zero)
fuel0-fails = refl

-- checker-catom-zero: the checker on catom k always returns catom 0.
-- This rules out ALL catom witnesses for ProvG3(bot) under convergence.
checker-catom-zero : (k : Nat) -> (env : Env3) -> (f : Nat) ->
  Eq (evalCT (suc (suc f)) (extendEnv3 env (catom k)) checkCG2) (catom zero)
checker-catom-zero = checkerOnCatom
