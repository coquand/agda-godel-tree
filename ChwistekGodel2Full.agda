{-# OPTIONS --without-K --exact-split #-}

module ChwistekGodel2Full where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekProofExt
open import ChwistekFuelChecker
open import ChwistekFuelGodel
open import ChwistekFuelGodel2

------------------------------------------------------------------------
-- APPROACH: Instead of internalizing checkProofN case by case,
-- observe that what Goedel II REALLY needs is:
--
--   "for all p, if checkProofN p = just G, then fbot"
--
-- This is GoedelSentence itself! And constructive Goedel I shows
-- the META-LEVEL version. The gap is universality.
--
-- KEY INSIGHT: We don't need to internalize the WHOLE checker.
-- We only need the system to verify ONE universal property:
--
--   ∀p. Prf(p, G) → Prf(sd(p), ⊥)
--
-- This is a statement about the SPECIFIC formula G, not about
-- all formulas. And the proof analyzes what happens when the
-- checker returns G — which constrains p to very specific shapes.
--
-- With code induction, we can prove this by cases on p:
-- - catom: checker returns nothing, vacuous
-- - cnode (catom tag) tc: analyze tag
--   * tags 30-32 (axioms): return feq/fimp shapes, never G
--   * tag 33 (mp): need IH on sub-codes
--   * tags 34-35 (gen/cgen): return fall/fcAll wrapping sub-result
--   * tag 36 (ax-eval): returns fceq, never G
--
-- The crucial observation: GoedelSentence = fcAll (fimp (fceq ...) fbot).
-- Its outermost constructor is fcAll. Only tags 35 (cgen) and 33 (mp)
-- can produce fcAll at the top level.
--
-- For tag 35: checkProofN returns fcAll A where checkProofN sub = just A.
-- For this to be GoedelSentence, A must be the body of GoedelSentence.
-- Then selfDestruct works on the sub-proof.
--
-- For tag 33 (mp): checkProofN returns B where sub1 proves fimp A B
-- and sub2 proves A. If B = GoedelSentence, then sub1 proves
-- fimp A GoedelSentence. The self-destruct applies recursively.
--
-- This case analysis IS the content of the proof. And it works
-- WITHOUT full computation axioms — we just need the system to
-- know that specific tags produce specific formula shapes.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- PART 1: Proof system with code induction
------------------------------------------------------------------------

-- ProofI: proof system with code-structural induction.
-- The induction principle says: if a property holds for all atoms
-- and is preserved by cnode, then it holds for all codes.

data ProofI (n : Nat) : Formula -> Set where
  baseI   : {A : Formula} -> Proof A -> ProofI n A
  axEvalI : (e : CExp) -> (c : Code) ->
            Eq (evalCExpN n e) (just c) -> ProofI n (fceq e (clit c))
  mpI     : {A B : Formula} -> ProofI n (fimp A B) -> ProofI n A -> ProofI n B
  genI    : {A : Formula} -> ProofI n A -> ProofI n (fall A)
  cgenI   : {A : Formula} -> ProofI n A -> ProofI n (fcAll A)
  cinstI  : {A : Formula} -> ProofI n (fcAll A) -> (c : Code) ->
            ProofI n (substFormulaCode0 (clit c) A)
  fceqTrI : {e1 e2 e3 : CExp} ->
            ProofI n (fceq e1 e2) -> ProofI n (fceq e2 e3) ->
            ProofI n (fceq e1 e3)
  fceqSyI : {e1 e2 : CExp} ->
            ProofI n (fceq e1 e2) -> ProofI n (fceq e2 e1)
  -- Code-structural induction:
  -- If P holds when checkProofN gives nothing (atom case),
  -- and P is preserved by cnode (the checker recurses on sub-codes),
  -- then P holds for all codes.
  --
  -- Actually, for Goedel II, we need a more specific principle.
  -- The property we want is: fimp (fceq (ccheck (cvar cvz)) X) fbot
  -- i.e., "if cvar proves X, then fbot."
  --
  -- This is exactly what Con and GoedelSentence assert
  -- (for X = encFbot and X = encG respectively).
  --
  -- The INTERNAL Goedel I says: GoedelSentence → fbot.
  -- But that requires the system to know that ANY proof of G
  -- leads to fbot. Which is what we need to prove by induction.
  --
  -- Instead of a general induction rule, we add a SPECIFIC
  -- computation principle: the system can verify what checkProofN
  -- does on each code shape. This is a set of axioms about
  -- the checker's behavior.

  -- Axiom: checkProofN on atoms gives nothing
  axCheckAtom : (m : Nat) ->
    ProofI n (fceq (ccheck (clit (catom m))) (clit (catom zero)))
    -- We use catom zero as a "nothing" sentinel.
    -- This is a simplification; see discussion below.

------------------------------------------------------------------------
-- STOP: There is a problem.
------------------------------------------------------------------------

-- The problem: we need to express "checkProofN returns nothing"
-- inside formulas. But fceq compares code expressions that
-- evaluate to CODES, and "nothing" is not a Code — it's a
-- Maybe Code. Our formula language can't express partiality.
--
-- Options:
-- (a) Add a "nothing" code sentinel (like catom zero) and modify
--     checkProofN to return it instead of nothing.
-- (b) Express the property NEGATIVELY: "checkProofN does NOT
--     return G" rather than "checkProofN returns nothing."
-- (c) Use a different formulation that avoids partiality.
--
-- Option (b) is cleanest: instead of axiomatizing what checkProofN
-- returns, axiomatize what it DOESN'T return. For Goedel II,
-- we only need: "for most codes, checkProofN doesn't return G."
--
-- But negative facts (≠) require fimp ... fbot, which is what
-- we're trying to prove!
--
-- Option (a) is simplest: totalize checkProofN by returning a
-- default code for failures. Then fceq can compare against this
-- default.
--
-- Actually, the cleanest approach: instead of axiomatizing the
-- checker, use the SEMANTIC approach from our existing development.
--
-- We already proved constructive-goedel1 at the META level.
-- The gap is universality. With code induction, we can prove
-- the SEMANTIC property universally and then use soundness.

------------------------------------------------------------------------
-- REVISED APPROACH: Semantic Goedel II via code induction
------------------------------------------------------------------------

-- Instead of axiomatizing checkProofN's behavior inside formulas,
-- we work at the META level with code induction on Agda's Code type.
--
-- The meta-level fact we need:
-- "For ALL codes p, if checkProofN n p = just GoedelSentence,
--  then checkProofN m (selfDestruct p) = just fbot."
--
-- This is a statement about Agda's Code, not about formula-level
-- codes. We can prove it by AGDA's structural induction on Code.
--
-- Then we use this meta-level universal fact to derive:
-- ProofI Con -> Empty (at the meta level)

------------------------------------------------------------------------
-- selfDestruct: the code transformation
------------------------------------------------------------------------

-- From a code p that proves GoedelSentence, construct a code that
-- proves fbot. Uses the 6-step chain from constructive Goedel I.

n37 : Nat
n37 = suc (suc n35)

n38 : Nat
n38 = suc n37

n39 : Nat
n39 = suc n38

selfDestruct : Code -> Code
selfDestruct p =
  let
    -- cinst: instantiate GoedelSentence at p
    step1 = cnode (catom n37) (cnode p p)
    -- ax-eval: ccheck(p) = encFormula(G)
    step2 = cnode (catom n36') (cnode (encCExp (ccheck (clit p)))
                                      (encFormula GoedelSentence))
    -- ax-eval: csub self-reference
    step3 = cnode (catom n36') (cnode (encCExp (csub (clit phiCode) (clit phiCode)))
                                      (encFormula GoedelSentence))
    -- fceq-sym
    step4 = cnode (catom n39) step3
    -- fceq-trans
    step5 = cnode (catom n38) (cnode step2 step4)
    -- mp
  in cnode (catom n33) (cnode step1 step5)

------------------------------------------------------------------------
-- Meta-level universal Goedel I
------------------------------------------------------------------------

-- For the meta-level Goedel II, we need:
-- ProofI n Con -> Empty
--
-- The argument:
-- 1. From ProofI n Con, by soundness: TrueFormulaN n Con
-- 2. TrueFormulaN n Con = for all c, checkProofN n c ≠ just fbot
-- 3. From constructive-goedel1: if checkProofN n p = just G,
--    then checkProofN m (selfDestruct p) = just fbot
-- 4. If GoedelSentence were provable (ProofI G), encoding gives
--    a code p with checkProofN p = just G
-- 5. Then selfDestruct(p) proves fbot, contradicting step 2
-- 6. So GoedelSentence is not provable
-- 7. BUT: this only gives MetaNot (ProofI G), not MetaNot (ProofI Con)
--
-- The full Goedel II needs: ProofI Con -> ProofI G (internal)
-- Which needs the system to know: "if consistent then G holds"
-- Which requires universal reasoning about the checker.
--
-- SO: we still need the same bridge. Code induction at the META
-- level (Agda's induction on Code) doesn't help because the
-- formula language can't express partiality.

------------------------------------------------------------------------
-- THE REAL SOLUTION: Totalize the checker
------------------------------------------------------------------------

-- If we make checkProofN total (returning a CODE instead of
-- Maybe Formula), then fceq can compare checker results with
-- formula codes, and code induction can be used inside formulas.
--
-- Define checkProofTotal : Nat -> Code -> Code
-- where the output is encFormula(A) if the code proves A,
-- or catom zero (a sentinel) if it doesn't.
--
-- Then Con = fcAll (fimp (fceq (ccheckT (cvar cvz)) (clit (encFormula fbot))) fbot)
-- where ccheckT uses the totalized checker.
--
-- And code induction can reason about ccheckT universally.

-- Totalized checker
checkProofTotal : Nat -> Code -> Code
checkProofTotal n p = totalizeResult (checkProofN n p)
  where
  totalizeResult : Maybe Formula -> Code
  totalizeResult nothing  = catom zero  -- sentinel for "no proof"
  totalizeResult (just a) = encFormula a

-- Totalized CExp evaluator
evalCExpTotal : Nat -> CExp -> Code
evalCExpTotal n e = totalizeResultC (evalCExpN n e)
  where
  totalizeResultC : Maybe Code -> Code
  totalizeResultC nothing  = catom zero
  totalizeResultC (just c) = c

-- New CExp constructor for the totalized checker
-- ccheckT : CExp -> CExp
-- evalCExpN n (ccheckT e) = checkProofTotal n (evalCExpTotal n e)
--
-- For now, we work at the meta-level with checkProofTotal.

------------------------------------------------------------------------
-- Meta-level Goedel II (genuine, using Agda's induction)
------------------------------------------------------------------------

data EmptyF : Set where

-- Soundness gives meta-consistency
soundBase-fbot : Proof fbot -> EmptyF
soundBase-fbot pf = absurdF (soundProof pf emptyTEnv emptyCEnv)
  where
  absurdF : Empty -> EmptyF
  absurdF ()

-- The meta-level Goedel I for the fuel system:
-- GoedelSentence is not provable.
-- (We already have goedel1-fuel in ChwistekFuelGodel2, but let's
-- restate it cleanly.)

-- GoedelSentence = fcAll body where body = fimp (fceq ...) fbot.
-- TrueFormulaN n GoedelSentence = for all c, TrueCodeEq... -> Empty.
-- This means: for all c, if checkProofN evaluates to encFormula G
-- at code c, then Empty.

-- From goedel1-fuel (ChwistekFuelGodel2):
-- ProofN (suc (suc n)) GoedelSentence + enc-correct -> Empty

-- Meta-Goedel-II:
-- "ProofI n Con" means the system proves its own consistency.
-- By soundness, the system IS consistent.
-- By goedel1-fuel, GoedelSentence is not provable.
-- But we need: Con being provable ITSELF leads to contradiction.
--
-- The genuine argument (at the meta level, using Agda's induction):
--
-- From soundness of ProofI: every ProofI-provable formula is true.
-- True(Con) = for all c, checkProofN c ≠ just fbot (meta-consistency).
-- True(GoedelSentence) = for all c, checkProofN c ≠ just G.
--
-- These are BOTH true (the system IS consistent and G IS unprovable).
-- Neither leads to contradiction.
--
-- The Goedel-II content is: Con is UNPROVABLE despite being TRUE.
-- This requires showing the system CANNOT derive Con.
--
-- At the meta level (in Agda), we can prove:
-- "there is no ProofI of Con" by analyzing what ProofI can derive.
-- This is a STRUCTURAL argument about the proof system, not a
-- semantic one.

------------------------------------------------------------------------
-- STRUCTURAL ARGUMENT: ProofI cannot derive fimp-to-fbot formulas
------------------------------------------------------------------------

-- Key property: a formula is "safe" if it doesn't have fbot as
-- the ultimate consequent reachable by mp chains.
-- Safe formulas: feq, fceq, fcode, and implications where the
-- consequent is safe.
-- Unsafe: fbot, fimp A fbot, fimp A (fimp B fbot), etc.
-- Con = fcAll (fimp (fceq ...) fbot) is unsafe (after cinstI + mpI).

-- Claim: no ProofI derivation produces fbot.
-- Therefore ProofI fbot -> Empty.
-- And since Con requires deriving fimp (fceq ...) fbot as a body,
-- which requires fbot, Con is also underivable.

-- The argument uses the SAME Good valuation from ChwistekConstructiveGodel!
-- Good(fbot) = Empty, Good(fceq) = Unit, Good(fimp A B) = Good A -> Good B.

-- Let me reuse that approach but prove it cleanly for ProofI.

data UnitF : Set where
  ttF : UnitF

CEnvF : Set
CEnvF = CVar -> Code

emptyEnvF : CEnvF
emptyEnvF _ = catom zero

extendEnvF : CEnvF -> Code -> CEnvF
extendEnvF env c cvz     = c
extendEnvF env c (cvs v) = env v

GoodF : CEnvF -> Formula -> Set
GoodF env fbot         = EmptyF
GoodF env (feq s t)    = UnitF
GoodF env (fimp a b)   = GoodF env a -> GoodF env b
GoodF env (fall _)     = UnitF
GoodF env (fcode _)    = UnitF
GoodF env (fceq _ _)   = UnitF
GoodF env (fcAll a)    = (c : Code) -> GoodF (extendEnvF env c) a

-- Soundness of base proofs under GoodF
soundGoodBaseF : {A : Formula} -> Proof A -> (env : CEnvF) -> GoodF env A
soundGoodBaseF (ax-refl t) env = ttF
soundGoodBaseF (ax-k A B) env = \ x _ -> x
soundGoodBaseF (ax-s A B C) env = \ f g a -> f a (g a)
soundGoodBaseF (mp pf1 pf2) env = soundGoodBaseF pf1 env (soundGoodBaseF pf2 env)
soundGoodBaseF (gen pf) env = ttF
soundGoodBaseF (cgen pf) env = \ c -> soundGoodBaseF pf (extendEnvF env c)

-- Substitution lemma for cinstI
substGoodF : (A : Formula) -> (env : CEnvF) -> (c : Code) ->
  GoodF (extendEnvF env c) A -> GoodF env (substFormulaCode0 (clit c) A)
unsubstGoodF : (A : Formula) -> (env : CEnvF) -> (c : Code) ->
  GoodF env (substFormulaCode0 (clit c) A) -> GoodF (extendEnvF env c) A

substGoodF fbot env c g = g
substGoodF (feq _ _) env c g = ttF
substGoodF (fimp a b) env c g = \ x -> substGoodF b env c (g (unsubstGoodF a env c x))
substGoodF (fall _) env c g = ttF
substGoodF (fcode _) env c g = ttF
substGoodF (fceq _ _) env c g = ttF
substGoodF (fcAll a) env c g = \ c' -> substGoodF a (extendEnvF env c') c (g c')

unsubstGoodF fbot env c g = g
unsubstGoodF (feq _ _) env c g = ttF
unsubstGoodF (fimp a b) env c g = \ x -> unsubstGoodF b env c (g (substGoodF a env c x))
unsubstGoodF (fall _) env c g = ttF
unsubstGoodF (fcode _) env c g = ttF
unsubstGoodF (fceq _ _) env c g = ttF
unsubstGoodF (fcAll a) env c g = \ c' -> unsubstGoodF a (extendEnvF env c') c (g c')

-- Soundness of ProofI under GoodF
soundGoodI : {n : Nat} {A : Formula} -> ProofI n A -> (env : CEnvF) -> GoodF env A
soundGoodI (baseI pf) env = soundGoodBaseF pf env
soundGoodI (axEvalI e c eq) env = ttF
soundGoodI (mpI pf1 pf2) env = soundGoodI pf1 env (soundGoodI pf2 env)
soundGoodI (genI pf) env = ttF
soundGoodI (cgenI pf) env = \ c -> soundGoodI pf (extendEnvF env c)
soundGoodI (cinstI {A} pf c) env = substGoodF A env c (soundGoodI pf env c)
soundGoodI (fceqTrI pf1 pf2) env = ttF
soundGoodI (fceqSyI pf) env = ttF
soundGoodI (axCheckAtom m) env = ttF

------------------------------------------------------------------------
-- GOEDEL II (genuine, for ProofI)
------------------------------------------------------------------------

-- GoodF env Con:
-- Con = fcAll (fimp (fceq (ccheck (cvar cvz)) (clit (encFormula fbot))) fbot)
-- GoodF env Con = (c : Code) -> GoodF (extendEnvF env c) (fimp (fceq ...) fbot)
--               = (c : Code) -> (UnitF -> EmptyF)
-- This is uninhabited (UnitF -> EmptyF has no element).

goedel2-genuine : {n : Nat} -> ProofI n Con -> EmptyF
goedel2-genuine pf = soundGoodI pf emptyEnvF (catom zero) ttF

------------------------------------------------------------------------
-- WAIT: This is the SAME trick as before (Good' / GoodSD).
-- The valuation makes fceq trivially true, so Con is automatically
-- false under this interpretation.
--
-- This is NOT genuine Goedel II. It's soundness + countermodel.
--
-- The analysis confirms: we CANNOT get genuine Goedel II from
-- a valuation argument alone. We need the SELF-REFERENTIAL
-- argument: Con -> G via the Goedel sentence.
--
-- Code induction alone doesn't help because the formula language
-- can't express the checker's behavior on code variables.
-- The totalized checker (checkProofTotal) would help, but
-- we'd need ccheckT as a CExp constructor and computation
-- axioms inside the proof system.
--
-- HONEST CONCLUSION:
-- Genuine Goedel II requires internalizing the checker's behavior
-- to the point where the system can prove Con -> GoedelSentence.
-- This is Guard's approach (p.16-17): he constructs specific
-- functors that formalize each step of the Goedel I proof.
-- In our tree-native framework, this requires:
-- (a) A totalized checker expressible in CExp
-- (b) Computation axioms for each case of the checker
-- (c) Code induction to prove the universal property
-- This is ~400+ lines and changes the system's character.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- WHAT WE CAN HONESTLY PROVE: meta-level Goedel II
------------------------------------------------------------------------

-- At the Agda meta level, we CAN prove "ProofI n Con -> EmptyF"
-- but only via the GoodF countermodel, which is NOT the genuine
-- Goedel-II argument.
--
-- The genuine argument requires the formula Con -> GoedelSentence
-- to be INTERNALLY derivable, which needs:
-- 1. The system to universally reason about checkProofN on variables
-- 2. Code induction + computation axioms for the checker
-- 3. The self-destruct transformation to be provably correct
--    inside the system
--
-- We have (3) at the meta level (constructive Goedel I).
-- We lack (1) and (2).
--
-- Adding axCheckAtom was a first step toward (2) but hit the
-- partiality problem: checkProofN returns Maybe Formula, and
-- "nothing" can't be expressed as a Code.
--
-- FINAL STATUS: Genuine tree-native Goedel II is feasible but
-- requires a totalized checker + ~400 lines of computation axioms.
-- The axSD approach gives Goedel II relative to a specific axiom.
-- The GoodF approach gives a structural result but not the
-- incompleteness-theoretic one.
