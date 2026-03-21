{-# OPTIONS --without-K --exact-split #-}

module ChwistekNelson where

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
-- PART 1 — OPEN FRAGMENT
------------------------------------------------------------------------

data OpenProof : Formula -> Set where
  ax-refl-o : (t : Term) -> OpenProof (feq t t)
  ax-k-o    : (A B : Formula) -> OpenProof (fimp A (fimp B A))
  ax-s-o    : (A B C : Formula) ->
              OpenProof (fimp (fimp A (fimp B C))
                        (fimp (fimp A B) (fimp A C)))
  mp-o      : {A B : Formula} ->
              OpenProof (fimp A B) -> OpenProof A -> OpenProof B

data Empty' : Set where

data Unit' : Set where
  tt' : Unit'

Good : Formula -> Set
Good fbot         = Empty'
Good (feq s t)    = Eq s t
Good (fimp a b)   = Good a -> Good b
Good (fall _)     = Unit'
Good (fcode _)    = Unit'
Good (fceq _ _)   = Unit'
Good (fcAll _)    = Unit'

open-sound : {A : Formula} -> OpenProof A -> Good A
open-sound (ax-refl-o t)   = refl
open-sound (ax-k-o A B)    = \ x -> \ _ -> x
open-sound (ax-s-o A B C)  = \ f -> \ g -> \ a -> f a (g a)
open-sound (mp-o pf1 pf2)  = open-sound pf1 (open-sound pf2)

open-consistent : OpenProof fbot -> Empty'
open-consistent pf = open-sound pf

------------------------------------------------------------------------
-- PART 2 — BOUNDED REFLECTION (fuel system)
------------------------------------------------------------------------

-- ReflectN n p A: the fuel system at level n can internally certify
-- that code p proves formula A.

ReflectN : Nat -> Code -> Formula -> Set
ReflectN n p A =
  Sigma Code (\ d ->
    Eq (checkProofN n d)
       (just (fceq (ccheck (clit p)) (clit (encFormula A)))))

instance-reflection :
  (n : Nat) (p : Code) (A : Formula) ->
  Eq (checkProofN (suc n) p) (just A) ->
  ReflectN (suc (suc (suc n))) p A
instance-reflection n p A hyp = D1-fuel p A n hyp

-- Iterated reflection (D3): the certification can be re-certified.
iterated-reflection :
  (n : Nat) (p : Code) (A : Formula) ->
  (hyp : Eq (checkProofN (suc n) p) (just A)) ->
  let d1 = D1-fuel p A n hyp in
  ReflectN (suc (suc (suc (suc (suc n)))))
           (sigFst d1)
           (fceq (ccheck (clit p)) (clit (encFormula A)))
iterated-reflection n p A hyp = D3-fuel p A n hyp

------------------------------------------------------------------------
-- PART 3 — CONSISTENCY FORMULAS
------------------------------------------------------------------------

-- ConN: "no proof code yields fbot" (same formula for all n;
-- the fuel level affects truth, not the formula itself)
ConN : Formula
ConN = fcAll (fimp (fceq (ccheck (cvar cvz))
                        (clit (encFormula fbot)))
                  fbot)

------------------------------------------------------------------------
-- PART 4 — META-LEVEL CONSISTENCY
------------------------------------------------------------------------

-- The FULL system is consistent at the meta-level.
-- soundProof gives TrueFormula fbot = (tenv)(cenv) -> Empty.

meta-consistent : Proof fbot -> Empty
meta-consistent pf = soundProof pf emptyTEnv emptyCEnv

-- The fuel-based system is also meta-consistent.
meta-consistent-fuel : {n : Nat} -> ProofN n fbot -> Empty'
meta-consistent-fuel pf = absurdE (soundProofN pf emptyTEnvL emptyCEnvL)
  where
  absurdE : Empty -> Empty'
  absurdE ()

------------------------------------------------------------------------
-- PART 5 — THE GAP: INTERNAL vs META
------------------------------------------------------------------------

-- META-LEVEL: the system IS consistent (proved above).
-- INTERNAL: can the system PROVE its own consistency?
--
-- ConN says "no proof code yields fbot."
-- To prove ConN internally (as a ProofN n formula), the system
-- would need to verify, for a GENERIC code variable, that it
-- doesn't prove fbot. But:
-- - ax-eval only works on CLOSED CExps (not code variables)
-- - cgen introduces the quantifier but the body can't be proved
--   without evaluating ccheck on a variable
-- - No axiom produces fimp (fceq ...) fbot directly
--
-- So ConN is NOT internally derivable via the current rules.
-- This is the Goedel-II barrier.

-- The internal consistency type (not inhabited):
InternalConsistencyN : Nat -> Set
InternalConsistencyN n =
  Sigma Code (\ p -> Eq (checkProofN n p) (just ConN))

-- We do NOT prove Not (InternalConsistencyN n) here, because
-- that would require structural analysis of all checkProofN outputs.
-- Instead, we note that:
-- - Instance reflection (Part 2) verifies each SPECIFIC code
-- - But cannot lift to the UNIVERSAL statement ConN
-- - This gap IS the content of Goedel II

------------------------------------------------------------------------
-- PART 6 — NELSON THEOREM (packaged)
------------------------------------------------------------------------

-- The corrected Nelson program, as a single record:
--
-- 1. The open (propositional) fragment is consistent.
-- 2. The fuel-based system can reflect each specific proof instance.
-- 3. The system is meta-level consistent.
-- 4. The gap: internal universal consistency is not derivable
--    from instance reflection.

-- Component 1: Open consistency
nelson-open : OpenProof fbot -> Empty'
nelson-open = open-consistent

-- Component 2: Instance-by-instance reflection
nelson-instance :
  (n : Nat) (p : Code) (A : Formula) ->
  Eq (checkProofN (suc n) p) (just A) ->
  ReflectN (suc (suc (suc n))) p A
nelson-instance = instance-reflection

-- Component 3: Meta-level consistency
nelson-meta : Proof fbot -> Empty
nelson-meta = meta-consistent

-- Component 4: The gap (stated as a type, not proved impossible,
-- but explained as the Goedel-II barrier)
NelsonGap : Set
NelsonGap = (n : Nat) -> InternalConsistencyN n -> Empty'

-- NelsonGap would say: ConN is unprovable at every fuel level.
-- This follows from Goedel II but we do not formalize the full
-- internal argument here.

------------------------------------------------------------------------
-- INTERPRETATION
------------------------------------------------------------------------

-- What Nelson got right:
--
-- 1. The open fragment admits a simple consistency proof (valuation).
--    Our open-sound proves this in 4 lines.
--
-- 2. Each specific proof can be individually verified by the system.
--    Our instance-reflection (D1-fuel) proves this.
--
-- 3. Instance verification can be iterated (D3-fuel): the system
--    can certify its own certifications, with bounded fuel overhead.
--
-- What Nelson's program required but could not achieve:
--
-- 4. Lifting instance verification to universal internal consistency.
--    Our formalization shows this IS the Goedel-II step:
--    - ax-eval works on closed CExps (specific codes)
--    - ConN requires reasoning about code VARIABLES
--    - The passage from one to the other needs internal soundness
--    - Which the system cannot provide for itself
--
-- The Buss-Tao objection ("requires assuming S* is consistent")
-- corresponds precisely to our observation that internal consistency
-- requires internal soundness, which is the Goedel-II barrier.
--
-- CONCLUSION:
--   Nelson correctly identified that instance verification is
--   available and open consistency is provable. The gap between
--   these and universal internal consistency is real, precisely
--   located, and is the formal content of Goedel's second theorem.
