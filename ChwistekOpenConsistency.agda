{-# OPTIONS --without-K --exact-split #-}

module ChwistekOpenConsistency where

open import ChwistekSyntax

------------------------------------------------------------------------
-- The open (quantifier-free) fragment of the proof system
------------------------------------------------------------------------

-- OpenProof is the subsystem without gen, cgen: only propositional
-- axioms and modus ponens. This is the "open" fragment in Nelson's
-- sense — no induction, no quantifiers.

data OpenProof : Formula -> Set where
  ax-refl-o : (t : Term) -> OpenProof (feq t t)
  ax-k-o    : (A B : Formula) -> OpenProof (fimp A (fimp B A))
  ax-s-o    : (A B C : Formula) ->
              OpenProof (fimp (fimp A (fimp B C))
                        (fimp (fimp A B)
                              (fimp A C)))
  mp-o      : {A B : Formula} ->
              OpenProof (fimp A B) -> OpenProof A -> OpenProof B

------------------------------------------------------------------------
-- Propositional valuation ("Good")
------------------------------------------------------------------------

-- A formula is "good" if it holds under the valuation where all
-- atoms (feq, fcode, fceq) are trivially true and quantified
-- formulas (fall, fcAll) are trivially true. Only the propositional
-- structure matters: fimp is function space, fbot is Empty.

data Empty : Set where

data Unit : Set where
  tt : Unit

Good : Formula -> Set
Good fbot         = Empty
Good (feq _ _)    = Unit
Good (fimp a b)   = Good a -> Good b
Good (fall _)     = Unit
Good (fcode _)    = Unit
Good (fceq _ _)   = Unit
Good (fcAll _)    = Unit

------------------------------------------------------------------------
-- Soundness of the open fragment under Good
------------------------------------------------------------------------

-- Every formula provable in the open fragment is Good.
-- The proof is the standard tautology argument.

open-sound : {A : Formula} -> OpenProof A -> Good A
open-sound (ax-refl-o t)   = tt
open-sound (ax-k-o A B)    = \ x -> \ _ -> x
open-sound (ax-s-o A B C)  = \ f -> \ g -> \ a -> f a (g a)
open-sound (mp-o pf1 pf2)  = open-sound pf1 (open-sound pf2)

------------------------------------------------------------------------
-- Open consistency
------------------------------------------------------------------------

-- The open fragment cannot prove fbot.
-- Proof: if OpenProof fbot, then Good fbot = Empty. Contradiction.

open-consistent : OpenProof fbot -> Empty
open-consistent pf = open-sound pf

------------------------------------------------------------------------
-- Connection to the full system
------------------------------------------------------------------------

-- The full system (Proof) extends OpenProof with gen and cgen.
-- Every OpenProof is a Proof:

embed : {A : Formula} -> OpenProof A -> Proof A
embed (ax-refl-o t)   = ax-refl t
embed (ax-k-o A B)    = ax-k A B
embed (ax-s-o A B C)  = ax-s A B C
embed (mp-o pf1 pf2)  = mp (embed pf1) (embed pf2)

-- So open-consistent says: no formula provable in the propositional
-- fragment of the full system is fbot. This is a proper consistency
-- result for a subsystem.

------------------------------------------------------------------------
-- Nelson's observation
------------------------------------------------------------------------

-- Nelson (2013/2015) pointed out that PRA can prove the "open
-- consistency" of its arithmetization — i.e., the consistency of
-- the quantifier-free/induction-free fragment.
--
-- Our open-consistent theorem is exactly this kind of result:
-- the propositional fragment (ax-refl, ax-k, ax-s, mp) is
-- consistent, and the proof is a simple valuation argument.
--
-- The proof works because:
-- 1. Good is a valid interpretation (fbot -> Empty, fimp -> function)
-- 2. All axioms are Good (they are propositional tautologies)
-- 3. mp preserves Good (modus ponens preserves truth)
-- 4. fbot is not Good
--
-- This is the Hilbert-Ackermann-style consistency argument that
-- Nelson planned to internalize within PRA itself.
--
-- KEY CONTRAST with Goedel II:
-- - Open consistency IS provable (by a simple valuation)
-- - Full consistency is NOT provable internally (Goedel II)
-- - The difference is exactly the quantifier/induction rules
--   that the open fragment omits
--
-- This confirms Nelson's structural observation: the "open"
-- fragment is weak enough to admit a self-consistency proof,
-- while the full system with induction/quantifiers crosses
-- the Goedel barrier.
