{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.BRA -- single-layer formal system over BRA-terms.
--
-- Faithful transcription of Guard 1963 BRA (Logic Seminar, Princeton,
-- 1958-59 / Church) at the Agda level, supplanting the two-layer
-- Deriv/Provable split.
--
-- Architecture (see Guard/BRA-DESIGN.md):
--
--   * The equational kernel (Deriv, thmT validator, ProofEnc for
--     equations, etc.) is reused unchanged.  Deriv-level theorems
--     embed into BRA via  fromDeriv  (polymorphic lift).
--
--   * The propositional/formula-level axioms Ax 11-13 and the rules
--     mp, sub, ind live at the BRA layer as constructors of this
--     data type.
--
--   * The equational axioms Ax 4-7 (equality congruences) are
--     available both as BRA constructors (for convenience in
--     propositional chains) and via  fromDeriv  on Deriv-level
--     congruences.  Ax 0-3 and 8-10 are subsumed via  fromDeriv  on
--     the corresponding Deriv axioms (axI, axFst, axConst, ...,
--     axComp2, axPost, ...).
--
--   * The substitution rule  ruleSub  carries an explicit
--     Eq-side-condition  substF x t hyp = hyp , matching Option A's
--     soundness discipline for the Deriv-level  ruleInst .  Use at
--     hyp = atomic Triv (closed) is free, matching the typical use
--     case.
--
--   *  ruleInd  (induction on var zero) is included as a reservation
--     but is not strictly needed for Guard Th 14.
--
-- This data type mirrors Guard 1963 Def 9-11 (axioms) and Guard's
-- derivation rules.  Guard's  th  enumerator is our  thmT  —
-- extended with formula-level dispatches in a follow-up commit.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.BRA where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv)
open import Guard.Formula

------------------------------------------------------------------------
-- BRA hyp P : "from a single Formula hypothesis  hyp ,  P  is
-- derivable in BRA".
--
-- Follows Guard 1963: axioms Ax 0-13 (equational ones embedded via
-- fromDeriv; propositional Ax 11-13 explicit), rules mp, sub, ind.

data BRA (hyp : Formula) : Formula -> Set where

  ------------------------------------------------------------------
  -- Embedding from the Deriv kernel.
  --
  -- Any Deriv-level equational fact polymorphic in its hypothesis
  -- (i.e. a theorem of the equational kernel) lifts to an atomic
  -- BRA statement at any BRA-level  hyp .  This is how equations
  -- like  axI, axFst, axComp, axRecNd, ...  enter BRA.

  fromDeriv : {eq : Equation} ->
              ({h : Equation} -> Deriv h eq) ->
              BRA hyp (atomic eq)

  ------------------------------------------------------------------
  -- Hypothesis.

  ruleHypB : BRA hyp hyp

  ------------------------------------------------------------------
  -- Propositional axioms (Guard 1963 Ax 11, 12, 13).

  -- Ax 11 (K):  P ⊃ . Q ⊃ P .
  axK : (P Q : Formula) ->
        BRA hyp (P imp (Q imp P))

  -- Ax 12 (S):  P ⊃ (Q ⊃ R) ⊃ . P ⊃ Q ⊃ . P ⊃ R .
  axS : (P Q R : Formula) ->
        BRA hyp ((P imp (Q imp R))
                  imp ((P imp Q) imp (P imp R)))

  -- Ax 13 (classical contraposition):  ~P ⊃ ~Q ⊃ . Q ⊃ P .
  axNeg : (P Q : Formula) ->
          BRA hyp ((not P) imp ((not Q) imp (Q imp P)))

  ------------------------------------------------------------------
  -- Equality axioms lifted to BRA (Guard 1963 Ax 4-7).
  --
  -- Available as BRA constructors for convenience when building
  -- propositional chains; equivalent to  fromDeriv  on the Deriv-
  -- level congruences.  Guard 1963 treats these uniformly alongside
  -- the propositional axioms in his single-layer system.

  -- Ax 4:  a = b ⊃ . a = c ⊃ b = c .
  axEqTrans : (a b c : Term) ->
              BRA hyp ((atomic (eqn a b))
                        imp ((atomic (eqn a c))
                              imp (atomic (eqn b c))))

  -- Ax 5:  a = b ⊃ f(a) = f(b) .
  axEqCong1 : (f : Fun1) (a b : Term) ->
              BRA hyp ((atomic (eqn a b))
                        imp (atomic (eqn (ap1 f a) (ap1 f b))))

  -- Ax 6:  a = b ⊃ g(a,c) = g(b,c) .
  axEqCongL : (g : Fun2) (a b c : Term) ->
              BRA hyp ((atomic (eqn a b))
                        imp (atomic (eqn (ap2 g a c) (ap2 g b c))))

  -- Ax 7:  a = b ⊃ g(c,a) = g(c,b) .
  axEqCongR : (g : Fun2) (a b c : Term) ->
              BRA hyp ((atomic (eqn a b))
                        imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

  ------------------------------------------------------------------
  -- Modus ponens.

  mp : {P Q : Formula} ->
       BRA hyp (P imp Q) ->
       BRA hyp P ->
       BRA hyp Q

  ------------------------------------------------------------------
  -- Substitution rule with Eq-side-condition (Option A discipline).
  --
  -- Under the side condition  substF x t hyp = hyp  (i.e., the
  -- substitution is a no-op on the ambient hypothesis), we may
  -- substitute  t  for  var x  in any BRA-derivable  P  to obtain a
  -- BRA-derivable  substF x t P .
  --
  -- When  hyp = atomic Triv  (the closed trivial hypothesis), the
  -- side condition is trivially satisfied for every  (x, t) .  This
  -- is the standard sound use case: substitution in closed-hypothesis
  -- theorems.
  --
  -- Mirrors Guard 1963's substitution rule (sb) in Def 12 alongside
  -- the corresponding sb / sbt / sbf / sub functors.

  ruleSub : (x : Nat) (t : Term) {P : Formula} ->
            Eq (substF x t hyp) hyp ->
            BRA hyp P ->
            BRA hyp (substF x t P)

  ------------------------------------------------------------------
  -- Induction rule (reserved; not needed for Guard Th 14).
  --
  -- Placeholder; if Guard Th 14's chain turns out to require it
  -- (Guard's rule ind), it will be filled in.  For the chain as
  -- outlined in guard15.pdf p.17, mp + sub + the encoded
  -- tautologies  t, t'  suffice.
  --
  -- The form would be:
  --
  --   ruleInd : (P : Formula) ->
  --             BRA hyp (substF zero O P) ->                      -- base P(0)
  --             BRA hyp (P imp substF zero (succ (var zero)) P) -> -- step P(x) -> P(s x)
  --             Eq (substF zero O hyp) hyp ->                      -- hyp closed in x_0
  --             BRA hyp P
  --
  -- not added at this stage; revisit if the chain proves to need it.

------------------------------------------------------------------------
-- Notes
--
-- (1) BRA subsumes Provable: every Provable constructor has a BRA
-- counterpart of the same type (renaming  ruleHypP  to  ruleHypB ).
-- Modules originally built against Provable port by substituting
-- names and adding the (trivial) Eq-side-condition for any
-- ruleSub introduction.
--
-- (2) The BRA-layer equality axioms  axEqTrans / axEqCong1 /
-- axEqCongL / axEqCongR  are propositionally equivalent to their
--  fromDeriv  forms.  Kept as constructors for ergonomics; callers
-- can use either.
--
-- (3) Soundness.  BRA admits a standard semantics where:
--     - Formulas are interpreted classically (not_, _imp_ standard).
--     - Atomic equations interpret via the standard tree model.
--     - mp, ruleSub preserve validity under the Eq side condition.
--     - axK, axS, axNeg are classical tautologies.
-- We do not re-prove the soundness bridge here; it mirrors
-- Guard/ProvableSound.agda with  ruleSub  discharged by its side-
-- condition witness.  Will be provided in a follow-up commit if
-- needed.
