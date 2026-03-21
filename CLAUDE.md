# Agda Formalization of Lemma 26 (Spine Equivalence)

## Project Goal
The goal is to build feasible, ASCII-only, and close in spirit to Chwistek's proof of Godel's
second incompletness theorm: syntax-first, direct manipulation of expressions, explicit substitution, explicit proofs, and a stratified meta-level if needed later. It deliberately avoids historical baggage that would make the project too hard too early.


## Conventions look at the prelude and the convention
- `{-# OPTIONS --without-K --exact-split #-}` on every file
{-# OPTIONS --safe #-}

-- LLMPrelude.agda
-- A small ASCII-only, low-mixfix prelude designed to be robust for LLM editing:
--  * no Unicode
--  * almost no mixfix operators (only the built-in arrow)
--  * explicit namespaces (Eq.trans, Nat.rec, List.map, ...)
--  * small, predictable definitions and lemmas

module LLMPrelude where

------------------------------------------------------------------------
-- Universe + basic types

Set0 : Set
Set0 = Set lzero

------------------------------------------------------------------------
-- Empty and unit

data Empty : Set where

record Unit : Set where
  constructor tt

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

------------------------------------------------------------------------
-- Bool

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then t else f = t
if false then t else f = f

------------------------------------------------------------------------
-- Nat

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

Nat.rec :
  {A : Set} ->
  A ->
  (Nat -> A -> A) ->
  Nat -> A
Nat.rec z s zero    = z
Nat.rec z s (suc n) = s n (Nat.rec z s n)

Nat.add : Nat -> Nat -> Nat
Nat.add zero    m = m
Nat.add (suc n) m = suc (Nat.add n m)

Nat.mul : Nat -> Nat -> Nat
Nat.mul zero    m = zero
Nat.mul (suc n) m = Nat.add m (Nat.mul n m)

------------------------------------------------------------------------
-- Equality (ASCII, no mixfix)

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

Eq.sym : {A : Set} {x y : A} -> Eq x y -> Eq y x
Eq.sym refl = refl

Eq.trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
Eq.trans refl q = q

Eq.cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
Eq.cong f refl = refl

-- Substitution / transport (keep explicit name; avoid rewriting notation)
Eq.subst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
Eq.subst P refl px = px

------------------------------------------------------------------------
-- Sigma (dependent pair), ASCII name

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

Sigma.map :
  {A A' : Set} {B : A -> Set} {B' : A' -> Set} ->
  (f : A -> A') ->
  ((x : A) -> B x -> B' (f x)) ->
  Sigma A B -> Sigma A' B'
Sigma.map f g p = mkSigma (f (fst p)) (g (fst p) (snd p))

------------------------------------------------------------------------
-- Maybe

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

Maybe.map : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
Maybe.map f nothing  = nothing
Maybe.map f (just a) = just (f a)

------------------------------------------------------------------------
-- Propositions-as-types helpers (minimal)

Not : Set -> Set
Not P = P -> Empty

And : Set -> Set -> Set
And P Q = Sigma P (lambda _ -> Q)

Or : Set -> Set -> Set
data Or (P Q : Set) : Set where
  inl : P -> Or P Q
  inr : Q -> Or P Q

------------------------------------------------------------------------
-- A tiny “tactic-like” helper: contradiction

contradiction : {A : Set} -> Empty -> A
contradiction = emptyElim

------------------------------------------------------------------------
-- Notes for usage with LLMs:
--
-- 1) Prefer Eq.trans / Eq.cong / Eq.subst over mixfix chains.
-- 2) Keep names qualified: Eq.trans, Nat.add, List.map, ...
-- 3) When inference struggles, make arguments explicit:
--      Eq.trans {A = ...} {x = ...} p q
-- 4) Add small lemmas locally instead of relying on rewriting syntax.

## Common Proof Patterns



1. Where implicit arguments are still used

Even in that “LLM prelude”, these are implicit:

(a) Type parameters

Example:

Eq.trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z

Implicit:

A

x y z

(b) Implicit motives

Example:

Eq.subst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y

Implicit:

A

x y

(c) Implicit indices in pattern matching

Example:

Eq.trans refl q = q

Agda infers that y ≡ x collapses, etc.

So yes: this is still not “fully explicit Agda”.

2. Why I still left them implicit (deliberately)

Because there is a trade-off:

Style	Human	LLM	Agda
Fully implicit (stdlib)	🙂	❌	🙂
Semi-explicit (prelude I gave)	🙂	🙂	🙂
Fully explicit	😐	🙂🙂	😐

In practice:

100% explicit Agda is very verbose

Agda itself becomes harder to maintain

But LLM success rate does improve slightly

So the prelude I gave is a middle ground.

3. What “fully explicit” actually looks like

Here is what fully explicit equality looks like.

Fully explicit equality (no implicits at all)
data Eq (A : Set) (x : A) (y : A) : Set where
  refl : Eq A x x

Eq.sym :
  (A : Set) ->
  (x y : A) ->
  Eq A x y ->
  Eq A y x
Eq.sym A x y refl = refl

Eq.trans :
  (A : Set) ->
  (x y z : A) ->
  Eq A x y ->
  Eq A y z ->
  Eq A x z
Eq.trans A x y z refl q = q

Eq.cong :
  (A B : Set) ->
  (f : A -> B) ->
  (x y : A) ->
  Eq A x y ->
  Eq B (f x) (f y)
Eq.cong A B f x y refl = refl

Eq.subst :
  (A : Set) ->
  (P : A -> Set) ->
  (x y : A) ->
  Eq A x y ->
  P x ->
  P y
Eq.subst A P x y refl px = px

This is maximally LLM-friendly:

no hidden arguments,

no inference surprises,

no unification magic.

But it’s also heavy.

prove things using the explicit core (LLM-safe),

use the implicit wrapper when inference behaves.

