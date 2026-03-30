{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Base where

------------------------------------------------------------------------
-- Natural numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

add : Nat -> Nat -> Nat
add zero    m = m
add (suc n) m = suc (add n m)

------------------------------------------------------------------------
-- Empty and Unit

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

record Unit : Set where
  constructor tt

------------------------------------------------------------------------
-- Propositional equality

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
eqSym refl = refl

eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl q = q

eqCong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
eqCong f refl = refl

eqCong2 : {A B C : Set} (f : A -> B -> C) {x1 x2 : A} {y1 y2 : B}
         -> Eq x1 x2 -> Eq y1 y2 -> Eq (f x1 y1) (f x2 y2)
eqCong2 f refl refl = refl

eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px

eqCong3 : {A B C D : Set} (f : A -> B -> C -> D)
         {x1 x2 : A} {y1 y2 : B} {z1 z2 : C}
         -> Eq x1 x2 -> Eq y1 y2 -> Eq z1 z2
         -> Eq (f x1 y1 z1) (f x2 y2 z2)
eqCong3 f refl refl refl = refl

------------------------------------------------------------------------
-- Arithmetic lemmas

add-zero : (n : Nat) -> Eq (add n zero) n
add-zero zero    = refl
add-zero (suc n) = eqCong suc (add-zero n)

add-suc : (n m : Nat) -> Eq (add n (suc m)) (suc (add n m))
add-suc zero    m = refl
add-suc (suc n) m = eqCong suc (add-suc n m)

------------------------------------------------------------------------
-- Maybe

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

maybeMap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
maybeMap f nothing  = nothing
maybeMap f (just a) = just (f a)

maybeBind : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
maybeBind nothing  f = nothing
maybeBind (just a) f = f a

------------------------------------------------------------------------
-- Sigma

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- Fin (de Bruijn indices)

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fz     = zero
finToNat (fs i) = suc (finToNat i)

natToFin : (n : Nat) -> Nat -> Maybe (Fin n)
natToFin zero    k       = nothing
natToFin (suc n) zero    = just fz
natToFin (suc n) (suc k) = maybeMap fs (natToFin n k)

------------------------------------------------------------------------
-- Ordering on Nat

data Ordering : Set where
  lt : Ordering
  eq : Ordering
  gt : Ordering

compareNat : Nat -> Nat -> Ordering
compareNat zero    zero    = eq
compareNat zero    (suc m) = lt
compareNat (suc n) zero    = gt
compareNat (suc n) (suc m) = compareNat n m

------------------------------------------------------------------------
-- Predecessor (partial, returning zero for zero)

pred : Nat -> Nat
pred zero    = zero
pred (suc n) = n

------------------------------------------------------------------------
-- Bool

data Bool : Set where
  true  : Bool
  false : Bool

boolAnd : Bool -> Bool -> Bool
boolAnd true  b = b
boolAnd false b = false
