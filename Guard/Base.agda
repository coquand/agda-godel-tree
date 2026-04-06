{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Base where

------------------------------------------------------------------------
-- Natural numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

------------------------------------------------------------------------
-- Bool

data Bool : Set where
  true  : Bool
  false : Bool

boolAnd : Bool -> Bool -> Bool
boolAnd true  b = b
boolAnd false b = false

natEq : Nat -> Nat -> Bool
natEq zero    zero    = true
natEq zero    (suc _) = false
natEq (suc _) zero    = false
natEq (suc n) (suc m) = natEq n m

boolCase : {A : Set} -> Bool -> A -> A -> A
boolCase true  t f = t
boolCase false t f = f

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

eqCong3 : {A B C D : Set} (f : A -> B -> C -> D)
         {x1 x2 : A} {y1 y2 : B} {z1 z2 : C}
         -> Eq x1 x2 -> Eq y1 y2 -> Eq z1 z2
         -> Eq (f x1 y1 z1) (f x2 y2 z2)
eqCong3 f refl refl refl = refl

eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px

------------------------------------------------------------------------
-- Sigma

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- Binary trees

data Tree : Set where
  lf : Tree
  nd : Tree -> Tree -> Tree

leftT : Tree -> Tree
leftT lf       = lf
leftT (nd a b) = a

rightT : Tree -> Tree
rightT lf       = lf
rightT (nd a b) = b

treeEq : Tree -> Tree -> Bool
treeEq lf       lf       = true
treeEq lf       (nd _ _) = false
treeEq (nd _ _) lf       = false
treeEq (nd a b) (nd c d) = boolAnd (treeEq a c) (treeEq b d)

------------------------------------------------------------------------
-- Tree recursion (metalevel)

treeRec : {A : Set} -> A -> (Tree -> Tree -> A -> A -> A) -> Tree -> A
treeRec z s lf       = z
treeRec z s (nd a b) = s a b (treeRec z s a) (treeRec z s b)

------------------------------------------------------------------------
-- natCode (encoding natural numbers as trees)

natCode : Nat -> Tree
natCode zero    = lf
natCode (suc n) = nd lf (natCode n)
