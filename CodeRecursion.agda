{-# OPTIONS --without-K --exact-split #-}

module CodeRecursion where

open import ChwistekSyntax
open import ChwistekCodeLogic
open import ChwistekSoundness

------------------------------------------------------------------------
-- Recursor for Code (binary trees)
------------------------------------------------------------------------

Code-rec : {X : Set} ->
  (Nat -> X) -> (Code -> Code -> X -> X -> X) -> Code -> X
Code-rec ac nc (catom n)   = ac n
Code-rec ac nc (cnode a b) = nc a b (Code-rec ac nc a) (Code-rec ac nc b)

------------------------------------------------------------------------
-- Uniqueness: any two functions satisfying the same recursion
-- equations on Code are pointwise equal
------------------------------------------------------------------------

Code-rec-unique :
  {X : Set} ->
  (ac : Nat -> X) ->
  (nc : Code -> Code -> X -> X -> X) ->
  (f g : Code -> X) ->
  ((n : Nat) -> Eq (f (catom n)) (ac n)) ->
  ((a b : Code) -> Eq (f (cnode a b)) (nc a b (f a) (f b))) ->
  ((n : Nat) -> Eq (g (catom n)) (ac n)) ->
  ((a b : Code) -> Eq (g (cnode a b)) (nc a b (g a) (g b))) ->
  (c : Code) -> Eq (f c) (g c)
Code-rec-unique ac nc f g fa fn ga gn (catom n) =
  eqTrans (fa n) (eqSym (ga n))
Code-rec-unique ac nc f g fa fn ga gn (cnode a b) =
  eqTrans (fn a b)
    (eqTrans
      (eqCong2 (nc a b)
        (Code-rec-unique ac nc f g fa fn ga gn a)
        (Code-rec-unique ac nc f g fa fn ga gn b))
      (eqSym (gn a b)))
  where
  eqCong2 : {A B C : Set} (h : A -> B -> C) {x1 x2 : A} {y1 y2 : B} ->
    Eq x1 x2 -> Eq y1 y2 -> Eq (h x1 y1) (h x2 y2)
  eqCong2 h refl refl = refl
