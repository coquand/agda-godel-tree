{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.AbsFun1 -- a single-variable bracket-abstraction DSL.
--
-- An  Exp  is a Term-valued expression in ONE distinguished variable
-- (the leaf  evar ), with leaves  econst c  ( c : Term  with  NoVar c )
-- and nodes  eap1 f / eap2 g  (object Fun1 / Fun2 application).
--
--   denote e x   : the Term obtained by plugging  x  for  evar .
--   compile e    : Fun1  --  the bracket-abstraction  \ evar -> denote e .
--   compile_eq   : Deriv (eqF (ap1 (compile e) x) (denote e x))   for ALL x.
--
-- This is the generic combinatory-completeness fact:  every Term
-- expression in one variable, built from object Fun1/Fun2 and var-free
-- constants, is the  ap1  image of a genuine  Fun1 , witnessed by a
-- PROVED  Deriv  (NOT a definitional/meta  Eq  --  ap1 (compile e) x
-- has head  ap1  while  denote e x  generally does not).
--
-- The const recursion specialises  BRA4.Thm12.ConstTermFun1 ; the only
-- new case is  evar -> u  ( ap1 u x = x  via  ax_u ).

module BRA4.AbsFun1 where

open import BRA4.Base
open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; constTermFun1 ; constTermFun1_eq )

------------------------------------------------------------------------
-- The one-variable expression language.

data Exp : Set where
  evar   : Exp
  econst : (c : Term) -> NoVar c -> Exp
  eap1   : Fun1 -> Exp -> Exp
  eap2   : Fun2 -> Exp -> Exp -> Exp

------------------------------------------------------------------------
-- Denotation : plug  x  for  evar .

denote : Exp -> Term -> Term
denote evar          x = x
denote (econst c _)  x = c
denote (eap1 f e)    x = ap1 f (denote e x)
denote (eap2 g a b)  x = ap2 g (denote a x) (denote b x)

------------------------------------------------------------------------
-- Compilation to a Fun1.

compile : Exp -> Fun1
compile evar          = u
compile (econst c _)  = constTermFun1 c
compile (eap1 f e)    = compose1U f (compile e)
compile (eap2 g a b)  = C g (compile a) (compile b)

------------------------------------------------------------------------
-- Correctness :  ap1 (compile e) x = denote e x   as a PROVED Deriv.

compile_eq :
  (e : Exp) (x : Term) ->
  Deriv (eqF (ap1 (compile e) x) (denote e x))
compile_eq evar         x = ax_u x
compile_eq (econst c nv) x = constTermFun1_eq c nv x
compile_eq (eap1 f e)   x =
  ruleTrans (axComp f (compile e) x) (cong1 f (compile_eq e x))
compile_eq (eap2 g a b) x =
  let e1 : Deriv (eqF (ap1 (C g (compile a) (compile b)) x)
                       (ap2 g (ap1 (compile a) x) (ap1 (compile b) x)))
      e1 = axComp2 g (compile a) (compile b) x

      eL : Deriv (eqF (ap2 g (ap1 (compile a) x) (ap1 (compile b) x))
                       (ap2 g (denote a x) (ap1 (compile b) x)))
      eL = congL g (ap1 (compile b) x) (compile_eq a x)

      eR : Deriv (eqF (ap2 g (denote a x) (ap1 (compile b) x))
                       (ap2 g (denote a x) (denote b x)))
      eR = congR g (denote a x) (compile_eq b x)
  in ruleTrans e1 (ruleTrans eL eR)
