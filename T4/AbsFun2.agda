{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.AbsFun2 -- a TWO-variable bracket-abstraction DSL (the Fun2
-- analogue of T4.AbsFun1).
--
-- An  Exp2  is a Term-valued expression in TWO distinguished variables
-- (leaves  evar0 / evar1 ), with leaves  econst c  ( c : Term  with
--  NoVar c )  and nodes  eap1 f / eap2 g  (object Fun1 / Fun2 application).
--
--   denote2 e a b  : the Term obtained by plugging  a  for  evar0  and
--                    b  for  evar1 .
--   compile2 e     : Fun2  --  the bracket-abstraction  \ evar0 evar1 -> denote2 e .
--   compile2_eq    : Deriv (eqF (ap2 (compile2 e) a b) (denote2 e a b))  for ALL a b.
--
-- This is the two-input combinatory-completeness fact:  every Term
-- expression in two variables, built from object Fun1/Fun2 and var-free
-- constants, is the  ap2  image of a genuine  Fun2 , witnessed by a
-- PROVED  Deriv .   Used to build the shared object  Fun2  K-functor
-- ( code K(num x0, r) = ap2 Kfunctor x0 r )  and any two-slot data term
-- of the surprise-GII reformulation (subject  x0  +  run/index  r ).

module T4.AbsFun2 where

open import T4.Base
open import T4.Thm12.ConstTermFun1
  using ( NoVar ; constTermFun1 ; constTermFun1_eq )

------------------------------------------------------------------------
-- The two-variable expression language.

data Exp2 : Set where
  evar0  : Exp2
  evar1  : Exp2
  econst : (c : Term) -> NoVar c -> Exp2
  eap1   : Fun1 -> Exp2 -> Exp2
  eap2   : Fun2 -> Exp2 -> Exp2 -> Exp2

------------------------------------------------------------------------
-- Denotation : plug  a  for  evar0 ,  b  for  evar1 .

denote2 : Exp2 -> Term -> Term -> Term
denote2 evar0          a b = a
denote2 evar1          a b = b
denote2 (econst c _)   a b = c
denote2 (eap1 f e)     a b = ap1 f (denote2 e a b)
denote2 (eap2 g x y)   a b = ap2 g (denote2 x a b) (denote2 y a b)

------------------------------------------------------------------------
-- Compilation to a Fun2.
--   evar0      -> Const   ( ap2 Const a b = a )
--   evar1      -> v       ( ap2 v a b = b )
--   econst c   -> Lift1 (constTermFun1 c)   ( ap2 _ a b = ap1 (constTermFun1 c) a = c )
--   eap1 f e   -> Post f (compile2 e)       ( ap2 (Post f h) a b = ap1 f (ap2 h a b) )
--   eap2 g x y -> Fan (compile2 x) (compile2 y) g
--                                           ( ap2 (Fan h1 h2 h) a b = ap2 h (ap2 h1 a b) (ap2 h2 a b) )

compile2 : Exp2 -> Fun2
compile2 evar0         = Const
compile2 evar1         = v
compile2 (econst c _)  = Lift1 (constTermFun1 c)
compile2 (eap1 f e)    = Post f (compile2 e)
compile2 (eap2 g x y)  = Fan (compile2 x) (compile2 y) g

------------------------------------------------------------------------
-- Correctness :  ap2 (compile2 e) a b = denote2 e a b   as a PROVED Deriv.

compile2_eq :
  (e : Exp2) (a b : Term) ->
  Deriv (eqF (ap2 (compile2 e) a b) (denote2 e a b))
compile2_eq evar0        a b = axConst a b
compile2_eq evar1        a b = ax_v a b
compile2_eq (econst c nv) a b =
  ruleTrans (axLift (constTermFun1 c) a b) (constTermFun1_eq c nv a)
compile2_eq (eap1 f e)   a b =
  ruleTrans (axPost f (compile2 e) a b) (cong1 f (compile2_eq e a b))
compile2_eq (eap2 g x y) a b =
  let e1 : Deriv (eqF (ap2 (Fan (compile2 x) (compile2 y) g) a b)
                       (ap2 g (ap2 (compile2 x) a b) (ap2 (compile2 y) a b)))
      e1 = axFan (compile2 x) (compile2 y) g a b

      eL : Deriv (eqF (ap2 g (ap2 (compile2 x) a b) (ap2 (compile2 y) a b))
                       (ap2 g (denote2 x a b) (ap2 (compile2 y) a b)))
      eL = congL g (ap2 (compile2 y) a b) (compile2_eq x a b)

      eR : Deriv (eqF (ap2 g (denote2 x a b) (ap2 (compile2 y) a b))
                       (ap2 g (denote2 x a b) (denote2 y a b)))
      eR = congR g (denote2 x a b) (compile2_eq y a b)
  in ruleTrans e1 (ruleTrans eL eR)
