{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.TermEq -- decidable equality functors for inspecting Term codes
-- inside the verifier.
--
-- Two distinct operations live here:
--
--   * tagEq : Fun2     -- Nat-equality on natCode-shaped Terms.  Used
--                         to check tag values  (e.g.  tagEq head
--                         (natCode tag_imp) ).  Reused from BRA3 as
--                         the existing  natEqF .  Returns  s O  on
--                         equal natCodes,  O  otherwise.
--
--   * codeEq : Fun2    -- Structural equality on Pair-coded Terms
--                         (recursive on Fst/Snd).  Returns  s O  on
--                         syntactically equal codes,  O  otherwise.
--                         Built via course-of-values recursion on the
--                         Cantor-index of the input.
--                         IMPLEMENTATION DEFERRED -- see PLAN below.
--
-- For the BRA4 handlers (mp / sb / ind):
--   * tag dispatch uses  tagEq head (natCode tag_X) .
--   * antecedent matching in mp_handler uses  codeEq val_ant x .
--
-- PLAN for codeEq (next session):
--   Use  BRA3.CourseOfValuesRec.courseOfValues  on the Cantor-index of
--   the first argument.  At each step, dispatch on (isLeaf? both, Pair?
--   both, mismatch): tagEq Fst/Fst -> condFork to recurse on Snd/Snd
--   via the prevTable, AND-chain results into a final  s O / O .
--   Strict-decrease holds because  Fst(Pair k x) < Pair k x  and
--   Snd(Pair k x) < Pair k x  in the Cantor order (since tag >= 1).

module BRA4.TermEq where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

------------------------------------------------------------------------
-- tagEq -- Nat-equality on natCode-shaped Terms.

open import BRA3.SubT.NatEq public using
  ( natEqF ; natEq_eq ; natEq_neq_gt )

tagEq : Fun2
tagEq = natEqF

------------------------------------------------------------------------
-- Closure lemmas:
--
--   tagEq_refl : ap2 tagEq (natCode n) (natCode n) =Deriv= s O
--   tagEq_neq  : ap2 tagEq (natCode (suc (addN a n))) (natCode n) =Deriv= O

tagEq_refl :
  (n : Nat) ->
  Deriv (eqF (ap2 tagEq (natCode n) (natCode n)) (ap1 s O))
tagEq_refl = natEq_eq

------------------------------------------------------------------------
-- codeEq -- structural equality on Pair-coded Terms.  STUB until full
-- implementation in next session.

-- codeEq : Fun2
-- codeEq = ...                                                         -- TODO
--
-- Closure equations needed:
--   codeEq_refl : (t : Term) -> Deriv (eqF (ap2 codeEq t t) (ap1 s O))
--   codeEq_neq_natCode :
--     (m n : Nat) -> Eq (natEq m n) false ->
--     Deriv (eqF (ap2 codeEq (natCode m) (natCode n)) O)
--   codeEq_neq_shape :
--     -- Pair vs leaf mismatch returns O.
--   codeEq_pair :
--     (a1 b1 a2 b2 : Term) ->
--     Deriv (eqF (ap2 codeEq (ap2 Pair a1 b1) (ap2 Pair a2 b2))
--                 (andTerm (ap2 codeEq a1 a2) (ap2 codeEq b1 b2)))
--     -- where andTerm is a Fun2 with andTerm (s O) (s O) = s O ; O else.
