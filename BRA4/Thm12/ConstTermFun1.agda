{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.ConstTermFun1 -- a Fun1 that returns a fixed (var-free)
-- Term constant regardless of its input.
--
--   NoVar : Term -> Set
--   NoVar predicate : Term is built from O, ap1 (any Fun1), ap2 (any
--   Fun2)  -- no  var  constructor.
--
--   constTermFun1 : Term -> Fun1
--   constTermFun1 z = a Fun1 whose application to any X equals z
--                     (assuming NoVar z).
--
--   constTermFun1_eq :
--     (z : Term) -> NoVar z -> (X : Term) ->
--     Deriv (eqF (ap1 (constTermFun1 z) X) z)
--
-- The construction mirrors z's structure :
--   O          -> o                        (ax_o gives O regardless)
--   ap1 f t    -> compose1U f (rec t)      (axComp)
--   ap2 g a b  -> C g (rec a) (rec b)      (ax_C)
--
-- The (var k) case is impossible under NoVar.  We use a placeholder
-- (o) but it is never reached during constTermFun1_eq evaluation.

module BRA4.Thm12.ConstTermFun1 where

open import BRA4.Base
open import BRA4.Tags

------------------------------------------------------------------------
-- A local Pair-of-evidence record (Agda has no built-in And).

record NoVarAnd (A B : Set) : Set where
  constructor mkAnd
  field
    fstAnd : A
    sndAnd : B
open NoVarAnd public

------------------------------------------------------------------------
-- NoVar predicate.

NoVar : Term -> Set
NoVar O          = Unit
NoVar (var _)    = Empty
NoVar (ap1 _ t)  = NoVar t
NoVar (ap2 _ a b) = NoVarAnd (NoVar a) (NoVar b)

------------------------------------------------------------------------
-- NoVar (natCode k) for any k.

NoVar_natCode : (k : Nat) -> NoVar (natCode k)
NoVar_natCode zero    = tt
NoVar_natCode (suc n) = NoVar_natCode n

------------------------------------------------------------------------
-- NoVar (Pair a b) helpers.

NoVar_pair :
  (a b : Term) -> NoVar a -> NoVar b -> NoVar (ap2 Pair a b)
NoVar_pair _ _ na nb = mkAnd na nb

NoVar_pair_natCode :
  (k : Nat) (b : Term) -> NoVar b -> NoVar (ap2 Pair (natCode k) b)
NoVar_pair_natCode k b nb = mkAnd (NoVar_natCode k) nb

------------------------------------------------------------------------
-- constTermFun1.

constTermFun1 : Term -> Fun1
constTermFun1 O           = o
constTermFun1 (var _)     = o            -- placeholder; unreachable under NoVar
constTermFun1 (ap1 f t)   = compose1U f (constTermFun1 t)
constTermFun1 (ap2 g a b) = C g (constTermFun1 a) (constTermFun1 b)

------------------------------------------------------------------------
-- Correctness : constTermFun1 z applied to anything returns z.

constTermFun1_eq :
  (z : Term) -> NoVar z -> (X : Term) ->
  Deriv (eqF (ap1 (constTermFun1 z) X) z)
constTermFun1_eq O          _           X = ax_o X
constTermFun1_eq (var _)    ()          X
constTermFun1_eq (ap1 f t)  nv          X =
  let ih : Deriv (eqF (ap1 (constTermFun1 t) X) t)
      ih = constTermFun1_eq t nv X
      e1 : Deriv (eqF (ap1 (compose1U f (constTermFun1 t)) X)
                       (ap1 f (ap1 (constTermFun1 t) X)))
      e1 = axComp f (constTermFun1 t) X
  in ruleTrans e1 (cong1 f ih)
constTermFun1_eq (ap2 g a b) (mkAnd na nb) X =
  let iha : Deriv (eqF (ap1 (constTermFun1 a) X) a)
      iha = constTermFun1_eq a na X
      ihb : Deriv (eqF (ap1 (constTermFun1 b) X) b)
      ihb = constTermFun1_eq b nb X
      e1 : Deriv (eqF (ap1 (C g (constTermFun1 a) (constTermFun1 b)) X)
                       (ap2 g (ap1 (constTermFun1 a) X) (ap1 (constTermFun1 b) X)))
      e1 = ax_C g (constTermFun1 a) (constTermFun1 b) X
  in ruleTrans e1
       (ruleTrans (congL g (ap1 (constTermFun1 b) X) iha)
                  (congR g a ihb))
