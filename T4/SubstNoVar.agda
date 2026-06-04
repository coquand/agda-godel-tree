{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SubstNoVar -- meta-equality lemma : substT is the identity on
-- closed (NoVar) Terms.
--
--   substT_NoVar :
--     (n : Nat) (t : Term) (s : Term) -> NoVar s ->
--     Eq (substT n t s) s
--
-- Structural induction on  s , dispatching on  NoVar 's three nontrivial
-- constructor cases (O, ap1, ap2)  and discharging the impossible  var
-- case with the absurd pattern  () .
--
-- This is the bridge needed by  T4.SurpriseG2.StageZeroNegsConj  to
-- collapse   substT zero O (ap1 enum (natCode progIx))   ===
--   ap1 enum (natCode progIx)
-- in the new conjunction-shape surprise-G2 framework's day-0 pigeonhole
-- discharge ( NoVar witnessed by  NoVar_natCode ) , and analogously for
-- any other closed-program slot .

module T4.SubstNoVar where

open import T4.Base
open import BRA3.Formula            using ( substT )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; NoVarAnd ; mkAnd ; fstAnd ; sndAnd )

------------------------------------------------------------------------
-- The lemma.

substT_NoVar :
  (n : Nat) (t : Term) (s : Term) ->
  NoVar s ->
  Eq (substT n t s) s
substT_NoVar n t O           _             = refl
substT_NoVar n t (var m)     ()
substT_NoVar n t (ap1 f a)   nv            =
  eqCong (ap1 f) (substT_NoVar n t a nv)
substT_NoVar n t (ap2 g a b) (mkAnd na nb) =
  let iha : Eq (substT n t a) a
      iha = substT_NoVar n t a na
      ihb : Eq (substT n t b) b
      ihb = substT_NoVar n t b nb
      -- ap2 g _ _ congruence in two steps.
      step1 : Eq (ap2 g (substT n t a) (substT n t b))
                 (ap2 g a            (substT n t b))
      step1 = eqCong (\ x -> ap2 g x (substT n t b)) iha
      step2 : Eq (ap2 g a (substT n t b)) (ap2 g a b)
      step2 = eqCong (\ y -> ap2 g a y) ihb
  in eqTrans step1 step2
