{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefBigConjN -- the number-code Pi_1 K-formula "no program  k <= M  describes
-- day  r ", as a right-nested big conjunction of per-program negations
-- ( clos line 14 :  K(u) > L*  =  /\_p not (define_p l u) ;
--   SURPRISE-GII-NUMBERCODE-HANDOFF S3.4 ).
--
-- Number-code mirror of  T4.SurpriseG2.KdefBigConj  with the describe atom
-- re-pointed to  runProgN  ( enum = identity, program  k  IS the number  k ).
--
--   perProgNegN r k = neg (describeAtN k r (var 0))
--                   = neg ( runProgN (natCode k) (var 0) = s (natCode r) )
--   KdefBigConjN M r = perProgNegN r M  /\  ...  /\  perProgNegN r 0
--
-- ( right-nested  conjF , largest index outermost -- matching
--   StepFrontEndN.aggregateImpN / AndLemmas.liftedAndIntro ).

open import T4.Base
open import T4.SurpriseG2.BigConjFormula using ( conjF )
open import T4.StagePredFN using ( describeAtN )

module T4.KdefBigConjN where

-- The per-program negation : program  k  does NOT describe day  r .
perProgNegN : (r : Nat) (k : Nat) -> Formula
perProgNegN r k = neg (describeAtN k r (var zero))

-- The big conjunction over programs  k = 0 .. M .
KdefBigConjN : (M : Nat) (r : Nat) -> Formula
KdefBigConjN zero     r = perProgNegN r zero
KdefBigConjN (suc M') r = conjF (perProgNegN r (suc M')) (KdefBigConjN M' r)
