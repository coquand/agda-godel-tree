{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.IterComp -- the OBJECT-level iteration-composition lemma for  stepU :
--
--   iter stepU c (sigma a b)  =  iter stepU (iter stepU c a) b
--
-- universal in object Terms  c , a , b  (the fuels are object  sigma -terms,
-- NOT meta  natCode ).  This is the new ingredient the object-fuel mu-loop
-- correctness (P1, T4/CHAITIN-G1-P1-DESIGN.md PART B) needs to peel one
-- position's worth of fuel off a run.
--
-- Proved by ONE  ruleIndNat  on the exponent (var 2), at fresh slots
-- c = var 0 , a = var 1 , b = var 2 ; instantiated to arbitrary Terms by the
-- SIMULTANEOUS substitution  ruleInst3v  (T4.Counting) -- which places c/a/b
-- at the leaves WITHOUT traversing them, so opaque subterms (the per-position
-- predicate fuel) survive (nested  ruleInst  would get stuck on them).

module T4.IterComp where

open import T4.Base
open import T4.EvalUStep using ( stepU )

open import BRA3.CourseOfValues    using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import BRA3.Church            using ( sigma ; T33 ; T34 )
open import BRA3.RuleInst2         using ( ruleInst2 )
open import BRA3.Logic             using ( prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive    using ( compI )
open import T4.Counting          using ( ruleInst3v )

------------------------------------------------------------------------
-- A single iteration:  iter stepU X (s O) = stepU X .

iterStepO : (X : Term) -> Deriv (eqF (ap2 (iter stepU) X (ap1 s O)) (ap1 stepU X))
iterStepO X =
  ruleTrans (iter_step_univ stepU X O) (cong1 stepU (iter_base_univ stepU X))

------------------------------------------------------------------------
-- The universal composition at  c = var 0 , a = var 1 , b = var 2  (b = the
-- induction variable).

iterCompU :
  Deriv (eqF (ap2 (iter stepU) (var 0) (ap2 sigma (var 1) (var 2)))
             (ap2 (iter stepU) (ap2 (iter stepU) (var 0) (var 1)) (var 2)))
iterCompU = ruleIndNat 2 {P = P} base step
  where
    cc : Term
    cc = var 0
    aa : Term
    aa = var 1
    bb : Term
    bb = var 2

    P : Formula
    P = eqF (ap2 (iter stepU) cc (ap2 sigma aa bb))
            (ap2 (iter stepU) (ap2 (iter stepU) cc aa) bb)

    base : Deriv (eqF (ap2 (iter stepU) cc (ap2 sigma aa O))
                      (ap2 (iter stepU) (ap2 (iter stepU) cc aa) O))
    base =
      ruleTrans (congR (iter stepU) cc (T33 aa))
                (ruleSym (iter_base_univ stepU (ap2 (iter stepU) cc aa)))

    T34inst : Deriv (eqF (ap2 sigma aa (ap1 s bb)) (ap1 s (ap2 sigma aa bb)))
    T34inst = ruleInst2 0 aa 1 bb refl T34

    A : Term
    A = ap2 (iter stepU) cc (ap2 sigma aa bb)
    B : Term
    B = ap2 (iter stepU) (ap2 (iter stepU) cc aa) bb
    A' : Term
    A' = ap2 (iter stepU) cc (ap2 sigma aa (ap1 s bb))
    B' : Term
    B' = ap2 (iter stepU) (ap2 (iter stepU) cc aa) (ap1 s bb)

    eL : Deriv (eqF A' (ap1 stepU A))
    eL = ruleTrans (congR (iter stepU) cc T34inst)
                   (iter_step_univ stepU cc (ap2 sigma aa bb))

    eR : Deriv (eqF (ap1 stepU B) B')
    eR = ruleSym (iter_step_univ stepU (ap2 (iter stepU) cc aa) bb)

    step : Deriv (imp P (eqF A' B'))
    step =
      compI (ax_eqCong1 stepU A B)
        (compI (prependEqLeft A' (ap1 stepU A) (ap1 stepU B) eL)
               (appendEqRight A' (ap1 stepU B) B' eR))

------------------------------------------------------------------------
-- The lemma at arbitrary object Terms (simultaneous instantiation).

iterComp : (c a b : Term) ->
  Deriv (eqF (ap2 (iter stepU) c (ap2 sigma a b))
             (ap2 (iter stepU) (ap2 (iter stepU) c a) b))
iterComp c a b = ruleInst3v c a b iterCompU
