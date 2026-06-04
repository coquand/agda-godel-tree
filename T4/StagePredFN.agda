{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StagePredFN -- the number-code stage predicate  S(r)  of surprise-GII
-- ( clos lines 27-31, 71-73 ;  SURPRISE-GII-NUMBERCODE-HANDOFF S3.6 ).
--
-- Number-code mirror of  T4.SurpriseG2.StagePredFormula / BigConjFormula  with
-- the describe atom re-pointed from  runProg (enum (natCode progIx))  to
-- runProgN (natCode progIx)  -- the enumeration is the IDENTITY, so the
-- progIx-th program IS the number  progIx .
--
-- clos's  K(x0, p_r, .., p_N) = define_{p_r}(x0, r) /\ ... /\ define_{p_N}(x0, N)
-- is the right-nested conjunction over days  [r..N] ;  S(r) = Deriv (neg K) ,
-- quantified ( meta ) over the per-day program choice  picks  with  picks d <= M .
--
--   describeAtN progIx day fuel = eqF (ap2 runProgN (natCode progIx) fuel)
--                                     (ap1 s (natCode day))
--   BigConjFormulaN N r picks   = bigConjCountN (countDays N r) r picks (open fuel var 0)
--   StagePredFN N M r           = (picks)(picks d <= M for d <= N) ->
--                                   Deriv (neg (BigConjFormulaN N r picks))
--   StageStepSpecFN N M         = (r) -> StagePredFN N M r -> StagePredFN N M (suc r)
--
-- The meta scaffolding ( conjF , trueF , countDays ) is REUSED verbatim from the
-- old framework ( it is atom-agnostic ) ;  only the describe atom changes.

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import T4.ParseN      using ( runProgN )
open import T4.SurpriseG2.BigConjFormula using ( conjF ; trueF ; countDays )

module T4.StagePredFN where

------------------------------------------------------------------------
-- SECTION 1.  The number-code describe atom ( runProgN ; enum = identity ).

describeAtN : (progIx : Nat) (day : Nat) (fuel : Term) -> Formula
describeAtN progIx day fuel =
  eqF (ap2 runProgN (natCode progIx) fuel) (ap1 s (natCode day))

------------------------------------------------------------------------
-- SECTION 2.  The right-nested big-And over days  [start .. start+count-1] .

bigConjCountN :
  (count : Nat) (start : Nat) (picks : Nat -> Nat) (halts : Nat -> Term) ->
  Formula
bigConjCountN zero    start picks halts = trueF
bigConjCountN (suc c) start picks halts =
  conjF (describeAtN (picks start) start (halts start))
        (bigConjCountN c (suc start) picks halts)

------------------------------------------------------------------------
-- SECTION 3.  The big-conjunction K over days  [r..N]  ( open fuel var 0 ).

openFuel : Nat -> Term
openFuel _ = var zero

BigConjFormulaN : (N : Nat) (r : Nat) (picks : Nat -> Nat) -> Formula
BigConjFormulaN N r picks = bigConjCountN (countDays N r) r picks openFuel

------------------------------------------------------------------------
-- SECTION 4.  The stage predicate  S(r)  and the inductive-step spec.
--   N = day count ,  M = program-count margin ( M + 1 enumerated programs ).

Picks : Set
Picks = Nat -> Nat

PicksBound : (N M : Nat) -> Picks -> Set
PicksBound N M picks = (d : Nat) -> NatLe d N -> NatLe (picks d) M

-- S(r) :  T proves the day-[r..N] big conjunction is FALSE, for every choice of
-- describing programs ( picks ) bounded by the program margin  M .
StagePredFN : (N M : Nat) -> Nat -> Set
StagePredFN N M r =
  (picks : Picks) (bound : PicksBound N M picks) ->
    Deriv (neg (BigConjFormulaN N r picks))

-- The inductive step  S(r) -> S(r+1)  ( clos Steps 1-6 ).
StageStepSpecFN : (N M : Nat) -> Set
StageStepSpecFN N M =
  (r : Nat) -> StagePredFN N M r -> StagePredFN N M (suc r)
