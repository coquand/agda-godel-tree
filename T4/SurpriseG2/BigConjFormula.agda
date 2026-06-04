{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.BigConjFormula --
--
-- The big-conjunction formula  describe(p_r, h_r, r) /\ ... /\ describe(p_N, h_N, N)
-- used by the FORMULA-LEVEL S(r) hypothesis in T4/clos lines 11-15.
--
-- =====================================================================
-- HISTORICAL SHAPE vs. CURRENT.
-- =====================================================================
--
-- The ORIGINAL shape used  fuel := var zero  uniformly across every
-- conjunct.   The CURRENT shape parametrises each conjunct over its
-- OWN  halts d : Term  ( per T4/clos line 13 :  each describe uses
-- its own halt time  l_d ) , because the inductive step body needs to
-- supply CLOSED halts for days  [r+1..N]  and OPEN  var 0  for day r .
--
-- The OLD names  describeAt / bigConjCount / BigConjFormula  are kept
-- as ALIASES at  halts := (\ _ -> var zero)  so the BASE case proof
-- ( T4.SurpriseG2.StageBaseFormula ) and the FINAL theorem
-- ( T4.SurpriseG2.SurpriseG2FinalFormula ) continue to compile
-- unchanged ; new code uses the T-suffixed variants .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * `describeAtT enum progIx day fuel : Formula`
--     The describe formula at fixed (program-by-index, day, fuel) :
--     eqF (ap2 runProg (ap1 enum (natCode progIx)) fuel) (ap1 s (natCode day))
--
-- * `conjF A B = neg (imp A (neg B))`  -- BRA's standard And-encoding .
--
-- * `trueF = eqF O O`                  -- the empty-conjunction sentinel ;
--                                          a Deriv is `axRefl O` .
--
-- * `bigConjCountT enum count start picks halts : Formula`
--     Right-associated big-And starting from day `start` , going up
--     `count` conjuncts ;   each conjunct uses `picks d` as the program
--     slot and `halts d` as the fuel at day  d .
--
-- * `BigConjFormulaT consts r picks halts : Formula`
--     = `bigConjCountT enum (countDays N r) r picks halts`  --  the
--     big-AND of describe-conjuncts over days  [r..N] .   When  r > N ,
--     the count is zero and  BigConjFormulaT = trueF .
--
-- * `describeAt` , `bigConjCount` , `BigConjFormula`  : aliases at
--   `halts := (\ _ -> var zero)` for backwards compatibility .

module T4.SurpriseG2.BigConjFormula where

open import T4.Base
open import T4.Kdef                       using ( runProg )
open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )

------------------------------------------------------------------------
-- The describe formula at fixed (program-by-index, day, fuel) .

describeAtT : Fun1 -> (progIx : Nat) (day : Nat) (fuel : Term) -> Formula
describeAtT enum progIx day fuel =
  eqF (ap2 runProg (ap1 enum (natCode progIx)) fuel)
       (ap1 s (natCode day))

------------------------------------------------------------------------
-- The And of two formulas via BRA's standard And-encoding .

conjF : Formula -> Formula -> Formula
conjF A B = neg (imp A (neg B))

------------------------------------------------------------------------
-- The empty-conjunction sentinel .   Deriv trueF = axRefl O .

trueF : Formula
trueF = eqF O O

------------------------------------------------------------------------
-- Right-associated big-And starting at day `start` with `count`
-- conjuncts , using `picks d` as the program slot and `halts d` as
-- the fuel at day  d .

bigConjCountT :
  Fun1 -> (count : Nat) (start : Nat) (picks : Nat -> Nat) (halts : Nat -> Term) ->
  Formula
bigConjCountT enum zero    start picks halts = trueF
bigConjCountT enum (suc c) start picks halts =
  conjF (describeAtT enum (picks start) start (halts start))
        (bigConjCountT enum c (suc start) picks halts)

------------------------------------------------------------------------
-- countDays N r  =  number of integers in  [r..N]  =  max(0, N+1-r) .
-- Structurally recursive on the smaller argument .

countAux : (cap : Nat) (r : Nat) -> Nat
countAux zero    _       = zero
countAux (suc n) zero    = suc n
countAux (suc n) (suc r) = countAux n r

countDays : (N : Nat) (r : Nat) -> Nat
countDays N r = countAux (suc N) r

------------------------------------------------------------------------
-- The main BigConj formula at start day  r , relative to  consts .

BigConjFormulaT :
  (consts : SurpriseConstsConj) -> (r : Nat) ->
  (picks : Nat -> Nat) (halts : Nat -> Term) -> Formula
BigConjFormulaT consts r picks halts =
  bigConjCountT (SurpriseConstsConj.enum consts)
                (countDays (SurpriseConstsConj.N consts) r) r picks halts

------------------------------------------------------------------------
-- BACKWARDS-COMPAT ALIASES : open-fuel  var zero  uniformly .

openFuel : Nat -> Term
openFuel _ = var zero

describeAt : Fun1 -> (progIx : Nat) (day : Nat) -> Formula
describeAt enum progIx day = describeAtT enum progIx day (var zero)

bigConjCount : Fun1 -> (count : Nat) (start : Nat) (picks : Nat -> Nat) -> Formula
bigConjCount enum count start picks =
  bigConjCountT enum count start picks openFuel

BigConjFormula :
  (consts : SurpriseConstsConj) -> (r : Nat) -> (picks : Nat -> Nat) -> Formula
BigConjFormula consts r picks =
  BigConjFormulaT consts r picks openFuel
