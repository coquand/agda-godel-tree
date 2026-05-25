{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.EvalUCorrect -- the correctness of the universal interpreter
-- (EVALU-DESIGN.md, Phase E1, layer 4 -- the gate).
--
-- The machine carries values that must be SYNTACTIC NUMERALS (so R's
-- condFork dispatch fires), so correctness is stated against a meta-level
-- reference semantics  evalN1 / evalN2 : the standard BRA semantics on
-- naturals.  `runs1` / `runs2` (mutual structural meta-induction over the
-- function, plus the numeric arg for R) show the machine, started on
-- `mcode f` at numeral args, REACHES the return-config holding the numeral
-- `evalN f`.  Step counts are packaged existentially in `Reaches` (this
-- subsumes the explicit run-lengths of the design sketch).  The reference
-- semantics is sound w.r.t. the BRA axioms (`evalN1_sound`), giving the
-- `s (ap1 f O)` form of `evalU_correct`.

module BRA4.EvalUCorrect where

open import BRA4.Base
open import BRA4.EvalU
open import BRA4.EvalUStep
open import BRA4.EvalUEval

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )

------------------------------------------------------------------------
-- Meta-level reference semantics (the standard BRA semantics on Nat).

evalN1 : Fun1 -> Nat -> Nat
evalN2 : Fun2 -> Nat -> Nat -> Nat

evalN1 s           n = suc n
evalN1 o           n = zero
evalN1 u           n = n
evalN1 (C g h1 h2) n = evalN2 g (evalN1 h1 n) (evalN1 h2 n)

evalN2 v           x y       = y
evalN2 (R g h1 h2) x zero    = evalN1 g x
evalN2 (R g h1 h2) x (suc y) = evalN2 h1 (evalN2 h2 x y) (evalN2 (R g h1 h2) x y)

------------------------------------------------------------------------
-- Meta addition (for iteration composition).

plus : Nat -> Nat -> Nat
plus zero    b = b
plus (suc a) b = suc (plus a b)

------------------------------------------------------------------------
-- Reaches c c' :  the machine drives c to c' in some number of steps.
--   = exists N. iter stepU c (natCode N) = c' .

record Reaches (c c' : Term) : Set where
  constructor mkReach
  field
    steps : Nat
    runs  : Deriv (eqF (ap2 (iter stepU) c (natCode steps)) c')

open Reaches public

-- iter composition:  stepU^(plus a b) (c) = stepU^a (stepU^b c) .

iter_add : (a b : Nat) (c : Term) ->
  Deriv (eqF (ap2 (iter stepU) c (natCode (plus a b)))
              (ap2 (iter stepU) (ap2 (iter stepU) c (natCode b)) (natCode a)))
iter_add zero b c =
  ruleSym (iter_base_univ stepU (ap2 (iter stepU) c (natCode b)))
iter_add (suc a) b c =
  ruleTrans (iter_step_univ stepU c (natCode (plus a b)))
    (ruleTrans (cong1 stepU (iter_add a b c))
               (ruleSym (iter_step_univ stepU (ap2 (iter stepU) c (natCode b)) (natCode a))))

------------------------------------------------------------------------
-- Reaches combinators.

reach_refl : (c : Term) -> Reaches c c
reach_refl c = mkReach zero (iter_base_univ stepU c)

reach_step1 : {c c' : Term} -> Deriv (eqF (ap1 stepU c) c') -> Reaches c c'
reach_step1 {c} {c'} e =
  mkReach (suc zero)
    (ruleTrans (iter_step_univ stepU c O)
      (ruleTrans (cong1 stepU (iter_base_univ stepU c)) e))

reach_trans : {c c' c'' : Term} -> Reaches c c' -> Reaches c' c'' -> Reaches c c''
reach_trans {c} {c'} {c''} (mkReach n1 e1) (mkReach n2 e2) =
  mkReach (plus n2 n1)
    (ruleTrans (iter_add n2 n1 c)
      (ruleTrans (congL (iter stepU) (natCode n2) e1) e2))

reach_eq_target : {c c' c'' : Term} -> Reaches c c' -> Deriv (eqF c' c'') -> Reaches c c''
reach_eq_target (mkReach n e) e' = mkReach n (ruleTrans e e')

------------------------------------------------------------------------
-- cfgRT value rewrite (used to normalise a returned value to a numeral).

cfgRT_val : (val val' K : Term) ->
  Deriv (eqF val val') -> Deriv (eqF (cfgRT val K) (cfgRT val' K))
cfgRT_val val val' K e = congR pi (natCode tagRT) (congL pi K e)

------------------------------------------------------------------------
-- The compositional invariant (mutual structural meta-induction over the
-- function, plus the numeric arg for R).  Kont-parametric (the C / R
-- sub-evaluations run under an extended continuation).

runs1 : (f : Fun1) (n : Nat) (K : Term) ->
        Reaches (cfgEV (mcode1 f) (natCode n) K) (cfgRT (natCode (evalN1 f n)) K)
runs2 : (g : Fun2) (x y : Nat) (K : Term) ->
        Reaches (cfgEV (mcode2 g) (ap2 pi (natCode x) (natCode y)) K)
                (cfgRT (natCode (evalN2 g x y)) K)

-- Fun1 leaves.
runs1 s n K = reach_step1 (stepU_at_evS (natCode n) K)
runs1 o n K = reach_step1 (stepU_at_evO (natCode n) K)
runs1 u n K = reach_step1 (stepU_at_evU (natCode n) K)

-- Fun1 composition.
runs1 (C g h1 h2) n K =
  let v1 : Nat
      v1 = evalN1 h1 n
      v2 : Nat
      v2 = evalN1 h2 n
      K1 : Term
      K1 = kons (frmC1 (mcode2 g) (mcode1 h2) (natCode n)) K
      K2 : Term
      K2 = kons (frmApp2 (mcode2 g) (natCode v1)) K
      step1 = reach_step1 (stepU_at_evC g h1 h2 (natCode n) K)
      rec_h1 = runs1 h1 n K1
      step2 = reach_step1 (stepU_at_rtC1 (natCode v1) (mcode2 g) (mcode1 h2) (natCode n) K)
      rec_h2 = runs1 h2 n K2
      step3 = reach_step1 (stepU_at_rtApp2 (natCode v2) (mcode2 g) (natCode v1) K)
      rec_g = runs2 g v1 v2 K
  in reach_trans step1
       (reach_trans rec_h1
         (reach_trans step2
           (reach_trans rec_h2
             (reach_trans step3 rec_g))))

-- Fun2 projection.
runs2 v x y K =
  reach_eq_target (reach_step1 (stepU_at_evV (ap2 pi (natCode x) (natCode y)) K))
    (cfgRT_val (ap1 Snd (ap2 pi (natCode x) (natCode y))) (natCode y) K
               (axSnd (natCode x) (natCode y)))

-- Fun2 recursion: base.
runs2 (R g h1 h2) x zero K =
  reach_trans (reach_step1 (stepU_at_evRbase g h1 h2 (natCode x) K))
              (runs1 g x K)

-- Fun2 recursion: step.
runs2 (R g h1 h2) x (suc y) K =
  let i : Nat
      i = evalN2 h2 x y
      r : Nat
      r = evalN2 (R g h1 h2) x y
      Kr1 : Term
      Kr1 = kons (frmR1 (mcode2 (R g h1 h2)) (mcode2 h1) (natCode x) (natCode y)) K
      Kapp : Term
      Kapp = kons (frmApp2 (mcode2 h1) (natCode i)) K
      step1 = reach_step1 (stepU_at_evRstep g h1 h2 (natCode x) (natCode y) K)
      rec_h2 = runs2 h2 x y Kr1
      step2 = reach_step1
                (stepU_at_rtR1 (natCode i) (mcode2 (R g h1 h2)) (mcode2 h1)
                               (natCode x) (natCode y) K)
      rec_R = runs2 (R g h1 h2) x y Kapp
      step3 = reach_step1 (stepU_at_rtApp2 (natCode r) (mcode2 h1) (natCode i) K)
      rec_h1 = runs2 h1 i r K
  in reach_trans step1
       (reach_trans rec_h2
         (reach_trans step2
           (reach_trans rec_R
             (reach_trans step3 rec_h1))))

------------------------------------------------------------------------
-- evalU_correct (numeral form): there is a fuel N with
--   evalU (mcode1 f) (natCode N) = s (natCode (evalN1 f 0)) .

record EvalsTo (e out : Term) : Set where
  constructor mkEvalsTo
  field
    fuel : Nat
    ev   : Deriv (eqF (ap2 evalU e (natCode fuel)) out)

open EvalsTo public

evalU_correct_num : (f : Fun1) -> EvalsTo (mcode1 f) (ap1 s (natCode (evalN1 f zero)))
evalU_correct_num f =
  let v : Nat
      v = evalN1 f zero
      r : Reaches (cfgEV (mcode1 f) O konEmpty) (cfgHALT (natCode v))
      r = reach_trans (runs1 f zero konEmpty)
                      (reach_step1 (stepU_at_rtEmpty (natCode v)))
      N : Nat
      N = steps r
      e : Deriv (eqF (ap2 (iter stepU) (cfgEV (mcode1 f) O konEmpty) (natCode N))
                     (cfgHALT (natCode v)))
      e = runs r
      u1 = evalU_unfold (mcode1 f) (natCode N)
      iterEq = congL (iter stepU) (natCode N) (initF_eq (mcode1 f))
      chain = ruleTrans iterEq e
      final = ruleTrans u1 (ruleTrans (cong1 readout chain) (readout_halt (natCode v)))
  in mkEvalsTo N final

------------------------------------------------------------------------
-- Reference-semantics soundness w.r.t. the BRA axioms.

evalN1_sound : (f : Fun1) (n : Nat) ->
  Deriv (eqF (natCode (evalN1 f n)) (ap1 f (natCode n)))
evalN2_sound : (g : Fun2) (x y : Nat) ->
  Deriv (eqF (natCode (evalN2 g x y)) (ap2 g (natCode x) (natCode y)))

evalN1_sound s n = axRefl (ap1 s (natCode n))
evalN1_sound o n = ruleSym (ax_o (natCode n))
evalN1_sound u n = ruleSym (ax_u (natCode n))
evalN1_sound (C g h1 h2) n =
  let a : Nat
      a = evalN1 h1 n
      b : Nat
      b = evalN1 h2 n
      s1 = evalN2_sound g a b
      s2 = congL g (natCode b) (evalN1_sound h1 n)
      s3 = congR g (ap1 h1 (natCode n)) (evalN1_sound h2 n)
      s4 = ruleSym (ax_C g h1 h2 (natCode n))
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

evalN2_sound v x y = ruleSym (ax_v (natCode x) (natCode y))
evalN2_sound (R g h1 h2) x zero =
  ruleTrans (evalN1_sound g x) (ruleSym (ax_R_base g h1 h2 (natCode x)))
evalN2_sound (R g h1 h2) x (suc y) =
  let i : Nat
      i = evalN2 h2 x y
      r : Nat
      r = evalN2 (R g h1 h2) x y
      s1 = evalN2_sound h1 i r
      s2 = congL h1 (natCode r) (evalN2_sound h2 x y)
      s3 = congR h1 (ap2 h2 (natCode x) (natCode y)) (evalN2_sound (R g h1 h2) x y)
      s4 = ruleSym (ax_R_step g h1 h2 (natCode x) (natCode y))
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- evalU_correct (the design-doc form):  evalU (mcode1 f) (natCode N) = s (ap1 f O) .

evalU_correct : (f : Fun1) -> EvalsTo (mcode1 f) (ap1 s (ap1 f O))
evalU_correct f =
  let base = evalU_correct_num f
  in mkEvalsTo (fuel base) (ruleTrans (ev base) (cong1 s (evalN1_sound f zero)))
