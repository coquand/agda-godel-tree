{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevRun -- STAGE I3 of attempt3 §11, layer 3: the RUN-TO-HALT assembly
-- of the complete-development CK machine, and the five  dev  closure
-- equations packaged as the meta-induction  runs .
--
-- The transition table  T4.DevTrans  gives, per machine configuration, the
-- single  devStepU  step.  Here we thread those steps through a whole run
-- of  dev  on a coded term, by META structural induction on the term (the
-- EXACT case split of the meta  dev : Tm -> Tm ).  The step counts are
-- packaged existentially in  Reaches  (the first genuine fuel argument, but
-- carried by the meta recursion rather than an object  ruleIndNat ; the
-- object  iter  laws  iter_base_univ / iter_step_univ  supply the fuel
-- arithmetic), so we never compute a concrete numeral.
--
-- Headline:
--   runs   : (t : Tm)(K) -> Reaches (cfgEV (code t) K) (cfgRT (code (dev t)) K)
--   devReaches : (t : Tm) -> Reaches (cfgEV (code t) konEmpty)
--                                     (cfgHALT (code (dev t)))
--
-- The five dev closure equations  dev_at_ze/su/adZe/adSu/adAd  are precisely
-- the five clauses of  runs  (each decomposes the run of  dev t  into the
-- machine step(s) plus the runs of the recursive subterm developments).
-- This is the I3 deliverable; I4 (TriObj) and I5 (ConflObj) build on top.
--
-- Modelled lemma-for-lemma on  T4.EvalUCorrect  (Reaches / runs1 / runs2);
-- the meta recursion is structural, no postulates, no holes.

module T4.DevRun where

open import T4.Base
open import T4.DevMachine
open import T4.DevStep   using ( devStepU )
open import T4.DevTrans
open import T4.TrsCodeObj   using ( ze# ; su# ; ad# )
open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code )
open import T4.ParTri      using ( dev )

open import BRA3.CourseOfValues   using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )

------------------------------------------------------------------------
-- Meta addition (for fuel composition).

plus : Nat -> Nat -> Nat
plus zero    b = b
plus (suc a) b = suc (plus a b)

------------------------------------------------------------------------
-- Reaches c c' :  the machine drives c to c' in some number of steps.
--   = exists N. iter devStepU c (natCode N) = c' .

record Reaches (c c' : Term) : Set where
  constructor mkReach
  field
    steps : Nat
    runsP : Deriv (eqF (ap2 (iter devStepU) c (natCode steps)) c')

open Reaches public

-- iter composition:  devStepU^(plus a b) (c) = devStepU^a (devStepU^b c) .

iter_add : (a b : Nat) (c : Term) ->
  Deriv (eqF (ap2 (iter devStepU) c (natCode (plus a b)))
              (ap2 (iter devStepU) (ap2 (iter devStepU) c (natCode b)) (natCode a)))
iter_add zero b c =
  ruleSym (iter_base_univ devStepU (ap2 (iter devStepU) c (natCode b)))
iter_add (suc a) b c =
  ruleTrans (iter_step_univ devStepU c (natCode (plus a b)))
    (ruleTrans (cong1 devStepU (iter_add a b c))
               (ruleSym (iter_step_univ devStepU (ap2 (iter devStepU) c (natCode b)) (natCode a))))

------------------------------------------------------------------------
-- Reaches combinators.

reach_refl : (c : Term) -> Reaches c c
reach_refl c = mkReach zero (iter_base_univ devStepU c)

reach_step1 : {c c' : Term} -> Deriv (eqF (ap1 devStepU c) c') -> Reaches c c'
reach_step1 {c} {c'} e =
  mkReach (suc zero)
    (ruleTrans (iter_step_univ devStepU c O)
      (ruleTrans (cong1 devStepU (iter_base_univ devStepU c)) e))

reach_trans : {c c' c'' : Term} -> Reaches c c' -> Reaches c' c'' -> Reaches c c''
reach_trans {c} {c'} {c''} (mkReach n1 e1) (mkReach n2 e2) =
  mkReach (plus n2 n1)
    (ruleTrans (iter_add n2 n1 c)
      (ruleTrans (congL (iter devStepU) (natCode n2) e1) e2))

reach_eq_target : {c c' c'' : Term} -> Reaches c c' -> Deriv (eqF c' c'') -> Reaches c c''
reach_eq_target (mkReach n e) e' = mkReach n (ruleTrans e e')

------------------------------------------------------------------------
-- The run of  dev  on a coded term, by META structural induction on  t
-- (the EXACT case split of  dev : Tm -> Tm ).  Kont-parametric: the
-- sub-developments run under an extended continuation.
--
-- These five clauses ARE the five dev closure equations, threaded through
-- the machine:  each shows the run of  dev t  decomposes into the matching
-- transition(s) and the runs of the recursive subterm developments.

runs : (t : Tm) (K : Term) ->
       Reaches (cfgEV (code t) K) (cfgRT (code (dev t)) K)

-- dev ze = ze :  one EV step  cfgEV ze# K -> cfgRT ze# K .
runs ze K = reach_step1 (devStepU_ze K)

-- dev (su t) = su (dev t) :  push frmSu, develop t, pop frmSu.
runs (su t) K =
  reach_trans (reach_step1 (devStepU_su (code t) K))
    (reach_trans (runs t (kons frmSu K))
                 (reach_step1 (devStepU_frmSu (code (dev t)) K)))

-- dev (ad ze y) = dev y :  drop the ad ze frame, develop y.
runs (ad ze y) K =
  reach_trans (reach_step1 (devStepU_adZe (code y) K))
              (runs y K)

-- dev (ad (su x) y) = su (ad (dev x) (dev y)) :
--   develop x under frmAdSu1 y, swap to frmAdSu2 (dev x), develop y, return.
runs (ad (su x) y) K =
  reach_trans (reach_step1 (devStepU_adSu (code x) (code y) K))
    (reach_trans (runs x (kons (frmAdSu1 (code y)) K))
      (reach_trans (reach_step1 (devStepU_frmAdSu1 (code (dev x)) (code y) K))
        (reach_trans (runs y (kons (frmAdSu2 (code (dev x))) K))
          (reach_step1 (devStepU_frmAdSu2 (code (dev y)) (code (dev x)) K)))))

-- dev (ad (ad p q) y) = ad (dev (ad p q)) (dev y) :
--   develop (ad p q) under frmAd1 y, swap to frmAd2 (dev (ad p q)),
--   develop y, return.
runs (ad (ad p q) y) K =
  reach_trans (reach_step1 (devStepU_adAd (code p) (code q) (code y) K))
    (reach_trans (runs (ad p q) (kons (frmAd1 (code y)) K))
      (reach_trans (reach_step1 (devStepU_frmAd1 (code (dev (ad p q))) (code y) K))
        (reach_trans (runs y (kons (frmAd2 (code (dev (ad p q)))) K))
          (reach_step1 (devStepU_frmAd2 (code (dev y)) (code (dev (ad p q))) K)))))

------------------------------------------------------------------------
-- The five dev closure equations (the I3 deliverable), as explicit named
-- machine-level facts.  Each is the matching clause of  runs , with the
-- coded development endpoint written in constructor-expanded form (equal
-- definitionally because  dev  reduces in the meta layer).  Together they
-- say the machine computes  dev  exactly by the five recursion clauses:
--   dev ze            = ze
--   dev (su t)        = su (dev t)
--   dev (ad ze y)     = dev y
--   dev (ad (su x) y) = su (ad (dev x) (dev y))
--   dev (ad (ad p q) y) = ad (dev (ad p q)) (dev y)

dev_at_ze : (K : Term) ->
  Reaches (cfgEV ze# K) (cfgRT ze# K)
dev_at_ze K = runs ze K

dev_at_su : (t : Tm) (K : Term) ->
  Reaches (cfgEV (su# (code t)) K) (cfgRT (su# (code (dev t))) K)
dev_at_su t K = runs (su t) K

dev_at_adZe : (y : Tm) (K : Term) ->
  Reaches (cfgEV (ad# ze# (code y)) K) (cfgRT (code (dev y)) K)
dev_at_adZe y K = runs (ad ze y) K

dev_at_adSu : (x y : Tm) (K : Term) ->
  Reaches (cfgEV (ad# (su# (code x)) (code y)) K)
          (cfgRT (su# (ad# (code (dev x)) (code (dev y)))) K)
dev_at_adSu x y K = runs (ad (su x) y) K

dev_at_adAd : (p q y : Tm) (K : Term) ->
  Reaches (cfgEV (ad# (ad# (code p) (code q)) (code y)) K)
          (cfgRT (ad# (code (dev (ad p q))) (code (dev y))) K)
dev_at_adAd p q y K = runs (ad (ad p q) y) K

------------------------------------------------------------------------
-- Run to HALT:  the machine, started developing  code t  with the empty
-- continuation, halts holding  code (dev t) .

devReaches : (t : Tm) ->
  Reaches (cfgEV (code t) konEmpty) (cfgHALT (code (dev t)))
devReaches t =
  reach_trans (runs t konEmpty)
              (reach_step1 (devStepU_halt (code (dev t))))
