{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Definable -- the decidable "p describes x in exactly n steps" predicate.
--
--   definable p x n  :=  evalU(parse p, n) = s x   AND   evalU(parse p, n-1) = O
--
-- "running the program named p for fuel n outputs x (the  s _  is the halt
-- marker, so output = x), and for one less step it is still 0 (not halted)."
--
-- By the machine's monotonicity this pins n as the FIRST (exact) halting time,
-- so the second conjunct is equivalent to "for every fuel < n the output is 0":
--   * readout = s value at HALT, O while running   (T4.EvalUEval.readout / readout_halt),
--   * HALT is a stepU-fixpoint                       (T4.EvalUStep.stepU_at_halt),
-- hence  evalU(parse p, .)  is  O,...,O, s x, s x,...  -- monotone -- and being O
-- at n-1 forces O at every m < n.
--
-- It is a Formula (a proposition), NOT a Fun1/Fun2: Fun1/Fun2 return a Term
-- (a value), whereas  definable  can be true or false.  Its matrix is a
-- conjunction of two equalities (a decidable matrix); instances are discharged
-- by running  evalU .  The Kolmogorov formula  K(x) > L  is built as the negated
-- length-bounded closure of  definable  (p, n the free program/fuel variables).

module T4.Definable where

open import T4.Base
open import T4.DefWit     using ( fAnd )
open import T4.EvalUEval  using ( evalU )
open import T4.ProgParse  using ( parse )

open import BRA3.Church     using ( predecessor )

definable : Term -> Term -> Term -> Formula      -- (p) (x) (n)
definable p x n =
  fAnd (eqF (ap2 evalU (ap1 parse p) n) (ap1 s x))
       (eqF (ap2 evalU (ap1 parse p) (ap1 predecessor n)) O)
