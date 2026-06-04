{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.Describes -- the OPEN "program  q  describes day  r "
-- formula.
--
--   Describes q r = eqF (ap2 runProg q (var zero)) (ap1 s r)
--
-- with the fuel  var 0  left open.  A closed  Deriv (Describes q r)
-- asserts that there is a fuel  n  (the  var 0  slot, to be supplied
-- by  ruleInst 0 _  downstream) for which  runProg q n = s r .
--
-- The subject  r  is the RAW value the machine outputs (no internal
-- coding around  r ): that matches  Kdef L x 's subject slot
-- ( T4.Kdef.Kdef L x  has  definable p x n = runProg p n = s x ).
-- The caller picks  r := natCode k  to talk about day  k : Nat .
--
-- =====================================================================
-- HISTORY  ( retiring the OLD framework ) .
-- =====================================================================
--
-- The OLD record  DescPack (consts : SurpriseConsts) (k : Nat)  carrying
-- progIx : Nat  +  runs : Deriv (Describes (shortProgs progIx)
-- (natCode k))  was specific to the OLD  SurpriseConsts -based
-- pipeline ( shortProgs : Nat -> Term  was a SurpriseConsts field ) .
-- It has been REPLACED by   T4.SurpriseG2.StageZeroNegsConj.DescPackConj
-- ( a  Sigma -alias over the new  SurpriseConstsConj  record , with
-- runs  at the new  ap1 enum (natCode progIx)  program shape ) .
--
-- This file is now standalone -- no  SurpriseConsts  dependency -- so
-- it can be reused by both the OLD ( retired ) and NEW ( live ) chains
-- during the migration .   After the OLD chain is fully retired only
-- the NEW chain consumes  Describes .

module T4.SurpriseG2.Describes where

open import T4.Base
open import T4.Kdef                  using ( runProg )

------------------------------------------------------------------------
-- The OPEN  "q  describes  r " formula (fuel slot = var 0).

Describes : Term -> Term -> Formula
Describes q r = eqF (ap2 runProg q (var zero)) (ap1 s r)
