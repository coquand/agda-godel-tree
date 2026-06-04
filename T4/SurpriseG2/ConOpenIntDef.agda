{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.ConOpenIntDef -- the open-consistency hypothesis
-- (Option 0 internalised form) used by the surprise-G2 framework's
-- final step.
--
--   ConOpenInt = Deriv (neg (eqF (ap1 thmT (var zero)) codeFalse))
--
-- A single  Deriv  open over  var 0  asserting
--   T |- ~ (thmT(x) = code(0=1))   for every  x .
-- Per-stage instantiation via  ruleInst zero x  yields the matching
-- closed Deriv at the relevant per-stage Term.
--
-- =====================================================================
-- HISTORY  ( retiring the OLD framework ) .
-- =====================================================================
--
-- This definition used to live in  T4.SurpriseG2.Pigeonhole  alongside
-- the OLD  stageZero  combinator .   With the OLD chain retired and
-- replaced by  T4.SurpriseG2.StageZeroNegsConj.descFamToNegs0  ( which
-- does NOT use  ConOpenInt  -- the new chain ex-falsoes DIRECTLY to the
-- per-prog neg via  axExFalso  on the  natCode i / natCode j
-- contradiction ) , the only remaining consumer is  SurpriseG2Conj 's
-- final  step_from_thm_fact -style closing .   So we extract  ConOpenInt
-- into its own one-definition module to avoid dragging  Pigeonhole.agda
-- through the migration .

module T4.SurpriseG2.ConOpenIntDef where

open import T4.Base
open import T4.Code  using ( codeFalse )
open import T4.ThmT  using ( thmT )

------------------------------------------------------------------------
-- The open-consistency hypothesis .

ConOpenInt : Set
ConOpenInt = Deriv (neg (eqF (ap1 thmT (var zero)) codeFalse))
