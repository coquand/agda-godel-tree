{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageStepSpec --
--
-- The ABSTRACT inductive step  S(r) -> S(r+1)  of the external
-- induction in T4/clos .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   StageStepSpec consts  :=  (r : Nat) -> StagePred consts r -> StagePred consts (suc r)
--
-- The TYPE of the inductive-step lemma .   The framework's structural
-- induction ( T4.SurpriseG2.StageInd ) and headline
-- ( T4.SurpriseG2.SurpriseG2Final ) consume this abstractly :  given
-- a base case ( T4.SurpriseG2.StageBase.stageBase ) and a StageStepSpec ,
-- they produce  Deriv (eqF O (ap1 s O))  by Nat.rec to  S(suc N)
-- ( vacuous antecedent ) .
--
-- =====================================================================
-- WHAT IS DEFERRED  (the principal mathematical residual).
-- =====================================================================
--
-- The CONCRETE body of  StageStepSpec consts  --  the construction
-- given a META function  Sr : StagePred consts r  ( = "extending the
-- family at day r yields Deriv 0=1" )  PLUS a DescribingFamily at
-- [r+1..N] , derive Deriv (eqF O (ap1 s O)) .   Per T4/clos , the
-- recipe is :
--
--   1. For each candidate enum-index  k  in  [0..M] , at the open fuel
--      var 0  (in the Describes form) , derive  Deriv (imp REST (neg
--      describesAt (enum k) v0 (natCode r)))  at the formula level
--      using Sr extended at day r .
--      (This is the "encoding of derivation and Thm13" step ;  in
--       Agda , directly available  because  Sr  is a META function
--       and the implication is built via BRA's  axContrapos  / liftP
--       lifting of the Sr application against a hypothetical
--       describes derivation -- the contrapositive of which yields
--       a CLOSED Deriv (imp REST (neg describesAt ...)) once we have
--       Deriv REST = And-intro of the family's runs Derivs . )
--
--   2. MP each with the formula-level Deriv REST ( aggregated And-
--      intro of  family d  's  runs  for  d  in  [r+1..N] )  to get
--      Deriv (neg describesAt (enum k) v0 (natCode r))  for each k .
--
--   3. Apply  T4.SurpriseG2.KdefConj.kdefConjFromNegs  to aggregate
--      the M+1 per-prog negs into  Deriv (KdefConj M enum (natCode r)) .
--
--   4. thmT_complete_rec  on the K-formula Deriv to get
--      Deriv (eqF (ap1 thmT (encode dKdef)) (codeFormula (KdefConj ...))) .
--
--   5. Bridge to the KcodeConj shape via  KcodeConj_correct  and apply
--      the abstract  CGIConjSpec.cgiConj  to get
--      Deriv (eqF (ap1 thmT z) codeFalse) .
--
--   6. ConOpenInt at  v0 := z , axExFalso to get Deriv (eqF O (ap1 s O)) .
--
-- The recipe is ENGINEERING-HEAVY ( ~400-600 LoC ) due to BRA's lack of
-- native conjunction and the need to wire encoded_mp at the thmT level
-- for the And-intro of REST .   By abstracting this step as
-- StageStepSpec , the framework ships the structural Nat-rec ( ~50 LoC )
-- and the headline ( ~80 LoC ) immediately ;  the inductive-step body
-- is the principal residual , analogous to  CGIConjSpec  for the
-- Berry-clash body  ( see  T4.SurpriseG2.CGIConjSpec ) .

module T4.SurpriseG2.StageStepSpec where

open import T4.Base
open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.StagePred       using ( StagePred )

------------------------------------------------------------------------
-- The abstract inductive-step spec .

StageStepSpec : SurpriseConstsConj -> Set
StageStepSpec consts =
  (r : Nat) -> StagePred consts r -> StagePred consts (suc r)
