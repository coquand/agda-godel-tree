{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.KFormulaFromNegsConj -- the framework wireup of the
-- K-formula assembly in the conjunction-shape ( Piece 1 of the
-- reformulation per  T4/NEXT-SESSION-KDEFCONJ.md ).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   PerProgramNegConj consts r :
--     The meta-function type supplying  M+1  per-program negs at day  r .
--     Replaces the old  PerProgramNeg  (which was indexed only by  Nat
--     and didn't carry the  NatLe  bound ;  see T4.SurpriseG2.Producer ).
--
--   kdefFromNegsConj :
--     (consts : SurpriseConstsConj) ->
--     (subject : Term) ->
--     PerProgramNegConj consts subject ->
--     Deriv (KdefConj (SurpriseConstsConj.M consts)
--                      (SurpriseConstsConj.enum consts)
--                      subject)
--
--   A direct wrapper over  T4.SurpriseG2.KdefConj.kdefConjFromNegs
--   that threads the SurpriseConstsConj record into the parametric
--   API .
--
-- =====================================================================
-- WHAT IS DEFERRED  (Pieces 2 & 3 per T4/NEXT-SESSION-KDEFCONJ.md).
-- =====================================================================
--
--   * Piece 2 :  Sigma_1 -internalisation  /  CGI_core_num_raw retarget
--                at the new  KcodeConj M enum (natCode r)  shape .   This
--                is what  sigma1KFormula  +  step_from_thm_fact  rewireup
--                produces ;  Berry chain needs the diag-index witness .
--
--   * Piece 3 :  Drop  shortProgs / shortProgs_size / sizeExhaust  from
--                the OLD  SurpriseConsts , migrating all callers to
--                SurpriseConstsConj .   For this session,  SurpriseConsts
--                ( the old record ) is INTACT ;  callers that want the
--                new pipeline use  SurpriseConstsConj  directly .

module T4.SurpriseG2.KFormulaFromNegsConj where

open import T4.Base
open import BRA3.ChurchLeq            using ( leq )
open import BRA3.RuleInst2            using ( NatLe )
open import T4.Kdef                 using ( definable )
open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )
open import T4.SurpriseG2.KdefConj  using ( KdefConj ; kdefConjFromNegs )

------------------------------------------------------------------------
-- The per-program-neg supply type.
--
-- For each  k <= M , supply  Deriv (~definable (ap1 enum (natCode k))
-- subject v1) .

PerProgramNegConj :
  (consts : SurpriseConstsConj) -> (subject : Term) -> Set
PerProgramNegConj consts subject =
  let open SurpriseConstsConj consts using ( M ; enum )
  in (k : Nat) -> NatLe k M ->
     Deriv (neg (definable (ap1 enum (natCode k)) subject (var (suc zero))))

------------------------------------------------------------------------
-- The K-formula assembly :  per-program-negs  ->  KdefConj  .

kdefFromNegsConj :
  (consts : SurpriseConstsConj) ->
  (subject : Term) ->
  PerProgramNegConj consts subject ->
  Deriv (KdefConj (SurpriseConstsConj.M consts)
                  (SurpriseConstsConj.enum consts)
                  subject)
kdefFromNegsConj consts subject negs =
  let open SurpriseConstsConj consts using ( M ; enum )
  in kdefConjFromNegs M enum subject negs
