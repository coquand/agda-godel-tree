{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageStepF --
--
-- The FORMULA-LEVEL inductive step  S(r) -> S(suc r)  of the surprise-G2
-- external induction, assembled around a single typed residual : the
-- day-r Chaitin clash.
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   stageStepF : StageStepSpecF consts
--     = (r : Nat) -> StagePredF consts r -> StagePredF consts (suc r)
--
-- given the single typed hypothesis
--
--   dayClash :
--     (r : Nat) -> NatLe r N -> StagePredF consts r ->
--     (picks : Picks) -> PicksBound consts picks ->
--     Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
--
-- "Given S(r) ( = T proves at least one of days [r..N] is incompressible )
--  and a choice of describing programs for days [r+1..N], if all of
--  [r+1..N] WERE jointly describable then T is inconsistent."   This is
-- exactly Kritchman-Raz step p.5 items 1-7 at day r : rule out day r
-- being the sole remaining incompressible day, via  StepFrontEnd.frontEnd
-- (S(r) => no short program describes day r, OBJECT level) + the encoded
-- Sigma1 lift of the runProg conjunction K_rest + the Chaitin diagonal +
-- consistency reflection (ConOpenInt).   It is the genuine long pole,
-- isolated here as a typed hypothesis per the repo STOP-rule
-- (hypothesis-first) so the step + headline typecheck before the clash
-- body / enum-identification are discharged.
--
-- WHY THE  imp K_rest falseF  SHAPE ( and not  imp (KdefBigConj ...)
-- falseF ) :  KdefBigConj(r) is the Pi-1 statement "no short program
-- describes day r" ; refuting it at the OBJECT level is NOT a theorem.
-- The actual clash routes through the PROVABILITY of  K_rest =
-- BigConjFormula (suc r)  ( a conjunction of Sigma-1 describe atoms, so
-- Sigma-1-liftable to its own provability ) ;  hence the residual is
-- stated as  imp K_rest falseF  (= the day-r case of  neg K_rest , the
-- very thing we are proving), with the IH  S(r)  threaded in so the
-- eventual construction can run  frontEnd .
--
-- =====================================================================
-- STRUCTURE OF THE STEP.
-- =====================================================================
--
-- For day  r  let  K_rest = BigConjFormula consts (suc r) picks .  We
-- want  Deriv (neg K_rest) .   Decide  r <= N :
--
--   * r <= N :   dayClash r rleN IH picks bound  gives  imp K_rest falseF ;
--                impFalseToNeg  yields  neg K_rest .
--
--   * r >  N :   the count  countDays N r = 0 = countDays N (suc r) , so
--                both  BigConjFormula consts r picks  and
--                BigConjFormula consts (suc r) picks  reduce to  trueF ;
--                transport the IH (neg trueF) across the count equalities.
--                (This branch is never reached by  stageIndF , which only
--                steps at  r = 0..N , but  StageStepSpecF  is total in r.)

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; le-zero ; le-suc )
open import T4.Code               using ( falseF )
open import T4.PHP                using ( impFalseToNeg )
open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula
  using ( BigConjFormula ; bigConjCount ; trueF ; countDays ; countAux )
open import T4.SurpriseG2.StagePredFormula
  using ( StagePredF ; StageStepSpecF ; Picks ; PicksBound )
open import T4.SurpriseG2.MetaPigeonhole as MP
  using ( Lt ; ltZ ; ltS ; ltWeaken ; Or ; inl ; inr )

module T4.SurpriseG2.StageStepF
  (consts : SurpriseConstsConj)
  (dayClash :
    (r : Nat) ->
    NatLe r (SurpriseConstsConj.N consts) ->
    StagePredF consts r ->
    (picks : Picks) -> PicksBound consts picks ->
    Deriv (imp (BigConjFormula consts (suc r) picks) falseF))
  where

private
  N : Nat
  N = SurpriseConstsConj.N consts
  enum : Fun1
  enum = SurpriseConstsConj.enum consts

------------------------------------------------------------------------
-- Totality of the  r <= N  decision (meta-arithmetic).

decLeN : (r n : Nat) -> Or (NatLe r n) (Lt n r)
decLeN zero    n       = inl (le-zero n)
decLeN (suc r) zero    = inr (ltZ r)
decLeN (suc r) (suc n) with decLeN r n
... | inl le = inl (le-suc le)
... | inr lt = inr (ltS n r lt)

------------------------------------------------------------------------
-- Lt a b  ->  NatLe (suc a) b , and the count-collapse above N .

ltToNatLe : {a b : Nat} -> Lt a b -> NatLe (suc a) b
ltToNatLe (ltZ n)     = le-suc (le-zero n)
ltToNatLe (ltS m n h) = le-suc (ltToNatLe h)

countAux_zero_ge : (cap r : Nat) -> NatLe cap r -> Eq (countAux cap r) zero
countAux_zero_ge zero    r        _           = refl
countAux_zero_ge (suc n) zero     ()
countAux_zero_ge (suc n) (suc r') (le-suc le) = countAux_zero_ge n r' le

countDays_zero_above : (n r : Nat) -> Lt n r -> Eq (countDays n r) zero
countDays_zero_above n r ltnr = countAux_zero_ge (suc n) r (ltToNatLe ltnr)

------------------------------------------------------------------------
-- The step.

stageStepF : StageStepSpecF consts
stageStepF r IH picks bound with decLeN r N
... | inl rleN =
      impFalseToNeg (BigConjFormula consts (suc r) picks)
                    (dayClash r rleN IH picks bound)
... | inr ltNr =
      let e_r : Eq (countDays N r) zero
          e_r = countDays_zero_above N r ltNr

          e_sr : Eq (countDays N (suc r)) zero
          e_sr = countDays_zero_above N (suc r) (ltWeaken ltNr)

          -- IH : Deriv (neg (bigConjCount enum (countDays N r) r picks)) ;
          -- transport along  countDays N r = 0  to  neg trueF .
          negTrue : Deriv (neg trueF)
          negTrue =
            eqSubst (\ F -> Deriv (neg F))
                    (eqCong (\ c -> bigConjCount enum c r picks) e_r)
                    (IH picks bound)
      in eqSubst (\ F -> Deriv (neg F))
                 (eqSym (eqCong (\ c -> bigConjCount enum c (suc r) picks) e_sr))
                 negTrue
