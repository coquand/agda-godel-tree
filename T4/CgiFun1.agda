{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiFun1 -- PROTOTYPE : the  imp + Fun1 G  restatement of
-- Chaitin-Goedel-I (CGI_core_num_raw / cgFalse).
--
-- =====================================================================
-- MOTIVATION  (user, 2026-06-01).
-- =====================================================================
--
-- The shipped  cgFalse / cgFalseImp  conclude about the META term
--   cgFun w : Term -> Term ,
-- which bakes in  closeW w = substT 0 O (substT 1 O w)  (a SYNTACTIC
-- substitution), forcing closedness bookkeeping on the witness.
--
-- But  cgFun w  is, by inspection of  T4.CgFun.cgFun , a FIXED
-- object-level combinator context  E[cw]  with  cw = closeW w  the only
-- w-dependence (cmp / exfProof / outerWrap / cPos / sigma / gRec / pi /
-- num / Pair / fuelMu_c / fuelG_c / outL_c / Df_runProg / cEqTm / cAp1f /
-- cAp2f -- all Fun1/Fun2 representable).   By combinatory completeness
-- there is a single  Fun1 G  with
--
--   gFact :  (w : Term) -> Eq (ap1 G (closeW w)) (cgFun w)
--
-- i.e.  cgFun = ap1 G . closeW .   The ONLY non-Fun1 ingredient is
-- closeW , the IDENTITY on witnesses closed at vars 0/1 (the witnesses
-- that actually arise: encoded-proof codes carrying only a fresh
-- Carneiro var k >= 2).
--
-- =====================================================================
-- WHAT THIS PROTOTYPE SHOWS.
-- =====================================================================
--
-- GIVEN the factorization  (G , gFact)  -- the SOLE remaining piece, a
-- mechanical bracket-abstraction of  cgFun 's body -- the clean
-- imp + Fun1 CGI statement follows in ONE line from the shipped
-- cgFalseImp  (NO closedness hypothesis on  w ), and for closed-at-0/1
-- witnesses ( closeW w = w )  it is exactly the user's target
--
--   Deriv (imp Rf (eqF (thmT w) (Kcode Lstar (outKdef Lstar w)))) ->
--   Deriv (imp Rf (eqF (thmT (ap1 G w)) codeFalse)) .
--
-- So Chaitin-Goedel-I as "a genuine Fun1 diagonal G with an imp-arrow
-- conclusion, no closedness" reduces ENTIRELY to constructing (G , gFact).

module T4.CgiFun1 where

open import T4.Base
open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.Kdef             using ( Kcode )
open import T4.KdefRecog        using ( outKdef )
open import T4.KGodel1BridgeDef using ( Lstar )
open import T4.CgFun            using ( cgFun )
open import T4.CloseW           using ( closeW )
open import T4.CgFalseImp       using ( cgFalseImp )
open import BRA3.RuleInst2        using ( simSubstF )
open import BRA3.Formula          using ( substF )

------------------------------------------------------------------------
-- The factorization hypothesis :  cgFun = ap1 G . closeW .
-- ( To be discharged by bracket-abstracting  cgFun 's combinator body. )

CgFunIsFun1 : Fun1 -> Set
CgFunIsFun1 G = (w : Term) -> Eq (ap1 G (closeW w)) (cgFun w)

------------------------------------------------------------------------
-- The imp + Fun1 restatement, general  w  ( closeW still present, but
-- the conclusion is now  ap1 G (closeW w) , a genuine Fun1 image ) .

cgiFun1 :
  (G : Fun1) -> CgFunIsFun1 G ->
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (eqF (ap1 thmT (closeW w))
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w))))) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap1 G (closeW w))) codeFalse))
cgiFun1 G gFact Rf w sub0_Rf sub1_Rf sim_Rf hyp =
  eqSubst (\ t -> Deriv (imp Rf (eqF (ap1 thmT t) codeFalse)))
          (eqSym (gFact w))
          (cgFalseImp Rf w sub0_Rf sub1_Rf sim_Rf hyp)

------------------------------------------------------------------------
-- The clean corollary on witnesses closed at vars 0/1 ( closeW w = w ) :
-- EXACTLY the user's target -- a genuine  Fun1 G , imp-arrow, no closeW.

cgiFun1Closed :
  (G : Fun1) -> CgFunIsFun1 G ->
  (Rf : Formula) (w : Term) ->
  Eq (closeW w) w ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (eqF (ap1 thmT w)
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap1 G w)) codeFalse))
cgiFun1Closed G gFact Rf w cwEq sub0_Rf sub1_Rf sim_Rf hyp =
  let -- rewrite the hypothesis's  closeW w  to  w  is unnecessary -- instead
      -- push  w -> closeW w  into the supplied hyp via  cwEq .
      hyp' : Deriv (imp Rf (eqF (ap1 thmT (closeW w))
                                 (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w)))))
      hyp' = eqSubst (\ t -> Deriv (imp Rf (eqF (ap1 thmT t)
                                                 (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) t)))))
                     (eqSym cwEq) hyp

      core : Deriv (imp Rf (eqF (ap1 thmT (ap1 G (closeW w))) codeFalse))
      core = cgiFun1 G gFact Rf w sub0_Rf sub1_Rf sim_Rf hyp'
  in eqSubst (\ t -> Deriv (imp Rf (eqF (ap1 thmT (ap1 G t)) codeFalse)))
             cwEq core
