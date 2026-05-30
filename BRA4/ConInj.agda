{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ConInj -- Con-injectivity, the core of Kritchman-Raz Phase KR-A.
--
-- "The same name defines at most one number, under Con."  If a name formula  G
-- th-defines both  x  and  x' , then  x = x' ; for DISTINCT  x , x'  that yields
-- falseF  under  Con .  This is the injectivity that feeds the counting
-- pigeonhole (`InjBelowObj` in BRA4.CountingObj, via the merged surprise-exam
-- induction):  distinct compressible numbers have distinct names.
--
-- FORMAT-AGNOSTIC (buildable before  parse / DefWit ).  The "G defines x" content
-- is supplied by the caller (KR-A's  compress_canonical / DefWit ) as
-- thmT-PROVABILITY facts:
--
--   du   : thmT proves  G_x -> (G_x' -> x=x')    -- uniqueness of  G  at  x , x'
--   da   : thmT proves  G_x                       -- G holds at  x
--   db   : thmT proves  G_x'                      -- G holds at  x'
--   dneq : thmT proves  (x=x') -> falseF          -- the distinct-numeral
--                                                 --   disequality, necessitated
--
-- (`du` is the uniqueness clause  forall v0 v1 (G(v0) /\ G(v1) -> v0=v1)  of
-- "G names x", instantiated at  x , x' ; `da`/`db` are membership; `dneq` is the
-- meta fact  x /= x'  necessitated via D1 -- all produced in KR-A.)
--
-- con_inj  then assembles the contradiction purely with the SHIPPED thmT-internal
-- modus ponens (`encoded_mp`, BRA4.Thm12.EncodedMp): two MPs combine
-- `du`/`da`/`db`  into  "thmT proves x=x'", a third MP with `dneq` gives
-- "thmT proves falseF", and  Con  (instantiated at that proof code) discharges it.
-- No reflection, no thmT-internal substitution: the instantiation lives in the
-- caller (it provides  du / dneq  already at  x , x').

module BRA4.ConInj where

open import BRA4.Base
open import BRA4.Tags          using ( tag_imp ; tag_mp )
open import BRA4.Code          using ( codeFalse ; falseF )
open import BRA4.ThmT          using ( thmT )
open import BRA4.Thm12.EncodedMp using ( encoded_mp )

open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- code of  (imp A B)  from the codes of  A , B  (the shape  encoded_mp  reads).

cimp : Term -> Term -> Term
cimp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

-- code of the modus-ponens proof  mp(pImp, pA) .
cmp : Term -> Term -> Term
cmp pImp pA = ap2 Pair (natCode tag_mp) (ap2 Pair pImp pA)

------------------------------------------------------------------------
-- Consistency schema (identical to the shipped diagonal  godelII 's).

ConSchema : Formula
ConSchema = neg (eqF (ap1 thmT (var zero)) codeFalse)

------------------------------------------------------------------------
-- con_inj.

con_inj :
  Deriv ConSchema ->
  (cGx cGx' cEq : Term)               -- codeFormula G_x , G_x' , (x = x')
  (pu pa pb pneg : Term)              -- proof codes
  (du   : Deriv (eqF (ap1 thmT pu)   (cimp cGx (cimp cGx' cEq)))) ->
  (da   : Deriv (eqF (ap1 thmT pa)   cGx)) ->
  (db   : Deriv (eqF (ap1 thmT pb)   cGx')) ->
  (dneq : Deriv (eqF (ap1 thmT pneg) (cimp cEq codeFalse))) ->
  Deriv falseF
con_inj con cGx cGx' cEq pu pa pb pneg du da db dneq =
  let p1 : Term
      p1 = cmp pu pa
      p2 : Term
      p2 = cmp p1 pb
      p3 : Term
      p3 = cmp pneg p2

      -- thmT proves  (G_x' -> x=x')   [MP of  du , da].
      step1 : Deriv (eqF (ap1 thmT p1) (cimp cGx' cEq))
      step1 = encoded_mp pu pa cGx (cimp cGx' cEq) du da

      -- thmT proves  x=x'             [MP of  step1 , db].
      step2 : Deriv (eqF (ap1 thmT p2) cEq)
      step2 = encoded_mp p1 pb cGx' cEq step1 db

      -- thmT proves  falseF           [MP of  dneq , step2].
      step3 : Deriv (eqF (ap1 thmT p3) codeFalse)
      step3 = encoded_mp pneg p2 cEq codeFalse dneq step2

      -- Con instantiated at the falseF-proof code refutes  step3 .
      con_inst : Deriv (neg (eqF (ap1 thmT p3) codeFalse))
      con_inst = ruleInst zero p3 con
  in mp (mp (axExFalso (eqF (ap1 thmT p3) codeFalse) falseF) step3) con_inst
