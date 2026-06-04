{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RunMonoLeq -- the iterated-fixpoint core of CONFIG-LEVEL run
-- monotonicity ( the tool  clos  Step 1's  max  device consumes ).
--
-- =====================================================================
-- WHY ( the two-fuel-variable finding ).
-- =====================================================================
--
-- clos's "by monotonicity of run" lifts a run-claim from one fuel to a
-- common bound  max(x0,x1) .   At the FORMULA level ( runProg p L = s val )
-- this is NOT internally derivable ( readout is not invertible : from
-- runProg p L = s val  one cannot recover the  cfgHALT  witness needed to
-- step the fuel up ; see  T4.RunMono / memory ).   It IS derivable at the
-- CONFIG level, GIVEN an explicit  cfgHALT  witness ( = the per-program
-- "Berry" run data ) : the HALT configuration is a  stepU -fixpoint, so
-- iterating  stepU  any number of further steps preserves it.
--
-- This file ships the fixpoint core :
--
--   iterFix val d :  iter stepU (cfgHALT val) d = cfgHALT val
--
-- ( for any object fuel  d ), by INTERNAL induction ( ruleIndNat ) on  d ,
-- using only  iter_base_univ / iter_step_univ  and  stepU_at_halt .   The
-- leq-monotone lift  ( run@L -> run@L'  for  leq L L' , via  L' = L + (L'-L)
-- and  iter additivity ) is built on top of this once the  cfgHALT
-- witness is available.

module T4.RunMonoLeq where

open import T4.Base
open import T4.EvalU      using ( cfgHALT )
open import T4.EvalUStep  using ( stepU ; stepU_at_halt )
open import T4.EvalUEval  using ( initF )
open import T4.Kdef       using ( runProg )
open import T4.ProgParse  using ( parse )
open import T4.RunMono    using ( runProgAt )

open import T4.SubstNoVar          using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar )

open import BRA3.CourseOfValues    using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import BRA3.Logic             using ( prependEqLeft ; appendEqRight ; impTrans )
open import BRA3.Church            using ( sigma ; T33 ; T34 ; cong1Imp )
open import BRA3.RuleInst2         using ( ruleInst2 )
open import BRA3.RuleInst3         using ( ruleInst3 )

------------------------------------------------------------------------
-- SECTION 1.  The iterated fixpoint, by internal induction on the fuel.
--   The value lives at the FRESH variable  var 1  ( distinct from the
--   induction variable  var 0 ), so the  ruleIndNat  motive substitution
--   ( on  var 0 ) never touches it ; the actual value/fuel are installed
--   by two  ruleInst -s at the end.

-- cfgHALT (var 1) , the fixpoint configuration with the value at  var 1 .
cHv : Term
cHv = cfgHALT (var (suc zero))

-- the induction motive at  var 0 :  iter stepU (cfgHALT (var 1)) (var 0) = cfgHALT (var 1) .
motive : Formula
motive = eqF (ap2 (iter stepU) cHv (var zero)) cHv

iterFix_base : Deriv (eqF (ap2 (iter stepU) cHv O) cHv)
iterFix_base = iter_base_univ stepU cHv

iterFix_step :
  Deriv (imp motive (eqF (ap2 (iter stepU) cHv (ap1 s (var zero))) cHv))
iterFix_step =
  let A : Term                       -- iter stepU cHv (var 0)
      A = ap2 (iter stepU) cHv (var zero)
      B : Term                       -- iter stepU cHv (s (var 0))
      B = ap2 (iter stepU) cHv (ap1 s (var zero))

      -- B = stepU A  ( iter unfold at suc ).
      e_su : Deriv (eqF B (ap1 stepU A))
      e_su = iter_step_univ stepU cHv (var zero)

      -- stepU (cfgHALT (var 1)) = cfgHALT (var 1) .
      e_halt : Deriv (eqF (ap1 stepU cHv) cHv)
      e_halt = stepU_at_halt (var (suc zero))

      -- congruence :  A = cHv  ->  stepU A = stepU cHv .
      congImp : Deriv (imp (eqF A cHv) (eqF (ap1 stepU A) (ap1 stepU cHv)))
      congImp = ax_eqCong1 stepU A cHv

      -- conclusion transform :  stepU A = stepU cHv  ->  B = cHv .
      transp : Deriv (imp (eqF (ap1 stepU A) (ap1 stepU cHv)) (eqF B cHv))
      transp =
        impTrans
          (prependEqLeft B (ap1 stepU A) (ap1 stepU cHv) e_su)
          (appendEqRight B (ap1 stepU cHv) cHv e_halt)
  in impTrans congImp transp

iterFix_univ : Deriv motive
iterFix_univ = ruleIndNat zero {P = motive} iterFix_base iterFix_step

-- Install the actual value ( var 1 := val ) and fuel ( var 0 := d ).
-- val  is closed in use ( the program output ) ; d  is the fuel gap.
iterFix :
  (val : Term) -> NoVar val -> (d : Term) ->
  Deriv (eqF (ap2 (iter stepU) (cfgHALT val) d) (cfgHALT val))
iterFix val nvVal d =
  eqSubst (\ v -> Deriv (eqF (ap2 (iter stepU) (cfgHALT v) d) (cfgHALT v)))
          (substT_NoVar zero d val nvVal)
          (ruleInst zero d (ruleInst (suc zero) val iterFix_univ))

------------------------------------------------------------------------
-- SECTION 2.  Generic  iter  additivity ( the  step -specific  iter_add_T
--   of  T4.StepU2Reach , re-proved generic in the function  f ).
--   iter f c (sigma n m) = iter f (iter f c n) m .

sigma_zero : (x : Term) -> Deriv (eqF (ap2 sigma x O) x)
sigma_zero = T33

sigma_succ : (x y : Term) ->
  Deriv (eqF (ap2 sigma x (ap1 s y)) (ap1 s (ap2 sigma x y)))
sigma_succ x y = ruleInst2 zero x (suc zero) y refl T34

iter_add_gen :
  (f : Fun1) (c n m : Term) ->
  Deriv (eqF (ap2 (iter f) c (ap2 sigma n m))
              (ap2 (iter f) (ap2 (iter f) c n) m))
iter_add_gen f c n m =
  let Pform : Formula
      Pform = eqF (ap2 (iter f) (var 0) (ap2 sigma (var 1) (var 2)))
                  (ap2 (iter f) (ap2 (iter f) (var 0) (var 1)) (var 2))

      baseCase : Deriv (eqF (ap2 (iter f) (var 0) (ap2 sigma (var 1) O))
                            (ap2 (iter f) (ap2 (iter f) (var 0) (var 1)) O))
      baseCase =
        ruleTrans (congR (iter f) (var 0) (sigma_zero (var 1)))
                  (ruleSym (iter_base_univ f (ap2 (iter f) (var 0) (var 1))))

      LHS_h : Term
      LHS_h = ap2 (iter f) (var 0) (ap2 sigma (var 1) (var 2))
      RHS_h : Term
      RHS_h = ap2 (iter f) (ap2 (iter f) (var 0) (var 1)) (var 2)
      LHS_c : Term
      LHS_c = ap2 (iter f) (var 0) (ap2 sigma (var 1) (ap1 s (var 2)))
      RHS_c : Term
      RHS_c = ap2 (iter f) (ap2 (iter f) (var 0) (var 1)) (ap1 s (var 2))
      stepLH : Term
      stepLH = ap1 f LHS_h
      stepRH : Term
      stepRH = ap1 f RHS_h

      eL : Deriv (eqF LHS_c stepLH)
      eL = ruleTrans (congR (iter f) (var 0) (sigma_succ (var 1) (var 2)))
                     (iter_step_univ f (var 0) (ap2 sigma (var 1) (var 2)))

      eR : Deriv (eqF RHS_c stepRH)
      eR = iter_step_univ f (ap2 (iter f) (var 0) (var 1)) (var 2)

      stepCase : Deriv (imp Pform (eqF LHS_c RHS_c))
      stepCase =
        impTrans
          (impTrans (cong1Imp f LHS_h RHS_h)
                    (prependEqLeft LHS_c stepLH stepRH eL))
          (appendEqRight LHS_c stepRH RHS_c (ruleSym eR))

      universal : Deriv Pform
      universal = ruleIndNat 2 {P = Pform} baseCase stepCase
  in ruleInst3 zero c (suc zero) n (suc (suc zero)) m refl refl refl universal

------------------------------------------------------------------------
-- SECTION 3.  The CONFIG-LEVEL monotone lift ( the tool the two-variable
--   construction consumes ) :  running  g  MORE steps preserves the HALT.
--   No  leq / subtraction / commutativity -- the extra fuel is added by
--   sigma L g , so the result holds at the strictly larger fuel  L + g .

runHaltPlus :
  (val : Term) -> NoVar val -> (c L g : Term) ->
  Deriv (eqF (ap2 (iter stepU) c L) (cfgHALT val)) ->
  Deriv (eqF (ap2 (iter stepU) c (ap2 sigma L g)) (cfgHALT val))
runHaltPlus val nvVal c L g h =
  ruleTrans (iter_add_gen stepU c L g)
    (ruleTrans (congL (iter stepU) g h)
               (iterFix val nvVal g))

------------------------------------------------------------------------
-- SECTION 4.  The  runProg -level monotone lift : from a per-program
--   cfgHALT  witness ( = the "Berry" config-level halt data ) at fuel  L ,
--   the describe formula  runProg p (L + g) = s val  holds at the common
--   ( strictly larger ) fuel  L + g .   This is exactly what the two-fuel
--   frontEnd needs : lift EACH program's run to a single common bound, so
--   the day-r incompressibility's run-length and  K_rest 's fuel can be
--   unified WITHOUT the ( internally underivable ) formula-level monotonicity.

runProgPlus :
  (p val L g : Term) -> NoVar val ->
  Deriv (eqF (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L) (cfgHALT val)) ->
  Deriv (eqF (ap2 runProg p (ap2 sigma L g)) (ap1 s val))
runProgPlus p val L g nvVal h =
  runProgAt p val (ap2 sigma L g)
    (runHaltPlus val nvVal (ap1 initF (ap1 parse p)) L g h)
