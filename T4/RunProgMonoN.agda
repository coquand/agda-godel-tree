{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RunProgMonoN -- number-code FORMULA-LEVEL run monotonicity ( clos lines
-- 35-36 :  "by monotonicity of run" ;  the x0,x1 step linchpin ).
--
--   runProgMonoPlusN     p val L g :  runProgN p L = s val  =>  runProgN p (L+g) = s val
--   imp_runProgMonoPlusN P p val L g :  imp P (runProgN p L = s val)
--                                       -> imp P (runProgN p (L+g) = s val)
--
-- Proven by REDUCTION to the shipped  T4.RunProgMono  ( on the OLD  runProg )
-- through the bridge
--
--   runProgN p y  =  runProg (candidate p) y
--
-- ( both reduce to  evalU (parse (candidate p)) y :  runProgN_eq + parseN_eq vs
--   runProg_eq ).   So the entire readout-inversion / stepU-fixpoint argument is
-- reused verbatim at the program NUMBER  p  ( decoded by  candidate ).

module T4.RunProgMonoN where

open import T4.Base
open import BRA3.Church       using ( sigma )
open import T4.EvalUEval      using ( evalU )
open import T4.ProgParse      using ( parse )
open import T4.Kdef           using ( runProg ; runProg_eq )
open import T4.Candidate      using ( candidate )
open import T4.ParseN         using ( runProgN ; runProgN_eq ; parseN ; parseN_eq )
open import T4.RunProgMono    using ( runProgMonoPlus ; imp_runProgMonoPlus )
open import T4.Thm12.ImpHelpers using ( impEqTrans ; impLift )

------------------------------------------------------------------------
-- The bridge :  runProgN p y = runProg (candidate p) y .

runProgN_as_runProg :
  (p y : Term) ->
  Deriv (eqF (ap2 runProgN p y) (ap2 runProg (ap1 candidate p) y))
runProgN_as_runProg p y =
  ruleTrans (runProgN_eq p y)
    (ruleTrans (congL evalU y (parseN_eq p))
               (ruleSym (runProg_eq (ap1 candidate p) y)))

------------------------------------------------------------------------
-- The number-code additive monotonicity ( object form ).

runProgMonoPlusN :
  (p val L g : Term) ->
  Deriv (eqF (ap2 runProgN p L) (ap1 s val)) ->
  Deriv (eqF (ap2 runProgN p (ap2 sigma L g)) (ap1 s val))
runProgMonoPlusN p val L g hyp =
  let cp : Term
      cp = ap1 candidate p
      brL : Deriv (eqF (ap2 runProgN p L) (ap2 runProg cp L))
      brL = runProgN_as_runProg p L
      h2 : Deriv (eqF (ap2 runProg cp L) (ap1 s val))
      h2 = ruleTrans (ruleSym brL) hyp
      mono : Deriv (eqF (ap2 runProg cp (ap2 sigma L g)) (ap1 s val))
      mono = runProgMonoPlus cp val L g h2
      brLg : Deriv (eqF (ap2 runProgN p (ap2 sigma L g)) (ap2 runProg cp (ap2 sigma L g)))
      brLg = runProgN_as_runProg p (ap2 sigma L g)
  in ruleTrans brLg mono

------------------------------------------------------------------------
-- The IMP-LIFTED form ( the two-fuel front end consumes this : a POSITIVE
--   runProgN = s val  conjunct available only UNDER a hypothesis  P ).

imp_runProgMonoPlusN :
  (P : Formula) (p val L g : Term) ->
  Deriv (imp P (eqF (ap2 runProgN p L) (ap1 s val))) ->
  Deriv (imp P (eqF (ap2 runProgN p (ap2 sigma L g)) (ap1 s val)))
imp_runProgMonoPlusN P p val L g hyp =
  let cp : Term
      cp = ap1 candidate p
      brL : Deriv (eqF (ap2 runProgN p L) (ap2 runProg cp L))
      brL = runProgN_as_runProg p L
      h2 : Deriv (imp P (eqF (ap2 runProg cp L) (ap1 s val)))
      h2 = impEqTrans {P} (ap2 runProg cp L) (ap2 runProgN p L) (ap1 s val)
             (impLift {P} (ruleSym brL)) hyp
      mono : Deriv (imp P (eqF (ap2 runProg cp (ap2 sigma L g)) (ap1 s val)))
      mono = imp_runProgMonoPlus P cp val L g h2
      brLg : Deriv (eqF (ap2 runProgN p (ap2 sigma L g)) (ap2 runProg cp (ap2 sigma L g)))
      brLg = runProgN_as_runProg p (ap2 sigma L g)
  in impEqTrans {P} (ap2 runProgN p (ap2 sigma L g)) (ap2 runProg cp (ap2 sigma L g))
       (ap1 s val) (impLift {P} brLg) mono
