{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DefIndReflN -- the per-day reflection turning a value-level FAIL
--   isZero ( defIndN p (pi z y) ) = O
-- into the describe EQUATION
--   runProgN p y = s z .
--
-- This is the per-conjunct core of the conj-bridge  Kr x0 = O  =>  K_rest(x0)
-- ( SURPRISE-GII-NUMBERCODE-HANDOFF S3.4 ) :  a zero fail-summand means that day
-- IS described.   Pure reflection ( natEqF_complete + isZero ), reusable.
--
--   defIndN_at_pi p z y : defIndN p (pi z y) = natEqF (runProgN p y) (s z)
--   failReflectN  p z y : imp ( isZero (defIndN p (pi z y)) = O )
--                             ( runProgN p y = s z )

module T4.DefIndReflN where

open import T4.Base
open import BRA3.Church          using ( isZero ; pi ; TisZeroZ )
open import BRA3.SubT.NatEq      using ( natEqF )
open import BRA3.Logic           using ( prependEqLeft ; eqSymImp )
open import BRA3.Contrapositive  using ( liftP ; identP ; compI )
open import BRA3.ChurchT80       using ( succEqO_to_anything )
open import BRA3.ChurchCM        using ( caseElim )
open import T4.NatEqReflect      using ( natEqF_complete ; app2 )
open import T4.Thm12.ImpHelpers  using ( impLift ; impCong1 ; impEqTrans ; impRuleSym )
open import T4.Counting          using ( mapUnder1 )
open import T4.ParseN            using ( runProgN )
open import T4.DefIndN           using ( defIndN ; defIndN_eq )

------------------------------------------------------------------------
-- Two-antecedent eqF-transitivity ( local copy of RunProgMono.impEqTrans2 ).

impEqTrans2 :
  {W1 W2 : Formula} (a b c : Term) ->
  Deriv (imp W1 (imp W2 (eqF a b))) ->
  Deriv (imp W1 (imp W2 (eqF b c))) ->
  Deriv (imp W1 (imp W2 (eqF a c)))
impEqTrans2 {W1} {W2} a b c f1 f2 =
  let f1flip : Deriv (imp W1 (imp W2 (eqF b a)))
      f1flip = app2 (impLift {W1} (impLift {W2} (eqSymImp a b))) f1
      lifted : Deriv (imp W1 (imp W2 (imp (eqF b c) (eqF a c))))
      lifted = app2 (impLift {W1} (impLift {W2} (ax_eqTrans b a c))) f1flip
  in app2 lifted f2

------------------------------------------------------------------------
-- defIndN at a packaged argument  pi z y .

defIndN_at_pi :
  (p z y : Term) ->
  Deriv (eqF (ap2 defIndN p (ap2 pi z y))
             (ap2 natEqF (ap2 runProgN p y) (ap1 s z)))
defIndN_at_pi p z y =
  let e1 : Deriv (eqF (ap2 defIndN p (ap2 pi z y))
                      (ap2 natEqF (ap2 runProgN p (ap1 Snd (ap2 pi z y)))
                                  (ap1 s (ap1 Fst (ap2 pi z y)))))
      e1 = defIndN_eq p (ap2 pi z y)
      e2 : Deriv (eqF (ap2 natEqF (ap2 runProgN p (ap1 Snd (ap2 pi z y)))
                                  (ap1 s (ap1 Fst (ap2 pi z y))))
                      (ap2 natEqF (ap2 runProgN p y)
                                  (ap1 s (ap1 Fst (ap2 pi z y)))))
      e2 = congL natEqF (ap1 s (ap1 Fst (ap2 pi z y)))
                 (congR runProgN p (axSnd z y))
      e3 : Deriv (eqF (ap2 natEqF (ap2 runProgN p y) (ap1 s (ap1 Fst (ap2 pi z y))))
                      (ap2 natEqF (ap2 runProgN p y) (ap1 s z)))
      e3 = congR natEqF (ap2 runProgN p y) (cong1 s (axFst z y))
  in ruleTrans e1 (ruleTrans e2 e3)

------------------------------------------------------------------------
-- The reflection :  fail = O  =>  the day IS described .

failReflectN :
  (p z y : Term) ->
  Deriv (imp (eqF (ap1 isZero (ap2 defIndN p (ap2 pi z y))) O)
             (eqF (ap2 runProgN p y) (ap1 s z)))
failReflectN p z y =
  let A : Term
      A = ap2 runProgN p y
      B : Term
      B = ap1 s z
      goal : Formula
      goal = eqF A B
      Hf : Formula
      Hf = eqF (ap1 isZero (ap2 defIndN p (ap2 pi z y))) O
      dpz : Term
      dpz = ap2 defIndN p (ap2 pi z y)

      e_di : Deriv (eqF dpz (ap2 natEqF A B))
      e_di = defIndN_at_pi p z y

      -- Under  ~goal :  natEqF A B = O ,  hence  dpz = O ,  hence  isZero dpz = s O .
      defO : Deriv (imp (neg goal) (eqF dpz O))
      defO = compI (natEqF_complete A B)
                   (prependEqLeft dpz (ap2 natEqF A B) O e_di)

      izSO : Deriv (imp (neg goal) (eqF (ap1 isZero dpz) (ap1 s O)))
      izSO = impEqTrans {neg goal} (ap1 isZero dpz) (ap1 isZero O) (ap1 s O)
               (impCong1 {neg goal} isZero dpz O defO)
               (impLift {neg goal} TisZeroZ)

      -- Under  [~goal , Hf] :  s O = isZero dpz = O .
      p1 : Deriv (imp (neg goal) (imp Hf (eqF (ap1 s O) (ap1 isZero dpz))))
      p1 = mapUnder1 (neg goal) (axK (eqF (ap1 s O) (ap1 isZero dpz)) Hf)
                     (impRuleSym izSO)
      p2 : Deriv (imp (neg goal) (imp Hf (eqF (ap1 isZero dpz) O)))
      p2 = liftP (neg goal) (identP Hf)
      sOeqO : Deriv (imp (neg goal) (imp Hf (eqF (ap1 s O) O)))
      sOeqO = impEqTrans2 {neg goal} {Hf} (ap1 s O) (ap1 isZero dpz) O p1 p2

      -- the by-cases branches for  imp Hf goal .
      Y_R : Deriv (imp (neg goal) (imp Hf goal))
      Y_R = app2 (liftP (neg goal) (liftP Hf (succEqO_to_anything O goal))) sOeqO
  in caseElim {goal} {neg goal} {imp Hf goal}
       (identP (neg goal)) (axK goal Hf) Y_R
