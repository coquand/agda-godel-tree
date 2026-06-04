{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Lift1Eval -- Generic evalU correctness for  Lift1 f  on symbolic
-- (a, b) , parametric in  f , its fuel function  fFuel : Fun1 , and its
-- own correctness witness  fEval .
--
-- Lift1 f = R f v v ; semantically  (Lift1 f)(a, b) = f a  (constant in b).
-- evalU walks the R-recursion structurally over the second argument b :
--   b = O :     1 evRbase  +  f's eval at a            (= 1 + fFuel(a) stepUs)
--   b = s b' :  5 stepUs (evRstep, evV, rtR1, rtApp2, evV)  +  recursive Lift1 at (a, b')
--
-- The cumulative fuel  mLift1 : Fun2  is built by R-recursion mirroring
-- the structure:
--   mLift1 (a, O)     = sigma (s O) (fFuel a)
--   mLift1 (a, s b')  = sigma (natCode 5) (mLift1 (a, b'))
-- The eval correctness  lift1Eval  is proved by INTERNAL  ruleIndNat  on
-- a fresh var  w  representing b's shape;  a / K  are CAV at  w .

module T4.Lift1Eval where

open import T4.Base
open import T4.EvalU using
  ( mcode1 ; mcode2 ; cfgEV ; cfgRT ; kons ; frmR1 ; frmApp2 )
open import T4.EvalUStep using
  ( stepU ; stepU_at_evRbase ; stepU_at_evRstep ; stepU_at_evV
  ; stepU_at_rtR1 ; stepU_at_rtApp2 )
open import T4.LoopReaches using
  ( ClosedAtVar ; cavSubst ; mkCAV
  ; cav_O ; cav_ap1 ; cav_ap2 ; cav_natCode )

open import BRA3.Church       using ( pi ; sigma )
open import BRA3.Fan          using ( Lift1 ; Fan ; compose1U ; compose1U_eq )
open import BRA3.PairAlgebra  using ( axLift ; axFan ; axSnd )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import T4.IterComp using ( iterComp ; iterStepO )

------------------------------------------------------------------------
-- Closed-form helpers:
--
--   const5 : Fun1   with  const5 x = natCode 5 .
--   constSO : Fun1  with  constSO x = ap1 s O .

constSO : Fun1
constSO = compose1U s o

constSO_eq : (x : Term) -> Deriv (eqF (ap1 constSO x) (ap1 s O))
constSO_eq x = ruleTrans (compose1U_eq s o x) (cong1 s (ax_o x))

const5 : Fun1
const5 = compose1U s (compose1U s (compose1U s (compose1U s constSO)))

const5_eq : (x : Term) -> Deriv (eqF (ap1 const5 x) (natCode 5))
const5_eq x =
  let e0 : Deriv (eqF (ap1 constSO x) (ap1 s O))
      e0 = constSO_eq x
      e1 : Deriv (eqF (ap1 (compose1U s constSO) x) (ap1 s (ap1 s O)))
      e1 = ruleTrans (compose1U_eq s constSO x) (cong1 s e0)
      e2 : Deriv (eqF (ap1 (compose1U s (compose1U s constSO)) x)
                       (ap1 s (ap1 s (ap1 s O))))
      e2 = ruleTrans (compose1U_eq s (compose1U s constSO) x) (cong1 s e1)
      e3 : Deriv (eqF (ap1 (compose1U s (compose1U s (compose1U s constSO))) x)
                       (ap1 s (ap1 s (ap1 s (ap1 s O)))))
      e3 = ruleTrans (compose1U_eq s (compose1U s (compose1U s constSO)) x) (cong1 s e2)
  in ruleTrans (compose1U_eq s (compose1U s (compose1U s (compose1U s constSO))) x)
       (cong1 s e3)

------------------------------------------------------------------------
-- The abstract Lift1Eval module.

module Lift1EvalModule
  (f : Fun1)
  (fFuel : Fun1)
  -- f's eval correctness: at any  a, K  with  a CAV at the chosen inner
  -- var (here  7 ), the evalU walk from  cfgEV (mcode1 f) a K  to
  --  cfgRT (ap1 f a) K  takes  ap1 fFuel a  Term-fueled steps.
  (fEval : (a K : Term) ->
           Deriv (eqF (ap2 (iter stepU) (cfgEV (mcode1 f) a K) (ap1 fFuel a))
                       (cfgRT (ap1 f a) K)))
  where

  ----------------------------------------------------------------------
  -- mLift1 : Fun2 .  The cumulative fuel for  Lift1 f at (a, b) .
  --
  --   mLift1 a O      = sigma (s O) (fFuel a)
  --   mLift1 a (s b') = sigma (natCode 5) (mLift1 a b')

  baseFun : Fun1
  baseFun = C sigma constSO fFuel
  -- baseFun a = sigma (constSO a) (fFuel a) = sigma (s O) (fFuel a).

  baseFun_eq : (a : Term) ->
    Deriv (eqF (ap1 baseFun a) (ap2 sigma (ap1 s O) (ap1 fFuel a)))
  baseFun_eq a =
    ruleTrans (ax_C sigma constSO fFuel a)
              (congL sigma (ap1 fFuel a) (constSO_eq a))

  stepFun : Fun2
  stepFun = Fan (Lift1 const5) v sigma
  -- stepFun a b = sigma (const5 a) b = sigma (natCode 5) b.

  stepFun_eq : (a b : Term) ->
    Deriv (eqF (ap2 stepFun a b) (ap2 sigma (natCode 5) b))
  stepFun_eq a b =
    let e1 : Deriv (eqF (ap2 stepFun a b)
                         (ap2 sigma (ap2 (Lift1 const5) a b) (ap2 v a b)))
        e1 = axFan (Lift1 const5) v sigma a b
        e2 : Deriv (eqF (ap2 (Lift1 const5) a b) (natCode 5))
        e2 = ruleTrans (axLift const5 a b) (const5_eq a)
        e3 : Deriv (eqF (ap2 v a b) b)
        e3 = ax_v a b
    in ruleTrans e1
         (ruleTrans (congL sigma (ap2 v a b) e2)
                    (congR sigma (natCode 5) e3))

  mLift1 : Fun2
  mLift1 = R baseFun stepFun v

  mLift1_at_O : (a : Term) ->
    Deriv (eqF (ap2 mLift1 a O) (ap2 sigma (ap1 s O) (ap1 fFuel a)))
  mLift1_at_O a =
    ruleTrans (ax_R_base baseFun stepFun v a) (baseFun_eq a)

  mLift1_at_S : (a b : Term) ->
    Deriv (eqF (ap2 mLift1 a (ap1 s b))
                (ap2 sigma (natCode 5) (ap2 mLift1 a b)))
  mLift1_at_S a b =
    let e1 : Deriv (eqF (ap2 mLift1 a (ap1 s b))
                         (ap2 stepFun (ap2 v a b) (ap2 mLift1 a b)))
        e1 = ax_R_step baseFun stepFun v a b
        e2 : Deriv (eqF (ap2 stepFun (ap2 v a b) (ap2 mLift1 a b))
                         (ap2 stepFun b (ap2 mLift1 a b)))
        e2 = congL stepFun (ap2 mLift1 a b) (ax_v a b)
        e3 : Deriv (eqF (ap2 stepFun b (ap2 mLift1 a b))
                         (ap2 sigma (natCode 5) (ap2 mLift1 a b)))
        e3 = stepFun_eq b (ap2 mLift1 a b)
    in ruleTrans e1 (ruleTrans e2 e3)

  ----------------------------------------------------------------------
  -- DESIGN NOTE for the remaining  lift1Eval : (a b K : Term) -> ... .
  --
  -- The natural inner ruleIndNat on  b  (at some fresh var  w )  with motive
  --   INV(b) = eqF (iter (cfgEV (mcode2 (Lift1 f)) (pi a b) K) (ap2 mLift1 a b))
  --                (cfgRT (ap1 f a) K)
  -- runs into the K-MANAGEMENT issue:  the step case (b = s b') uses 3
  -- stepUs to push a  frmApp2(mcode2 v, b')  frame on K, yielding the
  -- recursive Lift1 call at (a, b', Kapp) where Kapp = kons (frmApp2 ...) K .
  -- The propositional IH gives the eq at OUTER  K , not at  Kapp .
  --
  -- Resolutions (all require further design work):
  --
  -- 1. KSTACK : Fun2  giving the nested-kons stack as a function of b and K
  --    (KSTACK = R u stepFrameWithK v).  Reformulate the proof into 3 phases:
  --    (a) push 3b stepUs to arrive at cfgEV (Lift1 f) (a, O) (KSTACK(b, K)) ;
  --    (b) one evRbase + fFuel(a) stepUs to cfgRT (ap1 f a) (KSTACK(b, K)) ;
  --    (c) pop 2b stepUs to cfgRT (ap1 f a) K .
  --    Each phase is a separate ruleIndNat on b; no recursive IH-at-different-K.
  --
  -- 2. Generalize the motive to be UNIVERSAL in K via a free var X .  The IH
  --    at (var w, var X) can be ruleInst'd at K := Kapp, but only at the
  --    META level -- inside ruleIndNat's propositional step, this isn't
  --    directly available.  Would require a different induction principle
  --    or a custom Skolemization.
  --
  -- 3. Use FoldRec / a higher-order recursion scheme that allows K-variation
  --    as part of the recursive structure.
  --
  -- Option 1 (KSTACK split into 3 phases) seems cleanest -- each ruleIndNat
  -- on b has a uniform motive without K-conflict.  This is left for the
  -- next session.

