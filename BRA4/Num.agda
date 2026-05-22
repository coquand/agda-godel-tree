{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Num -- the internal numeralisation functor  num : Fun1 .
--
-- CONTRACT (universal closure, no  Closed  / freshness premise):
--
--   num_at_O : Deriv (eqF (ap1 num O) (codeTerm O))
--             ( = Deriv (eqF (ap1 num O) O)  by definition of codeTerm )
--
--   num_at_S : (t : Term) ->
--              Deriv (eqF (ap1 num (ap1 s t))
--                          (ap2 Pair (natCode tag_ap1)
--                            (ap2 Pair (codeFun1 s) (ap1 num t))))
--             ( = Deriv (eqF (ap1 num (ap1 s t))
--                            (ap2 Pair (natCode tag_ap1)
--                              (ap2 Pair (natCode tag_s) (ap1 num t))))
--             )
--
-- The matching nested-Pair form is essential.  In codeTerm (Option 2 in
-- BRA4/PLAN.md), an  ap1 f t  is encoded as  Pair tag_ap1 (Pair (codeFun1 f)
-- (codeTerm t)) , so for the equation  num n = codeTerm n  to hold on
-- numerals  n  by meta-induction, num's recursion must wrap each
--  s  in the SAME nested layout.
--
-- (BRA4/PLAN.md's  num_at_S  statement omits the outer  tag_ap1
-- wrapping; we fix that here so that the Deriv-level bridge
--  num_eq_code  in BRA4.IsNat is a straightforward meta-induction.)
--
-- CONSTRUCTION:
--
--   numStepInner : Fun2  -- inner Pair: Pair (natCode tag_s) b
--                = Fan (Lift1 (constN tag_s)) v Pair
--
--   numStep      : Fun2  -- outer wrap: Pair (natCode tag_ap1) (Pair tag_s b)
--                = Fan (Lift1 (constN tag_ap1)) numStepInner Pair
--
--   numAux       : Fun2  -- R-recursion on second arg, base case = O
--                = R o numStep v
--
--   num          : Fun1  -- specialise numAux's first arg to O
--                = C numAux o u

module BRA4.Num where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

------------------------------------------------------------------------
-- Inner step-functor:  numStepInner(a, b) = Pair (natCode tag_s) b .

numStepInner : Fun2
numStepInner = Fan (Lift1 (constN tag_s)) v Pair

numStepInner_eq :
  (a b : Term) ->
  Deriv (eqF (ap2 numStepInner a b)
              (ap2 Pair (natCode tag_s) b))
numStepInner_eq a b =
  let
    step1 :
      Deriv (eqF (ap2 numStepInner a b)
                  (ap2 Pair (ap2 (Lift1 (constN tag_s)) a b) (ap2 v a b)))
    step1 = axFan (Lift1 (constN tag_s)) v Pair a b

    step2_inner :
      Deriv (eqF (ap2 (Lift1 (constN tag_s)) a b)
                  (ap1 (constN tag_s) a))
    step2_inner = axLift (constN tag_s) a b

    step2 :
      Deriv (eqF (ap2 Pair (ap2 (Lift1 (constN tag_s)) a b) (ap2 v a b))
                  (ap2 Pair (ap1 (constN tag_s) a) (ap2 v a b)))
    step2 = congL Pair (ap2 v a b) step2_inner

    step3_inner :
      Deriv (eqF (ap1 (constN tag_s) a) (natCode tag_s))
    step3_inner = constN_eq tag_s a

    step3 :
      Deriv (eqF (ap2 Pair (ap1 (constN tag_s) a) (ap2 v a b))
                  (ap2 Pair (natCode tag_s) (ap2 v a b)))
    step3 = congL Pair (ap2 v a b) step3_inner

    step4 :
      Deriv (eqF (ap2 Pair (natCode tag_s) (ap2 v a b))
                  (ap2 Pair (natCode tag_s) b))
    step4 = congR Pair (natCode tag_s) (ax_v a b)
  in ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))

------------------------------------------------------------------------
-- Outer step-functor:  numStep(a, b) = Pair (natCode tag_ap1)
--                                            (Pair (natCode tag_s) b) .

numStep : Fun2
numStep = Fan (Lift1 (constN tag_ap1)) numStepInner Pair

numStep_eq :
  (a b : Term) ->
  Deriv (eqF (ap2 numStep a b)
              (ap2 Pair (natCode tag_ap1)
                (ap2 Pair (natCode tag_s) b)))
numStep_eq a b =
  let
    -- ap2 numStep a b
    --  = Pair (Lift1 (constN tag_ap1) (a, b)) (numStepInner (a, b))   [axFan]
    step1 :
      Deriv (eqF (ap2 numStep a b)
                  (ap2 Pair (ap2 (Lift1 (constN tag_ap1)) a b)
                              (ap2 numStepInner a b)))
    step1 = axFan (Lift1 (constN tag_ap1)) numStepInner Pair a b

    -- Lift1 (constN tag_ap1) (a, b) =Deriv= constN tag_ap1 (a) =Deriv= natCode tag_ap1
    step2_a :
      Deriv (eqF (ap2 (Lift1 (constN tag_ap1)) a b)
                  (ap1 (constN tag_ap1) a))
    step2_a = axLift (constN tag_ap1) a b

    step2_b :
      Deriv (eqF (ap1 (constN tag_ap1) a) (natCode tag_ap1))
    step2_b = constN_eq tag_ap1 a

    step2 :
      Deriv (eqF (ap2 Pair (ap2 (Lift1 (constN tag_ap1)) a b)
                            (ap2 numStepInner a b))
                  (ap2 Pair (natCode tag_ap1) (ap2 numStepInner a b)))
    step2 = congL Pair (ap2 numStepInner a b) (ruleTrans step2_a step2_b)

    -- numStepInner (a, b) =Deriv= Pair (natCode tag_s) b
    step3 :
      Deriv (eqF (ap2 Pair (natCode tag_ap1) (ap2 numStepInner a b))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) b)))
    step3 = congR Pair (natCode tag_ap1) (numStepInner_eq a b)
  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- 2-ary helper:  numAux  is the R-recursion driving num.

numAux : Fun2
numAux = R o numStep v

------------------------------------------------------------------------
-- 1-ary num: specialise numAux's first arg to O via C ... o u.

num : Fun1
num = C numAux o u

------------------------------------------------------------------------
-- Universal unfold:  ap1 num t  =Deriv=  ap2 numAux O t .

num_unfold :
  (t : Term) ->
  Deriv (eqF (ap1 num t) (ap2 numAux O t))
num_unfold t =
  let
    step1 :
      Deriv (eqF (ap1 num t)
                  (ap2 numAux (ap1 o t) (ap1 u t)))
    step1 = ax_C numAux o u t

    step2 :
      Deriv (eqF (ap2 numAux (ap1 o t) (ap1 u t))
                  (ap2 numAux O (ap1 u t)))
    step2 = congL numAux (ap1 u t) (ax_o t)

    step3 :
      Deriv (eqF (ap2 numAux O (ap1 u t))
                  (ap2 numAux O t))
    step3 = congR numAux O (ax_u t)
  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- num_at_O :  ap1 num O  =Deriv=  O  ( = codeTerm O ).

num_at_O : Deriv (eqF (ap1 num O) O)
num_at_O =
  let
    step1 : Deriv (eqF (ap1 num O) (ap2 numAux O O))
    step1 = num_unfold O

    step2 : Deriv (eqF (ap2 numAux O O) (ap1 o O))
    step2 = ax_R_base o numStep v O

    step3 : Deriv (eqF (ap1 o O) O)
    step3 = ax_o O
  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- num_at_S :  ap1 num (s t)
--             =Deriv= Pair (natCode tag_ap1) (Pair (natCode tag_s) (num t)) .
--
-- Chain (universal in t):
--   num (s t)
--    --[unfold]--> numAux O (s t)
--    --[ax_R_step]--> numStep (v O t) (numAux O t)
--    --[numStep_eq]--> Pair tag_ap1 (Pair tag_s (numAux O t))
--    --[unfold reversed inside]--> Pair tag_ap1 (Pair tag_s (num t))

num_at_S :
  (t : Term) ->
  Deriv (eqF (ap1 num (ap1 s t))
              (ap2 Pair (natCode tag_ap1)
                (ap2 Pair (natCode tag_s) (ap1 num t))))
num_at_S t =
  let
    step1 :
      Deriv (eqF (ap1 num (ap1 s t)) (ap2 numAux O (ap1 s t)))
    step1 = num_unfold (ap1 s t)

    step2 :
      Deriv (eqF (ap2 numAux O (ap1 s t))
                  (ap2 numStep (ap2 v O t) (ap2 numAux O t)))
    step2 = ax_R_step o numStep v O t

    step3 :
      Deriv (eqF (ap2 numStep (ap2 v O t) (ap2 numAux O t))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) (ap2 numAux O t))))
    step3 = numStep_eq (ap2 v O t) (ap2 numAux O t)

    -- Replace inner  numAux O t  with  num t .
    inner_bridge :
      Deriv (eqF (ap2 Pair (natCode tag_s) (ap2 numAux O t))
                  (ap2 Pair (natCode tag_s) (ap1 num t)))
    inner_bridge =
      congR Pair (natCode tag_s) (ruleSym (num_unfold t))

    step4 :
      Deriv (eqF (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) (ap2 numAux O t)))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) (ap1 num t))))
    step4 = congR Pair (natCode tag_ap1) inner_bridge
  in ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))
