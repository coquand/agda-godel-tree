{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.mario -- a worked example of the Carneiro deduction-theorem LIFT
-- (Mario Carneiro's trick, ndw2.pdf; see memory feedback-carneiro-lift-and-
-- ruleinst3 and T4.Thm12.ImpHelpers).
--
-- We derive, in BRA's OBJECT Hilbert calculus, the hypothesis-commutation
-- (flip / C-combinator) implication.  With  a0 = A , a1 = B , a2 = C :
--
--   flipImp : Deriv (imp (imp a0 (imp a1 a2)) (imp a1 (imp a0 a2)))
--
-- using ONLY the propositional axioms  axS / axK  and the carried-hypothesis
-- combinators  liftP / bCombTwo / impTrans  (BRA3.Contrapositive / BRA3.Logic).
-- No quantifiers, no ruleIndNat -- purely the lift.

module T4.mario where

open import T4.Base
open import BRA3.Logic          using ( impTrans )
open import BRA3.Contrapositive using ( liftP ; bCombTwo )

------------------------------------------------------------------------
-- The derivation.
--
-- Let  P = imp a0 (imp a1 a2)  (the hypothesis) and
--      Y = imp (imp a0 a1) (imp a0 a2) .
--
--   axS a0 a1 a2          : imp P Y                       -- Church's S axiom
--
-- Carneiro lift to build  imp Y (imp a1 (imp a0 a2))  (carry Y, then a1;
-- under {Y, a1} the goal (imp a0 a2) is reached by feeding the S-shaped Y the
-- trivial (imp a0 a1) obtained from a1 via K):
--
--   D1 = axK Y a1            : imp Y (imp a1 Y)           -- Y = imp (imp a0 a1) (imp a0 a2)
--                            : imp Y (imp a1 (imp (imp a0 a1) (imp a0 a2)))
--   D2 = liftP Y (axK a1 a0) : imp Y (imp a1 (imp a0 a1))
--   bCombTwo D1 D2           : imp Y (imp a1 (imp a0 a2)) -- 2-level S = the lift
--
-- Then  impTrans (axS a0 a1 a2) (...)  : imp P (imp a1 (imp a0 a2)) .

flipImp : (a0 a1 a2 : Formula) ->
          Deriv (imp (imp a0 (imp a1 a2)) (imp a1 (imp a0 a2)))
flipImp a0 a1 a2 =
  let Y : Formula
      Y = imp (imp a0 a1) (imp a0 a2)

      dYZ : Deriv (imp Y (imp a1 (imp a0 a2)))
      dYZ = bCombTwo {Y} {a1} {imp a0 a1} {imp a0 a2}
              (axK Y a1)
              (liftP Y (axK a1 a0))
  in impTrans (axS a0 a1 a2) dYZ
