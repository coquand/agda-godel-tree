{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.EnumRunProg -- the Fun2 combinator
--   enumRunProgOf enum := Fan (Lift1 enum) v runProg
-- with its single equational reduction
--   ap2 (enumRunProgOf enum) a b  =  ap2 runProg (ap1 enum a) b
-- proved by  axFan + axLift + ax_v + congL + congR  (literal mirror of
-- runProg_eq in T4.Kdef , where  parse  is replaced by  enum  and the
-- outer Fun2 is  runProg  instead of  evalU ).
--
-- =====================================================================
-- WHY THIS COMBINATOR.
-- =====================================================================
--
-- For the conjunction-shape K-formula  KdefConj M enum subject  ( see
-- T4.SurpriseG2.KdefConj ) the program slot was originally
--   ap2 runProg (ap1 enum v0) v1
-- whose substituted ~def code becomes  cAp2f runProg (cAp1f enum S0) S1
-- with a  cAp1f enum  wrapping that  thm13_binary  does NOT produce
-- ( thm13_binary at  runProg  produces  ap1 num <prog> , not  cAp1f
-- enum ) .   See  T4.SurpriseG2.CGIConjBody  header for the analysis .
--
-- Replacing the program slot by  ap2 (enumRunProgOf enum) v0 v1  makes
-- the substituted ~def code  cAp2f (enumRunProgOf enum) S0 S1 , which
-- thm13_binary at  enumRunProgOf enum  produces literally ; the
-- equational equivalence  enumRunProgOf_eq  proves the new K-formula
-- semantically equivalent to the old one .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   enumRunProgOf : Fun1 -> Fun2
--   enumRunProgOf_eq :
--     (enum : Fun1) (a b : Term) ->
--     Deriv (eqF (ap2 (enumRunProgOf enum) a b)
--                 (ap2 runProg (ap1 enum a) b))

module T4.SurpriseG2.EnumRunProg where

open import T4.Base
open import T4.Kdef using ( runProg )

------------------------------------------------------------------------
-- The combinator and its equational reduction .   BOTH wrapped in an
-- `abstract` block to keep  enumRunProgOf enum  OPAQUE for downstream
-- typecheck .   Reason ( per memory/feedback_slow_typecheck_means_abstract_constants
-- and the analysis in  T4/SurpriseG2/CgiClashConj.agda ) :   without
-- this abstraction ,  codeFun2 (enumRunProgOf enum)  expands the deep
-- Fan-of-Fan-of-Fun2 spine at every  cAp2f  invocation downstream ,
-- blowing the cgiClashConj typecheck above 60s .   With  abstract ,
-- the spine stays as  codeFun2 (enumRunProgOf enum)  symbolic and
-- typecheck stays  < 1.5s warm .
--
-- The `abstract` ALSO covers  enumRunProgOf_eq  so that downstream
-- proofs CAN refer to the equational law on the symbolic form without
-- forcing the underlying Fan/Lift1/v unfold .

abstract

  enumRunProgOf : Fun1 -> Fun2
  enumRunProgOf enum = Fan (Lift1 enum) v runProg

  enumRunProgOf_eq :
    (enum : Fun1) (a b : Term) ->
    Deriv (eqF (ap2 (enumRunProgOf enum) a b)
                (ap2 runProg (ap1 enum a) b))
  enumRunProgOf_eq enum a b =
    ruleTrans (axFan (Lift1 enum) v runProg a b)
      (ruleTrans (congL runProg (ap2 v a b) (axLift enum a b))
                 (congR runProg (ap1 enum a) (ax_v a b)))
