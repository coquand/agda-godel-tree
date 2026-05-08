{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Sb -- our tree-based analog of Guard's substitution functor
-- (Exercise 24 [4], guard15.pdf p.14):
--
--     sb(J("A", n), "P")  =  "S^{x_n}_{A} P"
--
-- That is: given a coded term codeA, a numeral n, and a coded
-- formula codeP, sb substitutes (the coded term) A for the variable
-- x_n in P.
--
-- This is the operation invoked by Definition 12 line 2 of  th
-- (guard15.pdf p.15):
--
--     th(4y+1) = sb(KKy, IKy, th(Iy))
--
-- under the convention that sb is 2-ary on Trees, with its first
-- argument the J-pair (codeA, n).  Here KKy = codeA, IKy = n,
-- th(Iy) = codeP.
--
-- In our tree setting, sb : Fun2 takes
--
--   arg1 : reified J-pair  ap2 Pair (reify codeA) (reify (natCode n))
--   arg2 : reified coded formula  reify codeP
--
-- and returns
--
--   reify (codedSubst codeA (code (var n)) codeP) .
--
-- sb is built from the existing  subT  combinator (BRA2.SubT) plus
-- Fan / Lift / KT / Post / Pair primitives -- no new primitives, no
-- postulates, no holes.
--
-- Spec (this file):
--   ap2 sb (ap2 Pair (reify codeA) (reify (natCode n)))
--          (reify codeP)
--     = reify (codedSubst codeA (code (var n)) codeP) .
--
-- This file's payoff: it lets later sessions internalise Definition
-- 12 line 2 of  th  (Goedel II step 4) without any new BRA-foundation
-- reflection axioms.

module BRA2.Sb where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.StepReduce
open import BRA2.SubT

------------------------------------------------------------------------
-- Constant: code of the variable tag, reified.
--
-- This is the literal Term  reify tagVar .  Combined with a numeral
--  reify (natCode n) , a Pair gives  reify (code (var n)) :
--
--   reify (code (var n))
--     = reify (nd tagVar (natCode n))
--     = ap2 Pair (reify tagVar) (reify (natCode n)) .
--
-- This identity is definitional and used implicitly below.

tagVarT : Term
tagVarT = reify tagVar

------------------------------------------------------------------------
-- Combinators for sb.
--
-- Decomposition of sb on inputs (arg1 = Pair codeA_term n_term,
-- arg2 = codeP_term):
--
--   1. buildVarCodeSb : Fun2 with
--        ap2 buildVarCodeSb arg1 arg2 = ap2 Pair tagVarT (Snd arg1)
--      i.e., produces  reify (code (var n))  from  arg1 .
--
--   2. repackageSb : Fun2 with
--        ap2 repackageSb arg1 arg2
--          = ap2 Pair (ap2 Pair tagVarT (Snd arg1)) (Fst arg1)
--      i.e., produces the substitution-data pair subT expects.
--
--   3. rightSb : Fun2 with
--        ap2 rightSb arg1 arg2 = arg2
--      i.e., projects the second argument unchanged.
--
--   4. sb = Fan repackageSb rightSb subT .

buildVarCodeSb : Fun2
buildVarCodeSb = Fan (Lift (KT tagVarT)) (Lift Snd) Pair

repackageSb : Fun2
repackageSb = Fan buildVarCodeSb (Lift Fst) Pair

rightSb : Fun2
rightSb = Post Snd Pair

sb : Fun2
sb = Fan repackageSb rightSb subT

------------------------------------------------------------------------
-- Lemma: buildVarCodeSb on (Pair p q, b) reduces to (Pair tagVarT q).

buildVarCodeSbAt : (p q b : Term) ->
  Deriv (atomic (eqn (ap2 buildVarCodeSb (ap2 Pair p q) b)
                      (ap2 Pair tagVarT q)))
buildVarCodeSbAt p q b =
  let arg1 : Term
      arg1 = ap2 Pair p q

      r1 : Deriv (atomic (eqn (ap2 buildVarCodeSb arg1 b)
                              (ap2 Pair (ap2 (Lift (KT tagVarT)) arg1 b)
                                        (ap2 (Lift Snd) arg1 b))))
      r1 = axFan (Lift (KT tagVarT)) (Lift Snd) Pair arg1 b

      r2 : Deriv (atomic (eqn (ap2 (Lift (KT tagVarT)) arg1 b) tagVarT))
      r2 = constF2Red tagVar tagVar_isValue arg1 b

      r3 : Deriv (atomic (eqn (ap2 (Lift Snd) arg1 b) q))
      r3 = ruleTrans (axLift Snd arg1 b) (axSnd p q)

      r4 : Deriv (atomic (eqn (ap2 Pair (ap2 (Lift (KT tagVarT)) arg1 b)
                                        (ap2 (Lift Snd) arg1 b))
                              (ap2 Pair tagVarT (ap2 (Lift Snd) arg1 b))))
      r4 = congL Pair (ap2 (Lift Snd) arg1 b) r2

      r5 : Deriv (atomic (eqn (ap2 Pair tagVarT (ap2 (Lift Snd) arg1 b))
                              (ap2 Pair tagVarT q)))
      r5 = congR Pair tagVarT r3
  in ruleTrans r1 (ruleTrans r4 r5)

------------------------------------------------------------------------
-- Lemma: repackageSb on (Pair p q, b) reduces to (Pair (Pair tagVarT q) p).

repackageSbAt : (p q b : Term) ->
  Deriv (atomic (eqn (ap2 repackageSb (ap2 Pair p q) b)
                      (ap2 Pair (ap2 Pair tagVarT q) p)))
repackageSbAt p q b =
  let arg1 : Term
      arg1 = ap2 Pair p q

      r1 : Deriv (atomic (eqn (ap2 repackageSb arg1 b)
                              (ap2 Pair (ap2 buildVarCodeSb arg1 b)
                                        (ap2 (Lift Fst) arg1 b))))
      r1 = axFan buildVarCodeSb (Lift Fst) Pair arg1 b

      r2 : Deriv (atomic (eqn (ap2 buildVarCodeSb arg1 b)
                              (ap2 Pair tagVarT q)))
      r2 = buildVarCodeSbAt p q b

      r3 : Deriv (atomic (eqn (ap2 (Lift Fst) arg1 b) p))
      r3 = ruleTrans (axLift Fst arg1 b) (axFst p q)

      r4 : Deriv (atomic (eqn (ap2 Pair (ap2 buildVarCodeSb arg1 b)
                                        (ap2 (Lift Fst) arg1 b))
                              (ap2 Pair (ap2 Pair tagVarT q)
                                        (ap2 (Lift Fst) arg1 b))))
      r4 = congL Pair (ap2 (Lift Fst) arg1 b) r2

      r5 : Deriv (atomic (eqn (ap2 Pair (ap2 Pair tagVarT q)
                                        (ap2 (Lift Fst) arg1 b))
                              (ap2 Pair (ap2 Pair tagVarT q) p)))
      r5 = congR Pair (ap2 Pair tagVarT q) r3
  in ruleTrans r1 (ruleTrans r4 r5)

------------------------------------------------------------------------
-- Lemma: rightSb on (a, b) reduces to b.

rightSbAt : (a b : Term) ->
  Deriv (atomic (eqn (ap2 rightSb a b) b))
rightSbAt a b = ruleTrans (axPost Snd Pair a b) (axSnd a b)

------------------------------------------------------------------------
-- Main lemma: sb's defining equation.
--
-- Note: the equality
--    ap2 Pair (reify tagVar) (reify (natCode n))
--      = reify (code (var n))
-- holds DEFINITIONALLY:
--   reify (code (var n)) = reify (nd tagVar (natCode n))
--                         = ap2 Pair (reify tagVar) (reify (natCode n))
--                         = ap2 Pair tagVarT (reify (natCode n)) .
-- So we can feed the result of repackageSb directly into subTDef
-- without an explicit coercion lemma.

sbDef : (codeA : Term) -> IsValue codeA -> (n : Nat) ->
        (codeP : Term) -> IsValue codeP ->
  Deriv (atomic (eqn (ap2 sb (ap2 Pair codeA (natCode n)) codeP)
                      (codedSubst codeA (code (var n)) codeP)))
sbDef codeA cA n codeP cP =
  let codeAT : Term
      codeAT = codeA

      nT : Term
      nT = natCode n

      codePT : Term
      codePT = codeP

      arg1 : Term
      arg1 = ap2 Pair codeAT nT

      -- Step 1: sb = Fan repackageSb rightSb subT, axFan unfolds.
      s1 : Deriv (atomic (eqn (ap2 sb arg1 codePT)
                              (ap2 subT (ap2 repackageSb arg1 codePT)
                                        (ap2 rightSb     arg1 codePT))))
      s1 = axFan repackageSb rightSb subT arg1 codePT

      lhsFinal : Term
      lhsFinal = ap2 Pair (ap2 Pair tagVarT nT) codeAT

      lhsR : Deriv (atomic (eqn (ap2 repackageSb arg1 codePT) lhsFinal))
      lhsR = repackageSbAt codeAT nT codePT

      rhsR : Deriv (atomic (eqn (ap2 rightSb arg1 codePT) codePT))
      rhsR = rightSbAt arg1 codePT

      s2 : Deriv (atomic (eqn (ap2 subT (ap2 repackageSb arg1 codePT)
                                        (ap2 rightSb     arg1 codePT))
                              (ap2 subT lhsFinal codePT)))
      s2 = ruleTrans (congL subT (ap2 rightSb arg1 codePT) lhsR)
                     (congR subT lhsFinal rhsR)

      s3 : Deriv (atomic (eqn (ap2 subT lhsFinal codePT)
                              (codedSubst codeA (code (var n)) codeP)))
      s3 = subTDef n codeA cA codeP cP

  in ruleTrans s1 (ruleTrans s2 s3)
