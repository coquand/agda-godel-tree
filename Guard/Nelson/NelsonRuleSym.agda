{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson unary case: ruleSym (tag 18).
-- Encoding: encSym sp = nd(natCode 18)(nd tagVar sp)
-- = Pair(tag18T, Pair(tagVarT, sp))
-- where tagVarT = Pair(Pair(Pair(O,O),O),O) — Pair-Pair-tagged.
--
-- case18 = mkEqF recsBR recsBL
-- Result: Pair(Snd(thFunTFor(sp)), Fst(thFunTFor(sp)))
-- i.e., the L-R swap.
--
-- The inner passthrough works because tagVarT = Pair(Pair(Pair(O,O),O),O)
-- is Pair-Pair-tagged: ndDispatchPairMiss applies.

module Guard.Nelson.NelsonRuleSym where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag18T : Term ; tag18T = reify (natCode n18)
  -- tagVarT = reify(tagVar) = Pair(Pair(Pair(O,O),O),O)
  tagVarT : Term ; tagVarT = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O

  -- Pair-Pair decomposition of tagVarT:
  -- tagVarT = Pair(Pair(Pair(O,O), O), O)
  --         = Pair(Pair(a1, a2), b) where a1=Pair(O,O), a2=O, b=O
  ppA1 : Term ; ppA1 = ap2 Pair O O
  ppA2 : Term ; ppA2 = O
  ppB  : Term ; ppB  = O

nelsonRuleSym :
  (s1 s2 : Term) -> {hyp : Equation} ->
  let sp = ap2 Pair s1 s2
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag18T (ap2 Pair tagVarT sp)))
                    (ap2 Pair (ap1 Snd (ap1 thFunTFor sp))
                              (ap1 Fst (ap1 thFunTFor sp))))
nelsonRuleSym s1 s2 =
  let sp = ap2 Pair s1 s2
      origT = ap2 Pair tag18T (ap2 Pair tagVarT sp)
      recsT = ap2 Pair (ap1 thFunTFor tag18T) (ap1 thFunTFor (ap2 Pair tagVarT sp))

      -- Phase 1+2: thFunTFor(origT) = case18(origT, recsT)
      step12 = ruleTrans (phase1Nd tag18T tagVarT sp)
                         (ndDispatchToCase18 (ap2 Pair tagVarT sp) recsT)

      -- Phase 3+4: case18 extractors via passthrough
      -- recsBR(origT, recsT) = Snd(thFunTFor(sp))
      rbR = recsBRWithPassthrough tag18T ppA1 ppA2 ppB s1 s2
      -- recsBL(origT, recsT) = Fst(thFunTFor(sp))
      rbL = recsBLWithPassthrough tag18T ppA1 ppA2 ppB s1 s2

      -- case18 = mkEqF recsBR recsBL = Fan recsBR recsBL Pair
      step4 = mkEqFRed recsBR recsBL origT recsT
                (ap1 Snd (ap1 thFunTFor sp))
                (ap1 Fst (ap1 thFunTFor sp))
                rbR rbL
  in
  ruleTrans step12 step4
