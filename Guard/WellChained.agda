{-# OPTIONS --safe --without-K --exact-split #-}

-- WellChained.agda
-- The well-chained fragment: proof encodings built from axRefl,
-- ruleSym, ruleTrans, with explicit matching side conditions.
--
-- This packages the local validity conditions into a single
-- inductive predicate, and proves semantic soundness by induction.
--
-- Key result: semantic truth composes cleanly through the structural
-- rules for any well-chained proof encoding.
--
-- The well-chained fragment is CLOSED under these rules because:
-- (1) All encodings with tags >= 1 are Pair-Pair-tagged
-- (2) The inner passthrough works via ndDispatchPairMiss
-- (3) The only side condition (middle term match for ruleTrans)
--     is carried explicitly in the WC type

module Guard.WellChained where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.EvalCode
open import Guard.NelsonDispatch
open import Guard.NelsonAxRefl using (nelsonAxRefl)
open import Guard.NelsonRuleSym using (nelsonRuleSym)
open import Guard.NelsonRuleTransFull using (nelsonRuleTransFull)
open import Guard.GodelII using (treeEqSelf)

private
  tag17T : Term ; tag17T = reify (natCode n17)
  tag18T : Term ; tag18T = reify (natCode n18)
  tag19T : Term ; tag19T = reify (natCode n19)
  tagVarT : Term ; tagVarT = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O
  v0 : Term ; v0 = var zero

------------------------------------------------------------------------
-- Semantic truth predicate (equational form)

SemTrue : Term -> Equation -> Set
SemTrue p hyp = Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor p)))
                                (ap1 evalCode (ap1 Snd (ap1 thFunTFor p))))

------------------------------------------------------------------------
-- Well-chained proof encodings.
--
-- WC p hyp means p is a well-chained encoding and all matching
-- conditions are satisfied.
--
-- All encodings here use var 0 as the free variable, so the
-- results hold universally (by implicit quantification).

data WC : Term -> Equation -> Set where
  -- axRefl: Pair(tag17, Pair(v0, O))
  wcRefl : {hyp : Equation} ->
    WC (ap2 Pair tag17T (ap2 Pair v0 O)) hyp

  -- ruleSym: Pair(tag18, Pair(tagVar, sp)) where sp is well-chained
  wcSym : (s1 s2 : Term) -> {hyp : Equation} ->
    WC (ap2 Pair s1 s2) hyp ->
    WC (ap2 Pair tag18T (ap2 Pair tagVarT (ap2 Pair s1 s2))) hyp

  -- ruleTrans: Pair(tag19, Pair(sp1, sp2)) with matching condition
  wcTrans : (a1 a2 b1 c1 c2 d1 : Term) -> {hyp : Equation} ->
    WC (ap2 Pair (ap2 Pair a1 a2) b1) hyp ->
    WC (ap2 Pair (ap2 Pair c1 c2) d1) hyp ->
    Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor (ap2 Pair (ap2 Pair a1 a2) b1)))
                    (ap1 Fst (ap1 thFunTFor (ap2 Pair (ap2 Pair c1 c2) d1)))) ->
    WC (ap2 Pair tag19T (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b1)
                                   (ap2 Pair (ap2 Pair c1 c2) d1))) hyp

------------------------------------------------------------------------
-- Semantic soundness for the well-chained fragment.
--
-- For any well-chained p: evalCode(Fst(thFunTFor(p))) = evalCode(Snd(thFunTFor(p)))

semSound : (p : Term) -> {hyp : Equation} -> WC p hyp -> SemTrue p hyp

-- Case axRefl: thFunTFor gives Pair(v0, v0), so Fst = Snd = v0.
semSound .(ap2 Pair tag17T (ap2 Pair v0 O)) wcRefl =
  let enc = ap2 Pair tag17T (ap2 Pair v0 O)
      nar = nelsonAxRefl
      fstR = ruleTrans (cong1 Fst nar) (axFst v0 v0)
      sndR = ruleTrans (cong1 Snd nar) (axSnd v0 v0)
  in ruleTrans (cong1 evalCode fstR) (ruleSym (cong1 evalCode sndR))

-- Case ruleSym: thFunTFor gives Pair(Snd(thFunTFor(sp)), Fst(thFunTFor(sp))).
-- IH gives evalCode(Fst(thFunTFor(sp))) = evalCode(Snd(thFunTFor(sp))).
-- Swap gives evalCode(Snd(thFunTFor(sp))) = evalCode(Fst(thFunTFor(sp))).
semSound .(ap2 Pair tag18T (ap2 Pair tagVarT (ap2 Pair s1 s2)))
         (wcSym s1 s2 wc) =
  let sp = ap2 Pair s1 s2
      enc = ap2 Pair tag18T (ap2 Pair tagVarT sp)
      ih = semSound sp wc
      nrs = nelsonRuleSym s1 s2
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      fstEnc = ruleTrans (cong1 Fst nrs) (axFst sndSp fstSp)
      sndEnc = ruleTrans (cong1 Snd nrs) (axSnd sndSp fstSp)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans (ruleSym ih)
                (ruleSym (cong1 evalCode sndEnc)))

-- Case ruleTrans: thFunTFor gives Pair(Fst(thFunTFor(sp1)), Snd(thFunTFor(sp2))).
-- IH1: evalCode(Fst(thFunTFor(sp1))) = evalCode(Snd(thFunTFor(sp1)))
-- IH2: evalCode(Fst(thFunTFor(sp2))) = evalCode(Snd(thFunTFor(sp2)))
-- match: Snd(thFunTFor(sp1)) = Fst(thFunTFor(sp2))
-- Chain: evalCode(Fst) = evalCode(Snd) via IH1 + match + IH2.
semSound .(ap2 Pair tag19T (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b1)
                                      (ap2 Pair (ap2 Pair c1 c2) d1)))
         (wcTrans a1 a2 b1 c1 c2 d1 wc1 wc2 match) =
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      enc = ap2 Pair tag19T (ap2 Pair sp1 sp2)
      ih1 = semSound sp1 wc1
      ih2 = semSound sp2 wc2
      nrt = nelsonRuleTransFull a1 a2 b1 c1 c2 d1
      fstSp1 = ap1 Fst (ap1 thFunTFor sp1)
      sndSp2 = ap1 Snd (ap1 thFunTFor sp2)
      fstEnc = ruleTrans (cong1 Fst nrt) (axFst fstSp1 sndSp2)
      sndEnc = ruleTrans (cong1 Snd nrt) (axSnd fstSp1 sndSp2)
      bridge = cong1 evalCode match
      chain = ruleTrans ih1 (ruleTrans bridge ih2)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans chain
                (ruleSym (cong1 evalCode sndEnc)))
