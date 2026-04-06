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
open import Guard.NelsonAxReflGen using (nelsonAxReflGen)
open import Guard.NelsonRuleSym using (nelsonRuleSym)
open import Guard.NelsonRuleTransFull using (nelsonRuleTransFull)
open import Guard.NelsonRuleTransOPair using (nelsonRuleTransOPair)
open import Guard.NelsonCong1 using (nelsonCong1)
open import Guard.NelsonCongL using (nelsonCongL)
open import Guard.NelsonCongR using (nelsonCongR)
open import Guard.NelsonAxI using (nelsonAxI)
open import Guard.NelsonRuleInst using (nelsonRuleInst)
open import Guard.NelsonRuleF using (nelsonRuleF)
open import Guard.NelsonAxKT using (nelsonAxKT)
open import Guard.SubstTFor using (substTFor)
open import Guard.NelsonAxFst using (nelsonAxFst)
open import Guard.NelsonAxSnd using (nelsonAxSnd)
open import Guard.NelsonAxConst using (nelsonAxConst)
open import Guard.EvalCodeMkAp1 using (evalCodeMkAp1)
open import Guard.GodelII using (treeEqSelf)

private
  tag0T  : Term ; tag0T  = reify (natCode n0)
  tag1T  : Term ; tag1T  = reify (natCode n1)
  tag2T  : Term ; tag2T  = reify (natCode n2)
  tag3T  : Term ; tag3T  = reify (natCode n3)
  tag17T : Term ; tag17T = reify (natCode n17)
  tag18T : Term ; tag18T = reify (natCode n18)
  tag19T : Term ; tag19T = reify (natCode n19)
  tag20T : Term ; tag20T = reify (natCode n20)
  tag21T : Term ; tag21T = reify (natCode n21)
  tag22T : Term ; tag22T = reify (natCode n22)
  tag23T : Term ; tag23T = reify (natCode n23)
  tag24T : Term ; tag24T = reify (natCode n24)
  tag25T : Term ; tag25T = reify (natCode n25)
  codeKTTag : Term ; codeKTTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))
  tagVarT : Term ; tagVarT = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero
  codeIF : Term ; codeIF = reify (codeF1 I)
  codeFstF : Term ; codeFstF = reify (codeF1 Fst)
  codeSndF : Term ; codeSndF = reify (codeF1 Snd)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  constCF : Term ; constCF = reify (codeF2 Const)
  var0CodeT : Term ; var0CodeT = reify (nd (nd (nd (nd lf lf) lf) lf) lf)

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

  -- axRefl generalized: Pair(tag17, Pair(x, O)) for any term x
  wcReflGen : (x : Term) -> {hyp : Equation} ->
    WC (ap2 Pair tag17T (ap2 Pair x O)) hyp

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

  -- axI: Pair(tag0, Pair(tC, O)) — tag-0 base case
  -- tC must be Pair-Pair-tagged for evalCode side conditions.
  -- Side conditions: evalCode on mkAp1(codeIF, tC) and evalCode on tC.
  wcAxI : (tC : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 evalCode (ap2 Pair (reify tagAp1) (ap2 Pair codeIF tC)))
                   (ap1 evalCode tC)) ->
    WC (ap2 Pair tag0T (ap2 Pair tC O)) hyp

  -- axFst: Pair(tag1, Pair(aC, bC))
  -- thFunTFor gives Pair(mkAp1(Fst, mkAp2(Pair, aC, bC)), aC)
  -- Side condition: evalCode on the LHS equals evalCode(aC)
  wcAxFst : (aC bC : Term) -> {hyp : Equation} ->
    let lhs = ap2 Pair (reify tagAp1) (ap2 Pair codeFstF
                (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))
    in Deriv hyp (eqn (ap1 evalCode lhs) (ap1 evalCode aC)) ->
       WC (ap2 Pair tag1T (ap2 Pair aC bC)) hyp

  -- axSnd: Pair(tag2, Pair(aC, bC))
  -- thFunTFor gives Pair(mkAp1(Snd, mkAp2(Pair, aC, bC)), bC)
  wcAxSnd : (aC bC : Term) -> {hyp : Equation} ->
    let lhs = ap2 Pair (reify tagAp1) (ap2 Pair codeSndF
                (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))
    in Deriv hyp (eqn (ap1 evalCode lhs) (ap1 evalCode bC)) ->
       WC (ap2 Pair tag2T (ap2 Pair aC bC)) hyp

  -- axConst: Pair(tag3, Pair(aC, bC))
  -- thFunTFor gives Pair(mkAp2(Const, aC, bC), aC)
  wcAxConst : (aC bC : Term) -> {hyp : Equation} ->
    let lhs = ap2 Pair (reify tagAp2) (ap2 Pair constCF (ap2 Pair aC bC))
    in Deriv hyp (eqn (ap1 evalCode lhs) (ap1 evalCode aC)) ->
       WC (ap2 Pair tag3T (ap2 Pair aC bC)) hyp

  -- ruleTrans with O-tagged sp1: Pair(tag19, Pair(sp1, sp2))
  -- sp1 = Pair(O, Pair(Pair(e1,e2), e3)) — O-Pair-tagged (tag-0 sub-proof)
  -- sp2 = Pair(Pair(c1,c2), d1) — PairPair-tagged
  wcTransO : (e1 e2 e3 c1 c2 d1 : Term) -> {hyp : Equation} ->
    let sp1 = ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3)
        sp2 = ap2 Pair (ap2 Pair c1 c2) d1
    in WC sp1 hyp -> WC sp2 hyp ->
       Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor sp1))
                       (ap1 Fst (ap1 thFunTFor sp2))) ->
       WC (ap2 Pair tag19T (ap2 Pair sp1 sp2)) hyp

  -- cong1: Pair(tag20, Pair(fCode, sp)) where fCode is Pair-Pair-tagged
  -- Side conditions:
  --   evalCode misses: TreeEq(fCode, O) and TreeEq(fCode, tagAp1T) both = Pair(O,O)
  wcCong1 : (f1 f2 f3 s1 s2 : Term) -> {hyp : Equation} ->
    let fCode = ap2 Pair (ap2 Pair f1 f2) f3
    in WC (ap2 Pair s1 s2) hyp ->
       Deriv hyp (eqn (ap2 TreeEq fCode O) poo) ->
       Deriv hyp (eqn (ap2 TreeEq fCode tagAp1T) poo) ->
       WC (ap2 Pair tag20T (ap2 Pair fCode (ap2 Pair s1 s2))) hyp

  -- congL: Pair(tag21, Pair(Pair(gCode, xCode), sp))
  -- gCode Pair-Pair-tagged for passthrough. Explicit evalCode condition.
  wcCongL : (g1 g2 g3 xCode s1 s2 : Term) -> {hyp : Equation} ->
    let gCode = ap2 Pair (ap2 Pair g1 g2) g3
        sp = ap2 Pair s1 s2
        fstSp = ap1 Fst (ap1 thFunTFor sp)
        sndSp = ap1 Snd (ap1 thFunTFor sp)
        lhsL = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair fstSp xCode))
        lhsR = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair sndSp xCode))
    in WC sp hyp ->
       Deriv hyp (eqn (ap1 evalCode lhsL) (ap1 evalCode lhsR)) ->
       WC (ap2 Pair tag21T (ap2 Pair (ap2 Pair gCode xCode) sp)) hyp

  -- congR: Pair(tag22, Pair(Pair(gCode, xCode), sp))
  wcCongR : (g1 g2 g3 xCode s1 s2 : Term) -> {hyp : Equation} ->
    let gCode = ap2 Pair (ap2 Pair g1 g2) g3
        sp = ap2 Pair s1 s2
        fstSp = ap1 Fst (ap1 thFunTFor sp)
        sndSp = ap1 Snd (ap1 thFunTFor sp)
        lhsL = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode fstSp))
        lhsR = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode sndSp))
    in WC sp hyp ->
       Deriv hyp (eqn (ap1 evalCode lhsL) (ap1 evalCode lhsR)) ->
       WC (ap2 Pair tag22T (ap2 Pair (ap2 Pair gCode xCode) sp)) hyp

  -- ruleInst: Pair(tag23, Pair(Pair(tC, xC), sp))
  -- tC Pair-Pair-tagged, sp Pair-Pair-tagged.
  -- thFunTFor gives Pair(substTFor(L), substTFor(R)).
  -- Side condition: evalCode(substTFor(L)) = evalCode(substTFor(R)).
  -- This is NOT derivable from IH — substTFor and evalCode don't commute.
  -- Each specific instance must supply the proof.
  wcRuleInst : (t1 t2 t3 xC s1 s2 s3 : Term) -> {hyp : Equation} ->
    let tC = ap2 Pair (ap2 Pair t1 t2) t3
        sp = ap2 Pair (ap2 Pair s1 s2) s3
        fstSp = ap1 Fst (ap1 thFunTFor sp)
        sndSp = ap1 Snd (ap1 thFunTFor sp)
    in WC sp hyp ->
       Deriv hyp (eqn (ap1 evalCode (ap1 substTFor fstSp))
                       (ap1 evalCode (ap1 substTFor sndSp))) ->
       WC (ap2 Pair tag23T (ap2 Pair (ap2 Pair tC xC) sp)) hyp

  -- ruleF: Pair(tag24, Pair(Pair(fC, gC), dataT))
  -- thFunTFor gives Pair(mkAp1(fC, var0Code), mkAp1(gC, var0Code)).
  -- evalCode strips both mkAp1, so both sides = evalCode(var0Code).
  -- Side condition: evalCode equalities (like cong1).
  wcRuleF : (fC gC dataT : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 evalCode (ap2 Pair (reify tagAp1) (ap2 Pair fC var0CodeT)))
                   (ap1 evalCode var0CodeT)) ->
    Deriv hyp (eqn (ap1 evalCode (ap2 Pair (reify tagAp1) (ap2 Pair gC var0CodeT)))
                   (ap1 evalCode var0CodeT)) ->
    WC (ap2 Pair tag24T (ap2 Pair (ap2 Pair fC gC) dataT)) hyp

  -- axKT: Pair(tag25, Pair(tC, xC))
  -- thFunTFor gives Pair(mkAp1(Pair(codeKTTag, tC), xC), tC).
  -- Side condition: evalCode on mkAp1 LHS = evalCode(tC).
  wcAxKT : (tC xC : Term) -> {hyp : Equation} ->
    let ktCode = ap2 Pair codeKTTag tC
    in Deriv hyp (eqn (ap1 evalCode (ap2 Pair (reify tagAp1) (ap2 Pair ktCode xC)))
                      (ap1 evalCode tC)) ->
       WC (ap2 Pair tag25T (ap2 Pair tC xC)) hyp

  -- Generic base case: any encoding with a Nelson proof and evalCode side condition.
  -- Covers all remaining base cases (tags 4-16) without separate constructors.
  -- The caller supplies:
  --   (1) Nelson proof: thFunTFor(enc) = Pair(lhs, rhs)
  --   (2) evalCode side condition: evalCode(lhs) = evalCode(rhs)
  wcBase : (enc lhs rhs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 thFunTFor enc) (ap2 Pair lhs rhs)) ->
    Deriv hyp (eqn (ap1 evalCode lhs) (ap1 evalCode rhs)) ->
    WC enc hyp

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

-- Case axRefl generalized: thFunTFor gives Pair(x, x).
semSound .(ap2 Pair tag17T (ap2 Pair x O)) (wcReflGen x) =
  let nar = nelsonAxReflGen x
      fstR = ruleTrans (cong1 Fst nar) (axFst x x)
      sndR = ruleTrans (cong1 Snd nar) (axSnd x x)
  in ruleTrans (cong1 evalCode fstR) (ruleSym (cong1 evalCode sndR))

-- Case axI: thFunTFor gives Pair(mkAp1(codeIF, tC), tC).
-- Side condition: evalCode(mkAp1(codeIF, tC)) = evalCode(tC)
-- Then evalCode(Fst) = evalCode(mkAp1(codeIF,tC)) = evalCode(tC) = evalCode(Snd)
semSound .(ap2 Pair tag0T (ap2 Pair tC O)) (wcAxI tC ecReduce) =
  let enc = ap2 Pair tag0T (ap2 Pair tC O)
      nai = nelsonAxI tC
      mkAp1Term = ap2 Pair (reify tagAp1) (ap2 Pair codeIF tC)
      fstEnc = ruleTrans (cong1 Fst nai) (axFst mkAp1Term tC)
      sndEnc = ruleTrans (cong1 Snd nai) (axSnd mkAp1Term tC)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecReduce
                (ruleSym (cong1 evalCode sndEnc)))

-- Case axFst: thFunTFor gives Pair(mkAp1(Fst, mkAp2(Pair, aC, bC)), aC).
semSound .(ap2 Pair tag1T (ap2 Pair aC bC)) (wcAxFst aC bC ecReduce) =
  let naf = nelsonAxFst aC bC
      lhs = ap2 Pair (reify tagAp1) (ap2 Pair codeFstF
              (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))
      fstEnc = ruleTrans (cong1 Fst naf) (axFst lhs aC)
      sndEnc = ruleTrans (cong1 Snd naf) (axSnd lhs aC)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecReduce
                (ruleSym (cong1 evalCode sndEnc)))

-- Case axSnd: thFunTFor gives Pair(mkAp1(Snd, mkAp2(Pair, aC, bC)), bC).
semSound .(ap2 Pair tag2T (ap2 Pair aC bC)) (wcAxSnd aC bC ecReduce) =
  let nas = nelsonAxSnd aC bC
      lhs = ap2 Pair (reify tagAp1) (ap2 Pair codeSndF
              (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))
      fstEnc = ruleTrans (cong1 Fst nas) (axFst lhs bC)
      sndEnc = ruleTrans (cong1 Snd nas) (axSnd lhs bC)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecReduce
                (ruleSym (cong1 evalCode sndEnc)))

-- Case axConst: thFunTFor gives Pair(mkAp2(Const, aC, bC), aC).
semSound .(ap2 Pair tag3T (ap2 Pair aC bC)) (wcAxConst aC bC ecReduce) =
  let nac = nelsonAxConst aC bC
      lhs = ap2 Pair (reify tagAp2) (ap2 Pair constCF (ap2 Pair aC bC))
      fstEnc = ruleTrans (cong1 Fst nac) (axFst lhs aC)
      sndEnc = ruleTrans (cong1 Snd nac) (axSnd lhs aC)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecReduce
                (ruleSym (cong1 evalCode sndEnc)))

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

-- Case ruleTransO: same as wcTrans but sp1 is O-Pair-tagged.
-- Uses nelsonRuleTransOPair instead of nelsonRuleTransFull.
semSound .(ap2 Pair tag19T (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3))
                                      (ap2 Pair (ap2 Pair c1 c2) d1)))
         (wcTransO e1 e2 e3 c1 c2 d1 wc1 wc2 match) =
  let sp1 = ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3)
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      ih1 = semSound sp1 wc1
      ih2 = semSound sp2 wc2
      nrt = nelsonRuleTransOPair e1 e2 e3 c1 c2 d1
      fstSp1 = ap1 Fst (ap1 thFunTFor sp1)
      sndSp2 = ap1 Snd (ap1 thFunTFor sp2)
      fstEnc = ruleTrans (cong1 Fst nrt) (axFst fstSp1 sndSp2)
      sndEnc = ruleTrans (cong1 Snd nrt) (axSnd fstSp1 sndSp2)
      bridge = cong1 evalCode match
      chain = ruleTrans ih1 (ruleTrans bridge ih2)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans chain
                (ruleSym (cong1 evalCode sndEnc)))

-- Case cong1: thFunTFor gives Pair(mkAp1(fCode, L), mkAp1(fCode, R)).
-- IH: evalCode(L) = evalCode(R) where L=Fst(thFunTFor(sp)), R=Snd(thFunTFor(sp))
-- evalCodeMkAp1: evalCode(mkAp1(fCode, X)) = evalCode(X) for suitable fCode
-- Chain: evalCode(mkAp1(fCode, L)) = evalCode(L) = evalCode(R) = evalCode(mkAp1(fCode, R))
semSound .(ap2 Pair tag20T (ap2 Pair (ap2 Pair (ap2 Pair f1 f2) f3) (ap2 Pair s1 s2)))
         (wcCong1 f1 f2 f3 s1 s2 wc fCodeMissO fCodeMissAp1) =
  let fCode = ap2 Pair (ap2 Pair f1 f2) f3
      sp = ap2 Pair s1 s2
      enc = ap2 Pair tag20T (ap2 Pair fCode sp)
      ih = semSound sp wc
      nc1 = nelsonCong1 f1 f2 f3 s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      mkAp1L = ap2 Pair (reify tagAp1) (ap2 Pair fCode fstSp)
      mkAp1R = ap2 Pair (reify tagAp1) (ap2 Pair fCode sndSp)
      -- Fst(thFunTFor(enc)) = mkAp1(fCode, L)
      fstEnc = ruleTrans (cong1 Fst nc1) (axFst mkAp1L mkAp1R)
      -- Snd(thFunTFor(enc)) = mkAp1(fCode, R)
      sndEnc = ruleTrans (cong1 Snd nc1) (axSnd mkAp1L mkAp1R)
      -- evalCode(mkAp1(fCode, L)) = evalCode(L)
      ecL = evalCodeMkAp1 fCode fstSp fCodeMissO fCodeMissAp1
      -- evalCode(mkAp1(fCode, R)) = evalCode(R)
      ecR = evalCodeMkAp1 fCode sndSp fCodeMissO fCodeMissAp1
      -- Chain: evalCode(Fst) = evalCode(mkAp1(fCode,L)) = evalCode(L) = evalCode(R) = evalCode(mkAp1(fCode,R)) = evalCode(Snd)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecL
     (ruleTrans ih
     (ruleTrans (ruleSym ecR)
                (ruleSym (cong1 evalCode sndEnc)))))

-- Case congL: thFunTFor gives Pair(mkAp2(g, L, x), mkAp2(g, R, x)).
-- Side condition provides evalCode(mkAp2(g,L,x)) = evalCode(mkAp2(g,R,x)).
semSound .(ap2 Pair tag21T (ap2 Pair (ap2 Pair (ap2 Pair (ap2 Pair g1 g2) g3) xCode) (ap2 Pair s1 s2)))
         (wcCongL g1 g2 g3 xCode s1 s2 wc ecSide) =
  let gCode = ap2 Pair (ap2 Pair g1 g2) g3
      sp = ap2 Pair s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      ncl = nelsonCongL g1 g2 g3 xCode s1 s2
      lhsL = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair fstSp xCode))
      lhsR = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair sndSp xCode))
      fstEnc = ruleTrans (cong1 Fst ncl) (axFst lhsL lhsR)
      sndEnc = ruleTrans (cong1 Snd ncl) (axSnd lhsL lhsR)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecSide
                (ruleSym (cong1 evalCode sndEnc)))

-- Case congR: thFunTFor gives Pair(mkAp2(g, x, L), mkAp2(g, x, R)).
semSound .(ap2 Pair tag22T (ap2 Pair (ap2 Pair (ap2 Pair (ap2 Pair g1 g2) g3) xCode) (ap2 Pair s1 s2)))
         (wcCongR g1 g2 g3 xCode s1 s2 wc ecSide) =
  let gCode = ap2 Pair (ap2 Pair g1 g2) g3
      sp = ap2 Pair s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      ncr = nelsonCongR g1 g2 g3 xCode s1 s2
      lhsL = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode fstSp))
      lhsR = ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode sndSp))
      fstEnc = ruleTrans (cong1 Fst ncr) (axFst lhsL lhsR)
      sndEnc = ruleTrans (cong1 Snd ncr) (axSnd lhsL lhsR)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecSide
                (ruleSym (cong1 evalCode sndEnc)))

-- Case ruleInst: thFunTFor gives Pair(substTFor(L), substTFor(R)).
-- Side condition provides the evalCode equality directly.
semSound .(ap2 Pair tag23T (ap2 Pair (ap2 Pair (ap2 Pair (ap2 Pair t1 t2) t3) xC)
                                      (ap2 Pair (ap2 Pair s1 s2) s3)))
         (wcRuleInst t1 t2 t3 xC s1 s2 s3 wc ecSide) =
  let sp = ap2 Pair (ap2 Pair s1 s2) s3
      nri = nelsonRuleInst t1 t2 t3 xC s1 s2 s3
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      stfL = ap1 substTFor fstSp
      stfR = ap1 substTFor sndSp
      fstEnc = ruleTrans (cong1 Fst nri) (axFst stfL stfR)
      sndEnc = ruleTrans (cong1 Snd nri) (axSnd stfL stfR)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecSide
                (ruleSym (cong1 evalCode sndEnc)))

-- Case ruleF: thFunTFor gives Pair(mkAp1(fC, var0Code), mkAp1(gC, var0Code)).
-- Both sides strip to evalCode(var0Code) via evalCode conditions.
semSound .(ap2 Pair tag24T (ap2 Pair (ap2 Pair fC gC) dataT))
         (wcRuleF fC gC dataT ecF ecG) =
  let nrf = nelsonRuleF fC gC dataT
      mkL = ap2 Pair (reify tagAp1) (ap2 Pair fC var0CodeT)
      mkR = ap2 Pair (reify tagAp1) (ap2 Pair gC var0CodeT)
      fstEnc = ruleTrans (cong1 Fst nrf) (axFst mkL mkR)
      sndEnc = ruleTrans (cong1 Snd nrf) (axSnd mkL mkR)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecF
     (ruleTrans (ruleSym ecG)
                (ruleSym (cong1 evalCode sndEnc))))

-- Case axKT: thFunTFor gives Pair(mkAp1(codeKT(tC), xC), tC).
semSound .(ap2 Pair tag25T (ap2 Pair tC xC)) (wcAxKT tC xC ecReduce) =
  let nkt = nelsonAxKT tC xC
      ktCode = ap2 Pair codeKTTag tC
      mkApTerm = ap2 Pair (reify tagAp1) (ap2 Pair ktCode xC)
      fstEnc = ruleTrans (cong1 Fst nkt) (axFst mkApTerm tC)
      sndEnc = ruleTrans (cong1 Snd nkt) (axSnd mkApTerm tC)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecReduce
                (ruleSym (cong1 evalCode sndEnc)))

-- Generic base case: uses supplied Nelson proof and evalCode condition.
semSound enc (wcBase .enc lhs rhs nelson ecSide) =
  let fstEnc = ruleTrans (cong1 Fst nelson) (axFst lhs rhs)
      sndEnc = ruleTrans (cong1 Snd nelson) (axSnd lhs rhs)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecSide
                (ruleSym (cong1 evalCode sndEnc)))
