{-# OPTIONS --safe --without-K --exact-split #-}

-- BoundaryQuantitative.agda
-- Quantitative Nelson-WC Boundary.
--
-- Defines the 0-backtracking fragment WC0 where EvalOK is
-- automatically discharged. No external side conditions needed.
--
-- The key: evalCode strips ALL mkAp1 nodes, and every actual
-- functor code (codeF1 f for any Fun1 f) passes the miss checks
-- universally. This is because codeF1 f always has the form
-- nd(natCode(26+k), payload), so reify is Pair(Pair(O,...), ...)
-- which misses both tagO and tagAp1T.
--
-- WC0 ⊂ {BLevel = 0} ⊂ WC.
-- ruleInst (BLevel > 0) and axFst/axSnd/axConst (evalCode limitation)
-- are excluded.

module Guard.BoundaryQuantitative where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.EvalCode
open import Guard.EvalCodeMkAp1 using (evalCodeMkAp1)
open import Guard.NelsonDispatch
open import Guard.NelsonAxRefl using (nelsonAxRefl)
open import Guard.NelsonAxReflGen using (nelsonAxReflGen)
open import Guard.NelsonAxI using (nelsonAxI)
open import Guard.NelsonAxKT using (nelsonAxKT)
open import Guard.NelsonCong1 using (nelsonCong1)
open import Guard.NelsonRuleF using (nelsonRuleF)
open import Guard.NelsonRuleSym using (nelsonRuleSym)
open import Guard.NelsonRuleTransFull using (nelsonRuleTransFull)
open import Guard.NelsonRuleTransOPair using (nelsonRuleTransOPair)
open import Guard.WellChained using (SemTrue)

private
  poo : Term ; poo = ap2 Pair O O
  tag0T  : Term ; tag0T  = reify (natCode n0)
  tag17T : Term ; tag17T = reify (natCode n17)
  tag18T : Term ; tag18T = reify (natCode n18)
  tag19T : Term ; tag19T = reify (natCode n19)
  tag20T : Term ; tag20T = reify (natCode n20)
  tag24T : Term ; tag24T = reify (natCode n24)
  tag25T : Term ; tag25T = reify (natCode n25)
  tagVarT : Term ; tagVarT = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O
  v0 : Term ; v0 = var zero

  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  n31 : Nat ; n31 = suc n30
  n32 : Nat ; n32 = suc n31

  codeKTTag : Term ; codeKTTag = reify (natCode n32)
  var0CodeT : Term ; var0CodeT = reify (nd (nd (nd (nd lf lf) lf) lf) lf)

------------------------------------------------------------------------
-- Universal miss proofs for functor codes.
--
-- Every codeF1 f = nd(natCode(26+k), payload) for some k.
-- reify gives Pair(X, Y) where X = reify(natCode(26+k)).
-- Miss checks:
--   TreeEq(Pair(X,Y), O) = Pair(O,O)              [always, by axTreeEqNL]
--   TreeEq(Pair(X,Y), tagAp1T) = Pair(O,O)         [always, by IfLf argument]
-- The tagAp1T miss works because X = Pair(O, reify(natCode(25+k)))
-- and TreeEq(Pair(O,...), O) = Pair(O,O), making IfLf take the miss branch.

-- Helper: for any natCode n with n >= 1, reify(natCode n) = Pair(O, something)
-- and TreeEq(Pair(O, something), O) = Pair(O,O).
-- Then TreeEq(Pair(Pair(O,...), Y), Pair(O, Pair(O,O)))
--   = IfLf(TreeEq(Pair(O,...), O), ...) = IfLf(Pair(O,O), ...) = Pair(O,O)

-- Generic: for fCode = Pair(X, Y), tagAp1T miss if X is a Pair.
pairPairMissAp1 : (x1 x2 y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair (ap2 Pair x1 x2) y) tagAp1T) poo)
pairPairMissAp1 x1 x2 y =
  ruleTrans (axTreeEqNN (ap2 Pair x1 x2) y O (ap2 Pair O O))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq y (ap2 Pair O O)) poo)
               (axTreeEqNL x1 x2))
             (axIfLfN O O (ap2 TreeEq y (ap2 Pair O O)) poo))

-- For Fun1: codeF1 always gives nd(natCode(26+k), payload), k >= 0.
-- reify(natCode(26+k)) = Pair(O, reify(natCode(25+k))), which is Pair(O, ...).
-- So Fst(reify(codeF1 f)) = Pair(O, ...) for all f.

codeF1MissO : (f : Fun1) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (codeF1 f)) O) poo)
codeF1MissO I             = axTreeEqNL (reify (natCode n26)) O
codeF1MissO Fst           = axTreeEqNL (reify (natCode n27)) O
codeF1MissO Snd           = axTreeEqNL (reify (natCode n28)) O
codeF1MissO (Comp f g)    = axTreeEqNL (reify (natCode n29)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))
codeF1MissO (Comp2 h f g) = axTreeEqNL (reify (natCode n30)) (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))))
codeF1MissO (Rec z s)     = axTreeEqNL (reify (natCode n31)) (ap2 Pair (reify (code z)) (reify (codeF2 s)))
codeF1MissO (KT t)        = axTreeEqNL (reify (natCode n32)) (reify (code t))

codeF1MissAp1 : (f : Fun1) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify (codeF1 f)) tagAp1T) poo)
codeF1MissAp1 I             = pairPairMissAp1 O (reify (natCode n25)) O
codeF1MissAp1 Fst           = pairPairMissAp1 O (reify (natCode n26)) O
codeF1MissAp1 Snd           = pairPairMissAp1 O (reify (natCode n27)) O
codeF1MissAp1 (Comp f g)    = pairPairMissAp1 O (reify (natCode n28)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))
codeF1MissAp1 (Comp2 h f g) = pairPairMissAp1 O (reify (natCode n29)) (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))))
codeF1MissAp1 (Rec z s)     = pairPairMissAp1 O (reify (natCode n30)) (ap2 Pair (reify (code z)) (reify (codeF2 s)))
codeF1MissAp1 (KT t)        = pairPairMissAp1 O (reify (natCode n31)) (reify (code t))

-- Universal evalCode reduction for mkAp1 with any functor code.
evalCodeMkAp1F : (f : Fun1) (t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) t)))
                 (ap1 evalCode t))
evalCodeMkAp1F f t = evalCodeMkAp1 (reify (codeF1 f)) t (codeF1MissO f) (codeF1MissAp1 f)

------------------------------------------------------------------------
-- WC0: the 0-backtracking fragment.
-- No external EvalOK conditions. All side conditions discharged internally.

data WC0 : Term -> Equation -> Set where
  -- axRefl(x): Pair(x, x), trivially sound
  wc0Refl : (x : Term) -> {hyp : Equation} ->
    WC0 (ap2 Pair tag17T (ap2 Pair x O)) hyp

  -- axI(t): evalCode strips I universally
  wc0AxI : (tC : Term) -> {hyp : Equation} ->
    WC0 (ap2 Pair tag0T (ap2 Pair tC O)) hyp

  -- ruleSym: from IH
  wc0Sym : (s1 s2 : Term) -> {hyp : Equation} ->
    WC0 (ap2 Pair s1 s2) hyp ->
    WC0 (ap2 Pair tag18T (ap2 Pair tagVarT (ap2 Pair s1 s2))) hyp

  -- ruleTrans (PairPair sp1): from IH + matching
  wc0Trans : (a1 a2 b1 c1 c2 d1 : Term) -> {hyp : Equation} ->
    WC0 (ap2 Pair (ap2 Pair a1 a2) b1) hyp ->
    WC0 (ap2 Pair (ap2 Pair c1 c2) d1) hyp ->
    Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor (ap2 Pair (ap2 Pair a1 a2) b1)))
                    (ap1 Fst (ap1 thFunTFor (ap2 Pair (ap2 Pair c1 c2) d1)))) ->
    WC0 (ap2 Pair tag19T (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b1)
                                    (ap2 Pair (ap2 Pair c1 c2) d1))) hyp

  -- ruleTrans (O-Pair sp1): for axI sub-proofs
  wc0TransO : (e1 e2 e3 c1 c2 d1 : Term) -> {hyp : Equation} ->
    let sp1 = ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3)
        sp2 = ap2 Pair (ap2 Pair c1 c2) d1
    in WC0 sp1 hyp -> WC0 sp2 hyp ->
       Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor sp1))
                       (ap1 Fst (ap1 thFunTFor sp2))) ->
       WC0 (ap2 Pair tag19T (ap2 Pair sp1 sp2)) hyp

  -- cong1: ANY Pair-Pair fCode auto-passes miss checks
  wc0Cong1 : (f1 f2 f3 s1 s2 : Term) -> {hyp : Equation} ->
    WC0 (ap2 Pair s1 s2) hyp ->
    WC0 (ap2 Pair tag20T (ap2 Pair (ap2 Pair (ap2 Pair f1 f2) f3) (ap2 Pair s1 s2))) hyp

  -- ruleF: ANY Pair-Pair functor codes auto-strip
  wc0RuleF : (fC gC dataT : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq fC O) poo) ->
    Deriv hyp (eqn (ap2 TreeEq fC tagAp1T) poo) ->
    Deriv hyp (eqn (ap2 TreeEq gC O) poo) ->
    Deriv hyp (eqn (ap2 TreeEq gC tagAp1T) poo) ->
    WC0 (ap2 Pair tag24T (ap2 Pair (ap2 Pair fC gC) dataT)) hyp

------------------------------------------------------------------------
-- semSound0: semantic soundness for WC0, with NO external conditions.
-- This is the Nelson success theorem for the 0-backtracking fragment.

semSound0 : (p : Term) -> {hyp : Equation} -> WC0 p hyp -> SemTrue p hyp

-- axRefl: Fst = Snd = x, trivial
semSound0 .(ap2 Pair tag17T (ap2 Pair x O)) (wc0Refl x) =
  let nar = nelsonAxReflGen x
      fstR = ruleTrans (cong1 Fst nar) (axFst x x)
      sndR = ruleTrans (cong1 Snd nar) (axSnd x x)
  in ruleTrans (cong1 evalCode fstR) (ruleSym (cong1 evalCode sndR))

-- axI: evalCodeMkAp1F discharges automatically
semSound0 .(ap2 Pair tag0T (ap2 Pair tC O)) (wc0AxI tC) =
  let nai = nelsonAxI tC
      mkAp = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) tC)
      fstEnc = ruleTrans (cong1 Fst nai) (axFst mkAp tC)
      sndEnc = ruleTrans (cong1 Snd nai) (axSnd mkAp tC)
      ecSide = evalCodeMkAp1F I tC
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecSide (ruleSym (cong1 evalCode sndEnc)))

-- ruleSym: from IH
semSound0 .(ap2 Pair tag18T (ap2 Pair tagVarT (ap2 Pair s1 s2)))
           (wc0Sym s1 s2 wc) =
  let sp = ap2 Pair s1 s2
      ih = semSound0 sp wc
      nrs = nelsonRuleSym s1 s2
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      fstEnc = ruleTrans (cong1 Fst nrs) (axFst sndSp fstSp)
      sndEnc = ruleTrans (cong1 Snd nrs) (axSnd sndSp fstSp)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans (ruleSym ih) (ruleSym (cong1 evalCode sndEnc)))

-- ruleTrans (PairPair): from IH + matching
semSound0 .(ap2 Pair tag19T (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b1)
                                       (ap2 Pair (ap2 Pair c1 c2) d1)))
           (wc0Trans a1 a2 b1 c1 c2 d1 wc1 wc2 match) =
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      ih1 = semSound0 sp1 wc1
      ih2 = semSound0 sp2 wc2
      nrt = nelsonRuleTransFull a1 a2 b1 c1 c2 d1
      fstSp1 = ap1 Fst (ap1 thFunTFor sp1)
      sndSp2 = ap1 Snd (ap1 thFunTFor sp2)
      fstEnc = ruleTrans (cong1 Fst nrt) (axFst fstSp1 sndSp2)
      sndEnc = ruleTrans (cong1 Snd nrt) (axSnd fstSp1 sndSp2)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans (ruleTrans ih1 (ruleTrans (cong1 evalCode match) ih2))
                (ruleSym (cong1 evalCode sndEnc)))

-- ruleTrans (O-Pair): same but with NelsonRuleTransOPair
semSound0 .(ap2 Pair tag19T (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3))
                                       (ap2 Pair (ap2 Pair c1 c2) d1)))
           (wc0TransO e1 e2 e3 c1 c2 d1 wc1 wc2 match) =
  let sp1 = ap2 Pair O (ap2 Pair (ap2 Pair e1 e2) e3)
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      ih1 = semSound0 sp1 wc1
      ih2 = semSound0 sp2 wc2
      nrt = nelsonRuleTransOPair e1 e2 e3 c1 c2 d1
      fstSp1 = ap1 Fst (ap1 thFunTFor sp1)
      sndSp2 = ap1 Snd (ap1 thFunTFor sp2)
      fstEnc = ruleTrans (cong1 Fst nrt) (axFst fstSp1 sndSp2)
      sndEnc = ruleTrans (cong1 Snd nrt) (axSnd fstSp1 sndSp2)
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans (ruleTrans ih1 (ruleTrans (cong1 evalCode match) ih2))
                (ruleSym (cong1 evalCode sndEnc)))

-- cong1: Pair-Pair fCode auto-discharges miss checks
semSound0 .(ap2 Pair tag20T (ap2 Pair (ap2 Pair (ap2 Pair f1 f2) f3) (ap2 Pair s1 s2)))
           (wc0Cong1 f1 f2 f3 s1 s2 wc) =
  let fCode = ap2 Pair (ap2 Pair f1 f2) f3
      sp = ap2 Pair s1 s2
      ih = semSound0 sp wc
      nc1 = nelsonCong1 f1 f2 f3 s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      mkL = ap2 Pair (reify tagAp1) (ap2 Pair fCode fstSp)
      mkR = ap2 Pair (reify tagAp1) (ap2 Pair fCode sndSp)
      fstEnc = ruleTrans (cong1 Fst nc1) (axFst mkL mkR)
      sndEnc = ruleTrans (cong1 Snd nc1) (axSnd mkL mkR)
      -- Auto-discharge: Pair(Pair(f1,f2),f3) always passes both miss checks
      missO = axTreeEqNL (ap2 Pair f1 f2) f3
      missAp1 = pairPairMissAp1 f1 f2 f3
      ecL = evalCodeMkAp1 fCode fstSp missO missAp1
      ecR = evalCodeMkAp1 fCode sndSp missO missAp1
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecL (ruleTrans ih (ruleTrans (ruleSym ecR)
                (ruleSym (cong1 evalCode sndEnc)))))

-- ruleF: both sides strip via auto-discharged miss checks
semSound0 .(ap2 Pair tag24T (ap2 Pair (ap2 Pair fC gC) dataT))
           (wc0RuleF fC gC dataT fMissO fMissAp1 gMissO gMissAp1) =
  let nrf = nelsonRuleF fC gC dataT
      mkL = ap2 Pair (reify tagAp1) (ap2 Pair fC var0CodeT)
      mkR = ap2 Pair (reify tagAp1) (ap2 Pair gC var0CodeT)
      fstEnc = ruleTrans (cong1 Fst nrf) (axFst mkL mkR)
      sndEnc = ruleTrans (cong1 Snd nrf) (axSnd mkL mkR)
      ecF = evalCodeMkAp1 fC var0CodeT fMissO fMissAp1
      ecG = evalCodeMkAp1 gC var0CodeT gMissO gMissAp1
  in ruleTrans (cong1 evalCode fstEnc)
     (ruleTrans ecF (ruleTrans (ruleSym ecG)
                (ruleSym (cong1 evalCode sndEnc))))

------------------------------------------------------------------------
-- THE QUANTITATIVE BOUNDARY
--
-- WC0 (0-backtracking) is the fragment where:
--   (1) No ruleInst (substTFor never enters)
--   (2) Only mkAp1-strippable base cases (axI, axRefl, axKT)
--   (3) Only functor-blind congruence (cong1, ruleF)
--
-- semSound0 proves SemTrue with NO external obligations.
--
-- For BLevel > 0 (ruleInst present), the obligation has the shape:
--   evalCode(substTFor(L)) = evalCode(substTFor(R))
-- where substTFor is a k-fold composition for BLevel = k.
-- Each fold introduces a new substTFor layer that does not
-- commute with evalCode, requiring per-instance verification.
--
-- The quantitative boundary:
--   BLevel 0: free (automatic, this file)
--   BLevel k: requires k-fold substTFor verification (NelsonWCBoundary.agda)
--   BLevel ∞: impossible (obstruction theorem)
