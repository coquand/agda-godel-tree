{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RoseLemma1 -- Rose's Lemma 1 at n=1: internalised derivability
-- under ONE hypothesis.
--
-- Given  d : Deriv H B  (derivation of B from hypothesis H), we build
-- a proof-encoding  V  (parameterised by a proof-code of H) such that
--
--   (tCorr: thmT hCode t = reify (codeEqn H)) =>
--   thmT hCode V = reify (codeEqn B).
--
-- The record Lemma1At1 carries:
--   * the pair-split (vPa, vPb) so V = ap2 Pair vPa vPb
--   * the correctness Deriv (vCorr)
--   * the dispatch-opacity Deriv (vPass), needed when V is itself a
--     sub-encoding inside another encoder.

module Guard.RoseLemma1 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT ; ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)
open import Guard.ThFunTForV3Pass using (ndDispatchV3PairMiss)
open import Guard.Thm14EV3
open import Guard.ProofEnc
open import Guard.SubstOp using (substOp ; substOpCorrect)

private
  hCodeOf : Equation -> Term
  hCodeOf H = reify (codeEqn H)

  n0  : Nat ; n0  = zero
  n1  : Nat ; n1  = suc n0
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n4  : Nat ; n4  = suc n3
  n5  : Nat ; n5  = suc n4
  n6  : Nat ; n6  = suc n5
  n7  : Nat ; n7  = suc n6
  n8  : Nat ; n8  = suc n7
  n9  : Nat ; n9  = suc n8
  n10 : Nat ; n10 = suc n9
  n11 : Nat ; n11 = suc n10
  n12 : Nat ; n12 = suc n11
  n13 : Nat ; n13 = suc n12
  n14 : Nat ; n14 = suc n13
  n15 : Nat ; n15 = suc n14
  n16 : Nat ; n16 = suc n15
  n17 : Nat ; n17 = suc n16
  n18 : Nat ; n18 = suc n17
  n19 : Nat ; n19 = suc n18
  n20 : Nat ; n20 = suc n19
  n21 : Nat ; n21 = suc n20
  n22 : Nat ; n22 = suc n21
  n23 : Nat ; n23 = suc n22
  n24 : Nat ; n24 = suc n23
  n25 : Nat ; n25 = suc n24

  -- Local copy of f2xDispMissV3 (private in Thm14EV3).  For every
  -- binary functor g, ndDispatchV3 misses at tag  Pair (codeF2 g) (code x) .

  f2xDM : (hCode : Term) (g : Fun2) (x : Term) (x' rc' : Term) ->
          {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x))) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x))) x') rc'))
  f2xDM hCode Pair         x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc n25))) O (reify (code x)) x' rc'
  f2xDM hCode Const        x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc n25)))) O (reify (code x)) x' rc'
  f2xDM hCode (Lift f)     x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc n25))))) (reify (codeF1 f))
      (reify (code x)) x' rc'
  f2xDM hCode (Post f h)   x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc n25))))))
      (ap2 Pair (reify (codeF1 f)) (reify (codeF2 h)))
      (reify (code x)) x' rc'
  f2xDM hCode (Fan h1 h2 h) x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc n25)))))))
      (ap2 Pair (reify (codeF2 h1)) (ap2 Pair (reify (codeF2 h2)) (reify (codeF2 h))))
      (reify (code x)) x' rc'
  f2xDM hCode IfLf         x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc n25))))))))
      O (reify (code x)) x' rc'
  f2xDM hCode TreeEq       x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc (suc n25)))))))))
      O (reify (code x)) x' rc'
  f2xDM hCode (RecP s)     x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc n25))))))))))
      (reify (codeF2 s)) (reify (code x)) x' rc'

  -- Local copy of f1DispMissV3 (private in Thm14EV3).

  f1DM : (hCode : Term) (f : Fun1) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (codeF1 f)) x') rc')
                   (ap2 sndArg2 (ap2 Pair (reify (codeF1 f)) x') rc'))
  f1DM hCode I             x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode n25)) O x' rc'
  f1DM hCode Fst           x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc n25))) O x' rc'
  f1DM hCode Snd           x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc n25)))) O x' rc'
  f1DM hCode (Comp f g)    x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc n25)))))
      (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x' rc'
  f1DM hCode (Comp2 h f g) x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc (suc n25))))))
      (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))))
      x' rc'
  f1DM hCode (Rec z s)     x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc (suc (suc n25)))))))
      (ap2 Pair (reify (code z)) (reify (codeF2 s))) x' rc'
  f1DM hCode (KT t)        x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc (suc (suc (suc n25))))))))
      (reify (code t)) x' rc'

  -- Local copy of aRPassV3: dispatch-miss at (code t, natCode x) pair
  -- used for ruleInst.

  aRPass : (hCode : Term) (t : Term) (x : Nat) (x' rc' : Term) ->
           {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                    (ap2 Pair (ap2 Pair (reify (code t)) (reify (natCode x))) x') rc')
                   (ap2 sndArg2
                    (ap2 Pair (ap2 Pair (reify (code t)) (reify (natCode x))) x') rc'))
  aRPass hCode O         x x' rc' =
    ndDispatchV3PairMiss hCode O O (reify (natCode x)) x' rc'
  aRPass hCode (var n)   x x' rc' =
    ndDispatchV3PairMiss hCode (reify tagVar) (reify (natCode n))
                               (reify (natCode x)) x' rc'
  aRPass hCode (ap1 f t) x x' rc' =
    ndDispatchV3PairMiss hCode (reify tagAp1)
      (ap2 Pair (reify (codeF1 f)) (reify (code t)))
      (reify (natCode x)) x' rc'
  aRPass hCode (ap2 g a b) x x' rc' =
    ndDispatchV3PairMiss hCode (reify tagAp2)
      (ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code a)) (reify (code b))))
      (reify (natCode x)) x' rc'

  -- Local copy of f1gDispMissV3 for Schema F.

  f1gDM : (hCode : Term) (f g : Fun1) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x') rc'))
  f1gDM hCode I             g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc n25))) O (reify (codeF1 g')) x' rc'
  f1gDM hCode Fst           g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc n25)))) O (reify (codeF1 g')) x' rc'
  f1gDM hCode Snd           g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc n25))))) O (reify (codeF1 g')) x' rc'
  f1gDM hCode (Comp f1 f2)  g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc n25))))))
      (ap2 Pair (reify (codeF1 f1)) (reify (codeF1 f2))) (reify (codeF1 g')) x' rc'
  f1gDM hCode (Comp2 h f1 f2) g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc n25)))))))
      (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f1)) (reify (codeF1 f2))))
      (reify (codeF1 g')) x' rc'
  f1gDM hCode (Rec z' s')   g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc n25))))))))
      (ap2 Pair (reify (code z')) (reify (codeF2 s'))) (reify (codeF1 g')) x' rc'
  f1gDM hCode (KT t)        g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc (suc n25)))))))))
      (reify (code t)) (reify (codeF1 g')) x' rc'

------------------------------------------------------------------------
-- Lemma1At1 record: a proof-encoding split into pa/pb with correctness
-- + pass properties.  The  "t"  parameter is the hypothetical proof-
-- code for the hypothesis H  (appears only in caller-supplied
-- invariants; the record itself is t-agnostic).

record Lemma1At1 (H B : Equation) : Set where
  constructor mkL1
  field
    vPa : Term
    vPb : Term
    vCorr : {hyp : Equation} ->
            Deriv hyp (eqn (ap1 (thmT (hCodeOf H))
                                (ap2 Pair vPa vPb))
                           (reify (codeEqn B)))
    vPass : (x rcs : Term) {hyp : Equation} ->
            Deriv hyp (eqn (ap2 (ndDispatchV3 (hCodeOf H))
                                (ap2 Pair (ap2 Pair vPa vPb) x) rcs)
                           (ap2 sndArg2
                                (ap2 Pair (ap2 Pair vPa vPb) x) rcs))

open Lemma1At1 public

-- V as a Term (convenience):
vTerm : {H B : Equation} -> Lemma1At1 H B -> Term
vTerm L = ap2 Pair (vPa L) (vPb L)

------------------------------------------------------------------------
-- Convert a ProofE3 into Lemma1At1 (for closed Deriv constructors
-- whose encoding doesn't use the hypothesis t).

fromProofE3 : {H B : Equation} -> ProofE3 H B -> Lemma1At1 H B
fromProofE3 pe = mkL1 (reify (pa pe)) (reify (pb pe))
                      (\{hyp} -> corr pe {hyp})
                      (\x rcs {hyp} -> pass pe x rcs {hyp})

------------------------------------------------------------------------
-- Closed cases: V comes from thm14EV3Ax* (no t dependency).

roseL1AxI : (H : Equation) (x : Term) ->
  Lemma1At1 H (eqn (ap1 I x) x)
roseL1AxI H x = fromProofE3 (thm14EV3AxI H x)

roseL1AxFst : (H : Equation) (a b : Term) ->
  Lemma1At1 H (eqn (ap1 Fst (ap2 Pair a b)) a)
roseL1AxFst H a b = fromProofE3 (thm14EV3AxFst H a b)

roseL1AxSnd : (H : Equation) (a b : Term) ->
  Lemma1At1 H (eqn (ap1 Snd (ap2 Pair a b)) b)
roseL1AxSnd H a b = fromProofE3 (thm14EV3AxSnd H a b)

roseL1AxConst : (H : Equation) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 Const a b) a)
roseL1AxConst H a b = fromProofE3 (thm14EV3AxConst H a b)

roseL1AxComp : (H : Equation) (f g : Fun1) (x : Term) ->
  Lemma1At1 H (eqn (ap1 (Comp f g) x) (ap1 f (ap1 g x)))
roseL1AxComp H f g x = fromProofE3 (thm14EV3AxComp H f g x)

roseL1AxComp2 : (H : Equation) (h : Fun2) (f g : Fun1) (x : Term) ->
  Lemma1At1 H (eqn (ap1 (Comp2 h f g) x) (ap2 h (ap1 f x) (ap1 g x)))
roseL1AxComp2 H h f g x = fromProofE3 (thm14EV3AxComp2 H h f g x)

roseL1AxLift : (H : Equation) (f : Fun1) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 (Lift f) a b) (ap1 f a))
roseL1AxLift H f a b = fromProofE3 (thm14EV3AxLift H f a b)

roseL1AxPost : (H : Equation) (f : Fun1) (h : Fun2) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b)))
roseL1AxPost H f h a b = fromProofE3 (thm14EV3AxPost H f h a b)

roseL1AxFan : (H : Equation) (h1 h2 h : Fun2) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 (Fan h1 h2 h) a b)
                   (ap2 h (ap2 h1 a b) (ap2 h2 a b)))
roseL1AxFan H h1 h2 h a b = fromProofE3 (thm14EV3AxFan H h1 h2 h a b)

roseL1AxKT : (H : Equation) (x y : Term) ->
  Lemma1At1 H (eqn (ap1 (KT x) y) x)
roseL1AxKT H x y = fromProofE3 (thm14EV3AxKT H x y)

roseL1AxRecLf : (H : Equation) (z : Term) (s : Fun2) ->
  Lemma1At1 H (eqn (ap1 (Rec z s) O) z)
roseL1AxRecLf H z s = fromProofE3 (thm14EV3AxRecLf H z s)

roseL1AxRecNd : (H : Equation) (z : Term) (s : Fun2) (a b : Term) ->
  Lemma1At1 H (eqn (ap1 (Rec z s) (ap2 Pair a b))
                   (ap2 s (ap2 Pair a b)
                          (ap2 Pair (ap1 (Rec z s) a)
                                    (ap1 (Rec z s) b))))
roseL1AxRecNd H z s a b = fromProofE3 (thm14EV3AxRecNd H z s a b)

roseL1AxIfLfL : (H : Equation) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 IfLf O (ap2 Pair a b)) a)
roseL1AxIfLfL H a b = fromProofE3 (thm14EV3AxIfLfL H a b)

roseL1AxIfLfN : (H : Equation) (x y a b : Term) ->
  Lemma1At1 H (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b)
roseL1AxIfLfN H x y a b = fromProofE3 (thm14EV3AxIfLfN H x y a b)

roseL1AxTreeEqLL : (H : Equation) ->
  Lemma1At1 H (eqn (ap2 TreeEq O O) O)
roseL1AxTreeEqLL H = fromProofE3 (thm14EV3AxTreeEqLL H)

roseL1AxTreeEqLN : (H : Equation) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O))
roseL1AxTreeEqLN H a b = fromProofE3 (thm14EV3AxTreeEqLN H a b)

roseL1AxTreeEqNL : (H : Equation) (a b : Term) ->
  Lemma1At1 H (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O))
roseL1AxTreeEqNL H a b = fromProofE3 (thm14EV3AxTreeEqNL H a b)

roseL1AxTreeEqNN : (H : Equation) (a1 a2 b1 b2 : Term) ->
  Lemma1At1 H (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                   (ap2 IfLf (ap2 TreeEq a1 b1)
                             (ap2 Pair (ap2 TreeEq a2 b2)
                                       (ap2 Pair O O))))
roseL1AxTreeEqNN H a1 a2 b1 b2 =
  fromProofE3 (thm14EV3AxTreeEqNN H a1 a2 b1 b2)

roseL1AxRecPLf : (H : Equation) (s : Fun2) (p : Term) ->
  Lemma1At1 H (eqn (ap2 (RecP s) p O) O)
roseL1AxRecPLf H s p = fromProofE3 (thm14EV3AxRecPLf H s p)

roseL1AxRecPNd : (H : Equation) (s : Fun2) (p a b : Term) ->
  Lemma1At1 H (eqn (ap2 (RecP s) p (ap2 Pair a b))
                   (ap2 s (ap2 Pair p (ap2 Pair a b))
                          (ap2 Pair (ap2 (RecP s) p a)
                                    (ap2 (RecP s) p b))))
roseL1AxRecPNd H s p a b = fromProofE3 (thm14EV3AxRecPNd H s p a b)

roseL1AxRefl : (H : Equation) (x : Term) ->
  Lemma1At1 H (eqn x x)
roseL1AxRefl H x = fromProofE3 (thm14EV3Refl H x)

------------------------------------------------------------------------
-- Hypothesis case: V = t itself, where t is provided in pair-split
-- form (tPa, tPb).  Caller supplies correctness + pass.

roseL1Hyp : (H : Equation) (tPa tPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT (hCodeOf H))
                        (ap2 Pair tPa tPb))
                   (reify (codeEqn H)))) ->
  ((x rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 (hCodeOf H))
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs))) ->
  Lemma1At1 H H
roseL1Hyp H tPa tPb tCorr tPass =
  mkL1 tPa tPb (\{hyp} -> tCorr {hyp}) (\x rcs {hyp} -> tPass x rcs {hyp})

------------------------------------------------------------------------
-- Structural rules: wrap sub-Lemma1At1s with encoder combinators.

-- ruleSym: given sub : Lemma1At1 H (eqn t u), produce result for  (eqn u t).

roseL1Sym : (H : Equation) (t u : Term) ->
  Lemma1At1 H (eqn t u) ->
  Lemma1At1 H (eqn u t)
roseL1Sym H t u sub = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term
  hCode = hCodeOf H

  tC : Term
  tC = reify (code t)

  uC : Term
  uC = reify (code u)

  -- encRuleSym output shape:
  --   ap2 Pair (reify (natCode n18)) (ap2 Pair (reify tagVar) (ap2 Pair sub.vPa sub.vPb))

  vPa' : Term
  vPa' = reify (natCode n18)

  vPb' : Term
  vPb' = ap2 Pair (reify tagVar) (ap2 Pair (vPa sub) (vPb sub))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn u t))))
  corr' {hyp} = encRuleSymCorr hCode (vPa sub) (vPb sub) tC uC (vCorr sub)

  pass' : (x rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x) rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x) rcs))
  pass' x rcs = encRuleSymPass hCode (vPa sub) (vPb sub) x rcs

-- ruleTrans: combine Lemma1At1 H (eqn t u) and Lemma1At1 H (eqn u v)
-- into Lemma1At1 H (eqn t v).

roseL1Trans : (H : Equation) (t u v : Term) ->
  Lemma1At1 H (eqn t u) ->
  Lemma1At1 H (eqn u v) ->
  Lemma1At1 H (eqn t v)
roseL1Trans H t u v sub1 sub2 = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term ; hCode = hCodeOf H
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  vC : Term ; vC = reify (code v)

  vPa' : Term
  vPa' = reify (natCode n19)

  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair (vPa sub1) (vPb sub1))
                  (ap2 Pair (vPa sub2) (vPb sub2))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn t v))))
  corr' {hyp} =
    encRuleTransCorr hCode (vPa sub1) (vPb sub1) (vPa sub2) (vPb sub2)
                     tC uC vC
                     (\x rcs {hyp'} -> vPass sub1 x rcs {hyp'})
                     (vCorr sub1)
                     (vCorr sub2)

  pass' : (x rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x) rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x) rcs))
  pass' x rcs = encRuleTransPass hCode (vPa sub1) (vPb sub1)
                                  (vPa sub2) (vPb sub2) x rcs

-- congL: Lemma1At1 H (eqn t u) -> Lemma1At1 H (eqn (ap2 g t x) (ap2 g u x)).

roseL1CongL : (H : Equation) (t u : Term) (g : Fun2) (x : Term) ->
  Lemma1At1 H (eqn t u) ->
  Lemma1At1 H (eqn (ap2 g t x) (ap2 g u x))
roseL1CongL H t u g x sub = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term ; hCode = hCodeOf H
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  xC : Term ; xC = reify (code x)
  gC : Term ; gC = reify (codeF2 g)

  vPa' : Term
  vPa' = reify (natCode n21)

  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair gC xC) (ap2 Pair (vPa sub) (vPb sub))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn (ap2 g t x) (ap2 g u x)))))
  corr' {hyp} =
    encCongLCorr hCode g xC (vPa sub) (vPb sub) tC uC
      (\x' rc' {hyp'} -> f2xDM hCode g x x' rc')
      (vCorr sub)

  pass' : (x' rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs))
  pass' x' rcs = encCongLPass hCode g xC (vPa sub) (vPb sub) x' rcs

-- cong1: Lemma1At1 H (eqn t u) -> Lemma1At1 H (eqn (ap1 f t) (ap1 f u)).

roseL1Cong1 : (H : Equation) (t u : Term) (f : Fun1) ->
  Lemma1At1 H (eqn t u) ->
  Lemma1At1 H (eqn (ap1 f t) (ap1 f u))
roseL1Cong1 H t u f sub = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term ; hCode = hCodeOf H
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  fC : Term ; fC = reify (codeF1 f)

  vPa' : Term
  vPa' = reify (natCode n20)

  vPb' : Term
  vPb' = ap2 Pair fC (ap2 Pair (vPa sub) (vPb sub))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn (ap1 f t) (ap1 f u)))))
  corr' {hyp} =
    encRuleCong1Corr hCode f (vPa sub) (vPb sub) tC uC
      (\x' rc' {hyp'} -> f1DM hCode f x' rc')
      (vCorr sub)

  pass' : (x' rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs))
  pass' x' rcs = encRuleCong1Pass hCode f (vPa sub) (vPb sub) x' rcs

-- congR: Lemma1At1 H (eqn t u) -> Lemma1At1 H (eqn (ap2 g x t) (ap2 g x u)).

roseL1CongR : (H : Equation) (t u : Term) (g : Fun2) (x : Term) ->
  Lemma1At1 H (eqn t u) ->
  Lemma1At1 H (eqn (ap2 g x t) (ap2 g x u))
roseL1CongR H t u g x sub = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term ; hCode = hCodeOf H
  tC : Term ; tC = reify (code t)
  uC : Term ; uC = reify (code u)
  xC : Term ; xC = reify (code x)
  gC : Term ; gC = reify (codeF2 g)

  vPa' : Term
  vPa' = reify (natCode n22)

  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair gC xC) (ap2 Pair (vPa sub) (vPb sub))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn (ap2 g x t) (ap2 g x u)))))
  corr' {hyp} =
    encCongRCorr hCode g xC (vPa sub) (vPb sub) tC uC
      (\x' rc' {hyp'} -> f2xDM hCode g x x' rc')
      (vCorr sub)

  pass' : (x' rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs))
  pass' x' rcs = encCongRPass hCode g xC (vPa sub) (vPb sub) x' rcs

-- ruleInst: Lemma1At1 H (eqn l r') -> Lemma1At1 H (eqn (subst x t l) (subst x t r')).
--
-- encRuleInstCorr's output is in terms of substOp; we bridge via
-- substOpCorrect to express the result as  reify (codeEqn (subst ..))

roseL1Inst : (H : Equation) (l r' : Term) (x : Nat) (t : Term) ->
  Lemma1At1 H (eqn l r') ->
  Lemma1At1 H (eqn (subst x t l) (subst x t r'))
roseL1Inst H l r' x t sub = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term ; hCode = hCodeOf H
  tC : Term ; tC = reify (code t)
  xC : Term ; xC = reify (natCode x)
  lC : Term ; lC = reify (code l)
  r'C : Term ; r'C = reify (code r')
  aR : Term ; aR = ap2 Pair tC xC

  vPa' : Term
  vPa' = reify (natCode n23)

  vPb' : Term
  vPb' = ap2 Pair aR (ap2 Pair (vPa sub) (vPb sub))

  -- Bridge: Pair (substOp aR lC) (substOp aR r'C) = Pair (code (subst x t l)) (code (subst x t r'))

  substBoth : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap2 substOp aR lC) (ap2 substOp aR r'C))
                   (ap2 Pair (reify (code (subst x t l)))
                             (reify (code (subst x t r')))))
  substBoth =
    ruleTrans (congL Pair (ap2 substOp aR r'C) (substOpCorrect t x l))
              (congR Pair (reify (code (subst x t l)))
                          (substOpCorrect t x r'))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn (subst x t l) (subst x t r')))))
  corr' {hyp} =
    ruleTrans
      (encRuleInstCorr hCode aR (vPa sub) (vPb sub) lC r'C
        (\x' rc' {hyp'} -> aRPass hCode t x x' rc')
        (vCorr sub))
      substBoth

  pass' : (x' rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs))
  pass' x' rcs = encRuleInstPass hCode aR (vPa sub) (vPb sub) x' rcs

-- ruleF (Schema F): four sub-derivations combine into a conclusion
-- about f and g.  V takes the four sub-V's from our four sub-Lemma1At1s.
--
-- Deriv rule: from four premises (f-base, f-step, g-base, g-step),
-- conclude  eqn (ap1 f (var 0)) (ap1 g (var 0)).

roseL1F : (H : Equation) (f g : Fun1) (z : Term) (s : Fun2) ->
  Lemma1At1 H (eqn (ap1 f O) z) ->
  Lemma1At1 H (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
                    (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                           (ap2 Pair (ap1 f (var zero))
                                     (ap1 f (var (suc zero)))))) ->
  Lemma1At1 H (eqn (ap1 g O) z) ->
  Lemma1At1 H (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
                    (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                           (ap2 Pair (ap1 g (var zero))
                                     (ap1 g (var (suc zero)))))) ->
  Lemma1At1 H (eqn (ap1 f (var zero)) (ap1 g (var zero)))
roseL1F H f g z s sub1 sub2 sub3 sub4 = mkL1 vPa' vPb' corr' pass'
  where
  hCode : Term ; hCode = hCodeOf H
  zC : Term ; zC = reify (code z)
  sC : Term ; sC = reify (codeF2 s)

  vPa' : Term
  vPa' = reify (natCode n24)

  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))
                  (ap2 Pair (ap2 Pair zC sC)
                            (ap2 Pair (ap2 Pair (vTerm sub1) (vTerm sub2))
                                      (ap2 Pair (vTerm sub3) (vTerm sub4))))

  corr' : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair vPa' vPb'))
                         (reify (codeEqn (eqn (ap1 f (var zero))
                                              (ap1 g (var zero))))))
  corr' {hyp} =
    encRuleFCorr hCode f g zC sC
      (vTerm sub1) (vTerm sub2) (vTerm sub3) (vTerm sub4)
      (\x' rc' {hyp'} -> f1gDM hCode f g x' rc')

  pass' : (x' rcs : Term) {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs)
                         (ap2 sndArg2
                              (ap2 Pair (ap2 Pair vPa' vPb') x') rcs))
  pass' x' rcs = encRuleFPass hCode f g zC sC
                   (vTerm sub1) (vTerm sub2) (vTerm sub3) (vTerm sub4)
                   x' rcs

------------------------------------------------------------------------
-- Top-level recursion: apply Rose's Lemma 1 to any Deriv.
--
-- Given d : Deriv H B, produce a Lemma1At1 H B parameterised by the
-- caller-supplied hypothesis proof-code (tPa, tPb) + tCorr + tPass.
--
-- The recursion structurally mirrors thm14EV3, except that the
-- hypothesis case returns t = ap2 Pair tPa tPb  instead of case26-
-- encoded  reify (codeEqn H).

roseLemma1 : {H B : Equation} (d : Deriv H B) ->
  (tPa tPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT (hCodeOf H)) (ap2 Pair tPa tPb))
                   (reify (codeEqn H)))) ->
  ((x' rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 (hCodeOf H))
                        (ap2 Pair (ap2 Pair tPa tPb) x') rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair tPa tPb) x') rcs))) ->
  Lemma1At1 H B
roseLemma1 {H} (axI x)          tPa tPb _ _ = roseL1AxI H x
roseLemma1 {H} (axFst a b)      tPa tPb _ _ = roseL1AxFst H a b
roseLemma1 {H} (axSnd a b)      tPa tPb _ _ = roseL1AxSnd H a b
roseLemma1 {H} (axConst a b)    tPa tPb _ _ = roseL1AxConst H a b
roseLemma1 {H} (axComp f g x)   tPa tPb _ _ = roseL1AxComp H f g x
roseLemma1 {H} (axComp2 h f g x) tPa tPb _ _ = roseL1AxComp2 H h f g x
roseLemma1 {H} (axLift f a b)   tPa tPb _ _ = roseL1AxLift H f a b
roseLemma1 {H} (axPost f h a b) tPa tPb _ _ = roseL1AxPost H f h a b
roseLemma1 {H} (axFan h1 h2 h a b) tPa tPb _ _ = roseL1AxFan H h1 h2 h a b
roseLemma1 {H} (axKT x y)       tPa tPb _ _ = roseL1AxKT H x y
roseLemma1 {H} (axRecLf z s)    tPa tPb _ _ = roseL1AxRecLf H z s
roseLemma1 {H} (axRecNd z s a b) tPa tPb _ _ = roseL1AxRecNd H z s a b
roseLemma1 {H} (axRecPLf s p)   tPa tPb _ _ = roseL1AxRecPLf H s p
roseLemma1 {H} (axRecPNd s p a b) tPa tPb _ _ = roseL1AxRecPNd H s p a b
roseLemma1 {H} (axIfLfL a b)    tPa tPb _ _ = roseL1AxIfLfL H a b
roseLemma1 {H} (axIfLfN x y a b) tPa tPb _ _ = roseL1AxIfLfN H x y a b
roseLemma1 {H} axTreeEqLL       tPa tPb _ _ = roseL1AxTreeEqLL H
roseLemma1 {H} (axTreeEqLN a b) tPa tPb _ _ = roseL1AxTreeEqLN H a b
roseLemma1 {H} (axTreeEqNL a b) tPa tPb _ _ = roseL1AxTreeEqNL H a b
roseLemma1 {H} (axTreeEqNN a1 a2 b1 b2) tPa tPb _ _ =
  roseL1AxTreeEqNN H a1 a2 b1 b2
roseLemma1 {H} (axRefl x)       tPa tPb _ _ = roseL1AxRefl H x
roseLemma1 {H} ruleHyp          tPa tPb tCorr tPass =
  roseL1Hyp H tPa tPb tCorr tPass
roseLemma1 {H} (ruleSym {t} {u} d) tPa tPb tCorr tPass =
  roseL1Sym H t u (roseLemma1 d tPa tPb tCorr tPass)
roseLemma1 {H} (ruleTrans {t} {u} {v} d1 d2) tPa tPb tCorr tPass =
  roseL1Trans H t u v
    (roseLemma1 d1 tPa tPb tCorr tPass)
    (roseLemma1 d2 tPa tPb tCorr tPass)
roseLemma1 {H} (cong1 f {t} {u} d) tPa tPb tCorr tPass =
  roseL1Cong1 H t u f (roseLemma1 d tPa tPb tCorr tPass)
roseLemma1 {H} (congL g {t} {u} x d) tPa tPb tCorr tPass =
  roseL1CongL H t u g x (roseLemma1 d tPa tPb tCorr tPass)
roseLemma1 {H} (congR g x {t} {u} d) tPa tPb tCorr tPass =
  roseL1CongR H t u g x (roseLemma1 d tPa tPb tCorr tPass)
roseLemma1 {H} (ruleInst x t {eqn l r'} d) tPa tPb tCorr tPass =
  roseL1Inst H l r' x t (roseLemma1 d tPa tPb tCorr tPass)
roseLemma1 {H} (ruleF f g z s d1 d2 d3 d4) tPa tPb tCorr tPass =
  roseL1F H f g z s
    (roseLemma1 d1 tPa tPb tCorr tPass)
    (roseLemma1 d2 tPa tPb tCorr tPass)
    (roseLemma1 d3 tPa tPb tCorr tPass)
    (roseLemma1 d4 tPa tPb tCorr tPass)
