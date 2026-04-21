{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RoseLemma1T -- Ryan-style Lemma 1 over a fixed ambient thmT.
--
-- Unlike Guard.RoseLemma1 (which uses  thmT (hCodeOf H)  for whatever
-- H is chosen as the meta-level hypothesis of  d : Deriv H B ), this
-- module fixes the ambient evaluator to  thmT trivCT .  That is: the
-- *ambient theory* for encoding purposes is Triv (the tautology
-- hypothesis).  The hypothesis H of the input derivation is
-- internalised at the ENCODING level via the caller-supplied tCorr,
-- NOT at the  thmT  evaluator level.
--
-- This matches Ryan (1978) Lemma 1 and Rose (1967) Lemma 1: the
-- evaluator is the ambient theory's  th ; the hypotheses E_1, ..., E_n
-- appear only through caller-supplied encodings (placeholders
-- x_1, ..., x_n) that V splices in wherever  ruleHyp  is used in d.
--
-- Implementation: same structure as Guard/RoseLemma1.agda, but with
-- the local abbreviation  hCode = trivCT  in place of  hCode =
-- reify (codeEqn H) .  The proof-encoders from Guard/ProofEnc are
-- hCode-parametric and work here unchanged.
--
-- For closed Deriv axioms (axI, axFst, ..., axRefl) the V-encoding is
-- structurally identical to RoseLemma1's  fromProofE3 (thm14EV3Ax*) ,
-- but the correctness proof now uses  thmT trivCT  directly via
-- enc*Corr from ProofEnc.
--
-- No postulates, no holes.

module Guard.RoseLemma1T where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT ; ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)
open import Guard.ThFunTForV3Pass using (ndDispatchV3PairMiss)
open import Guard.SubstTForPrecompClassical using (trivCT)
open import Guard.ProofEnc
open import Guard.SubstOp using (substOp ; substOpCorrect)

------------------------------------------------------------------------
-- Nat abbreviations (private, mirroring RoseLemma1.agda).

private
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

  ------------------------------------------------------------------------
  -- Dispatch-miss helpers at  hCode = trivCT .  These are the same as
  -- RoseLemma1.agda's f2xDM / f1DM / aRPass / f1gDM, just with hCode
  -- parameter (inherited from ndDispatchV3PairMiss) specialised in-
  -- stance.  We keep hCode as a parameter for uniformity with the
  -- structural-rule callers.

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
-- Lemma1T H B: Ryan-style Lemma 1 record (thmT trivCT fixed).

record Lemma1T (H B : Equation) : Set where
  constructor mkL1T
  field
    vPa : Term
    vPb : Term
    vCorr : {hyp : Equation} ->
            Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair vPa vPb))
                           (reify (codeEqn B)))
    vPass : (x rcs : Term) {hyp : Equation} ->
            Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT)
                                (ap2 Pair (ap2 Pair vPa vPb) x) rcs)
                           (ap2 sndArg2
                                (ap2 Pair (ap2 Pair vPa vPb) x) rcs))

open Lemma1T public

vTermT : {H B : Equation} -> Lemma1T H B -> Term
vTermT L = ap2 Pair (vPa L) (vPb L)

------------------------------------------------------------------------
-- Hypothesis case.

roseL1T_Hyp : (H : Equation) (tPa tPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair tPa tPb))
                   (reify (codeEqn H)))) ->
  ((x rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT)
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair tPa tPb) x) rcs))) ->
  Lemma1T H H
roseL1T_Hyp H tPa tPb tCorr tPass =
  mkL1T tPa tPb (\{hyp} -> tCorr {hyp}) (\x rcs {hyp} -> tPass x rcs {hyp})

------------------------------------------------------------------------
-- Closed axiom cases.  Each uses enc*Corr / enc*Pass from
-- Guard.ProofEnc at hCode = trivCT.

roseL1T_AxI : (H : Equation) (x : Term) -> Lemma1T H (eqn (ap1 I x) x)
roseL1T_AxI H x = mkL1T O (ap2 Pair (reify (code x)) O)
  (encAxICorr trivCT (reify (code x)))
  (\x' rcs -> encAxIPass trivCT x x' rcs)

roseL1T_AxFst : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap1 Fst (ap2 Pair a b)) a)
roseL1T_AxFst H a b = mkL1T
  (reify (natCode n1))
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxFstCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxFstPass trivCT a b x' rcs)

roseL1T_AxSnd : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap1 Snd (ap2 Pair a b)) b)
roseL1T_AxSnd H a b = mkL1T
  (reify (natCode n2))
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxSndCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxSndPass trivCT a b x' rcs)

roseL1T_AxConst : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap2 Const a b) a)
roseL1T_AxConst H a b = mkL1T
  (reify (natCode n3))
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxConstCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxConstPass trivCT a b x' rcs)

roseL1T_AxComp : (H : Equation) (f g : Fun1) (t : Term) ->
  Lemma1T H (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))
roseL1T_AxComp H f g t = mkL1T
  (reify (natCode n4))
  (ap2 Pair (reify (codeF1 f)) (ap2 Pair (reify (codeF1 g)) (reify (code t))))
  (encAxCompCorr trivCT (reify (codeF1 f)) (reify (codeF1 g)) (reify (code t)))
  (\x' rcs -> encAxCompPass trivCT f g t x' rcs)

roseL1T_AxComp2 : (H : Equation) (h : Fun2) (f g : Fun1) (t : Term) ->
  Lemma1T H (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t)))
roseL1T_AxComp2 H h f g t = mkL1T
  (reify (natCode n5))
  (ap2 Pair (reify (codeF2 h))
    (ap2 Pair (reify (codeF1 f)) (ap2 Pair (reify (codeF1 g)) (reify (code t)))))
  (encAxComp2Corr trivCT (reify (codeF2 h)) (reify (codeF1 f))
                         (reify (codeF1 g)) (reify (code t)))
  (\x' rcs -> encAxComp2Pass trivCT h f g t x' rcs)

roseL1T_AxLift : (H : Equation) (f : Fun1) (a b : Term) ->
  Lemma1T H (eqn (ap2 (Lift f) a b) (ap1 f a))
roseL1T_AxLift H f a b = mkL1T
  (reify (natCode n6))
  (ap2 Pair (reify (codeF1 f)) (ap2 Pair (reify (code a)) (reify (code b))))
  (encAxLiftCorr trivCT (reify (codeF1 f)) (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxLiftPass trivCT f a b x' rcs)

roseL1T_AxPost : (H : Equation) (f : Fun1) (h : Fun2) (a b : Term) ->
  Lemma1T H (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b)))
roseL1T_AxPost H f h a b = mkL1T
  (reify (natCode n7))
  (ap2 Pair (reify (codeF1 f))
    (ap2 Pair (reify (codeF2 h))
              (ap2 Pair (reify (code a)) (reify (code b)))))
  (encAxPostCorr trivCT (reify (codeF1 f)) (reify (codeF2 h))
                        (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxPostPass trivCT f h a b x' rcs)

roseL1T_AxFan : (H : Equation) (h1 h2 h : Fun2) (a b : Term) ->
  Lemma1T H (eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b)))
roseL1T_AxFan H h1 h2 h a b = mkL1T
  (reify (natCode n8))
  (ap2 Pair (reify (codeF2 h1))
    (ap2 Pair (reify (codeF2 h2))
      (ap2 Pair (reify (codeF2 h))
                (ap2 Pair (reify (code a)) (reify (code b))))))
  (encAxFanCorr trivCT (reify (codeF2 h1)) (reify (codeF2 h2))
                       (reify (codeF2 h))
                       (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxFanPass trivCT h1 h2 h a b x' rcs)

roseL1T_AxKT : (H : Equation) (t x : Term) ->
  Lemma1T H (eqn (ap1 (KT t) x) t)
roseL1T_AxKT H t x = mkL1T
  (reify (natCode n25))
  (ap2 Pair (reify (code t)) (reify (code x)))
  (encAxKTCorr trivCT (reify (code t)) (reify (code x)))
  (\x' rcs -> encAxKTPass trivCT t x x' rcs)

roseL1T_AxRecLf : (H : Equation) (z : Term) (s : Fun2) ->
  Lemma1T H (eqn (ap1 (Rec z s) O) z)
roseL1T_AxRecLf H z s = mkL1T
  (reify (natCode n9))
  (ap2 Pair (reify (code z)) (reify (codeF2 s)))
  (encAxRecLfCorr trivCT (reify (code z)) (reify (codeF2 s)))
  (\x' rcs -> encAxRecLfPass trivCT z s x' rcs)

roseL1T_AxRecNd : (H : Equation) (z : Term) (s : Fun2) (a b : Term) ->
  Lemma1T H (eqn (ap1 (Rec z s) (ap2 Pair a b))
                 (ap2 s (ap2 Pair a b)
                        (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b))))
roseL1T_AxRecNd H z s a b = mkL1T
  (reify (natCode n10))
  (ap2 Pair (reify (code z))
    (ap2 Pair (reify (codeF2 s))
      (ap2 Pair (reify (code a)) (reify (code b)))))
  (encAxRecNdCorr trivCT (reify (code z)) (reify (codeF2 s))
    (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxRecNdPass trivCT z s a b x' rcs)

roseL1T_AxIfLfL : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap2 IfLf O (ap2 Pair a b)) a)
roseL1T_AxIfLfL H a b = mkL1T
  (reify (natCode n11))
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxIfLfLCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxIfLfLPass trivCT a b x' rcs)

roseL1T_AxIfLfN : (H : Equation) (x y a b : Term) ->
  Lemma1T H (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b)
roseL1T_AxIfLfN H x y a b = mkL1T
  (reify (natCode n12))
  (ap2 Pair (reify (code x))
    (ap2 Pair (reify (code y))
      (ap2 Pair (reify (code a)) (reify (code b)))))
  (encAxIfLfNCorr trivCT (reify (code x)) (reify (code y))
    (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxIfLfNPass trivCT x y a b x' rcs)

roseL1T_AxTreeEqLL : (H : Equation) ->
  Lemma1T H (eqn (ap2 TreeEq O O) O)
roseL1T_AxTreeEqLL H = mkL1T
  (reify (natCode n13)) O
  (encAxTreeEqLLCorr trivCT)
  (\x' rcs -> encAxTreeEqLLPass trivCT x' rcs)

roseL1T_AxTreeEqLN : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O))
roseL1T_AxTreeEqLN H a b = mkL1T
  (reify (natCode n14))
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxTreeEqLNCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxTreeEqLNPass trivCT a b x' rcs)

roseL1T_AxTreeEqNL : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O))
roseL1T_AxTreeEqNL H a b = mkL1T
  (reify (natCode n15))
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxTreeEqNLCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxTreeEqNLPass trivCT a b x' rcs)

roseL1T_AxTreeEqNN : (H : Equation) (a1 a2 b1 b2 : Term) ->
  Lemma1T H (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                 (ap2 IfLf (ap2 TreeEq a1 b1)
                           (ap2 Pair (ap2 TreeEq a2 b2)
                                     (ap2 Pair O O))))
roseL1T_AxTreeEqNN H a1 a2 b1 b2 = mkL1T
  (reify (natCode n16))
  (ap2 Pair (reify (code a1))
    (ap2 Pair (reify (code a2))
      (ap2 Pair (reify (code b1)) (reify (code b2)))))
  (encAxTreeEqNNCorr trivCT (reify (code a1)) (reify (code a2))
                            (reify (code b1)) (reify (code b2)))
  (\x' rcs -> encAxTreeEqNNPass trivCT a1 a2 b1 b2 x' rcs)

roseL1T_AxRefl : (H : Equation) (x : Term) -> Lemma1T H (eqn x x)
roseL1T_AxRefl H x = mkL1T
  (reify (natCode n17))
  (ap2 Pair (reify (code x)) O)
  (encAxReflCorr trivCT (reify (code x)))
  (\x' rcs -> encAxReflPass trivCT x x' rcs)

roseL1T_AxRecPLf : (H : Equation) (s : Fun2) (p : Term) ->
  Lemma1T H (eqn (ap2 (RecP s) p O) O)
roseL1T_AxRecPLf H s p = mkL1T
  (reify (natCode (suc (suc n25))))  -- n27
  (ap2 Pair (reify (codeF2 s)) (reify (code p)))
  (encAxRecPLfCorr trivCT (reify (codeF2 s)) (reify (code p)))
  (\x' rcs -> encAxRecPLfPass trivCT s p x' rcs)

roseL1T_AxRecPNd : (H : Equation) (s : Fun2) (p a b : Term) ->
  Lemma1T H (eqn (ap2 (RecP s) p (ap2 Pair a b))
                 (ap2 s (ap2 Pair p (ap2 Pair a b))
                        (ap2 Pair (ap2 (RecP s) p a)
                                  (ap2 (RecP s) p b))))
roseL1T_AxRecPNd H s p a b = mkL1T
  (reify (natCode (suc (suc (suc n25)))))  -- n28
  (ap2 Pair (reify (codeF2 s))
    (ap2 Pair (reify (code p))
      (ap2 Pair (reify (code a)) (reify (code b)))))
  (encAxRecPNdCorr trivCT (reify (codeF2 s)) (reify (code p))
                          (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxRecPNdPass trivCT s p a b x' rcs)

roseL1T_AxGoodstein : (H : Equation) (a b : Term) ->
  Lemma1T H (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                 (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O)))
roseL1T_AxGoodstein H a b = mkL1T
  (reify (natCode (suc (suc (suc (suc n25))))))  -- n29
  (ap2 Pair (reify (code a)) (reify (code b)))
  (encAxGoodsteinCorr trivCT (reify (code a)) (reify (code b)))
  (\x' rcs -> encAxGoodsteinPass trivCT a b x' rcs)

------------------------------------------------------------------------
-- Structural rule wrappers.

roseL1T_Sym : (H : Equation) (t u : Term) ->
  Lemma1T H (eqn t u) -> Lemma1T H (eqn u t)
roseL1T_Sym H t u sub = mkL1T vPa' vPb'
  (\{hyp} -> encRuleSymCorr trivCT (vPa sub) (vPb sub)
                            (reify (code t)) (reify (code u)) (vCorr sub))
  (\x rcs -> encRuleSymPass trivCT (vPa sub) (vPb sub) x rcs)
  where
  vPa' : Term ; vPa' = reify (natCode n18)
  vPb' : Term
  vPb' = ap2 Pair (reify tagVar) (ap2 Pair (vPa sub) (vPb sub))

roseL1T_Trans : (H : Equation) (t u v : Term) ->
  Lemma1T H (eqn t u) -> Lemma1T H (eqn u v) -> Lemma1T H (eqn t v)
roseL1T_Trans H t u v sub1 sub2 = mkL1T vPa' vPb'
  (\{hyp} ->
    encRuleTransCorr trivCT (vPa sub1) (vPb sub1) (vPa sub2) (vPb sub2)
                     (reify (code t)) (reify (code u)) (reify (code v))
                     (\x rcs {hyp'} -> vPass sub1 x rcs {hyp'})
                     (vCorr sub1) (vCorr sub2))
  (\x rcs -> encRuleTransPass trivCT (vPa sub1) (vPb sub1)
                               (vPa sub2) (vPb sub2) x rcs)
  where
  vPa' : Term ; vPa' = reify (natCode n19)
  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair (vPa sub1) (vPb sub1))
                  (ap2 Pair (vPa sub2) (vPb sub2))

roseL1T_Cong1 : (H : Equation) (t u : Term) (f : Fun1) ->
  Lemma1T H (eqn t u) -> Lemma1T H (eqn (ap1 f t) (ap1 f u))
roseL1T_Cong1 H t u f sub = mkL1T vPa' vPb'
  (\{hyp} ->
    encRuleCong1Corr trivCT f (vPa sub) (vPb sub)
                     (reify (code t)) (reify (code u))
                     (\x' rc' {hyp'} -> f1DM trivCT f x' rc')
                     (vCorr sub))
  (\x' rcs -> encRuleCong1Pass trivCT f (vPa sub) (vPb sub) x' rcs)
  where
  vPa' : Term ; vPa' = reify (natCode n20)
  vPb' : Term
  vPb' = ap2 Pair (reify (codeF1 f)) (ap2 Pair (vPa sub) (vPb sub))

roseL1T_CongL : (H : Equation) (t u : Term) (g : Fun2) (x : Term) ->
  Lemma1T H (eqn t u) -> Lemma1T H (eqn (ap2 g t x) (ap2 g u x))
roseL1T_CongL H t u g x sub = mkL1T vPa' vPb'
  (\{hyp} ->
    encCongLCorr trivCT g (reify (code x)) (vPa sub) (vPb sub)
                 (reify (code t)) (reify (code u))
                 (\x' rc' {hyp'} -> f2xDM trivCT g x x' rc')
                 (vCorr sub))
  (\x' rcs -> encCongLPass trivCT g (reify (code x)) (vPa sub) (vPb sub) x' rcs)
  where
  vPa' : Term ; vPa' = reify (natCode n21)
  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x)))
                  (ap2 Pair (vPa sub) (vPb sub))

roseL1T_CongR : (H : Equation) (t u : Term) (g : Fun2) (x : Term) ->
  Lemma1T H (eqn t u) -> Lemma1T H (eqn (ap2 g x t) (ap2 g x u))
roseL1T_CongR H t u g x sub = mkL1T vPa' vPb'
  (\{hyp} ->
    encCongRCorr trivCT g (reify (code x)) (vPa sub) (vPb sub)
                 (reify (code t)) (reify (code u))
                 (\x' rc' {hyp'} -> f2xDM trivCT g x x' rc')
                 (vCorr sub))
  (\x' rcs -> encCongRPass trivCT g (reify (code x)) (vPa sub) (vPb sub) x' rcs)
  where
  vPa' : Term ; vPa' = reify (natCode n22)
  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x)))
                  (ap2 Pair (vPa sub) (vPb sub))

roseL1T_Inst : (H : Equation) (l r' : Term) (x : Nat) (t : Term) ->
  Lemma1T H (eqn l r') ->
  Lemma1T H (eqn (subst x t l) (subst x t r'))
roseL1T_Inst H l r' x t sub = mkL1T vPa' vPb' corr' pass'
  where
  tC : Term ; tC = reify (code t)
  xC : Term ; xC = reify (natCode x)
  lC : Term ; lC = reify (code l)
  r'C : Term ; r'C = reify (code r')
  aR : Term ; aR = ap2 Pair tC xC

  vPa' : Term ; vPa' = reify (natCode n23)
  vPb' : Term
  vPb' = ap2 Pair aR (ap2 Pair (vPa sub) (vPb sub))

  substBoth : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap2 substOp aR lC) (ap2 substOp aR r'C))
                   (ap2 Pair (reify (code (subst x t l)))
                             (reify (code (subst x t r')))))
  substBoth =
    ruleTrans (congL Pair (ap2 substOp aR r'C) (substOpCorrect t x l))
              (congR Pair (reify (code (subst x t l)))
                          (substOpCorrect t x r'))

  corr' : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair vPa' vPb'))
                   (reify (codeEqn (eqn (subst x t l) (subst x t r')))))
  corr' {hyp} =
    ruleTrans
      (encRuleInstCorr trivCT aR (vPa sub) (vPb sub) lC r'C
        (\x' rc' {hyp'} -> aRPass trivCT t x x' rc')
        (vCorr sub))
      substBoth

  pass' : (x' rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT)
                        (ap2 Pair (ap2 Pair vPa' vPb') x') rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair vPa' vPb') x') rcs))
  pass' x' rcs = encRuleInstPass trivCT aR (vPa sub) (vPb sub) x' rcs

roseL1T_F : (H : Equation) (f g : Fun1) (z : Term) (s : Fun2) ->
  Lemma1T H (eqn (ap1 f O) z) ->
  Lemma1T H (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
                 (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                        (ap2 Pair (ap1 f (var zero))
                                  (ap1 f (var (suc zero)))))) ->
  Lemma1T H (eqn (ap1 g O) z) ->
  Lemma1T H (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
                 (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                        (ap2 Pair (ap1 g (var zero))
                                  (ap1 g (var (suc zero)))))) ->
  Lemma1T H (eqn (ap1 f (var zero)) (ap1 g (var zero)))
roseL1T_F H f g z s sub1 sub2 sub3 sub4 = mkL1T vPa' vPb'
  (\{hyp} ->
    encRuleFCorr trivCT f g (reify (code z)) (reify (codeF2 s))
      (vTermT sub1) (vTermT sub2) (vTermT sub3) (vTermT sub4)
      (\x' rc' {hyp'} -> f1gDM trivCT f g x' rc'))
  (\x' rcs -> encRuleFPass trivCT f g (reify (code z)) (reify (codeF2 s))
                (vTermT sub1) (vTermT sub2) (vTermT sub3) (vTermT sub4)
                x' rcs)
  where
  vPa' : Term ; vPa' = reify (natCode n24)
  vPb' : Term
  vPb' = ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))
                  (ap2 Pair (ap2 Pair (reify (code z)) (reify (codeF2 s)))
                            (ap2 Pair (ap2 Pair (vTermT sub1) (vTermT sub2))
                                      (ap2 Pair (vTermT sub3) (vTermT sub4))))

------------------------------------------------------------------------
-- Top-level recursion.  Mirrors Guard/RoseLemma1.agda's roseLemma1.

roseLemma1T : {H B : Equation} (d : Deriv H B) ->
  (tPa tPb : Term) ->
  ({hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 Pair tPa tPb))
                   (reify (codeEqn H)))) ->
  ((x' rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT)
                        (ap2 Pair (ap2 Pair tPa tPb) x') rcs)
                   (ap2 sndArg2
                        (ap2 Pair (ap2 Pair tPa tPb) x') rcs))) ->
  Lemma1T H B
roseLemma1T {H} (axI x)                   _ _ _ _ = roseL1T_AxI H x
roseLemma1T {H} (axFst a b)               _ _ _ _ = roseL1T_AxFst H a b
roseLemma1T {H} (axSnd a b)               _ _ _ _ = roseL1T_AxSnd H a b
roseLemma1T {H} (axConst a b)             _ _ _ _ = roseL1T_AxConst H a b
roseLemma1T {H} (axComp f g x)            _ _ _ _ = roseL1T_AxComp H f g x
roseLemma1T {H} (axComp2 h f g x)         _ _ _ _ = roseL1T_AxComp2 H h f g x
roseLemma1T {H} (axLift f a b)            _ _ _ _ = roseL1T_AxLift H f a b
roseLemma1T {H} (axPost f h a b)          _ _ _ _ = roseL1T_AxPost H f h a b
roseLemma1T {H} (axFan h1 h2 h a b)       _ _ _ _ = roseL1T_AxFan H h1 h2 h a b
roseLemma1T {H} (axKT x y)                _ _ _ _ = roseL1T_AxKT H x y
roseLemma1T {H} (axRecLf z s)             _ _ _ _ = roseL1T_AxRecLf H z s
roseLemma1T {H} (axRecNd z s a b)         _ _ _ _ = roseL1T_AxRecNd H z s a b
roseLemma1T {H} (axRecPLf s p)            _ _ _ _ = roseL1T_AxRecPLf H s p
roseLemma1T {H} (axRecPNd s p a b)        _ _ _ _ = roseL1T_AxRecPNd H s p a b
roseLemma1T {H} (axIfLfL a b)             _ _ _ _ = roseL1T_AxIfLfL H a b
roseLemma1T {H} (axIfLfN x y a b)         _ _ _ _ = roseL1T_AxIfLfN H x y a b
roseLemma1T {H} axTreeEqLL                _ _ _ _ = roseL1T_AxTreeEqLL H
roseLemma1T {H} (axTreeEqLN a b)          _ _ _ _ = roseL1T_AxTreeEqLN H a b
roseLemma1T {H} (axTreeEqNL a b)          _ _ _ _ = roseL1T_AxTreeEqNL H a b
roseLemma1T {H} (axTreeEqNN a1 a2 b1 b2)  _ _ _ _ = roseL1T_AxTreeEqNN H a1 a2 b1 b2
roseLemma1T {H} (axGoodstein a b)         _ _ _ _ = roseL1T_AxGoodstein H a b
roseLemma1T {H} (axRefl x)                _ _ _ _ = roseL1T_AxRefl H x
roseLemma1T {H} ruleHyp                   tPa tPb tCorr tPass =
  roseL1T_Hyp H tPa tPb tCorr tPass
roseLemma1T {H} (ruleSym {t} {u} d)       tPa tPb tCorr tPass =
  roseL1T_Sym H t u (roseLemma1T d tPa tPb tCorr tPass)
roseLemma1T {H} (ruleTrans {t} {u} {v} d1 d2) tPa tPb tCorr tPass =
  roseL1T_Trans H t u v
    (roseLemma1T d1 tPa tPb tCorr tPass)
    (roseLemma1T d2 tPa tPb tCorr tPass)
roseLemma1T {H} (cong1 f {t} {u} d)       tPa tPb tCorr tPass =
  roseL1T_Cong1 H t u f (roseLemma1T d tPa tPb tCorr tPass)
roseLemma1T {H} (congL g {t} {u} x d)     tPa tPb tCorr tPass =
  roseL1T_CongL H t u g x (roseLemma1T d tPa tPb tCorr tPass)
roseLemma1T {H} (congR g x {t} {u} d)     tPa tPb tCorr tPass =
  roseL1T_CongR H t u g x (roseLemma1T d tPa tPb tCorr tPass)
roseLemma1T {H} (ruleInst x t {eqn l r'} d) tPa tPb tCorr tPass =
  roseL1T_Inst H l r' x t (roseLemma1T d tPa tPb tCorr tPass)
roseLemma1T {H} (ruleF f g z s d1 d2 d3 d4) tPa tPb tCorr tPass =
  roseL1T_F H f g z s
    (roseLemma1T d1 tPa tPb tCorr tPass)
    (roseLemma1T d2 tPa tPb tCorr tPass)
    (roseLemma1T d3 tPa tPb tCorr tPass)
    (roseLemma1T d4 tPa tPb tCorr tPass)
