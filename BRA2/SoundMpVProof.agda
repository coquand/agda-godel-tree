{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SoundMpVProof
--
-- Evaluation proof for body_mp_v (verifying mp body) under the
-- "pass" branch hypotheses.  Closed-Formula version: all witnesses
-- are Term-level, no thmT involvement.
--
-- Given:
--   * distH : ap1 Snd bb = ap2 Pair t1 t2.
--   * d1    : t1 = ap2 Pair (reify tagImp) (ap2 Pair pT qT).
--   * dh    : t2 = pT.
--   * innerRefl : ap2 TreeEq pT pT = O.    [supplied by caller]
-- conclude:
--   ap2 body_mp_v a bb = qT.
--
-- The outer reflexivity TreeEq tagImp tagImp = O is closed and is
-- discharged inline via  treeEqRed tagImp tagImp .  The inner
-- reflexivity is parametric in pT, so we take it as a hypothesis;
-- callers can supply  treeEqRed (codeFormula P)(codeFormula P)
-- when pT is closed (i.e. = reify (codeFormula P)) or a parametric
-- treeEqRefl_param when pT is an open Term.
--
-- Identifier convention: camelCase throughout.  Mid-identifier
-- underscores collide with Agda's mixfix grammar (every let-binding
-- "x_y" is parsed as a 1-argument operator, breaking applications
-- of nearby names).
--
-- ASCII only.  No postulates, no holes, no with-abstraction.

module BRA2.SoundMpVProof where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.SubT using (treeEqRed)
open import BRA2.Thm.EvalHelpers
  using ( liftAxiom ; liftedRuleTrans ; liftedCong1 ; liftedCongL ; liftedCongR )

----------------------------------------------------------------------
-- Body and helpers (formerly in BRA2.SoundMpProto).

----------------------------------------------------------------------
-- Encoded codeTriv.
--
-- codeFormula (atomic (eqn O O)) = nd (code O) (code O) = nd lf lf.
-- reify (nd lf lf) = ap2 Pair O O = falseT (definitionally).

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

-- Sanity check: codeTriv definitionally equals falseT.
codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- Extractors over the synthesized pair  t = (ap2 Pair a b)
-- (introduced by  Post _ Pair  via axPost).
--
-- Since  ap1 Fst t = a  and  ap1 Snd t = b , extractors that reach
-- into b are written as  Comp _ Snd  chains.

-- thmT y1T = Fst (Snd b) = Fst (Snd (Snd t)).
getD1 : Fun1
getD1 = Comp Fst (Comp Snd Snd)

-- thmT y2T = Snd (Snd b) = Snd (Snd (Snd t)).
getD2 : Fun1
getD2 = Comp Snd (Comp Snd Snd)

-- Fst (thmT y1T) = head (should be tagImp).
getHead : Fun1
getHead = Comp Fst getD1

-- Snd (thmT y1T) = body (Pair pT qT).
-- Fst (Snd (thmT y1T)) = pT.
getPT : Fun1
getPT = Comp Fst (Comp Snd getD1)

-- Snd (Snd (thmT y1T)) = qT.
getQT : Fun1
getQT = Comp Snd (Comp Snd getD1)

----------------------------------------------------------------------
-- The verifier as a Fun1 over  t = (Pair a b) .
--
-- verifierF1 = if (combinedCheck) then qT else codeTriv,
-- expressed as  Comp2 IfLf ccF1 qfailPairF1 .
--
-- ccF1 = if (outerCheck) then innerCheck else falseT,
-- expressed as  Comp2 IfLf outerCheckF1 innerOrFalsePairF1 .

outerCheckF1 : Fun1
outerCheckF1 = Comp2 TreeEq getHead (KT (reify tagImp))

innerCheckF1 : Fun1
innerCheckF1 = Comp2 TreeEq getD2 getPT

innerOrFalsePairF1 : Fun1
innerOrFalsePairF1 = Comp2 Pair innerCheckF1 (KT falseT)

ccF1 : Fun1
ccF1 = Comp2 IfLf outerCheckF1 innerOrFalsePairF1

qfailPairF1 : Fun1
qfailPairF1 = Comp2 Pair getQT (KT codeTriv)

verifierF1 : Fun1
verifierF1 = Comp2 IfLf ccF1 qfailPairF1

----------------------------------------------------------------------
-- The verifying body for mp.

body_mp_v : Fun2
body_mp_v = Post verifierF1 Pair

----------------------------------------------------------------------
-- The combinator typechecks; the eval proof  body_mp_v_eval_pass
-- lives in  BRA2.SoundMpVProof  (closed-Formula version).
----------------------------------------------------------------------
-- The main lemma.

body_mp_v_eval_pass :
  (a bb : Term) (t1 t2 pT qT : Term) ->
  Deriv (atomic (eqn (ap1 Snd bb) (ap2 Pair t1 t2))) ->
  Deriv (atomic (eqn t1 (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
  Deriv (atomic (eqn t2 pT)) ->
  Deriv (atomic (eqn (ap2 TreeEq pT pT) O)) ->
  Deriv (atomic (eqn (ap2 body_mp_v a bb) qT))
body_mp_v_eval_pass a bb t1 t2 pT qT distH d1 dh innerRefl =
  let
      t : Term
      t = ap2 Pair a bb

      ----------------------------------------------------------------
      -- Section A: projections through t.

      a1 : Deriv (atomic (eqn (ap1 Snd t) bb))
      a1 = axSnd a bb

      a2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t)) (ap1 Snd bb)))
      a2 = cong1 Snd a1

      a3 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t)) (ap2 Pair t1 t2)))
      a3 = ruleTrans a2 distH

      a4 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap1 Snd (ap1 Snd t))))
      a4 = axComp Snd Snd t

      a5 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap2 Pair t1 t2)))
      a5 = ruleTrans a4 a3

      a6 : Deriv (atomic (eqn (ap1 getD1 t) (ap1 Fst (ap1 (Comp Snd Snd) t))))
      a6 = axComp Fst (Comp Snd Snd) t

      a7 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Snd) t))
                              (ap1 Fst (ap2 Pair t1 t2))))
      a7 = cong1 Fst a5

      a8 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair t1 t2)) t1))
      a8 = axFst t1 t2

      getD1T : Deriv (atomic (eqn (ap1 getD1 t) t1))
      getD1T = ruleTrans a6 (ruleTrans a7 a8)

      b1 : Deriv (atomic (eqn (ap1 getD2 t) (ap1 Snd (ap1 (Comp Snd Snd) t))))
      b1 = axComp Snd (Comp Snd Snd) t

      b2 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) t))
                              (ap1 Snd (ap2 Pair t1 t2))))
      b2 = cong1 Snd a5

      b3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair t1 t2)) t2))
      b3 = axSnd t1 t2

      getD2T : Deriv (atomic (eqn (ap1 getD2 t) t2))
      getD2T = ruleTrans b1 (ruleTrans b2 b3)

      getD2TpT : Deriv (atomic (eqn (ap1 getD2 t) pT))
      getD2TpT = ruleTrans getD2T dh

      ----------------------------------------------------------------
      -- Section B: extract through t1 = Pair tagImp (Pair pT qT).

      tagImpT : Term
      tagImpT = reify tagImp

      pqPair : Term
      pqPair = ap2 Pair pT qT

      c1 : Deriv (atomic (eqn (ap1 Fst t1)
                              (ap1 Fst (ap2 Pair tagImpT pqPair))))
      c1 = cong1 Fst d1

      c2 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagImpT pqPair)) tagImpT))
      c2 = axFst tagImpT pqPair

      fstT1 : Deriv (atomic (eqn (ap1 Fst t1) tagImpT))
      fstT1 = ruleTrans c1 c2

      c3 : Deriv (atomic (eqn (ap1 Snd t1)
                              (ap1 Snd (ap2 Pair tagImpT pqPair))))
      c3 = cong1 Snd d1

      c4 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tagImpT pqPair)) pqPair))
      c4 = axSnd tagImpT pqPair

      sndT1 : Deriv (atomic (eqn (ap1 Snd t1) pqPair))
      sndT1 = ruleTrans c3 c4

      c5 : Deriv (atomic (eqn (ap1 Fst (ap1 Snd t1)) (ap1 Fst pqPair)))
      c5 = cong1 Fst sndT1

      c6 : Deriv (atomic (eqn (ap1 Fst pqPair) pT))
      c6 = axFst pT qT

      fstSndT1 : Deriv (atomic (eqn (ap1 Fst (ap1 Snd t1)) pT))
      fstSndT1 = ruleTrans c5 c6

      c7 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t1)) (ap1 Snd pqPair)))
      c7 = cong1 Snd sndT1

      c8 : Deriv (atomic (eqn (ap1 Snd pqPair) qT))
      c8 = axSnd pT qT

      sndSndT1 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t1)) qT))
      sndSndT1 = ruleTrans c7 c8

      ----------------------------------------------------------------
      -- Section C: getHead/getPT/getQT extracted via getD1.

      d1a : Deriv (atomic (eqn (ap1 getHead t) (ap1 Fst (ap1 getD1 t))))
      d1a = axComp Fst getD1 t

      d1b : Deriv (atomic (eqn (ap1 Fst (ap1 getD1 t)) (ap1 Fst t1)))
      d1b = cong1 Fst getD1T

      getHeadT : Deriv (atomic (eqn (ap1 getHead t) tagImpT))
      getHeadT = ruleTrans d1a (ruleTrans d1b fstT1)

      d2a : Deriv (atomic (eqn (ap1 getPT t)
                                (ap1 Fst (ap1 (Comp Snd getD1) t))))
      d2a = axComp Fst (Comp Snd getD1) t

      d2b : Deriv (atomic (eqn (ap1 (Comp Snd getD1) t)
                                (ap1 Snd (ap1 getD1 t))))
      d2b = axComp Snd getD1 t

      d2c : Deriv (atomic (eqn (ap1 Snd (ap1 getD1 t)) (ap1 Snd t1)))
      d2c = cong1 Snd getD1T

      d2bc : Deriv (atomic (eqn (ap1 (Comp Snd getD1) t) (ap1 Snd t1)))
      d2bc = ruleTrans d2b d2c

      d2d : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd getD1) t))
                                (ap1 Fst (ap1 Snd t1))))
      d2d = cong1 Fst d2bc

      getPTT : Deriv (atomic (eqn (ap1 getPT t) pT))
      getPTT = ruleTrans d2a (ruleTrans d2d fstSndT1)

      d3a : Deriv (atomic (eqn (ap1 getQT t)
                                (ap1 Snd (ap1 (Comp Snd getD1) t))))
      d3a = axComp Snd (Comp Snd getD1) t

      d3d : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd getD1) t))
                                (ap1 Snd (ap1 Snd t1))))
      d3d = cong1 Snd d2bc

      getQTT : Deriv (atomic (eqn (ap1 getQT t) qT))
      getQTT = ruleTrans d3a (ruleTrans d3d sndSndT1)

      ----------------------------------------------------------------
      -- Section D: outerCheckF1 t = O.

      e1 : Deriv (atomic (eqn (ap1 outerCheckF1 t)
                              (ap2 TreeEq (ap1 getHead t)
                                          (ap1 (KT tagImpT) t))))
      e1 = axComp2 TreeEq getHead (KT tagImpT) t

      e2 : Deriv (atomic (eqn (ap1 (KT tagImpT) t) tagImpT))
      e2 = axKT tagImp tagImp_isValue t

      e3a : Deriv (atomic (eqn (ap2 TreeEq (ap1 getHead t)
                                            (ap1 (KT tagImpT) t))
                                (ap2 TreeEq tagImpT (ap1 (KT tagImpT) t))))
      e3a = congL TreeEq (ap1 (KT tagImpT) t) getHeadT

      e3b : Deriv (atomic (eqn (ap2 TreeEq tagImpT (ap1 (KT tagImpT) t))
                                (ap2 TreeEq tagImpT tagImpT)))
      e3b = congR TreeEq tagImpT e2

      e3 : Deriv (atomic (eqn (ap2 TreeEq (ap1 getHead t)
                                            (ap1 (KT tagImpT) t))
                              (ap2 TreeEq tagImpT tagImpT)))
      e3 = ruleTrans e3a e3b

      e4 : Deriv (atomic (eqn (ap2 TreeEq tagImpT tagImpT) O))
      e4 = treeEqRed tagImp tagImp_isValue tagImp tagImp_isValue

      outerCheckO : Deriv (atomic (eqn (ap1 outerCheckF1 t) O))
      outerCheckO = ruleTrans e1 (ruleTrans e3 e4)

      ----------------------------------------------------------------
      -- Section E: innerCheckF1 t = O.

      f1 : Deriv (atomic (eqn (ap1 innerCheckF1 t)
                              (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t))))
      f1 = axComp2 TreeEq getD2 getPT t

      f2a : Deriv (atomic (eqn (ap2 TreeEq (ap1 getD2 t)(ap1 getPT t))
                                (ap2 TreeEq pT (ap1 getPT t))))
      f2a = congL TreeEq (ap1 getPT t) getD2TpT

      f2b : Deriv (atomic (eqn (ap2 TreeEq pT (ap1 getPT t))
                                (ap2 TreeEq pT pT)))
      f2b = congR TreeEq pT getPTT

      f2 : Deriv (atomic (eqn (ap2 TreeEq (ap1 getD2 t)(ap1 getPT t))
                              (ap2 TreeEq pT pT)))
      f2 = ruleTrans f2a f2b

      innerCheckO : Deriv (atomic (eqn (ap1 innerCheckF1 t) O))
      innerCheckO = ruleTrans f1 (ruleTrans f2 innerRefl)

      ----------------------------------------------------------------
      -- Section F: innerOrFalsePairF1 t = Pair O falseT.

      g1 : Deriv (atomic (eqn (ap1 innerOrFalsePairF1 t)
                              (ap2 Pair (ap1 innerCheckF1 t)
                                        (ap1 (KT falseT) t))))
      g1 = axComp2 Pair innerCheckF1 (KT falseT) t

      g2 : Deriv (atomic (eqn (ap1 (KT falseT) t) falseT))
      g2 = axKT (nd lf lf) (valNd lf lf valO valO) t

      g3a : Deriv (atomic (eqn (ap2 Pair (ap1 innerCheckF1 t)
                                          (ap1 (KT falseT) t))
                                (ap2 Pair O (ap1 (KT falseT) t))))
      g3a = congL Pair (ap1 (KT falseT) t) innerCheckO

      g3b : Deriv (atomic (eqn (ap2 Pair O (ap1 (KT falseT) t))
                                (ap2 Pair O falseT)))
      g3b = congR Pair O g2

      innerOrFalsePairEq :
        Deriv (atomic (eqn (ap1 innerOrFalsePairF1 t)
                            (ap2 Pair O falseT)))
      innerOrFalsePairEq = ruleTrans g1 (ruleTrans g3a g3b)

      ----------------------------------------------------------------
      -- Section G: ccF1 t = O.

      h1 : Deriv (atomic (eqn (ap1 ccF1 t)
                              (ap2 IfLf (ap1 outerCheckF1 t)
                                        (ap1 innerOrFalsePairF1 t))))
      h1 = axComp2 IfLf outerCheckF1 innerOrFalsePairF1 t

      h2a : Deriv (atomic (eqn (ap2 IfLf (ap1 outerCheckF1 t)
                                          (ap1 innerOrFalsePairF1 t))
                                (ap2 IfLf O (ap1 innerOrFalsePairF1 t))))
      h2a = congL IfLf (ap1 innerOrFalsePairF1 t) outerCheckO

      h2b : Deriv (atomic (eqn (ap2 IfLf O (ap1 innerOrFalsePairF1 t))
                                (ap2 IfLf O (ap2 Pair O falseT))))
      h2b = congR IfLf O innerOrFalsePairEq

      h3 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair O falseT)) O))
      h3 = axIfLfL O falseT

      ccO : Deriv (atomic (eqn (ap1 ccF1 t) O))
      ccO = ruleTrans h1 (ruleTrans h2a (ruleTrans h2b h3))

      ----------------------------------------------------------------
      -- Section H: qfailPairF1 t = Pair qT codeTriv.

      i1 : Deriv (atomic (eqn (ap1 qfailPairF1 t)
                              (ap2 Pair (ap1 getQT t)
                                        (ap1 (KT codeTriv) t))))
      i1 = axComp2 Pair getQT (KT codeTriv) t

      i2 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      i2 = axKT (nd lf lf) (valNd lf lf valO valO) t

      i3a : Deriv (atomic (eqn (ap2 Pair (ap1 getQT t)
                                          (ap1 (KT codeTriv) t))
                                (ap2 Pair qT (ap1 (KT codeTriv) t))))
      i3a = congL Pair (ap1 (KT codeTriv) t) getQTT

      i3b : Deriv (atomic (eqn (ap2 Pair qT (ap1 (KT codeTriv) t))
                                (ap2 Pair qT codeTriv)))
      i3b = congR Pair qT i2

      qfailPairEq :
        Deriv (atomic (eqn (ap1 qfailPairF1 t) (ap2 Pair qT codeTriv)))
      qfailPairEq = ruleTrans i1 (ruleTrans i3a i3b)

      ----------------------------------------------------------------
      -- Section I: verifierF1 t = qT.

      j1 : Deriv (atomic (eqn (ap1 verifierF1 t)
                              (ap2 IfLf (ap1 ccF1 t)
                                        (ap1 qfailPairF1 t))))
      j1 = axComp2 IfLf ccF1 qfailPairF1 t

      j2a : Deriv (atomic (eqn (ap2 IfLf (ap1 ccF1 t)(ap1 qfailPairF1 t))
                                (ap2 IfLf O (ap1 qfailPairF1 t))))
      j2a = congL IfLf (ap1 qfailPairF1 t) ccO

      j2b : Deriv (atomic (eqn (ap2 IfLf O (ap1 qfailPairF1 t))
                                (ap2 IfLf O (ap2 Pair qT codeTriv))))
      j2b = congR IfLf O qfailPairEq

      j3 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair qT codeTriv)) qT))
      j3 = axIfLfL qT codeTriv

      verifierEq : Deriv (atomic (eqn (ap1 verifierF1 t) qT))
      verifierEq = ruleTrans j1 (ruleTrans j2a (ruleTrans j2b j3))

      ----------------------------------------------------------------
      -- Section J: body_mp_v(a, bb) = qT  via axPost.

      k1 : Deriv (atomic (eqn (ap2 body_mp_v a bb) (ap1 verifierF1 t)))
      k1 = axPost verifierF1 Pair a bb

  in ruleTrans k1 verifierEq

----------------------------------------------------------------------
-- Lifted variant: same theorem under an arbitrary auxiliary formula P.
--
-- All hypotheses are lifted under P; result is lifted under P.  Used
-- by  thmTDispMp_param_l  (BRA2.Thm.ThmT) to close the verifying mp
-- dispatcher when consumers carry their inner-check witnesses under
-- a proof-recovery formula like  PrAtX x = atomic (eqn (thmT x) cG) .
--
-- The proof mirrors  body_mp_v_eval_pass  step-for-step, replacing
-- each closed   ruleTrans / cong / axiom  with the corresponding
-- lifted helper from BRA2.Thm.EvalHelpers .  Closed sub-derivations
-- (axioms, congruences over closed equations) are still closed; they
-- get promoted via   liftAxiom P  at the points where they meet the
-- lifted chain.

body_mp_v_eval_pass_l :
  (P : Formula) (a bb : Term) (t1 t2 pT qT : Term) ->
  Deriv (P imp atomic (eqn (ap1 Snd bb) (ap2 Pair t1 t2))) ->
  Deriv (P imp atomic (eqn t1 (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
  Deriv (P imp atomic (eqn t2 pT)) ->
  Deriv (P imp atomic (eqn (ap2 TreeEq pT pT) O)) ->
  Deriv (P imp atomic (eqn (ap2 body_mp_v a bb) qT))
body_mp_v_eval_pass_l P a bb t1 t2 pT qT distHL d1L dhL innerReflL =
  let
      t : Term
      t = ap2 Pair a bb

      ----------------------------------------------------------------
      -- Section A.

      a1L : Deriv (P imp atomic (eqn (ap1 Snd t) bb))
      a1L = liftAxiom P (axSnd a bb)

      a2L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd t)) (ap1 Snd bb)))
      a2L = liftedCong1 P Snd (ap1 Snd t) bb a1L

      a3L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd t)) (ap2 Pair t1 t2)))
      a3L = liftedRuleTrans P (ap1 Snd (ap1 Snd t)) (ap1 Snd bb) (ap2 Pair t1 t2)
              a2L distHL

      a4 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap1 Snd (ap1 Snd t))))
      a4 = axComp Snd Snd t

      a5L : Deriv (P imp atomic (eqn (ap1 (Comp Snd Snd) t) (ap2 Pair t1 t2)))
      a5L = liftedRuleTrans P (ap1 (Comp Snd Snd) t) (ap1 Snd (ap1 Snd t))
              (ap2 Pair t1 t2)
              (liftAxiom P a4) a3L

      a6 : Deriv (atomic (eqn (ap1 getD1 t) (ap1 Fst (ap1 (Comp Snd Snd) t))))
      a6 = axComp Fst (Comp Snd Snd) t

      a7L : Deriv (P imp atomic (eqn (ap1 Fst (ap1 (Comp Snd Snd) t))
                                       (ap1 Fst (ap2 Pair t1 t2))))
      a7L = liftedCong1 P Fst (ap1 (Comp Snd Snd) t) (ap2 Pair t1 t2) a5L

      a8 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair t1 t2)) t1))
      a8 = axFst t1 t2

      getD1TL : Deriv (P imp atomic (eqn (ap1 getD1 t) t1))
      getD1TL = liftedRuleTrans P (ap1 getD1 t) (ap1 Fst (ap1 (Comp Snd Snd) t)) t1
                  (liftAxiom P a6)
                  (liftedRuleTrans P (ap1 Fst (ap1 (Comp Snd Snd) t))
                                     (ap1 Fst (ap2 Pair t1 t2)) t1
                     a7L (liftAxiom P a8))

      b1 : Deriv (atomic (eqn (ap1 getD2 t) (ap1 Snd (ap1 (Comp Snd Snd) t))))
      b1 = axComp Snd (Comp Snd Snd) t

      b2L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) t))
                                       (ap1 Snd (ap2 Pair t1 t2))))
      b2L = liftedCong1 P Snd (ap1 (Comp Snd Snd) t) (ap2 Pair t1 t2) a5L

      b3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair t1 t2)) t2))
      b3 = axSnd t1 t2

      getD2TL : Deriv (P imp atomic (eqn (ap1 getD2 t) t2))
      getD2TL = liftedRuleTrans P (ap1 getD2 t) (ap1 Snd (ap1 (Comp Snd Snd) t)) t2
                  (liftAxiom P b1)
                  (liftedRuleTrans P (ap1 Snd (ap1 (Comp Snd Snd) t))
                                     (ap1 Snd (ap2 Pair t1 t2)) t2
                     b2L (liftAxiom P b3))

      getD2TpTL : Deriv (P imp atomic (eqn (ap1 getD2 t) pT))
      getD2TpTL = liftedRuleTrans P (ap1 getD2 t) t2 pT getD2TL dhL

      ----------------------------------------------------------------
      -- Section B: extract through t1 = Pair tagImpT pqPair.

      tagImpT : Term
      tagImpT = reify tagImp

      pqPair : Term
      pqPair = ap2 Pair pT qT

      c1L : Deriv (P imp atomic (eqn (ap1 Fst t1)
                                       (ap1 Fst (ap2 Pair tagImpT pqPair))))
      c1L = liftedCong1 P Fst t1 (ap2 Pair tagImpT pqPair) d1L

      c2 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagImpT pqPair)) tagImpT))
      c2 = axFst tagImpT pqPair

      fstT1L : Deriv (P imp atomic (eqn (ap1 Fst t1) tagImpT))
      fstT1L = liftedRuleTrans P (ap1 Fst t1) (ap1 Fst (ap2 Pair tagImpT pqPair))
                 tagImpT c1L (liftAxiom P c2)

      c3L : Deriv (P imp atomic (eqn (ap1 Snd t1)
                                       (ap1 Snd (ap2 Pair tagImpT pqPair))))
      c3L = liftedCong1 P Snd t1 (ap2 Pair tagImpT pqPair) d1L

      c4 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tagImpT pqPair)) pqPair))
      c4 = axSnd tagImpT pqPair

      sndT1L : Deriv (P imp atomic (eqn (ap1 Snd t1) pqPair))
      sndT1L = liftedRuleTrans P (ap1 Snd t1) (ap1 Snd (ap2 Pair tagImpT pqPair))
                 pqPair c3L (liftAxiom P c4)

      c5L : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Snd t1)) (ap1 Fst pqPair)))
      c5L = liftedCong1 P Fst (ap1 Snd t1) pqPair sndT1L

      c6 : Deriv (atomic (eqn (ap1 Fst pqPair) pT))
      c6 = axFst pT qT

      fstSndT1L : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Snd t1)) pT))
      fstSndT1L = liftedRuleTrans P (ap1 Fst (ap1 Snd t1)) (ap1 Fst pqPair) pT
                    c5L (liftAxiom P c6)

      c7L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd t1)) (ap1 Snd pqPair)))
      c7L = liftedCong1 P Snd (ap1 Snd t1) pqPair sndT1L

      c8 : Deriv (atomic (eqn (ap1 Snd pqPair) qT))
      c8 = axSnd pT qT

      sndSndT1L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd t1)) qT))
      sndSndT1L = liftedRuleTrans P (ap1 Snd (ap1 Snd t1)) (ap1 Snd pqPair) qT
                    c7L (liftAxiom P c8)

      ----------------------------------------------------------------
      -- Section C: getHead/getPT/getQT extracted via getD1.

      d1aA : Deriv (atomic (eqn (ap1 getHead t) (ap1 Fst (ap1 getD1 t))))
      d1aA = axComp Fst getD1 t

      d1bL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 getD1 t)) (ap1 Fst t1)))
      d1bL = liftedCong1 P Fst (ap1 getD1 t) t1 getD1TL

      getHeadTL : Deriv (P imp atomic (eqn (ap1 getHead t) tagImpT))
      getHeadTL = liftedRuleTrans P (ap1 getHead t) (ap1 Fst (ap1 getD1 t)) tagImpT
                    (liftAxiom P d1aA)
                    (liftedRuleTrans P (ap1 Fst (ap1 getD1 t)) (ap1 Fst t1) tagImpT
                       d1bL fstT1L)

      d2aA : Deriv (atomic (eqn (ap1 getPT t)
                                 (ap1 Fst (ap1 (Comp Snd getD1) t))))
      d2aA = axComp Fst (Comp Snd getD1) t

      d2bA : Deriv (atomic (eqn (ap1 (Comp Snd getD1) t)
                                 (ap1 Snd (ap1 getD1 t))))
      d2bA = axComp Snd getD1 t

      d2cL : Deriv (P imp atomic (eqn (ap1 Snd (ap1 getD1 t)) (ap1 Snd t1)))
      d2cL = liftedCong1 P Snd (ap1 getD1 t) t1 getD1TL

      d2bcL : Deriv (P imp atomic (eqn (ap1 (Comp Snd getD1) t) (ap1 Snd t1)))
      d2bcL = liftedRuleTrans P (ap1 (Comp Snd getD1) t) (ap1 Snd (ap1 getD1 t))
                (ap1 Snd t1) (liftAxiom P d2bA) d2cL

      d2dL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 (Comp Snd getD1) t))
                                        (ap1 Fst (ap1 Snd t1))))
      d2dL = liftedCong1 P Fst (ap1 (Comp Snd getD1) t) (ap1 Snd t1) d2bcL

      getPTTL : Deriv (P imp atomic (eqn (ap1 getPT t) pT))
      getPTTL = liftedRuleTrans P (ap1 getPT t)
                  (ap1 Fst (ap1 (Comp Snd getD1) t)) pT
                  (liftAxiom P d2aA)
                  (liftedRuleTrans P (ap1 Fst (ap1 (Comp Snd getD1) t))
                                     (ap1 Fst (ap1 Snd t1)) pT
                     d2dL fstSndT1L)

      d3aA : Deriv (atomic (eqn (ap1 getQT t)
                                 (ap1 Snd (ap1 (Comp Snd getD1) t))))
      d3aA = axComp Snd (Comp Snd getD1) t

      d3dL : Deriv (P imp atomic (eqn (ap1 Snd (ap1 (Comp Snd getD1) t))
                                        (ap1 Snd (ap1 Snd t1))))
      d3dL = liftedCong1 P Snd (ap1 (Comp Snd getD1) t) (ap1 Snd t1) d2bcL

      getQTTL : Deriv (P imp atomic (eqn (ap1 getQT t) qT))
      getQTTL = liftedRuleTrans P (ap1 getQT t)
                  (ap1 Snd (ap1 (Comp Snd getD1) t)) qT
                  (liftAxiom P d3aA)
                  (liftedRuleTrans P (ap1 Snd (ap1 (Comp Snd getD1) t))
                                     (ap1 Snd (ap1 Snd t1)) qT
                     d3dL sndSndT1L)

      ----------------------------------------------------------------
      -- Section D: outerCheckF1 t = O.

      e1A : Deriv (atomic (eqn (ap1 outerCheckF1 t)
                                (ap2 TreeEq (ap1 getHead t)
                                            (ap1 (KT tagImpT) t))))
      e1A = axComp2 TreeEq getHead (KT tagImpT) t

      e2A : Deriv (atomic (eqn (ap1 (KT tagImpT) t) tagImpT))
      e2A = axKT tagImp tagImp_isValue t

      e3aL : Deriv (P imp atomic (eqn (ap2 TreeEq (ap1 getHead t)
                                                    (ap1 (KT tagImpT) t))
                                        (ap2 TreeEq tagImpT (ap1 (KT tagImpT) t))))
      e3aL = liftedCongL P TreeEq (ap1 getHead t) tagImpT
               (ap1 (KT tagImpT) t) getHeadTL

      e3bA : Deriv (atomic (eqn (ap2 TreeEq tagImpT (ap1 (KT tagImpT) t))
                                 (ap2 TreeEq tagImpT tagImpT)))
      e3bA = congR TreeEq tagImpT e2A

      e3L : Deriv (P imp atomic (eqn (ap2 TreeEq (ap1 getHead t)
                                                   (ap1 (KT tagImpT) t))
                                       (ap2 TreeEq tagImpT tagImpT)))
      e3L = liftedRuleTrans P (ap2 TreeEq (ap1 getHead t) (ap1 (KT tagImpT) t))
              (ap2 TreeEq tagImpT (ap1 (KT tagImpT) t))
              (ap2 TreeEq tagImpT tagImpT) e3aL (liftAxiom P e3bA)

      e4A : Deriv (atomic (eqn (ap2 TreeEq tagImpT tagImpT) O))
      e4A = treeEqRed tagImp tagImp_isValue tagImp tagImp_isValue

      outerCheckOL : Deriv (P imp atomic (eqn (ap1 outerCheckF1 t) O))
      outerCheckOL = liftedRuleTrans P (ap1 outerCheckF1 t)
                       (ap2 TreeEq (ap1 getHead t) (ap1 (KT tagImpT) t)) O
                       (liftAxiom P e1A)
                       (liftedRuleTrans P
                          (ap2 TreeEq (ap1 getHead t) (ap1 (KT tagImpT) t))
                          (ap2 TreeEq tagImpT tagImpT) O
                          e3L (liftAxiom P e4A))

      ----------------------------------------------------------------
      -- Section E: innerCheckF1 t = O.

      f1A : Deriv (atomic (eqn (ap1 innerCheckF1 t)
                                (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t))))
      f1A = axComp2 TreeEq getD2 getPT t

      f2aL : Deriv (P imp atomic (eqn (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t))
                                        (ap2 TreeEq pT (ap1 getPT t))))
      f2aL = liftedCongL P TreeEq (ap1 getD2 t) pT (ap1 getPT t) getD2TpTL

      f2bL : Deriv (P imp atomic (eqn (ap2 TreeEq pT (ap1 getPT t))
                                        (ap2 TreeEq pT pT)))
      f2bL = liftedCongR P TreeEq (ap1 getPT t) pT pT getPTTL

      f2L : Deriv (P imp atomic (eqn (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t))
                                       (ap2 TreeEq pT pT)))
      f2L = liftedRuleTrans P (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t))
              (ap2 TreeEq pT (ap1 getPT t)) (ap2 TreeEq pT pT) f2aL f2bL

      innerCheckOL : Deriv (P imp atomic (eqn (ap1 innerCheckF1 t) O))
      innerCheckOL = liftedRuleTrans P (ap1 innerCheckF1 t)
                       (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t)) O
                       (liftAxiom P f1A)
                       (liftedRuleTrans P (ap2 TreeEq (ap1 getD2 t) (ap1 getPT t))
                                          (ap2 TreeEq pT pT) O
                          f2L innerReflL)

      ----------------------------------------------------------------
      -- Section F: innerOrFalsePairF1 t = Pair O falseT.

      g1A : Deriv (atomic (eqn (ap1 innerOrFalsePairF1 t)
                                (ap2 Pair (ap1 innerCheckF1 t)
                                          (ap1 (KT falseT) t))))
      g1A = axComp2 Pair innerCheckF1 (KT falseT) t

      g2A : Deriv (atomic (eqn (ap1 (KT falseT) t) falseT))
      g2A = axKT (nd lf lf) (valNd lf lf valO valO) t

      g3aL : Deriv (P imp atomic (eqn (ap2 Pair (ap1 innerCheckF1 t)
                                                  (ap1 (KT falseT) t))
                                        (ap2 Pair O (ap1 (KT falseT) t))))
      g3aL = liftedCongL P Pair (ap1 innerCheckF1 t) O
               (ap1 (KT falseT) t) innerCheckOL

      g3bA : Deriv (atomic (eqn (ap2 Pair O (ap1 (KT falseT) t))
                                 (ap2 Pair O falseT)))
      g3bA = congR Pair O g2A

      innerOrFalsePairEqL :
        Deriv (P imp atomic (eqn (ap1 innerOrFalsePairF1 t)
                                  (ap2 Pair O falseT)))
      innerOrFalsePairEqL = liftedRuleTrans P (ap1 innerOrFalsePairF1 t)
        (ap2 Pair (ap1 innerCheckF1 t) (ap1 (KT falseT) t))
        (ap2 Pair O falseT)
        (liftAxiom P g1A)
        (liftedRuleTrans P
           (ap2 Pair (ap1 innerCheckF1 t) (ap1 (KT falseT) t))
           (ap2 Pair O (ap1 (KT falseT) t))
           (ap2 Pair O falseT)
           g3aL (liftAxiom P g3bA))

      ----------------------------------------------------------------
      -- Section G: ccF1 t = O.

      h1A : Deriv (atomic (eqn (ap1 ccF1 t)
                                (ap2 IfLf (ap1 outerCheckF1 t)
                                          (ap1 innerOrFalsePairF1 t))))
      h1A = axComp2 IfLf outerCheckF1 innerOrFalsePairF1 t

      h2aL : Deriv (P imp atomic (eqn
        (ap2 IfLf (ap1 outerCheckF1 t) (ap1 innerOrFalsePairF1 t))
        (ap2 IfLf O (ap1 innerOrFalsePairF1 t))))
      h2aL = liftedCongL P IfLf (ap1 outerCheckF1 t) O
               (ap1 innerOrFalsePairF1 t) outerCheckOL

      h2bL : Deriv (P imp atomic (eqn
        (ap2 IfLf O (ap1 innerOrFalsePairF1 t))
        (ap2 IfLf O (ap2 Pair O falseT))))
      h2bL = liftedCongR P IfLf (ap1 innerOrFalsePairF1 t) (ap2 Pair O falseT) O
               innerOrFalsePairEqL

      h3A : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair O falseT)) O))
      h3A = axIfLfL O falseT

      ccOL : Deriv (P imp atomic (eqn (ap1 ccF1 t) O))
      ccOL = liftedRuleTrans P (ap1 ccF1 t)
        (ap2 IfLf (ap1 outerCheckF1 t) (ap1 innerOrFalsePairF1 t)) O
        (liftAxiom P h1A)
        (liftedRuleTrans P
          (ap2 IfLf (ap1 outerCheckF1 t) (ap1 innerOrFalsePairF1 t))
          (ap2 IfLf O (ap1 innerOrFalsePairF1 t)) O
          h2aL
          (liftedRuleTrans P
            (ap2 IfLf O (ap1 innerOrFalsePairF1 t))
            (ap2 IfLf O (ap2 Pair O falseT)) O
            h2bL (liftAxiom P h3A)))

      ----------------------------------------------------------------
      -- Section H: qfailPairF1 t = Pair qT codeTriv.

      i1A : Deriv (atomic (eqn (ap1 qfailPairF1 t)
                                (ap2 Pair (ap1 getQT t)
                                          (ap1 (KT codeTriv) t))))
      i1A = axComp2 Pair getQT (KT codeTriv) t

      i2A : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      i2A = axKT (nd lf lf) (valNd lf lf valO valO) t

      i3aL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getQT t) (ap1 (KT codeTriv) t))
        (ap2 Pair qT (ap1 (KT codeTriv) t))))
      i3aL = liftedCongL P Pair (ap1 getQT t) qT (ap1 (KT codeTriv) t) getQTTL

      i3bA : Deriv (atomic (eqn (ap2 Pair qT (ap1 (KT codeTriv) t))
                                 (ap2 Pair qT codeTriv)))
      i3bA = congR Pair qT i2A

      qfailPairEqL :
        Deriv (P imp atomic (eqn (ap1 qfailPairF1 t) (ap2 Pair qT codeTriv)))
      qfailPairEqL = liftedRuleTrans P (ap1 qfailPairF1 t)
        (ap2 Pair (ap1 getQT t) (ap1 (KT codeTriv) t)) (ap2 Pair qT codeTriv)
        (liftAxiom P i1A)
        (liftedRuleTrans P
          (ap2 Pair (ap1 getQT t) (ap1 (KT codeTriv) t))
          (ap2 Pair qT (ap1 (KT codeTriv) t))
          (ap2 Pair qT codeTriv)
          i3aL (liftAxiom P i3bA))

      ----------------------------------------------------------------
      -- Section I: verifierF1 t = qT.

      j1A : Deriv (atomic (eqn (ap1 verifierF1 t)
                                (ap2 IfLf (ap1 ccF1 t)
                                          (ap1 qfailPairF1 t))))
      j1A = axComp2 IfLf ccF1 qfailPairF1 t

      j2aL : Deriv (P imp atomic (eqn
        (ap2 IfLf (ap1 ccF1 t) (ap1 qfailPairF1 t))
        (ap2 IfLf O (ap1 qfailPairF1 t))))
      j2aL = liftedCongL P IfLf (ap1 ccF1 t) O (ap1 qfailPairF1 t) ccOL

      j2bL : Deriv (P imp atomic (eqn
        (ap2 IfLf O (ap1 qfailPairF1 t))
        (ap2 IfLf O (ap2 Pair qT codeTriv))))
      j2bL = liftedCongR P IfLf (ap1 qfailPairF1 t) (ap2 Pair qT codeTriv) O
               qfailPairEqL

      j3A : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair qT codeTriv)) qT))
      j3A = axIfLfL qT codeTriv

      verifierEqL : Deriv (P imp atomic (eqn (ap1 verifierF1 t) qT))
      verifierEqL = liftedRuleTrans P (ap1 verifierF1 t)
        (ap2 IfLf (ap1 ccF1 t) (ap1 qfailPairF1 t)) qT
        (liftAxiom P j1A)
        (liftedRuleTrans P
          (ap2 IfLf (ap1 ccF1 t) (ap1 qfailPairF1 t))
          (ap2 IfLf O (ap1 qfailPairF1 t)) qT
          j2aL
          (liftedRuleTrans P
            (ap2 IfLf O (ap1 qfailPairF1 t))
            (ap2 IfLf O (ap2 Pair qT codeTriv)) qT
            j2bL (liftAxiom P j3A)))

      ----------------------------------------------------------------
      -- Section J.

      k1A : Deriv (atomic (eqn (ap2 body_mp_v a bb) (ap1 verifierF1 t)))
      k1A = axPost verifierF1 Pair a bb

  in liftedRuleTrans P (ap2 body_mp_v a bb) (ap1 verifierF1 t) qT
       (liftAxiom P k1A) verifierEqL
