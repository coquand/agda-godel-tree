{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SoundCongLVProof
--
-- Evaluation proof for body_congL_v.  Hypotheses:
--   * payGExt : ap1 Fst (ap1 Fst (ap1 Snd a)) = payG
--   * payXExt : ap1 Snd (ap1 Fst (ap1 Snd a)) = payX
--   * ihShape : ap1 Snd (ap1 Snd bb) = ap2 Pair fp sp
-- Conclusion:
--   ap2 body_congL_v a bb =
--     ap2 Pair (ap2 Pair tagAp2 (ap2 Pair payG (ap2 Pair fp payX)))
--               (ap2 Pair tagAp2 (ap2 Pair payG (ap2 Pair sp payX))).

module BRA2.SoundCongLVProof where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.EvalHelpers
  using ( liftAxiom ; liftAxiomTwo
        ; liftedRuleTrans ; liftedRuleTransTwo
        ; liftedCong1 ; liftedCong1Two
        ; liftedCongL ; liftedCongLTwo
        ; liftedCongR ; liftedCongRTwo )

----------------------------------------------------------------------
-- Body and helpers (formerly in BRA2.SoundCongLProto).

----------------------------------------------------------------------
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Snd a            = Snd(Fst t)
--   Fst(Snd a)       = Fst(Snd(Fst t))   -- this is (Pair payG payX)
--   Fst(Fst(Snd a))  = Fst(Fst(Snd(Fst t))) = payG
--   Snd(Fst(Snd a))  = Snd(Fst(Snd(Fst t))) = payX
--   Snd(Snd bb)      = Snd(Snd(Snd t))   -- the IH

getInnerArgs : Fun1
getInnerArgs = Comp Fst (Comp Snd Fst)
  -- ap1 t = Fst(Snd(Fst t)) = Fst(Snd a) = (Pair payG payX)

getPayG : Fun1
getPayG = Comp Fst getInnerArgs

getPayX : Fun1
getPayX = Comp Snd getInnerArgs

getIH : Fun1
getIH = Comp Snd (Comp Snd Snd)

getFstIH : Fun1
getFstIH = Comp Fst getIH

getSndIH : Fun1
getSndIH = Comp Snd getIH

----------------------------------------------------------------------
-- Half-assemblers : Pair tagAp2 (Pair payG (Pair partIH payX))
-- where partIH is either Fst(IH) or Snd(IH).

assemblyHalfL : Fun1 -> Fun1
assemblyHalfL getPart =
  Comp2 Pair (KT (reify tagAp2))
    (Comp2 Pair getPayG
      (Comp2 Pair getPart getPayX))

assemblyLeftF1 : Fun1
assemblyLeftF1 = assemblyHalfL getFstIH

assemblyRightF1 : Fun1
assemblyRightF1 = assemblyHalfL getSndIH

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair assemblyLeftF1 assemblyRightF1

verifierCLF1 : Fun1
verifierCLF1 =
  Comp2 IfLf getIH
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

body_congL_v : Fun2
body_congL_v = Post verifierCLF1 Pair
----------------------------------------------------------------------
-- Helper: extract Snd(Fst t) = Snd a (via getInnerArgs's intermediate).
-- Reused for payG, payX, both built atop getInnerArgs.

private
  getInnerArgsEq : (a bb : Term) ->
    Deriv (atomic (eqn (ap1 getInnerArgs (ap2 Pair a bb)) (ap1 Fst (ap1 Snd a))))
  getInnerArgsEq a bb =
    let t = ap2 Pair a bb
        e1 : Deriv (atomic (eqn (ap1 getInnerArgs t)
                                  (ap1 Fst (ap1 (Comp Snd Fst) t))))
        e1 = axComp Fst (Comp Snd Fst) t
        e2 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) t) (ap1 Snd (ap1 Fst t))))
        e2 = axComp Snd Fst t
        e3 : Deriv (atomic (eqn (ap1 Fst t) a))
        e3 = axFst a bb
        e4 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst t)) (ap1 Snd a)))
        e4 = cong1 Snd e3
        e5 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) t) (ap1 Snd a)))
        e5 = ruleTrans e2 e4
        e6 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Fst) t))
                                  (ap1 Fst (ap1 Snd a))))
        e6 = cong1 Fst e5
    in ruleTrans e1 e6

  getIHEq : (a bb : Term) ->
    Deriv (atomic (eqn (ap1 getIH (ap2 Pair a bb)) (ap1 Snd (ap1 Snd bb))))
  getIHEq a bb =
    let t = ap2 Pair a bb
        e1 : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 (Comp Snd Snd) t))))
        e1 = axComp Snd (Comp Snd Snd) t
        e2 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap1 Snd (ap1 Snd t))))
        e2 = axComp Snd Snd t
        e3 : Deriv (atomic (eqn (ap1 Snd t) bb))
        e3 = axSnd a bb
        e4 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t)) (ap1 Snd bb)))
        e4 = cong1 Snd e3
        e5 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap1 Snd bb)))
        e5 = ruleTrans e2 e4
        e6 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) t))
                                  (ap1 Snd (ap1 Snd bb))))
        e6 = cong1 Snd e5
    in ruleTrans e1 e6

----------------------------------------------------------------------
body_congL_v_eval_pass :
  (a bb : Term) (payG payX fp sp : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG)) ->
  Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX)) ->
  Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp))) ->
  Deriv (atomic (eqn (ap2 body_congL_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair fp payX)))
                                (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair sp payX))))))
body_congL_v_eval_pass a bb payG payX fp sp payGExt payXExt ihShape =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp2T : Term
      tagAp2T = reify tagAp2
      outLeft : Term
      outLeft = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair fp payX))
      outRight : Term
      outRight = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair sp payX))

      ----------------------------------------------------------------
      -- Section A: getPayG, getPayX equalities.

      innerArgsEq : Deriv (atomic (eqn (ap1 getInnerArgs t) (ap1 Fst (ap1 Snd a))))
      innerArgsEq = getInnerArgsEq a bb

      a1 : Deriv (atomic (eqn (ap1 getPayG t) (ap1 Fst (ap1 getInnerArgs t))))
      a1 = axComp Fst getInnerArgs t

      a2 : Deriv (atomic (eqn (ap1 Fst (ap1 getInnerArgs t))
                              (ap1 Fst (ap1 Fst (ap1 Snd a)))))
      a2 = cong1 Fst innerArgsEq

      payGEq : Deriv (atomic (eqn (ap1 getPayG t) payG))
      payGEq = ruleTrans a1 (ruleTrans a2 payGExt)

      b1 : Deriv (atomic (eqn (ap1 getPayX t) (ap1 Snd (ap1 getInnerArgs t))))
      b1 = axComp Snd getInnerArgs t

      b2 : Deriv (atomic (eqn (ap1 Snd (ap1 getInnerArgs t))
                              (ap1 Snd (ap1 Fst (ap1 Snd a)))))
      b2 = cong1 Snd innerArgsEq

      payXEq : Deriv (atomic (eqn (ap1 getPayX t) payX))
      payXEq = ruleTrans b1 (ruleTrans b2 payXExt)

      ----------------------------------------------------------------
      -- Section B: getIH = Pair fp sp; getFstIH = fp; getSndIH = sp.

      ihExtracted : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd bb))))
      ihExtracted = getIHEq a bb

      ihPair : Deriv (atomic (eqn (ap1 getIH t) (ap2 Pair fp sp)))
      ihPair = ruleTrans ihExtracted ihShape

      c1 : Deriv (atomic (eqn (ap1 getFstIH t) (ap1 Fst (ap1 getIH t))))
      c1 = axComp Fst getIH t
      c2 : Deriv (atomic (eqn (ap1 Fst (ap1 getIH t)) (ap1 Fst (ap2 Pair fp sp))))
      c2 = cong1 Fst ihPair
      c3 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair fp sp)) fp))
      c3 = axFst fp sp
      getFstIHEq : Deriv (atomic (eqn (ap1 getFstIH t) fp))
      getFstIHEq = ruleTrans c1 (ruleTrans c2 c3)

      d1 : Deriv (atomic (eqn (ap1 getSndIH t) (ap1 Snd (ap1 getIH t))))
      d1 = axComp Snd getIH t
      d2 : Deriv (atomic (eqn (ap1 Snd (ap1 getIH t)) (ap1 Snd (ap2 Pair fp sp))))
      d2 = cong1 Snd ihPair
      d3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair fp sp)) sp))
      d3 = axSnd fp sp
      getSndIHEq : Deriv (atomic (eqn (ap1 getSndIH t) sp))
      getSndIHEq = ruleTrans d1 (ruleTrans d2 d3)

      ----------------------------------------------------------------
      -- Section E: assemblyLeftF1 t = outLeft.
      --   assemblyLeftF1 = Comp2 Pair (KT tagAp2)
      --                       (Comp2 Pair getPayG
      --                          (Comp2 Pair getFstIH getPayX))

      e1 : Deriv (atomic (eqn (ap1 assemblyLeftF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getFstIH getPayX)) t))))
      e1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t

      ktTag : Deriv (atomic (eqn (ap1 (KT tagAp2T) t) tagAp2T))
      ktTag = axKT tagAp2 tagAp2_isValue t

      e2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getFstIH getPayX) t))))
      e2 = axComp2 Pair getPayG (Comp2 Pair getFstIH getPayX) t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getFstIH getPayX) t)
                              (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))))
      e3 = axComp2 Pair getFstIH getPayX t

      -- Reduce inner Pair: Pair (getFstIH t) (getPayX t) -> Pair fp payX.
      eInnerLA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))
        (ap2 Pair fp (ap1 getPayX t))))
      eInnerLA = congL Pair (ap1 getPayX t) getFstIHEq

      eInnerLB : Deriv (atomic (eqn (ap2 Pair fp (ap1 getPayX t))
                                     (ap2 Pair fp payX)))
      eInnerLB = congR Pair fp payXEq

      eInnerL : Deriv (atomic (eqn (ap1 (Comp2 Pair getFstIH getPayX) t)
                                    (ap2 Pair fp payX)))
      eInnerL = ruleTrans e3 (ruleTrans eInnerLA eInnerLB)

      -- Reduce middle Pair: Pair (getPayG t) (innerL) -> Pair payG (Pair fp payX).
      eMidLA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))))
      eMidLA = congL Pair (ap1 (Comp2 Pair getFstIH getPayX) t) payGEq

      eMidLB : Deriv (atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))
                                    (ap2 Pair payG (ap2 Pair fp payX))))
      eMidLB = congR Pair payG eInnerL

      eMidL : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                                  (ap2 Pair payG (ap2 Pair fp payX))))
      eMidL = ruleTrans e2 (ruleTrans eMidLA eMidLB)

      -- Outer: Pair tagAp2 (mid) -> outLeft.
      eOuterLA : Deriv (atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))))
      eOuterLA = congL Pair (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t) ktTag

      eOuterLB : Deriv (atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
        outLeft))
      eOuterLB = congR Pair tagAp2T eMidL

      assemblyLeftEq : Deriv (atomic (eqn (ap1 assemblyLeftF1 t) outLeft))
      assemblyLeftEq = ruleTrans e1 (ruleTrans eOuterLA eOuterLB)

      ----------------------------------------------------------------
      -- Section F: assemblyRightF1 t = outRight (mirror with sp).

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getSndIH getPayX)) t))))
      f1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t

      f2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getSndIH getPayX) t))))
      f2 = axComp2 Pair getPayG (Comp2 Pair getSndIH getPayX) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getSndIH getPayX) t)
                              (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))))
      f3 = axComp2 Pair getSndIH getPayX t

      fInnerRA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))
        (ap2 Pair sp (ap1 getPayX t))))
      fInnerRA = congL Pair (ap1 getPayX t) getSndIHEq

      fInnerRB : Deriv (atomic (eqn (ap2 Pair sp (ap1 getPayX t))
                                     (ap2 Pair sp payX)))
      fInnerRB = congR Pair sp payXEq

      fInnerR : Deriv (atomic (eqn (ap1 (Comp2 Pair getSndIH getPayX) t)
                                    (ap2 Pair sp payX)))
      fInnerR = ruleTrans f3 (ruleTrans fInnerRA fInnerRB)

      fMidRA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))))
      fMidRA = congL Pair (ap1 (Comp2 Pair getSndIH getPayX) t) payGEq

      fMidRB : Deriv (atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))
                                    (ap2 Pair payG (ap2 Pair sp payX))))
      fMidRB = congR Pair payG fInnerR

      fMidR : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                                  (ap2 Pair payG (ap2 Pair sp payX))))
      fMidR = ruleTrans f2 (ruleTrans fMidRA fMidRB)

      fOuterRA : Deriv (atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))))
      fOuterRA = congL Pair (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t) ktTag

      fOuterRB : Deriv (atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
        outRight))
      fOuterRB = congR Pair tagAp2T fMidR

      assemblyRightEq : Deriv (atomic (eqn (ap1 assemblyRightF1 t) outRight))
      assemblyRightEq = ruleTrans f1 (ruleTrans fOuterRA fOuterRB)

      ----------------------------------------------------------------
      -- Section G: doAssemblyF1 t = Pair outLeft outRight.

      g1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                              (ap2 Pair (ap1 assemblyLeftF1 t)
                                        (ap1 assemblyRightF1 t))))
      g1 = axComp2 Pair assemblyLeftF1 assemblyRightF1 t

      gA : Deriv (atomic (eqn (ap2 Pair (ap1 assemblyLeftF1 t)
                                         (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft (ap1 assemblyRightF1 t))))
      gA = congL Pair (ap1 assemblyRightF1 t) assemblyLeftEq

      gB : Deriv (atomic (eqn (ap2 Pair outLeft (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft outRight)))
      gB = congR Pair outLeft assemblyRightEq

      doAssemblyEq : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                                         (ap2 Pair outLeft outRight)))
      doAssemblyEq = ruleTrans g1 (ruleTrans gA gB)

      ----------------------------------------------------------------
      -- Section H: verifierCLF1 t reduces via axIfLfN.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      h1 : Deriv (atomic (eqn (ap1 verifierCLF1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      h1 = axComp2 IfLf getIH branchesF1 t

      h2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O)))
                (codeFormula_isValue (atomic (eqn O O))) t

      h4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
                              (ap2 Pair codeTriv (ap1 doAssemblyF1 t))))
      h4 = congL Pair (ap1 doAssemblyF1 t) h3

      h5 : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
                              (ap2 Pair codeTriv (ap2 Pair outLeft outRight))))
      h5 = congR Pair codeTriv doAssemblyEq

      branchesEq : Deriv (atomic (eqn (ap1 branchesF1 t)
                                       (ap2 Pair codeTriv (ap2 Pair outLeft outRight))))
      branchesEq = ruleTrans h2 (ruleTrans h4 h5)

      h6 : Deriv (atomic (eqn (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))))
      h6 = congL IfLf (ap1 branchesF1 t) ihPair

      h7 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))))
      h7 = congR IfLf (ap2 Pair fp sp) branchesEq

      h8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))
                              (ap2 Pair outLeft outRight)))
      h8 = axIfLfN fp sp codeTriv (ap2 Pair outLeft outRight)

      verifierEq : Deriv (atomic (eqn (ap1 verifierCLF1 t) (ap2 Pair outLeft outRight)))
      verifierEq = ruleTrans h1 (ruleTrans h6 (ruleTrans h7 h8))

      ----------------------------------------------------------------
      i1 : Deriv (atomic (eqn (ap2 body_congL_v a bb) (ap1 verifierCLF1 t)))
      i1 = axPost verifierCLF1 Pair a bb
  in ruleTrans i1 verifierEq

----------------------------------------------------------------------
-- Helpers (closed): the closed inner-args extractors  getInnerArgsEq /
-- getIHEq  are reused under  liftAxiom P  in the lifted variants below.
-- We keep them private to this module.

----------------------------------------------------------------------
-- Lifted variant: same theorem under an arbitrary auxiliary formula P.
--
-- Closed axioms (axComp, axFst, axSnd, axKT, axLift, axPost, axIfLfN,
-- axRefl) are promoted via  liftAxiom P ; chained equalities use
-- liftedRuleTrans / liftedCong1 / liftedCongL / liftedCongR.

body_congL_v_eval_pass_l :
  (P : Formula) (a bb : Term) (payG payX fp sp : Term) ->
  Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG)) ->
  Deriv (P imp atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX)) ->
  Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp))) ->
  Deriv (P imp atomic (eqn (ap2 body_congL_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair fp payX)))
                                (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair sp payX))))))
body_congL_v_eval_pass_l P a bb payG payX fp sp payGExtL payXExtL ihShapeL =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp2T : Term
      tagAp2T = reify tagAp2
      outLeft : Term
      outLeft = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair fp payX))
      outRight : Term
      outRight = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair sp payX))

      ----------------------------------------------------------------
      -- Section A (lifted): payGEqL, payXEqL.
      --
      -- innerArgsEq is closed; lift it via liftAxiom P.

      innerArgsEq : Deriv (atomic (eqn (ap1 getInnerArgs t) (ap1 Fst (ap1 Snd a))))
      innerArgsEq = getInnerArgsEq a bb

      a1 : Deriv (atomic (eqn (ap1 getPayG t) (ap1 Fst (ap1 getInnerArgs t))))
      a1 = axComp Fst getInnerArgs t

      a2 : Deriv (atomic (eqn (ap1 Fst (ap1 getInnerArgs t))
                              (ap1 Fst (ap1 Fst (ap1 Snd a)))))
      a2 = cong1 Fst innerArgsEq

      payGEqL : Deriv (P imp atomic (eqn (ap1 getPayG t) payG))
      payGEqL =
        liftedRuleTrans P (ap1 getPayG t)
          (ap1 Fst (ap1 getInnerArgs t)) payG
          (liftAxiom P a1)
          (liftedRuleTrans P (ap1 Fst (ap1 getInnerArgs t))
             (ap1 Fst (ap1 Fst (ap1 Snd a))) payG
             (liftAxiom P a2) payGExtL)

      b1 : Deriv (atomic (eqn (ap1 getPayX t) (ap1 Snd (ap1 getInnerArgs t))))
      b1 = axComp Snd getInnerArgs t

      b2 : Deriv (atomic (eqn (ap1 Snd (ap1 getInnerArgs t))
                              (ap1 Snd (ap1 Fst (ap1 Snd a)))))
      b2 = cong1 Snd innerArgsEq

      payXEqL : Deriv (P imp atomic (eqn (ap1 getPayX t) payX))
      payXEqL =
        liftedRuleTrans P (ap1 getPayX t)
          (ap1 Snd (ap1 getInnerArgs t)) payX
          (liftAxiom P b1)
          (liftedRuleTrans P (ap1 Snd (ap1 getInnerArgs t))
             (ap1 Snd (ap1 Fst (ap1 Snd a))) payX
             (liftAxiom P b2) payXExtL)

      ----------------------------------------------------------------
      -- Section B (lifted): getIH = Pair fp sp; Fst/Snd extractions.
      --
      -- ihExtracted is closed; ihPair gets lifted by combining with ihShapeL.

      ihExtracted : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd bb))))
      ihExtracted = getIHEq a bb

      ihPairL : Deriv (P imp atomic (eqn (ap1 getIH t) (ap2 Pair fp sp)))
      ihPairL =
        liftedRuleTrans P (ap1 getIH t) (ap1 Snd (ap1 Snd bb))
          (ap2 Pair fp sp) (liftAxiom P ihExtracted) ihShapeL

      c1 : Deriv (atomic (eqn (ap1 getFstIH t) (ap1 Fst (ap1 getIH t))))
      c1 = axComp Fst getIH t
      c3 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair fp sp)) fp))
      c3 = axFst fp sp

      c2L : Deriv (P imp atomic (eqn (ap1 Fst (ap1 getIH t)) (ap1 Fst (ap2 Pair fp sp))))
      c2L = liftedCong1 P Fst (ap1 getIH t) (ap2 Pair fp sp) ihPairL

      getFstIHEqL : Deriv (P imp atomic (eqn (ap1 getFstIH t) fp))
      getFstIHEqL =
        liftedRuleTrans P (ap1 getFstIH t) (ap1 Fst (ap1 getIH t)) fp
          (liftAxiom P c1)
          (liftedRuleTrans P (ap1 Fst (ap1 getIH t))
             (ap1 Fst (ap2 Pair fp sp)) fp c2L (liftAxiom P c3))

      d1 : Deriv (atomic (eqn (ap1 getSndIH t) (ap1 Snd (ap1 getIH t))))
      d1 = axComp Snd getIH t
      d3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair fp sp)) sp))
      d3 = axSnd fp sp

      d2L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 getIH t)) (ap1 Snd (ap2 Pair fp sp))))
      d2L = liftedCong1 P Snd (ap1 getIH t) (ap2 Pair fp sp) ihPairL

      getSndIHEqL : Deriv (P imp atomic (eqn (ap1 getSndIH t) sp))
      getSndIHEqL =
        liftedRuleTrans P (ap1 getSndIH t) (ap1 Snd (ap1 getIH t)) sp
          (liftAxiom P d1)
          (liftedRuleTrans P (ap1 Snd (ap1 getIH t))
             (ap1 Snd (ap2 Pair fp sp)) sp d2L (liftAxiom P d3))

      ----------------------------------------------------------------
      -- Section E (lifted): assemblyLeftF1 t = outLeft.

      e1 : Deriv (atomic (eqn (ap1 assemblyLeftF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getFstIH getPayX)) t))))
      e1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t

      ktTag : Deriv (atomic (eqn (ap1 (KT tagAp2T) t) tagAp2T))
      ktTag = axKT tagAp2 tagAp2_isValue t

      e2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getFstIH getPayX) t))))
      e2 = axComp2 Pair getPayG (Comp2 Pair getFstIH getPayX) t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getFstIH getPayX) t)
                              (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))))
      e3 = axComp2 Pair getFstIH getPayX t

      eInnerLAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))
        (ap2 Pair fp (ap1 getPayX t))))
      eInnerLAL = liftedCongL P Pair (ap1 getFstIH t) fp (ap1 getPayX t) getFstIHEqL

      eInnerLBL : Deriv (P imp atomic (eqn (ap2 Pair fp (ap1 getPayX t))
                                     (ap2 Pair fp payX)))
      eInnerLBL = liftedCongR P Pair (ap1 getPayX t) payX fp payXEqL

      eInnerLL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getFstIH getPayX) t)
                                    (ap2 Pair fp payX)))
      eInnerLL =
        liftedRuleTrans P (ap1 (Comp2 Pair getFstIH getPayX) t)
          (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t)) (ap2 Pair fp payX)
          (liftAxiom P e3)
          (liftedRuleTrans P (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))
             (ap2 Pair fp (ap1 getPayX t)) (ap2 Pair fp payX)
             eInnerLAL eInnerLBL)

      eMidLAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))))
      eMidLAL = liftedCongL P Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getFstIH getPayX) t) payGEqL

      eMidLBL : Deriv (P imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))
                                    (ap2 Pair payG (ap2 Pair fp payX))))
      eMidLBL = liftedCongR P Pair (ap1 (Comp2 Pair getFstIH getPayX) t)
                  (ap2 Pair fp payX) payG eInnerLL

      eMidLL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                                  (ap2 Pair payG (ap2 Pair fp payX))))
      eMidLL =
        liftedRuleTrans P (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
          (ap2 Pair payG (ap2 Pair fp payX))
          (liftAxiom P e2)
          (liftedRuleTrans P
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))
             (ap2 Pair payG (ap2 Pair fp payX))
             eMidLAL eMidLBL)

      eOuterLAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))))
      eOuterLAL = liftedCongL P Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                    (liftAxiom P ktTag)

      eOuterLBL : Deriv (P imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
        outLeft))
      eOuterLBL = liftedCongR P Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                    (ap2 Pair payG (ap2 Pair fp payX)) tagAp2T eMidLL

      assemblyLeftEqL : Deriv (P imp atomic (eqn (ap1 assemblyLeftF1 t) outLeft))
      assemblyLeftEqL =
        liftedRuleTrans P (ap1 assemblyLeftF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
          outLeft
          (liftAxiom P e1)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
             outLeft
             eOuterLAL eOuterLBL)

      ----------------------------------------------------------------
      -- Section F (lifted): assemblyRightF1 t = outRight.

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getSndIH getPayX)) t))))
      f1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t

      f2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getSndIH getPayX) t))))
      f2 = axComp2 Pair getPayG (Comp2 Pair getSndIH getPayX) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getSndIH getPayX) t)
                              (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))))
      f3 = axComp2 Pair getSndIH getPayX t

      fInnerRAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))
        (ap2 Pair sp (ap1 getPayX t))))
      fInnerRAL = liftedCongL P Pair (ap1 getSndIH t) sp (ap1 getPayX t) getSndIHEqL

      fInnerRBL : Deriv (P imp atomic (eqn (ap2 Pair sp (ap1 getPayX t))
                                     (ap2 Pair sp payX)))
      fInnerRBL = liftedCongR P Pair (ap1 getPayX t) payX sp payXEqL

      fInnerRL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getSndIH getPayX) t)
                                    (ap2 Pair sp payX)))
      fInnerRL =
        liftedRuleTrans P (ap1 (Comp2 Pair getSndIH getPayX) t)
          (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t)) (ap2 Pair sp payX)
          (liftAxiom P f3)
          (liftedRuleTrans P (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))
             (ap2 Pair sp (ap1 getPayX t)) (ap2 Pair sp payX)
             fInnerRAL fInnerRBL)

      fMidRAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))))
      fMidRAL = liftedCongL P Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getSndIH getPayX) t) payGEqL

      fMidRBL : Deriv (P imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))
                                    (ap2 Pair payG (ap2 Pair sp payX))))
      fMidRBL = liftedCongR P Pair (ap1 (Comp2 Pair getSndIH getPayX) t)
                  (ap2 Pair sp payX) payG fInnerRL

      fMidRL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                                  (ap2 Pair payG (ap2 Pair sp payX))))
      fMidRL =
        liftedRuleTrans P (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
          (ap2 Pair payG (ap2 Pair sp payX))
          (liftAxiom P f2)
          (liftedRuleTrans P
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))
             (ap2 Pair payG (ap2 Pair sp payX))
             fMidRAL fMidRBL)

      fOuterRAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))))
      fOuterRAL = liftedCongL P Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                    (liftAxiom P ktTag)

      fOuterRBL : Deriv (P imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
        outRight))
      fOuterRBL = liftedCongR P Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                    (ap2 Pair payG (ap2 Pair sp payX)) tagAp2T fMidRL

      assemblyRightEqL : Deriv (P imp atomic (eqn (ap1 assemblyRightF1 t) outRight))
      assemblyRightEqL =
        liftedRuleTrans P (ap1 assemblyRightF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
          outRight
          (liftAxiom P f1)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
             outRight
             fOuterRAL fOuterRBL)

      ----------------------------------------------------------------
      -- Section G (lifted): doAssemblyF1 t = Pair outLeft outRight.

      g1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                              (ap2 Pair (ap1 assemblyLeftF1 t)
                                        (ap1 assemblyRightF1 t))))
      g1 = axComp2 Pair assemblyLeftF1 assemblyRightF1 t

      gAL : Deriv (P imp atomic (eqn (ap2 Pair (ap1 assemblyLeftF1 t)
                                         (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft (ap1 assemblyRightF1 t))))
      gAL = liftedCongL P Pair (ap1 assemblyLeftF1 t) outLeft
              (ap1 assemblyRightF1 t) assemblyLeftEqL

      gBL : Deriv (P imp atomic (eqn (ap2 Pair outLeft (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft outRight)))
      gBL = liftedCongR P Pair (ap1 assemblyRightF1 t) outRight outLeft assemblyRightEqL

      doAssemblyEqL : Deriv (P imp atomic (eqn (ap1 doAssemblyF1 t)
                                         (ap2 Pair outLeft outRight)))
      doAssemblyEqL =
        liftedRuleTrans P (ap1 doAssemblyF1 t)
          (ap2 Pair (ap1 assemblyLeftF1 t) (ap1 assemblyRightF1 t))
          (ap2 Pair outLeft outRight)
          (liftAxiom P g1)
          (liftedRuleTrans P
             (ap2 Pair (ap1 assemblyLeftF1 t) (ap1 assemblyRightF1 t))
             (ap2 Pair outLeft (ap1 assemblyRightF1 t))
             (ap2 Pair outLeft outRight) gAL gBL)

      ----------------------------------------------------------------
      -- Section H (lifted): verifierCLF1 t reduces via axIfLfN.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      h1 : Deriv (atomic (eqn (ap1 verifierCLF1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      h1 = axComp2 IfLf getIH branchesF1 t

      h2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O)))
                (codeFormula_isValue (atomic (eqn O O))) t

      h4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
                              (ap2 Pair codeTriv (ap1 doAssemblyF1 t))))
      h4 = congL Pair (ap1 doAssemblyF1 t) h3

      h5L : Deriv (P imp atomic (eqn (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
                              (ap2 Pair codeTriv (ap2 Pair outLeft outRight))))
      h5L = liftedCongR P Pair (ap1 doAssemblyF1 t) (ap2 Pair outLeft outRight)
              codeTriv doAssemblyEqL

      branchesEqL : Deriv (P imp atomic (eqn (ap1 branchesF1 t)
                                       (ap2 Pair codeTriv (ap2 Pair outLeft outRight))))
      branchesEqL =
        liftedRuleTrans P (ap1 branchesF1 t)
          (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
          (ap2 Pair codeTriv (ap2 Pair outLeft outRight))
          (liftAxiom P h2)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap2 Pair outLeft outRight))
             (liftAxiom P h4) h5L)

      h6L : Deriv (P imp atomic (eqn (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))))
      h6L = liftedCongL P IfLf (ap1 getIH t) (ap2 Pair fp sp)
              (ap1 branchesF1 t) ihPairL

      h7L : Deriv (P imp atomic (eqn (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))))
      h7L = liftedCongR P IfLf (ap1 branchesF1 t)
              (ap2 Pair codeTriv (ap2 Pair outLeft outRight)) (ap2 Pair fp sp) branchesEqL

      h8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))
                              (ap2 Pair outLeft outRight)))
      h8 = axIfLfN fp sp codeTriv (ap2 Pair outLeft outRight)

      verifierEqL : Deriv (P imp atomic (eqn (ap1 verifierCLF1 t) (ap2 Pair outLeft outRight)))
      verifierEqL =
        liftedRuleTrans P (ap1 verifierCLF1 t)
          (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t)) (ap2 Pair outLeft outRight)
          (liftAxiom P h1)
          (liftedRuleTrans P
             (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
             (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
             (ap2 Pair outLeft outRight)
             h6L
             (liftedRuleTrans P
                (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                (ap2 IfLf (ap2 Pair fp sp)
                          (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))
                (ap2 Pair outLeft outRight)
                h7L (liftAxiom P h8)))

      ----------------------------------------------------------------
      i1 : Deriv (atomic (eqn (ap2 body_congL_v a bb) (ap1 verifierCLF1 t)))
      i1 = axPost verifierCLF1 Pair a bb
  in liftedRuleTrans P (ap2 body_congL_v a bb) (ap1 verifierCLF1 t)
       (ap2 Pair outLeft outRight) (liftAxiom P i1) verifierEqL

----------------------------------------------------------------------
-- Doubly-lifted variant: same theorem under formulas P1, P2.
-- Mirrors the lifted variant; uses ...Two helpers throughout.

body_congL_v_eval_pass_dl :
  (P1 P2 : Formula) (a bb : Term) (payG payX fp sp : Term) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp)))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap2 body_congL_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair fp payX)))
                                (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair sp payX)))))))
body_congL_v_eval_pass_dl P1 P2 a bb payG payX fp sp payGExtL payXExtL ihShapeL =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp2T : Term
      tagAp2T = reify tagAp2
      outLeft : Term
      outLeft = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair fp payX))
      outRight : Term
      outRight = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair sp payX))

      innerArgsEq : Deriv (atomic (eqn (ap1 getInnerArgs t) (ap1 Fst (ap1 Snd a))))
      innerArgsEq = getInnerArgsEq a bb

      a1 : Deriv (atomic (eqn (ap1 getPayG t) (ap1 Fst (ap1 getInnerArgs t))))
      a1 = axComp Fst getInnerArgs t

      a2 : Deriv (atomic (eqn (ap1 Fst (ap1 getInnerArgs t))
                              (ap1 Fst (ap1 Fst (ap1 Snd a)))))
      a2 = cong1 Fst innerArgsEq

      payGEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getPayG t) payG)))
      payGEqL =
        liftedRuleTransTwo P1 P2 (ap1 getPayG t)
          (ap1 Fst (ap1 getInnerArgs t)) payG
          (liftAxiomTwo P1 P2 a1)
          (liftedRuleTransTwo P1 P2 (ap1 Fst (ap1 getInnerArgs t))
             (ap1 Fst (ap1 Fst (ap1 Snd a))) payG
             (liftAxiomTwo P1 P2 a2) payGExtL)

      b1 : Deriv (atomic (eqn (ap1 getPayX t) (ap1 Snd (ap1 getInnerArgs t))))
      b1 = axComp Snd getInnerArgs t

      b2 : Deriv (atomic (eqn (ap1 Snd (ap1 getInnerArgs t))
                              (ap1 Snd (ap1 Fst (ap1 Snd a)))))
      b2 = cong1 Snd innerArgsEq

      payXEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getPayX t) payX)))
      payXEqL =
        liftedRuleTransTwo P1 P2 (ap1 getPayX t)
          (ap1 Snd (ap1 getInnerArgs t)) payX
          (liftAxiomTwo P1 P2 b1)
          (liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 getInnerArgs t))
             (ap1 Snd (ap1 Fst (ap1 Snd a))) payX
             (liftAxiomTwo P1 P2 b2) payXExtL)

      ihExtracted : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd bb))))
      ihExtracted = getIHEq a bb

      ihPairL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getIH t) (ap2 Pair fp sp))))
      ihPairL =
        liftedRuleTransTwo P1 P2 (ap1 getIH t) (ap1 Snd (ap1 Snd bb))
          (ap2 Pair fp sp) (liftAxiomTwo P1 P2 ihExtracted) ihShapeL

      c1 : Deriv (atomic (eqn (ap1 getFstIH t) (ap1 Fst (ap1 getIH t))))
      c1 = axComp Fst getIH t
      c3 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair fp sp)) fp))
      c3 = axFst fp sp

      c2L : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Fst (ap1 getIH t)) (ap1 Fst (ap2 Pair fp sp)))))
      c2L = liftedCong1Two P1 P2 Fst (ap1 getIH t) (ap2 Pair fp sp) ihPairL

      getFstIHEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getFstIH t) fp)))
      getFstIHEqL =
        liftedRuleTransTwo P1 P2 (ap1 getFstIH t) (ap1 Fst (ap1 getIH t)) fp
          (liftAxiomTwo P1 P2 c1)
          (liftedRuleTransTwo P1 P2 (ap1 Fst (ap1 getIH t))
             (ap1 Fst (ap2 Pair fp sp)) fp c2L (liftAxiomTwo P1 P2 c3))

      d1 : Deriv (atomic (eqn (ap1 getSndIH t) (ap1 Snd (ap1 getIH t))))
      d1 = axComp Snd getIH t
      d3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair fp sp)) sp))
      d3 = axSnd fp sp

      d2L : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 getIH t)) (ap1 Snd (ap2 Pair fp sp)))))
      d2L = liftedCong1Two P1 P2 Snd (ap1 getIH t) (ap2 Pair fp sp) ihPairL

      getSndIHEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getSndIH t) sp)))
      getSndIHEqL =
        liftedRuleTransTwo P1 P2 (ap1 getSndIH t) (ap1 Snd (ap1 getIH t)) sp
          (liftAxiomTwo P1 P2 d1)
          (liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 getIH t))
             (ap1 Snd (ap2 Pair fp sp)) sp d2L (liftAxiomTwo P1 P2 d3))

      e1 : Deriv (atomic (eqn (ap1 assemblyLeftF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getFstIH getPayX)) t))))
      e1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t

      ktTag : Deriv (atomic (eqn (ap1 (KT tagAp2T) t) tagAp2T))
      ktTag = axKT tagAp2 tagAp2_isValue t

      e2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getFstIH getPayX) t))))
      e2 = axComp2 Pair getPayG (Comp2 Pair getFstIH getPayX) t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getFstIH getPayX) t)
                              (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))))
      e3 = axComp2 Pair getFstIH getPayX t

      eInnerLAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))
        (ap2 Pair fp (ap1 getPayX t)))))
      eInnerLAL = liftedCongLTwo P1 P2 Pair (ap1 getFstIH t) fp (ap1 getPayX t) getFstIHEqL

      eInnerLBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair fp (ap1 getPayX t))
                                     (ap2 Pair fp payX))))
      eInnerLBL = liftedCongRTwo P1 P2 Pair (ap1 getPayX t) payX fp payXEqL

      eInnerLL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getFstIH getPayX) t)
                                    (ap2 Pair fp payX))))
      eInnerLL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getFstIH getPayX) t)
          (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t)) (ap2 Pair fp payX)
          (liftAxiomTwo P1 P2 e3)
          (liftedRuleTransTwo P1 P2 (ap2 Pair (ap1 getFstIH t) (ap1 getPayX t))
             (ap2 Pair fp (ap1 getPayX t)) (ap2 Pair fp payX)
             eInnerLAL eInnerLBL)

      eMidLAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t)))))
      eMidLAL = liftedCongLTwo P1 P2 Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getFstIH getPayX) t) payGEqL

      eMidLBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))
                                    (ap2 Pair payG (ap2 Pair fp payX)))))
      eMidLBL = liftedCongRTwo P1 P2 Pair (ap1 (Comp2 Pair getFstIH getPayX) t)
                  (ap2 Pair fp payX) payG eInnerLL

      eMidLL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                                  (ap2 Pair payG (ap2 Pair fp payX)))))
      eMidLL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
          (ap2 Pair payG (ap2 Pair fp payX))
          (liftAxiomTwo P1 P2 e2)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getFstIH getPayX) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getFstIH getPayX) t))
             (ap2 Pair payG (ap2 Pair fp payX))
             eMidLAL eMidLBL)

      eOuterLAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)))))
      eOuterLAL = liftedCongLTwo P1 P2 Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                    (liftAxiomTwo P1 P2 ktTag)

      eOuterLBL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
        outLeft)))
      eOuterLBL = liftedCongRTwo P1 P2 Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t)
                    (ap2 Pair payG (ap2 Pair fp payX)) tagAp2T eMidLL

      assemblyLeftEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 assemblyLeftF1 t) outLeft)))
      assemblyLeftEqL =
        liftedRuleTransTwo P1 P2 (ap1 assemblyLeftF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
          outLeft
          (liftAxiomTwo P1 P2 e1)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getFstIH getPayX)) t))
             outLeft
             eOuterLAL eOuterLBL)

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getSndIH getPayX)) t))))
      f1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t

      f2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getSndIH getPayX) t))))
      f2 = axComp2 Pair getPayG (Comp2 Pair getSndIH getPayX) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getSndIH getPayX) t)
                              (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))))
      f3 = axComp2 Pair getSndIH getPayX t

      fInnerRAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))
        (ap2 Pair sp (ap1 getPayX t)))))
      fInnerRAL = liftedCongLTwo P1 P2 Pair (ap1 getSndIH t) sp (ap1 getPayX t) getSndIHEqL

      fInnerRBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair sp (ap1 getPayX t))
                                     (ap2 Pair sp payX))))
      fInnerRBL = liftedCongRTwo P1 P2 Pair (ap1 getPayX t) payX sp payXEqL

      fInnerRL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getSndIH getPayX) t)
                                    (ap2 Pair sp payX))))
      fInnerRL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getSndIH getPayX) t)
          (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t)) (ap2 Pair sp payX)
          (liftAxiomTwo P1 P2 f3)
          (liftedRuleTransTwo P1 P2 (ap2 Pair (ap1 getSndIH t) (ap1 getPayX t))
             (ap2 Pair sp (ap1 getPayX t)) (ap2 Pair sp payX)
             fInnerRAL fInnerRBL)

      fMidRAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t)))))
      fMidRAL = liftedCongLTwo P1 P2 Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getSndIH getPayX) t) payGEqL

      fMidRBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))
                                    (ap2 Pair payG (ap2 Pair sp payX)))))
      fMidRBL = liftedCongRTwo P1 P2 Pair (ap1 (Comp2 Pair getSndIH getPayX) t)
                  (ap2 Pair sp payX) payG fInnerRL

      fMidRL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                                  (ap2 Pair payG (ap2 Pair sp payX)))))
      fMidRL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
          (ap2 Pair payG (ap2 Pair sp payX))
          (liftAxiomTwo P1 P2 f2)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getSndIH getPayX) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getSndIH getPayX) t))
             (ap2 Pair payG (ap2 Pair sp payX))
             fMidRAL fMidRBL)

      fOuterRAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)))))
      fOuterRAL = liftedCongLTwo P1 P2 Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                    (liftAxiomTwo P1 P2 ktTag)

      fOuterRBL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
        outRight)))
      fOuterRBL = liftedCongRTwo P1 P2 Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t)
                    (ap2 Pair payG (ap2 Pair sp payX)) tagAp2T fMidRL

      assemblyRightEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 assemblyRightF1 t) outRight)))
      assemblyRightEqL =
        liftedRuleTransTwo P1 P2 (ap1 assemblyRightF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
          outRight
          (liftAxiomTwo P1 P2 f1)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getSndIH getPayX)) t))
             outRight
             fOuterRAL fOuterRBL)

      g1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                              (ap2 Pair (ap1 assemblyLeftF1 t)
                                        (ap1 assemblyRightF1 t))))
      g1 = axComp2 Pair assemblyLeftF1 assemblyRightF1 t

      gAL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair (ap1 assemblyLeftF1 t)
                                         (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft (ap1 assemblyRightF1 t)))))
      gAL = liftedCongLTwo P1 P2 Pair (ap1 assemblyLeftF1 t) outLeft
              (ap1 assemblyRightF1 t) assemblyLeftEqL

      gBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair outLeft (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft outRight))))
      gBL = liftedCongRTwo P1 P2 Pair (ap1 assemblyRightF1 t) outRight outLeft assemblyRightEqL

      doAssemblyEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 doAssemblyF1 t)
                                         (ap2 Pair outLeft outRight))))
      doAssemblyEqL =
        liftedRuleTransTwo P1 P2 (ap1 doAssemblyF1 t)
          (ap2 Pair (ap1 assemblyLeftF1 t) (ap1 assemblyRightF1 t))
          (ap2 Pair outLeft outRight)
          (liftAxiomTwo P1 P2 g1)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 assemblyLeftF1 t) (ap1 assemblyRightF1 t))
             (ap2 Pair outLeft (ap1 assemblyRightF1 t))
             (ap2 Pair outLeft outRight) gAL gBL)

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      h1 : Deriv (atomic (eqn (ap1 verifierCLF1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      h1 = axComp2 IfLf getIH branchesF1 t

      h2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O)))
                (codeFormula_isValue (atomic (eqn O O))) t

      h4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
                              (ap2 Pair codeTriv (ap1 doAssemblyF1 t))))
      h4 = congL Pair (ap1 doAssemblyF1 t) h3

      h5L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
                              (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))))
      h5L = liftedCongRTwo P1 P2 Pair (ap1 doAssemblyF1 t) (ap2 Pair outLeft outRight)
              codeTriv doAssemblyEqL

      branchesEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 branchesF1 t)
                                       (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))))
      branchesEqL =
        liftedRuleTransTwo P1 P2 (ap1 branchesF1 t)
          (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
          (ap2 Pair codeTriv (ap2 Pair outLeft outRight))
          (liftAxiomTwo P1 P2 h2)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap2 Pair outLeft outRight))
             (liftAxiomTwo P1 P2 h4) h5L)

      h6L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t)))))
      h6L = liftedCongLTwo P1 P2 IfLf (ap1 getIH t) (ap2 Pair fp sp)
              (ap1 branchesF1 t) ihPairL

      h7L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight))))))
      h7L = liftedCongRTwo P1 P2 IfLf (ap1 branchesF1 t)
              (ap2 Pair codeTriv (ap2 Pair outLeft outRight)) (ap2 Pair fp sp) branchesEqL

      h8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))
                              (ap2 Pair outLeft outRight)))
      h8 = axIfLfN fp sp codeTriv (ap2 Pair outLeft outRight)

      verifierEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 verifierCLF1 t) (ap2 Pair outLeft outRight))))
      verifierEqL =
        liftedRuleTransTwo P1 P2 (ap1 verifierCLF1 t)
          (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t)) (ap2 Pair outLeft outRight)
          (liftAxiomTwo P1 P2 h1)
          (liftedRuleTransTwo P1 P2
             (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
             (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
             (ap2 Pair outLeft outRight)
             h6L
             (liftedRuleTransTwo P1 P2
                (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                (ap2 IfLf (ap2 Pair fp sp)
                          (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))
                (ap2 Pair outLeft outRight)
                h7L (liftAxiomTwo P1 P2 h8)))

      i1 : Deriv (atomic (eqn (ap2 body_congL_v a bb) (ap1 verifierCLF1 t)))
      i1 = axPost verifierCLF1 Pair a bb
  in liftedRuleTransTwo P1 P2 (ap2 body_congL_v a bb) (ap1 verifierCLF1 t)
       (ap2 Pair outLeft outRight) (liftAxiomTwo P1 P2 i1) verifierEqL
