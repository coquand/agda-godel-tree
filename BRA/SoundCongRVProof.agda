{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundCongRVProof
--
-- Evaluation proof for body_congR_v.  Mirrors SoundCongLVProof with the
-- inner Pair  swapped: congR outputs  Pair payX partIH  (vs congL's
-- Pair partIH payX).

module BRA.SoundCongRVProof where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.EvalHelpers
  using ( liftAxiom ; liftAxiomTwo
        ; liftedRuleTrans ; liftedRuleTransTwo
        ; liftedCong1 ; liftedCong1Two
        ; liftedCongL ; liftedCongLTwo
        ; liftedCongR ; liftedCongRTwo )

open import BRA.SoundCongRProto
  using ( body_congR_v ; verifierCRF1 ; doAssemblyF1
        ; assemblyLeftF1 ; assemblyRightF1
        ; getInnerArgs ; getPayG ; getPayX
        ; getIH ; getFstIH ; getSndIH ; codeTriv )

private
  getInnerArgsEq : (a bb : Term) ->
    Deriv (atomic (eqn (ap1 getInnerArgs (ap2 Pair a bb)) (ap1 Fst (ap1 Snd a))))
  getInnerArgsEq a bb =
    let t = ap2 Pair a bb
        e1 = axComp Fst (Comp Snd Fst) t
        e2 = axComp Snd Fst t
        e3 = axFst a bb
        e4 = cong1 Snd e3
        e5 = ruleTrans e2 e4
        e6 = cong1 Fst e5
    in ruleTrans e1 e6

  getIHEq : (a bb : Term) ->
    Deriv (atomic (eqn (ap1 getIH (ap2 Pair a bb)) (ap1 Snd (ap1 Snd bb))))
  getIHEq a bb =
    let t = ap2 Pair a bb
        e1 = axComp Snd (Comp Snd Snd) t
        e2 = axComp Snd Snd t
        e3 = axSnd a bb
        e4 = cong1 Snd e3
        e5 = ruleTrans e2 e4
        e6 = cong1 Snd e5
    in ruleTrans e1 e6

body_congR_v_eval_pass :
  (a bb : Term) (payG payX fp sp : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG)) ->
  Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX)) ->
  Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp))) ->
  Deriv (atomic (eqn (ap2 body_congR_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair payX fp)))
                                (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair payX sp))))))
body_congR_v_eval_pass a bb payG payX fp sp payGExt payXExt ihShape =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp2T : Term
      tagAp2T = reify tagAp2
      outLeft : Term
      outLeft = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair payX fp))
      outRight : Term
      outRight = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair payX sp))

      innerArgsEq : Deriv (atomic (eqn (ap1 getInnerArgs t) (ap1 Fst (ap1 Snd a))))
      innerArgsEq = getInnerArgsEq a bb

      a1 = axComp Fst getInnerArgs t
      a2 = cong1 Fst innerArgsEq
      payGEq : Deriv (atomic (eqn (ap1 getPayG t) payG))
      payGEq = ruleTrans a1 (ruleTrans a2 payGExt)

      b1 = axComp Snd getInnerArgs t
      b2 = cong1 Snd innerArgsEq
      payXEq : Deriv (atomic (eqn (ap1 getPayX t) payX))
      payXEq = ruleTrans b1 (ruleTrans b2 payXExt)

      ihExtracted : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd bb))))
      ihExtracted = getIHEq a bb

      ihPair : Deriv (atomic (eqn (ap1 getIH t) (ap2 Pair fp sp)))
      ihPair = ruleTrans ihExtracted ihShape

      c1 = axComp Fst getIH t
      c2 = cong1 Fst ihPair
      c3 = axFst fp sp
      getFstIHEq : Deriv (atomic (eqn (ap1 getFstIH t) fp))
      getFstIHEq = ruleTrans c1 (ruleTrans c2 c3)

      d1 = axComp Snd getIH t
      d2 = cong1 Snd ihPair
      d3 = axSnd fp sp
      getSndIHEq : Deriv (atomic (eqn (ap1 getSndIH t) sp))
      getSndIHEq = ruleTrans d1 (ruleTrans d2 d3)

      ----------------------------------------------------------------
      -- Section E: assemblyLeftF1 t = outLeft.
      --   Inner Pair: Pair (getPayX t) (getFstIH t) -> Pair payX fp.

      e1 : Deriv (atomic (eqn (ap1 assemblyLeftF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getPayX getFstIH)) t))))
      e1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t

      ktTag : Deriv (atomic (eqn (ap1 (KT tagAp2T) t) tagAp2T))
      ktTag = axKT tagAp2 t

      e2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getPayX getFstIH) t))))
      e2 = axComp2 Pair getPayG (Comp2 Pair getPayX getFstIH) t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getFstIH) t)
                              (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))))
      e3 = axComp2 Pair getPayX getFstIH t

      eInnerLA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))
        (ap2 Pair payX (ap1 getFstIH t))))
      eInnerLA = congL Pair (ap1 getFstIH t) payXEq

      eInnerLB : Deriv (atomic (eqn (ap2 Pair payX (ap1 getFstIH t))
                                     (ap2 Pair payX fp)))
      eInnerLB = congR Pair payX getFstIHEq

      eInnerL : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getFstIH) t)
                                    (ap2 Pair payX fp)))
      eInnerL = ruleTrans e3 (ruleTrans eInnerLA eInnerLB)

      eMidLA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))))
      eMidLA = congL Pair (ap1 (Comp2 Pair getPayX getFstIH) t) payGEq

      eMidLB : Deriv (atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))
                                    (ap2 Pair payG (ap2 Pair payX fp))))
      eMidLB = congR Pair payG eInnerL

      eMidL : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                                  (ap2 Pair payG (ap2 Pair payX fp))))
      eMidL = ruleTrans e2 (ruleTrans eMidLA eMidLB)

      eOuterLA : Deriv (atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))))
      eOuterLA = congL Pair (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t) ktTag

      eOuterLB : Deriv (atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
        outLeft))
      eOuterLB = congR Pair tagAp2T eMidL

      assemblyLeftEq : Deriv (atomic (eqn (ap1 assemblyLeftF1 t) outLeft))
      assemblyLeftEq = ruleTrans e1 (ruleTrans eOuterLA eOuterLB)

      ----------------------------------------------------------------
      -- Section F: assemblyRightF1 t = outRight (sp instead of fp).

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getPayX getSndIH)) t))))
      f1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t

      f2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getPayX getSndIH) t))))
      f2 = axComp2 Pair getPayG (Comp2 Pair getPayX getSndIH) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getSndIH) t)
                              (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))))
      f3 = axComp2 Pair getPayX getSndIH t

      fInnerRA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))
        (ap2 Pair payX (ap1 getSndIH t))))
      fInnerRA = congL Pair (ap1 getSndIH t) payXEq

      fInnerRB : Deriv (atomic (eqn (ap2 Pair payX (ap1 getSndIH t))
                                     (ap2 Pair payX sp)))
      fInnerRB = congR Pair payX getSndIHEq

      fInnerR : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getSndIH) t)
                                    (ap2 Pair payX sp)))
      fInnerR = ruleTrans f3 (ruleTrans fInnerRA fInnerRB)

      fMidRA : Deriv (atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))))
      fMidRA = congL Pair (ap1 (Comp2 Pair getPayX getSndIH) t) payGEq

      fMidRB : Deriv (atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))
                                    (ap2 Pair payG (ap2 Pair payX sp))))
      fMidRB = congR Pair payG fInnerR

      fMidR : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                                  (ap2 Pair payG (ap2 Pair payX sp))))
      fMidR = ruleTrans f2 (ruleTrans fMidRA fMidRB)

      fOuterRA : Deriv (atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))))
      fOuterRA = congL Pair (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t) ktTag

      fOuterRB : Deriv (atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
        outRight))
      fOuterRB = congR Pair tagAp2T fMidR

      assemblyRightEq : Deriv (atomic (eqn (ap1 assemblyRightF1 t) outRight))
      assemblyRightEq = ruleTrans f1 (ruleTrans fOuterRA fOuterRB)

      ----------------------------------------------------------------
      g1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                              (ap2 Pair (ap1 assemblyLeftF1 t)
                                        (ap1 assemblyRightF1 t))))
      g1 = axComp2 Pair assemblyLeftF1 assemblyRightF1 t

      gA = congL Pair (ap1 assemblyRightF1 t) assemblyLeftEq
      gB = congR Pair outLeft assemblyRightEq

      doAssemblyEq : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                                         (ap2 Pair outLeft outRight)))
      doAssemblyEq = ruleTrans g1 (ruleTrans gA gB)

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      h1 = axComp2 IfLf getIH branchesF1 t
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t
      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O))) t
      h4 = congL Pair (ap1 doAssemblyF1 t) h3
      h5 = congR Pair codeTriv doAssemblyEq
      branchesEq = ruleTrans h2 (ruleTrans h4 h5)
      h6 = congL IfLf (ap1 branchesF1 t) ihPair
      h7 = congR IfLf (ap2 Pair fp sp) branchesEq
      h8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair outLeft outRight)))
                              (ap2 Pair outLeft outRight)))
      h8 = axIfLfN fp sp codeTriv (ap2 Pair outLeft outRight)

      verifierEq : Deriv (atomic (eqn (ap1 verifierCRF1 t) (ap2 Pair outLeft outRight)))
      verifierEq = ruleTrans h1 (ruleTrans h6 (ruleTrans h7 h8))

      i1 : Deriv (atomic (eqn (ap2 body_congR_v a bb) (ap1 verifierCRF1 t)))
      i1 = axPost verifierCRF1 Pair a bb
  in ruleTrans i1 verifierEq

----------------------------------------------------------------------
-- Lifted variant for congR.

body_congR_v_eval_pass_l :
  (P : Formula) (a bb : Term) (payG payX fp sp : Term) ->
  Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG)) ->
  Deriv (P imp atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX)) ->
  Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp))) ->
  Deriv (P imp atomic (eqn (ap2 body_congR_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair payX fp)))
                                (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair payX sp))))))
body_congR_v_eval_pass_l P a bb payG payX fp sp payGExtL payXExtL ihShapeL =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp2T : Term
      tagAp2T = reify tagAp2
      outLeft : Term
      outLeft = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair payX fp))
      outRight : Term
      outRight = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair payX sp))

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
      -- Inner Pair: Pair (getPayX t) (getFstIH t) -> Pair payX fp.

      e1 : Deriv (atomic (eqn (ap1 assemblyLeftF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getPayX getFstIH)) t))))
      e1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t

      ktTag : Deriv (atomic (eqn (ap1 (KT tagAp2T) t) tagAp2T))
      ktTag = axKT tagAp2 t

      e2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getPayX getFstIH) t))))
      e2 = axComp2 Pair getPayG (Comp2 Pair getPayX getFstIH) t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getFstIH) t)
                              (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))))
      e3 = axComp2 Pair getPayX getFstIH t

      eInnerLAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))
        (ap2 Pair payX (ap1 getFstIH t))))
      eInnerLAL = liftedCongL P Pair (ap1 getPayX t) payX (ap1 getFstIH t) payXEqL

      eInnerLBL : Deriv (P imp atomic (eqn (ap2 Pair payX (ap1 getFstIH t))
                                     (ap2 Pair payX fp)))
      eInnerLBL = liftedCongR P Pair (ap1 getFstIH t) fp payX getFstIHEqL

      eInnerLL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getPayX getFstIH) t)
                                    (ap2 Pair payX fp)))
      eInnerLL =
        liftedRuleTrans P (ap1 (Comp2 Pair getPayX getFstIH) t)
          (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t)) (ap2 Pair payX fp)
          (liftAxiom P e3)
          (liftedRuleTrans P (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))
             (ap2 Pair payX (ap1 getFstIH t)) (ap2 Pair payX fp)
             eInnerLAL eInnerLBL)

      eMidLAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))))
      eMidLAL = liftedCongL P Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getPayX getFstIH) t) payGEqL

      eMidLBL : Deriv (P imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))
                                    (ap2 Pair payG (ap2 Pair payX fp))))
      eMidLBL = liftedCongR P Pair (ap1 (Comp2 Pair getPayX getFstIH) t)
                  (ap2 Pair payX fp) payG eInnerLL

      eMidLL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                                  (ap2 Pair payG (ap2 Pair payX fp))))
      eMidLL =
        liftedRuleTrans P (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
          (ap2 Pair payG (ap2 Pair payX fp))
          (liftAxiom P e2)
          (liftedRuleTrans P
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))
             (ap2 Pair payG (ap2 Pair payX fp))
             eMidLAL eMidLBL)

      eOuterLAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))))
      eOuterLAL = liftedCongL P Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                    (liftAxiom P ktTag)

      eOuterLBL : Deriv (P imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
        outLeft))
      eOuterLBL = liftedCongR P Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                    (ap2 Pair payG (ap2 Pair payX fp)) tagAp2T eMidLL

      assemblyLeftEqL : Deriv (P imp atomic (eqn (ap1 assemblyLeftF1 t) outLeft))
      assemblyLeftEqL =
        liftedRuleTrans P (ap1 assemblyLeftF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
          outLeft
          (liftAxiom P e1)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
             outLeft
             eOuterLAL eOuterLBL)

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getPayX getSndIH)) t))))
      f1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t

      f2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getPayX getSndIH) t))))
      f2 = axComp2 Pair getPayG (Comp2 Pair getPayX getSndIH) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getSndIH) t)
                              (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))))
      f3 = axComp2 Pair getPayX getSndIH t

      fInnerRAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))
        (ap2 Pair payX (ap1 getSndIH t))))
      fInnerRAL = liftedCongL P Pair (ap1 getPayX t) payX (ap1 getSndIH t) payXEqL

      fInnerRBL : Deriv (P imp atomic (eqn (ap2 Pair payX (ap1 getSndIH t))
                                     (ap2 Pair payX sp)))
      fInnerRBL = liftedCongR P Pair (ap1 getSndIH t) sp payX getSndIHEqL

      fInnerRL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getPayX getSndIH) t)
                                    (ap2 Pair payX sp)))
      fInnerRL =
        liftedRuleTrans P (ap1 (Comp2 Pair getPayX getSndIH) t)
          (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t)) (ap2 Pair payX sp)
          (liftAxiom P f3)
          (liftedRuleTrans P (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))
             (ap2 Pair payX (ap1 getSndIH t)) (ap2 Pair payX sp)
             fInnerRAL fInnerRBL)

      fMidRAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))))
      fMidRAL = liftedCongL P Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getPayX getSndIH) t) payGEqL

      fMidRBL : Deriv (P imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))
                                    (ap2 Pair payG (ap2 Pair payX sp))))
      fMidRBL = liftedCongR P Pair (ap1 (Comp2 Pair getPayX getSndIH) t)
                  (ap2 Pair payX sp) payG fInnerRL

      fMidRL : Deriv (P imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                                  (ap2 Pair payG (ap2 Pair payX sp))))
      fMidRL =
        liftedRuleTrans P (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
          (ap2 Pair payG (ap2 Pair payX sp))
          (liftAxiom P f2)
          (liftedRuleTrans P
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))
             (ap2 Pair payG (ap2 Pair payX sp))
             fMidRAL fMidRBL)

      fOuterRAL : Deriv (P imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))))
      fOuterRAL = liftedCongL P Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                    (liftAxiom P ktTag)

      fOuterRBL : Deriv (P imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
        outRight))
      fOuterRBL = liftedCongR P Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                    (ap2 Pair payG (ap2 Pair payX sp)) tagAp2T fMidRL

      assemblyRightEqL : Deriv (P imp atomic (eqn (ap1 assemblyRightF1 t) outRight))
      assemblyRightEqL =
        liftedRuleTrans P (ap1 assemblyRightF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
          outRight
          (liftAxiom P f1)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
             outRight
             fOuterRAL fOuterRBL)

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

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      h1 : Deriv (atomic (eqn (ap1 verifierCRF1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      h1 = axComp2 IfLf getIH branchesF1 t

      h2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O))) t

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

      verifierEqL : Deriv (P imp atomic (eqn (ap1 verifierCRF1 t) (ap2 Pair outLeft outRight)))
      verifierEqL =
        liftedRuleTrans P (ap1 verifierCRF1 t)
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

      i1 : Deriv (atomic (eqn (ap2 body_congR_v a bb) (ap1 verifierCRF1 t)))
      i1 = axPost verifierCRF1 Pair a bb
  in liftedRuleTrans P (ap2 body_congR_v a bb) (ap1 verifierCRF1 t)
       (ap2 Pair outLeft outRight) (liftAxiom P i1) verifierEqL

----------------------------------------------------------------------
-- Doubly-lifted variant for congR.

body_congR_v_eval_pass_dl :
  (P1 P2 : Formula) (a bb : Term) (payG payX fp sp : Term) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp)))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap2 body_congR_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair payX fp)))
                                (ap2 Pair (reify tagAp2)
                                          (ap2 Pair payG (ap2 Pair payX sp)))))))
body_congR_v_eval_pass_dl P1 P2 a bb payG payX fp sp payGExtL payXExtL ihShapeL =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp2T : Term
      tagAp2T = reify tagAp2
      outLeft : Term
      outLeft = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair payX fp))
      outRight : Term
      outRight = ap2 Pair tagAp2T (ap2 Pair payG (ap2 Pair payX sp))

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
                                                (Comp2 Pair getPayX getFstIH)) t))))
      e1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t

      ktTag : Deriv (atomic (eqn (ap1 (KT tagAp2T) t) tagAp2T))
      ktTag = axKT tagAp2 t

      e2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getPayX getFstIH) t))))
      e2 = axComp2 Pair getPayG (Comp2 Pair getPayX getFstIH) t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getFstIH) t)
                              (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))))
      e3 = axComp2 Pair getPayX getFstIH t

      eInnerLAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))
        (ap2 Pair payX (ap1 getFstIH t)))))
      eInnerLAL = liftedCongLTwo P1 P2 Pair (ap1 getPayX t) payX (ap1 getFstIH t) payXEqL

      eInnerLBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair payX (ap1 getFstIH t))
                                     (ap2 Pair payX fp))))
      eInnerLBL = liftedCongRTwo P1 P2 Pair (ap1 getFstIH t) fp payX getFstIHEqL

      eInnerLL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getPayX getFstIH) t)
                                    (ap2 Pair payX fp))))
      eInnerLL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getPayX getFstIH) t)
          (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t)) (ap2 Pair payX fp)
          (liftAxiomTwo P1 P2 e3)
          (liftedRuleTransTwo P1 P2 (ap2 Pair (ap1 getPayX t) (ap1 getFstIH t))
             (ap2 Pair payX (ap1 getFstIH t)) (ap2 Pair payX fp)
             eInnerLAL eInnerLBL)

      eMidLAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t)))))
      eMidLAL = liftedCongLTwo P1 P2 Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getPayX getFstIH) t) payGEqL

      eMidLBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))
                                    (ap2 Pair payG (ap2 Pair payX fp)))))
      eMidLBL = liftedCongRTwo P1 P2 Pair (ap1 (Comp2 Pair getPayX getFstIH) t)
                  (ap2 Pair payX fp) payG eInnerLL

      eMidLL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                                  (ap2 Pair payG (ap2 Pair payX fp)))))
      eMidLL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
          (ap2 Pair payG (ap2 Pair payX fp))
          (liftAxiomTwo P1 P2 e2)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getFstIH) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getPayX getFstIH) t))
             (ap2 Pair payG (ap2 Pair payX fp))
             eMidLAL eMidLBL)

      eOuterLAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)))))
      eOuterLAL = liftedCongLTwo P1 P2 Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                    (liftAxiomTwo P1 P2 ktTag)

      eOuterLBL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
        outLeft)))
      eOuterLBL = liftedCongRTwo P1 P2 Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t)
                    (ap2 Pair payG (ap2 Pair payX fp)) tagAp2T eMidLL

      assemblyLeftEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 assemblyLeftF1 t) outLeft)))
      assemblyLeftEqL =
        liftedRuleTransTwo P1 P2 (ap1 assemblyLeftF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
          outLeft
          (liftAxiomTwo P1 P2 e1)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getFstIH)) t))
             outLeft
             eOuterLAL eOuterLBL)

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp2T) t)
                                        (ap1 (Comp2 Pair getPayG
                                                (Comp2 Pair getPayX getSndIH)) t))))
      f1 = axComp2 Pair (KT tagAp2T)
              (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t

      f2 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                              (ap2 Pair (ap1 getPayG t)
                                        (ap1 (Comp2 Pair getPayX getSndIH) t))))
      f2 = axComp2 Pair getPayG (Comp2 Pair getPayX getSndIH) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayX getSndIH) t)
                              (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))))
      f3 = axComp2 Pair getPayX getSndIH t

      fInnerRAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))
        (ap2 Pair payX (ap1 getSndIH t)))))
      fInnerRAL = liftedCongLTwo P1 P2 Pair (ap1 getPayX t) payX (ap1 getSndIH t) payXEqL

      fInnerRBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair payX (ap1 getSndIH t))
                                     (ap2 Pair payX sp))))
      fInnerRBL = liftedCongRTwo P1 P2 Pair (ap1 getSndIH t) sp payX getSndIHEqL

      fInnerRL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getPayX getSndIH) t)
                                    (ap2 Pair payX sp))))
      fInnerRL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getPayX getSndIH) t)
          (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t)) (ap2 Pair payX sp)
          (liftAxiomTwo P1 P2 f3)
          (liftedRuleTransTwo P1 P2 (ap2 Pair (ap1 getPayX t) (ap1 getSndIH t))
             (ap2 Pair payX (ap1 getSndIH t)) (ap2 Pair payX sp)
             fInnerRAL fInnerRBL)

      fMidRAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
        (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t)))))
      fMidRAL = liftedCongLTwo P1 P2 Pair (ap1 getPayG t) payG
                  (ap1 (Comp2 Pair getPayX getSndIH) t) payGEqL

      fMidRBL : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))
                                    (ap2 Pair payG (ap2 Pair payX sp)))))
      fMidRBL = liftedCongRTwo P1 P2 Pair (ap1 (Comp2 Pair getPayX getSndIH) t)
                  (ap2 Pair payX sp) payG fInnerRL

      fMidRL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                                  (ap2 Pair payG (ap2 Pair payX sp)))))
      fMidRL =
        liftedRuleTransTwo P1 P2 (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
          (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
          (ap2 Pair payG (ap2 Pair payX sp))
          (liftAxiomTwo P1 P2 f2)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 getPayG t) (ap1 (Comp2 Pair getPayX getSndIH) t))
             (ap2 Pair payG (ap1 (Comp2 Pair getPayX getSndIH) t))
             (ap2 Pair payG (ap2 Pair payX sp))
             fMidRAL fMidRBL)

      fOuterRAL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair (ap1 (KT tagAp2T) t)
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
        (ap2 Pair tagAp2T
                  (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)))))
      fOuterRAL = liftedCongLTwo P1 P2 Pair (ap1 (KT tagAp2T) t) tagAp2T
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                    (liftAxiomTwo P1 P2 ktTag)

      fOuterRBL : Deriv (P1 imp (P2 imp atomic (eqn
        (ap2 Pair tagAp2T (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
        outRight)))
      fOuterRBL = liftedCongRTwo P1 P2 Pair
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t)
                    (ap2 Pair payG (ap2 Pair payX sp)) tagAp2T fMidRL

      assemblyRightEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 assemblyRightF1 t) outRight)))
      assemblyRightEqL =
        liftedRuleTransTwo P1 P2 (ap1 assemblyRightF1 t)
          (ap2 Pair (ap1 (KT tagAp2T) t)
                    (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
          outRight
          (liftAxiomTwo P1 P2 f1)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 (KT tagAp2T) t)
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
             (ap2 Pair tagAp2T
                       (ap1 (Comp2 Pair getPayG (Comp2 Pair getPayX getSndIH)) t))
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

      h1 : Deriv (atomic (eqn (ap1 verifierCRF1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      h1 = axComp2 IfLf getIH branchesF1 t

      h2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O))) t

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

      verifierEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 verifierCRF1 t) (ap2 Pair outLeft outRight))))
      verifierEqL =
        liftedRuleTransTwo P1 P2 (ap1 verifierCRF1 t)
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

      i1 : Deriv (atomic (eqn (ap2 body_congR_v a bb) (ap1 verifierCRF1 t)))
      i1 = axPost verifierCRF1 Pair a bb
  in liftedRuleTransTwo P1 P2 (ap2 body_congR_v a bb) (ap1 verifierCRF1 t)
       (ap2 Pair outLeft outRight) (liftAxiomTwo P1 P2 i1) verifierEqL
