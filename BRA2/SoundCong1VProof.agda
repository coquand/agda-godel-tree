{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SoundCong1VProof
--
-- Evaluation proof for body_cong1_v under the "pass" branch hypotheses:
--   * payFExt : ap1 Fst (ap1 Snd a) = payF              (closed args extractor)
--   * ihShape : ap1 Snd (ap1 Snd bb) = ap2 Pair fp sp   (IH Pair-shape)
--
-- conclude:
--   ap2 body_cong1_v a bb =
--     ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair payF fp))
--               (ap2 Pair (reify tagAp1) (ap2 Pair payF sp)).
--
-- Identifier convention: camelCase.  ASCII only.

module BRA2.SoundCong1VProof where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.EvalHelpers
  using ( liftAxiom ; liftedRuleTrans ; liftedCong1 ; liftedCongL ; liftedCongR )

----------------------------------------------------------------------
-- Body and helpers (formerly in SoundCong1Proto).

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

-- Extractors over t = Pair a bb.
--   Fst(Snd(Fst t))  = Fst(Snd a)   = payF
--   Snd(Snd(Snd t))  = Snd(Snd bb)  = thmT y_h_r  (the IH)

getPayF : Fun1
getPayF = Comp Fst (Comp Snd Fst)

getIH : Fun1
getIH = Comp Snd (Comp Snd Snd)

getFstIH : Fun1
getFstIH = Comp Fst getIH

getSndIH : Fun1
getSndIH = Comp Snd getIH

-- Half-assemblers : build Pair tagAp1 (Pair payF X) where X = Fst(IH) or Snd(IH).

assemblyHalf : Fun1 -> Fun1
assemblyHalf getX = Comp2 Pair (KT (reify tagAp1)) (Comp2 Pair getPayF getX)

assemblyLeftF1 : Fun1
assemblyLeftF1 = assemblyHalf getFstIH

assemblyRightF1 : Fun1
assemblyRightF1 = assemblyHalf getSndIH

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair assemblyLeftF1 assemblyRightF1

-- Verifier: IfLf-gate on the IH (= Snd(Snd bb)).

verifierC1F1 : Fun1
verifierC1F1 =
  Comp2 IfLf getIH
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

-- The verifying body for cong1.

body_cong1_v : Fun2
body_cong1_v = Post verifierC1F1 Pair

----------------------------------------------------------------------
-- Closed-Term variant.

body_cong1_v_eval_pass :
  (a bb : Term) (payF fp sp : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) payF)) ->
  Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair fp sp))) ->
  Deriv (atomic (eqn (ap2 body_cong1_v a bb)
                     (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair payF fp))
                                (ap2 Pair (reify tagAp1) (ap2 Pair payF sp)))))
body_cong1_v_eval_pass a bb payF fp sp payFExt ihShape =
  let
      t : Term
      t = ap2 Pair a bb
      tagAp1T : Term
      tagAp1T = reify tagAp1
      outLeft : Term
      outLeft = ap2 Pair tagAp1T (ap2 Pair payF fp)
      outRight : Term
      outRight = ap2 Pair tagAp1T (ap2 Pair payF sp)

      ----------------------------------------------------------------
      -- Section A: ap1 getPayF t = payF.
      --   getPayF = Comp Fst (Comp Snd Fst)
      --   ap1 getPayF t = Fst(Comp Snd Fst t)
      --                 = Fst(Snd(Fst t)) = Fst(Snd a) = payF (via payFExt).

      a1 : Deriv (atomic (eqn (ap1 getPayF t)
                              (ap1 Fst (ap1 (Comp Snd Fst) t))))
      a1 = axComp Fst (Comp Snd Fst) t

      a2 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) t) (ap1 Snd (ap1 Fst t))))
      a2 = axComp Snd Fst t

      a3 : Deriv (atomic (eqn (ap1 Fst t) a))
      a3 = axFst a bb

      a4 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst t)) (ap1 Snd a)))
      a4 = cong1 Snd a3

      a5 : Deriv (atomic (eqn (ap1 (Comp Snd Fst) t) (ap1 Snd a)))
      a5 = ruleTrans a2 a4

      a6 : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Fst) t))
                              (ap1 Fst (ap1 Snd a))))
      a6 = cong1 Fst a5

      payFEq : Deriv (atomic (eqn (ap1 getPayF t) payF))
      payFEq = ruleTrans a1 (ruleTrans a6 payFExt)

      ----------------------------------------------------------------
      -- Section B: ap1 getIH t = ap1 Snd (ap1 Snd bb), then = Pair fp sp.
      --   getIH = Comp Snd (Comp Snd Snd)
      --   ap1 getIH t = Snd(Comp Snd Snd t) = Snd(Snd(Snd t)) = Snd(Snd bb) = Pair fp sp.

      b1 : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 (Comp Snd Snd) t))))
      b1 = axComp Snd (Comp Snd Snd) t

      b2 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap1 Snd (ap1 Snd t))))
      b2 = axComp Snd Snd t

      b3 : Deriv (atomic (eqn (ap1 Snd t) bb))
      b3 = axSnd a bb

      b4 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t)) (ap1 Snd bb)))
      b4 = cong1 Snd b3

      b5 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) t) (ap1 Snd bb)))
      b5 = ruleTrans b2 b4

      b6 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) t))
                              (ap1 Snd (ap1 Snd bb))))
      b6 = cong1 Snd b5

      getIHEq : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd bb))))
      getIHEq = ruleTrans b1 b6

      ihPair : Deriv (atomic (eqn (ap1 getIH t) (ap2 Pair fp sp)))
      ihPair = ruleTrans getIHEq ihShape

      ----------------------------------------------------------------
      -- Section C: ap1 getFstIH t = fp, ap1 getSndIH t = sp.

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
      --   assemblyLeftF1 = Comp2 Pair (KT tagAp1) (Comp2 Pair getPayF getFstIH)
      --   ap1 assemblyLeftF1 t = Pair (KT tagAp1 t) (Pair (getPayF t) (getFstIH t))
      --                        = Pair tagAp1 (Pair payF fp)

      e1 : Deriv (atomic (eqn (ap1 assemblyLeftF1 t)
                              (ap2 Pair (ap1 (KT tagAp1T) t)
                                        (ap1 (Comp2 Pair getPayF getFstIH) t))))
      e1 = axComp2 Pair (KT tagAp1T) (Comp2 Pair getPayF getFstIH) t

      e2 : Deriv (atomic (eqn (ap1 (KT tagAp1T) t) tagAp1T))
      e2 = axKT tagAp1 tagAp1_isValue t

      e3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayF getFstIH) t)
                              (ap2 Pair (ap1 getPayF t) (ap1 getFstIH t))))
      e3 = axComp2 Pair getPayF getFstIH t

      e4 : Deriv (atomic (eqn (ap2 Pair (ap1 getPayF t) (ap1 getFstIH t))
                              (ap2 Pair payF (ap1 getFstIH t))))
      e4 = congL Pair (ap1 getFstIH t) payFEq

      e5 : Deriv (atomic (eqn (ap2 Pair payF (ap1 getFstIH t)) (ap2 Pair payF fp)))
      e5 = congR Pair payF getFstIHEq

      e_inner : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayF getFstIH) t)
                                    (ap2 Pair payF fp)))
      e_inner = ruleTrans e3 (ruleTrans e4 e5)

      e6 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT tagAp1T) t)
                                         (ap1 (Comp2 Pair getPayF getFstIH) t))
                              (ap2 Pair tagAp1T
                                         (ap1 (Comp2 Pair getPayF getFstIH) t))))
      e6 = congL Pair (ap1 (Comp2 Pair getPayF getFstIH) t) e2

      e7 : Deriv (atomic (eqn (ap2 Pair tagAp1T
                                         (ap1 (Comp2 Pair getPayF getFstIH) t))
                              outLeft))
      e7 = congR Pair tagAp1T e_inner

      assemblyLeftEq : Deriv (atomic (eqn (ap1 assemblyLeftF1 t) outLeft))
      assemblyLeftEq = ruleTrans e1 (ruleTrans e6 e7)

      ----------------------------------------------------------------
      -- Section F: assemblyRightF1 t = outRight (mirror of E with sp instead of fp).

      f1 : Deriv (atomic (eqn (ap1 assemblyRightF1 t)
                              (ap2 Pair (ap1 (KT tagAp1T) t)
                                        (ap1 (Comp2 Pair getPayF getSndIH) t))))
      f1 = axComp2 Pair (KT tagAp1T) (Comp2 Pair getPayF getSndIH) t

      f3 : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayF getSndIH) t)
                              (ap2 Pair (ap1 getPayF t) (ap1 getSndIH t))))
      f3 = axComp2 Pair getPayF getSndIH t

      f4 : Deriv (atomic (eqn (ap2 Pair (ap1 getPayF t) (ap1 getSndIH t))
                              (ap2 Pair payF (ap1 getSndIH t))))
      f4 = congL Pair (ap1 getSndIH t) payFEq

      f5 : Deriv (atomic (eqn (ap2 Pair payF (ap1 getSndIH t)) (ap2 Pair payF sp)))
      f5 = congR Pair payF getSndIHEq

      f_inner : Deriv (atomic (eqn (ap1 (Comp2 Pair getPayF getSndIH) t)
                                    (ap2 Pair payF sp)))
      f_inner = ruleTrans f3 (ruleTrans f4 f5)

      f6 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT tagAp1T) t)
                                         (ap1 (Comp2 Pair getPayF getSndIH) t))
                              (ap2 Pair tagAp1T
                                         (ap1 (Comp2 Pair getPayF getSndIH) t))))
      f6 = congL Pair (ap1 (Comp2 Pair getPayF getSndIH) t) e2

      f7 : Deriv (atomic (eqn (ap2 Pair tagAp1T
                                         (ap1 (Comp2 Pair getPayF getSndIH) t))
                              outRight))
      f7 = congR Pair tagAp1T f_inner

      assemblyRightEq : Deriv (atomic (eqn (ap1 assemblyRightF1 t) outRight))
      assemblyRightEq = ruleTrans f1 (ruleTrans f6 f7)

      ----------------------------------------------------------------
      -- Section G: doAssemblyF1 t = Pair outLeft outRight.

      g1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                              (ap2 Pair (ap1 assemblyLeftF1 t)
                                        (ap1 assemblyRightF1 t))))
      g1 = axComp2 Pair assemblyLeftF1 assemblyRightF1 t

      g2 : Deriv (atomic (eqn (ap2 Pair (ap1 assemblyLeftF1 t)
                                         (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft (ap1 assemblyRightF1 t))))
      g2 = congL Pair (ap1 assemblyRightF1 t) assemblyLeftEq

      g3 : Deriv (atomic (eqn (ap2 Pair outLeft (ap1 assemblyRightF1 t))
                              (ap2 Pair outLeft outRight)))
      g3 = congR Pair outLeft assemblyRightEq

      doAssemblyEq : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                                         (ap2 Pair outLeft outRight)))
      doAssemblyEq = ruleTrans g1 (ruleTrans g2 g3)

      ----------------------------------------------------------------
      -- Section H: verifierC1F1 t reduces (via axIfLfN on Pair-shaped IH).

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      h1 : Deriv (atomic (eqn (ap1 verifierC1F1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      h1 = axComp2 IfLf getIH branchesF1 t

      h2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      h2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      h3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      h3 = axKT (codeFormula (atomic (eqn O O))) (codeFormula_isValue (atomic (eqn O O))) t

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

      verifierEq : Deriv (atomic (eqn (ap1 verifierC1F1 t) (ap2 Pair outLeft outRight)))
      verifierEq = ruleTrans h1 (ruleTrans h6 (ruleTrans h7 h8))

      ----------------------------------------------------------------
      -- Section I: body_cong1_v(a, bb) = ap1 verifierC1F1 t  via axPost.

      i1 : Deriv (atomic (eqn (ap2 body_cong1_v a bb) (ap1 verifierC1F1 t)))
      i1 = axPost verifierC1F1 Pair a bb

  in ruleTrans i1 verifierEq
