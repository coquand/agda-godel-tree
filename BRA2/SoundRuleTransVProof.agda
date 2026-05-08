{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SoundRuleTransVProof
--
-- Evaluation proofs for body_ruleTrans_v.  Three variants:
--   * closed:        body_ruleTrans_v_eval_pass
--   * lifted:        body_ruleTrans_v_eval_pass_l   (Deriv (P imp ...))
--   * doubly lifted: body_ruleTrans_v_eval_pass_dl  (Deriv (P1 imp (P2 imp ...)))
--
-- Hypotheses (closed form):
--   * ihShape : ap1 Snd bb = ap2 Pair tjY1 tjY2     (= distH)
--   * d1      : tjY1 = ap2 Pair u1 u2
--   * d2      : tjY2 = ap2 Pair u3 u4
-- Conclusion:
--   ap2 body_ruleTrans_v a bb = ap2 Pair u1 u4 .

module BRA2.SoundRuleTransVProof where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.EvalHelpers
  using ( liftAxiom ; liftAxiomTwo
        ; liftedRuleTrans ; liftedRuleTransTwo
        ; liftedCong1 ; liftedCong1Two
        ; liftedCongL ; liftedCongLTwo
        ; liftedCongR ; liftedCongRTwo )

----------------------------------------------------------------------
-- Body and helpers (formerly in BRA2.SoundRuleTransProto).

----------------------------------------------------------------------
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Snd t            = bb
--   Snd(Snd t)       = Snd bb               -- the IH distribution
--   Fst(Snd(Snd t))  = Fst(Snd bb) = tjY1
--   Fst(Fst(Snd(Snd t))) = Fst tjY1 = u1
--   Snd(Snd(Snd t))  = Snd(Snd bb) = tjY2
--   Snd(Snd(Snd(Snd t))) = Snd tjY2 = u4

getDisc : Fun1
getDisc = Comp Snd Snd

getU1 : Fun1
getU1 = Comp Fst (Comp Fst getDisc)

getU4 : Fun1
getU4 = Comp Snd (Comp Snd getDisc)

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair getU1 getU4

verifierRTF1 : Fun1
verifierRTF1 =
  Comp2 IfLf getDisc
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

body_ruleTrans_v : Fun2
body_ruleTrans_v = Post verifierRTF1 Pair
----------------------------------------------------------------------
-- Common helper: ap1 (Comp Snd Snd) (Pair a bb) = Snd bb .
private
  getDiscEq : (a bb : Term) ->
    Deriv (atomic (eqn (ap1 getDisc (ap2 Pair a bb)) (ap1 Snd bb)))
  getDiscEq a bb =
    let t = ap2 Pair a bb
        e1 = axComp Snd Snd t
        e2 = axSnd a bb
        e3 = cong1 Snd e2
    in ruleTrans e1 e3

----------------------------------------------------------------------
-- Closed variant.

body_ruleTrans_v_eval_pass :
  (a bb : Term) (tjY1 tjY2 u1 u2 u3 u4 : Term) ->
  Deriv (atomic (eqn (ap1 Snd bb) (ap2 Pair tjY1 tjY2))) ->
  Deriv (atomic (eqn tjY1 (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn tjY2 (ap2 Pair u3 u4))) ->
  Deriv (atomic (eqn (ap2 body_ruleTrans_v a bb) (ap2 Pair u1 u4)))
body_ruleTrans_v_eval_pass a bb tjY1 tjY2 u1 u2 u3 u4 ihShape d1 d2 =
  let
      t : Term
      t = ap2 Pair a bb

      ----------------------------------------------------------------
      -- Section A: getU1 t = u1.  Chain through positions
      --   A = getU1 t
      --   B = Fst (Comp Fst getDisc t)
      --   C = Fst (Fst (getDisc t))
      --   D = Fst (Fst (Snd bb))
      --   E = Fst (Fst (Pair tjY1 tjY2)) = Fst tjY1
      --   F = Fst (Pair u1 u2)
      --   H = u1

      discEq : Deriv (atomic (eqn (ap1 getDisc t) (ap1 Snd bb)))
      discEq = getDiscEq a bb

      ab : Deriv (atomic (eqn (ap1 getU1 t) (ap1 Fst (ap1 (Comp Fst getDisc) t))))
      ab = axComp Fst (Comp Fst getDisc) t

      bc : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Fst getDisc) t))
                               (ap1 Fst (ap1 Fst (ap1 getDisc t)))))
      bc = cong1 Fst (axComp Fst getDisc t)

      cd : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 getDisc t)))
                               (ap1 Fst (ap1 Fst (ap1 Snd bb)))))
      cd = cong1 Fst (cong1 Fst discEq)

      de : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd bb)))
                               (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))))
      de = cong1 Fst (cong1 Fst ihShape)

      ef : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))
                               (ap1 Fst tjY1)))
      ef = cong1 Fst (axFst tjY1 tjY2)

      fg : Deriv (atomic (eqn (ap1 Fst tjY1) (ap1 Fst (ap2 Pair u1 u2))))
      fg = cong1 Fst d1

      gh : Deriv (atomic (eqn (ap1 Fst (ap2 Pair u1 u2)) u1))
      gh = axFst u1 u2

      getU1Eq : Deriv (atomic (eqn (ap1 getU1 t) u1))
      getU1Eq = ruleTrans ab (ruleTrans bc (ruleTrans cd
                 (ruleTrans de (ruleTrans ef (ruleTrans fg gh)))))

      ----------------------------------------------------------------
      -- Section B: getU4 t = u4.  Mirror chain.

      ab2 : Deriv (atomic (eqn (ap1 getU4 t) (ap1 Snd (ap1 (Comp Snd getDisc) t))))
      ab2 = axComp Snd (Comp Snd getDisc) t

      bc2 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd getDisc) t))
                                (ap1 Snd (ap1 Snd (ap1 getDisc t)))))
      bc2 = cong1 Snd (axComp Snd getDisc t)

      cd2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap1 getDisc t)))
                                (ap1 Snd (ap1 Snd (ap1 Snd bb)))))
      cd2 = cong1 Snd (cong1 Snd discEq)

      de2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap1 Snd bb)))
                                (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))))
      de2 = cong1 Snd (cong1 Snd ihShape)

      ef2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))
                                (ap1 Snd tjY2)))
      ef2 = cong1 Snd (axSnd tjY1 tjY2)

      fg2 : Deriv (atomic (eqn (ap1 Snd tjY2) (ap1 Snd (ap2 Pair u3 u4))))
      fg2 = cong1 Snd d2

      gh2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair u3 u4)) u4))
      gh2 = axSnd u3 u4

      getU4Eq : Deriv (atomic (eqn (ap1 getU4 t) u4))
      getU4Eq = ruleTrans ab2 (ruleTrans bc2 (ruleTrans cd2
                 (ruleTrans de2 (ruleTrans ef2 (ruleTrans fg2 gh2)))))

      ----------------------------------------------------------------
      -- Section C: doAssemblyF1 t = Pair u1 u4.

      assStep1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                                     (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))))
      assStep1 = axComp2 Pair getU1 getU4 t

      assStep2 : Deriv (atomic (eqn (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))
                                     (ap2 Pair u1 (ap1 getU4 t))))
      assStep2 = congL Pair (ap1 getU4 t) getU1Eq

      assStep3 : Deriv (atomic (eqn (ap2 Pair u1 (ap1 getU4 t)) (ap2 Pair u1 u4)))
      assStep3 = congR Pair u1 getU4Eq

      doAssemblyEq : Deriv (atomic (eqn (ap1 doAssemblyF1 t) (ap2 Pair u1 u4)))
      doAssemblyEq = ruleTrans assStep1 (ruleTrans assStep2 assStep3)

      ----------------------------------------------------------------
      -- Section D: verifierRTF1 t = Pair u1 u4 via axIfLfN.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      vStep1 : Deriv (atomic (eqn (ap1 verifierRTF1 t)
                                   (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))))
      vStep1 = axComp2 IfLf getDisc branchesF1 t

      vStep2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                                   (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      vStep2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      vStep3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      vStep3 = axKT (codeFormula (atomic (eqn O O)))
                    (codeFormula_isValue (atomic (eqn O O)))
                    t

      vStep4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
                                   (ap2 Pair codeTriv (ap1 doAssemblyF1 t))))
      vStep4 = congL Pair (ap1 doAssemblyF1 t) vStep3

      vStep5 : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
                                   (ap2 Pair codeTriv (ap2 Pair u1 u4))))
      vStep5 = congR Pair codeTriv doAssemblyEq

      branchesEq : Deriv (atomic (eqn (ap1 branchesF1 t)
                                       (ap2 Pair codeTriv (ap2 Pair u1 u4))))
      branchesEq = ruleTrans vStep2 (ruleTrans vStep4 vStep5)

      -- Combine: discriminant equals  Pair tjY1 tjY2 .
      discPair : Deriv (atomic (eqn (ap1 getDisc t) (ap2 Pair tjY1 tjY2)))
      discPair = ruleTrans discEq ihShape

      vStep6 : Deriv (atomic (eqn (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))
                                   (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))))
      vStep6 = congL IfLf (ap1 branchesF1 t) discPair

      vStep7 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
                                   (ap2 IfLf (ap2 Pair tjY1 tjY2)
                                              (ap2 Pair codeTriv (ap2 Pair u1 u4)))))
      vStep7 = congR IfLf (ap2 Pair tjY1 tjY2) branchesEq

      vStep8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair tjY1 tjY2)
                                              (ap2 Pair codeTriv (ap2 Pair u1 u4)))
                                   (ap2 Pair u1 u4)))
      vStep8 = axIfLfN tjY1 tjY2 codeTriv (ap2 Pair u1 u4)

      verifierEq : Deriv (atomic (eqn (ap1 verifierRTF1 t) (ap2 Pair u1 u4)))
      verifierEq = ruleTrans vStep1 (ruleTrans vStep6 (ruleTrans vStep7 vStep8))

      ----------------------------------------------------------------
      i1 : Deriv (atomic (eqn (ap2 body_ruleTrans_v a bb) (ap1 verifierRTF1 t)))
      i1 = axPost verifierRTF1 Pair a bb
  in ruleTrans i1 verifierEq

----------------------------------------------------------------------
-- Lifted variant.

body_ruleTrans_v_eval_pass_l :
  (P : Formula) (a bb : Term) (tjY1 tjY2 u1 u2 u3 u4 : Term) ->
  Deriv (P imp atomic (eqn (ap1 Snd bb) (ap2 Pair tjY1 tjY2))) ->
  Deriv (P imp atomic (eqn tjY1 (ap2 Pair u1 u2))) ->
  Deriv (P imp atomic (eqn tjY2 (ap2 Pair u3 u4))) ->
  Deriv (P imp atomic (eqn (ap2 body_ruleTrans_v a bb) (ap2 Pair u1 u4)))
body_ruleTrans_v_eval_pass_l P a bb tjY1 tjY2 u1 u2 u3 u4 ihShapeL d1L d2L =
  let
      t : Term
      t = ap2 Pair a bb

      discEq : Deriv (atomic (eqn (ap1 getDisc t) (ap1 Snd bb)))
      discEq = getDiscEq a bb

      ----------------------------------------------------------------
      -- Section A (lifted): getU1 t = u1.

      ab : Deriv (atomic (eqn (ap1 getU1 t) (ap1 Fst (ap1 (Comp Fst getDisc) t))))
      ab = axComp Fst (Comp Fst getDisc) t

      bc : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Fst getDisc) t))
                               (ap1 Fst (ap1 Fst (ap1 getDisc t)))))
      bc = cong1 Fst (axComp Fst getDisc t)

      cd : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 getDisc t)))
                               (ap1 Fst (ap1 Fst (ap1 Snd bb)))))
      cd = cong1 Fst (cong1 Fst discEq)

      deL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd bb)))
                               (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))))
      deL = liftedCong1 P Fst (ap1 Fst (ap1 Snd bb)) (ap1 Fst (ap2 Pair tjY1 tjY2))
              (liftedCong1 P Fst (ap1 Snd bb) (ap2 Pair tjY1 tjY2) ihShapeL)

      ef : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))
                               (ap1 Fst tjY1)))
      ef = cong1 Fst (axFst tjY1 tjY2)

      fgL : Deriv (P imp atomic (eqn (ap1 Fst tjY1) (ap1 Fst (ap2 Pair u1 u2))))
      fgL = liftedCong1 P Fst tjY1 (ap2 Pair u1 u2) d1L

      gh : Deriv (atomic (eqn (ap1 Fst (ap2 Pair u1 u2)) u1))
      gh = axFst u1 u2

      getU1EqL : Deriv (P imp atomic (eqn (ap1 getU1 t) u1))
      getU1EqL =
        liftedRuleTrans P (ap1 getU1 t) (ap1 Fst (ap1 (Comp Fst getDisc) t)) u1
          (liftAxiom P ab)
          (liftedRuleTrans P (ap1 Fst (ap1 (Comp Fst getDisc) t))
             (ap1 Fst (ap1 Fst (ap1 getDisc t))) u1
             (liftAxiom P bc)
             (liftedRuleTrans P (ap1 Fst (ap1 Fst (ap1 getDisc t)))
                (ap1 Fst (ap1 Fst (ap1 Snd bb))) u1
                (liftAxiom P cd)
                (liftedRuleTrans P (ap1 Fst (ap1 Fst (ap1 Snd bb)))
                   (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2))) u1
                   deL
                   (liftedRuleTrans P (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))
                      (ap1 Fst tjY1) u1
                      (liftAxiom P ef)
                      (liftedRuleTrans P (ap1 Fst tjY1) (ap1 Fst (ap2 Pair u1 u2)) u1
                         fgL (liftAxiom P gh))))))

      ----------------------------------------------------------------
      -- Section B (lifted): getU4 t = u4.

      ab2 : Deriv (atomic (eqn (ap1 getU4 t) (ap1 Snd (ap1 (Comp Snd getDisc) t))))
      ab2 = axComp Snd (Comp Snd getDisc) t

      bc2 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd getDisc) t))
                                (ap1 Snd (ap1 Snd (ap1 getDisc t)))))
      bc2 = cong1 Snd (axComp Snd getDisc t)

      cd2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap1 getDisc t)))
                                (ap1 Snd (ap1 Snd (ap1 Snd bb)))))
      cd2 = cong1 Snd (cong1 Snd discEq)

      de2L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd (ap1 Snd bb)))
                                (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))))
      de2L = liftedCong1 P Snd (ap1 Snd (ap1 Snd bb)) (ap1 Snd (ap2 Pair tjY1 tjY2))
               (liftedCong1 P Snd (ap1 Snd bb) (ap2 Pair tjY1 tjY2) ihShapeL)

      ef2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))
                                (ap1 Snd tjY2)))
      ef2 = cong1 Snd (axSnd tjY1 tjY2)

      fg2L : Deriv (P imp atomic (eqn (ap1 Snd tjY2) (ap1 Snd (ap2 Pair u3 u4))))
      fg2L = liftedCong1 P Snd tjY2 (ap2 Pair u3 u4) d2L

      gh2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair u3 u4)) u4))
      gh2 = axSnd u3 u4

      getU4EqL : Deriv (P imp atomic (eqn (ap1 getU4 t) u4))
      getU4EqL =
        liftedRuleTrans P (ap1 getU4 t) (ap1 Snd (ap1 (Comp Snd getDisc) t)) u4
          (liftAxiom P ab2)
          (liftedRuleTrans P (ap1 Snd (ap1 (Comp Snd getDisc) t))
             (ap1 Snd (ap1 Snd (ap1 getDisc t))) u4
             (liftAxiom P bc2)
             (liftedRuleTrans P (ap1 Snd (ap1 Snd (ap1 getDisc t)))
                (ap1 Snd (ap1 Snd (ap1 Snd bb))) u4
                (liftAxiom P cd2)
                (liftedRuleTrans P (ap1 Snd (ap1 Snd (ap1 Snd bb)))
                   (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2))) u4
                   de2L
                   (liftedRuleTrans P (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))
                      (ap1 Snd tjY2) u4
                      (liftAxiom P ef2)
                      (liftedRuleTrans P (ap1 Snd tjY2) (ap1 Snd (ap2 Pair u3 u4)) u4
                         fg2L (liftAxiom P gh2))))))

      ----------------------------------------------------------------
      -- Section C (lifted): doAssemblyF1 t = Pair u1 u4.

      assStep1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                                     (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))))
      assStep1 = axComp2 Pair getU1 getU4 t

      assStep2L : Deriv (P imp atomic (eqn (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))
                                            (ap2 Pair u1 (ap1 getU4 t))))
      assStep2L = liftedCongL P Pair (ap1 getU1 t) u1 (ap1 getU4 t) getU1EqL

      assStep3L : Deriv (P imp atomic (eqn (ap2 Pair u1 (ap1 getU4 t)) (ap2 Pair u1 u4)))
      assStep3L = liftedCongR P Pair (ap1 getU4 t) u4 u1 getU4EqL

      doAssemblyEqL : Deriv (P imp atomic (eqn (ap1 doAssemblyF1 t) (ap2 Pair u1 u4)))
      doAssemblyEqL =
        liftedRuleTrans P (ap1 doAssemblyF1 t)
          (ap2 Pair (ap1 getU1 t) (ap1 getU4 t)) (ap2 Pair u1 u4)
          (liftAxiom P assStep1)
          (liftedRuleTrans P (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))
             (ap2 Pair u1 (ap1 getU4 t)) (ap2 Pair u1 u4) assStep2L assStep3L)

      ----------------------------------------------------------------
      -- Section D (lifted): verifierRTF1 t = Pair u1 u4.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      vStep1 : Deriv (atomic (eqn (ap1 verifierRTF1 t)
                                   (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))))
      vStep1 = axComp2 IfLf getDisc branchesF1 t

      vStep2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                                   (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      vStep2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      vStep3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      vStep3 = axKT (codeFormula (atomic (eqn O O)))
                    (codeFormula_isValue (atomic (eqn O O)))
                    t

      vStep4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
                                   (ap2 Pair codeTriv (ap1 doAssemblyF1 t))))
      vStep4 = congL Pair (ap1 doAssemblyF1 t) vStep3

      vStep5L : Deriv (P imp atomic (eqn (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
                                          (ap2 Pair codeTriv (ap2 Pair u1 u4))))
      vStep5L = liftedCongR P Pair (ap1 doAssemblyF1 t) (ap2 Pair u1 u4)
                  codeTriv doAssemblyEqL

      branchesEqL : Deriv (P imp atomic (eqn (ap1 branchesF1 t)
                                              (ap2 Pair codeTriv (ap2 Pair u1 u4))))
      branchesEqL =
        liftedRuleTrans P (ap1 branchesF1 t)
          (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
          (ap2 Pair codeTriv (ap2 Pair u1 u4))
          (liftAxiom P vStep2)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap2 Pair u1 u4))
             (liftAxiom P vStep4) vStep5L)

      discPairL : Deriv (P imp atomic (eqn (ap1 getDisc t) (ap2 Pair tjY1 tjY2)))
      discPairL = liftedRuleTrans P (ap1 getDisc t) (ap1 Snd bb) (ap2 Pair tjY1 tjY2)
                    (liftAxiom P discEq) ihShapeL

      vStep6L : Deriv (P imp atomic (eqn (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))
                                          (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))))
      vStep6L = liftedCongL P IfLf (ap1 getDisc t) (ap2 Pair tjY1 tjY2)
                  (ap1 branchesF1 t) discPairL

      vStep7L : Deriv (P imp atomic (eqn (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
                                          (ap2 IfLf (ap2 Pair tjY1 tjY2)
                                                     (ap2 Pair codeTriv (ap2 Pair u1 u4)))))
      vStep7L = liftedCongR P IfLf (ap1 branchesF1 t)
                  (ap2 Pair codeTriv (ap2 Pair u1 u4)) (ap2 Pair tjY1 tjY2) branchesEqL

      vStep8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair tjY1 tjY2)
                                              (ap2 Pair codeTriv (ap2 Pair u1 u4)))
                                   (ap2 Pair u1 u4)))
      vStep8 = axIfLfN tjY1 tjY2 codeTriv (ap2 Pair u1 u4)

      verifierEqL : Deriv (P imp atomic (eqn (ap1 verifierRTF1 t) (ap2 Pair u1 u4)))
      verifierEqL =
        liftedRuleTrans P (ap1 verifierRTF1 t)
          (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t)) (ap2 Pair u1 u4)
          (liftAxiom P vStep1)
          (liftedRuleTrans P
             (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))
             (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
             (ap2 Pair u1 u4)
             vStep6L
             (liftedRuleTrans P
                (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
                (ap2 IfLf (ap2 Pair tjY1 tjY2)
                          (ap2 Pair codeTriv (ap2 Pair u1 u4)))
                (ap2 Pair u1 u4)
                vStep7L (liftAxiom P vStep8)))

      i1 : Deriv (atomic (eqn (ap2 body_ruleTrans_v a bb) (ap1 verifierRTF1 t)))
      i1 = axPost verifierRTF1 Pair a bb
  in liftedRuleTrans P (ap2 body_ruleTrans_v a bb) (ap1 verifierRTF1 t)
       (ap2 Pair u1 u4) (liftAxiom P i1) verifierEqL

----------------------------------------------------------------------
-- Doubly-lifted variant.

body_ruleTrans_v_eval_pass_dl :
  (P1 P2 : Formula) (a bb : Term) (tjY1 tjY2 u1 u2 u3 u4 : Term) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd bb) (ap2 Pair tjY1 tjY2)))) ->
  Deriv (P1 imp (P2 imp atomic (eqn tjY1 (ap2 Pair u1 u2)))) ->
  Deriv (P1 imp (P2 imp atomic (eqn tjY2 (ap2 Pair u3 u4)))) ->
  Deriv (P1 imp (P2 imp atomic (eqn (ap2 body_ruleTrans_v a bb) (ap2 Pair u1 u4))))
body_ruleTrans_v_eval_pass_dl P1 P2 a bb tjY1 tjY2 u1 u2 u3 u4 ihShapeL d1L d2L =
  let
      t : Term
      t = ap2 Pair a bb

      discEq : Deriv (atomic (eqn (ap1 getDisc t) (ap1 Snd bb)))
      discEq = getDiscEq a bb

      ab : Deriv (atomic (eqn (ap1 getU1 t) (ap1 Fst (ap1 (Comp Fst getDisc) t))))
      ab = axComp Fst (Comp Fst getDisc) t
      bc : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Fst getDisc) t))
                               (ap1 Fst (ap1 Fst (ap1 getDisc t)))))
      bc = cong1 Fst (axComp Fst getDisc t)
      cd : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 getDisc t)))
                               (ap1 Fst (ap1 Fst (ap1 Snd bb)))))
      cd = cong1 Fst (cong1 Fst discEq)

      deL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd bb)))
                               (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2))))))
      deL = liftedCong1Two P1 P2 Fst (ap1 Fst (ap1 Snd bb)) (ap1 Fst (ap2 Pair tjY1 tjY2))
              (liftedCong1Two P1 P2 Fst (ap1 Snd bb) (ap2 Pair tjY1 tjY2) ihShapeL)

      ef : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))
                               (ap1 Fst tjY1)))
      ef = cong1 Fst (axFst tjY1 tjY2)

      fgL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Fst tjY1) (ap1 Fst (ap2 Pair u1 u2)))))
      fgL = liftedCong1Two P1 P2 Fst tjY1 (ap2 Pair u1 u2) d1L

      gh : Deriv (atomic (eqn (ap1 Fst (ap2 Pair u1 u2)) u1))
      gh = axFst u1 u2

      getU1EqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getU1 t) u1)))
      getU1EqL =
        liftedRuleTransTwo P1 P2 (ap1 getU1 t) (ap1 Fst (ap1 (Comp Fst getDisc) t)) u1
          (liftAxiomTwo P1 P2 ab)
          (liftedRuleTransTwo P1 P2 (ap1 Fst (ap1 (Comp Fst getDisc) t))
             (ap1 Fst (ap1 Fst (ap1 getDisc t))) u1
             (liftAxiomTwo P1 P2 bc)
             (liftedRuleTransTwo P1 P2 (ap1 Fst (ap1 Fst (ap1 getDisc t)))
                (ap1 Fst (ap1 Fst (ap1 Snd bb))) u1
                (liftAxiomTwo P1 P2 cd)
                (liftedRuleTransTwo P1 P2 (ap1 Fst (ap1 Fst (ap1 Snd bb)))
                   (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2))) u1
                   deL
                   (liftedRuleTransTwo P1 P2 (ap1 Fst (ap1 Fst (ap2 Pair tjY1 tjY2)))
                      (ap1 Fst tjY1) u1
                      (liftAxiomTwo P1 P2 ef)
                      (liftedRuleTransTwo P1 P2 (ap1 Fst tjY1) (ap1 Fst (ap2 Pair u1 u2)) u1
                         fgL (liftAxiomTwo P1 P2 gh))))))

      ab2 : Deriv (atomic (eqn (ap1 getU4 t) (ap1 Snd (ap1 (Comp Snd getDisc) t))))
      ab2 = axComp Snd (Comp Snd getDisc) t
      bc2 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd getDisc) t))
                                (ap1 Snd (ap1 Snd (ap1 getDisc t)))))
      bc2 = cong1 Snd (axComp Snd getDisc t)
      cd2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap1 getDisc t)))
                                (ap1 Snd (ap1 Snd (ap1 Snd bb)))))
      cd2 = cong1 Snd (cong1 Snd discEq)

      de2L : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Snd (ap1 Snd bb)))
                                (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2))))))
      de2L = liftedCong1Two P1 P2 Snd (ap1 Snd (ap1 Snd bb)) (ap1 Snd (ap2 Pair tjY1 tjY2))
               (liftedCong1Two P1 P2 Snd (ap1 Snd bb) (ap2 Pair tjY1 tjY2) ihShapeL)

      ef2 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))
                                (ap1 Snd tjY2)))
      ef2 = cong1 Snd (axSnd tjY1 tjY2)

      fg2L : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd tjY2) (ap1 Snd (ap2 Pair u3 u4)))))
      fg2L = liftedCong1Two P1 P2 Snd tjY2 (ap2 Pair u3 u4) d2L

      gh2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair u3 u4)) u4))
      gh2 = axSnd u3 u4

      getU4EqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getU4 t) u4)))
      getU4EqL =
        liftedRuleTransTwo P1 P2 (ap1 getU4 t) (ap1 Snd (ap1 (Comp Snd getDisc) t)) u4
          (liftAxiomTwo P1 P2 ab2)
          (liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 (Comp Snd getDisc) t))
             (ap1 Snd (ap1 Snd (ap1 getDisc t))) u4
             (liftAxiomTwo P1 P2 bc2)
             (liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 Snd (ap1 getDisc t)))
                (ap1 Snd (ap1 Snd (ap1 Snd bb))) u4
                (liftAxiomTwo P1 P2 cd2)
                (liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 Snd (ap1 Snd bb)))
                   (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2))) u4
                   de2L
                   (liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 Snd (ap2 Pair tjY1 tjY2)))
                      (ap1 Snd tjY2) u4
                      (liftAxiomTwo P1 P2 ef2)
                      (liftedRuleTransTwo P1 P2 (ap1 Snd tjY2) (ap1 Snd (ap2 Pair u3 u4)) u4
                         fg2L (liftAxiomTwo P1 P2 gh2))))))

      assStep1 : Deriv (atomic (eqn (ap1 doAssemblyF1 t)
                                     (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))))
      assStep1 = axComp2 Pair getU1 getU4 t

      assStep2L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))
                                            (ap2 Pair u1 (ap1 getU4 t)))))
      assStep2L = liftedCongLTwo P1 P2 Pair (ap1 getU1 t) u1 (ap1 getU4 t) getU1EqL

      assStep3L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair u1 (ap1 getU4 t)) (ap2 Pair u1 u4))))
      assStep3L = liftedCongRTwo P1 P2 Pair (ap1 getU4 t) u4 u1 getU4EqL

      doAssemblyEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 doAssemblyF1 t) (ap2 Pair u1 u4))))
      doAssemblyEqL =
        liftedRuleTransTwo P1 P2 (ap1 doAssemblyF1 t)
          (ap2 Pair (ap1 getU1 t) (ap1 getU4 t)) (ap2 Pair u1 u4)
          (liftAxiomTwo P1 P2 assStep1)
          (liftedRuleTransTwo P1 P2 (ap2 Pair (ap1 getU1 t) (ap1 getU4 t))
             (ap2 Pair u1 (ap1 getU4 t)) (ap2 Pair u1 u4) assStep2L assStep3L)

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doAssemblyF1

      vStep1 : Deriv (atomic (eqn (ap1 verifierRTF1 t)
                                   (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))))
      vStep1 = axComp2 IfLf getDisc branchesF1 t

      vStep2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                                   (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))))
      vStep2 = axComp2 Pair (KT codeTriv) doAssemblyF1 t

      vStep3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      vStep3 = axKT (codeFormula (atomic (eqn O O)))
                    (codeFormula_isValue (atomic (eqn O O)))
                    t

      vStep4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
                                   (ap2 Pair codeTriv (ap1 doAssemblyF1 t))))
      vStep4 = congL Pair (ap1 doAssemblyF1 t) vStep3

      vStep5L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
                                          (ap2 Pair codeTriv (ap2 Pair u1 u4)))))
      vStep5L = liftedCongRTwo P1 P2 Pair (ap1 doAssemblyF1 t) (ap2 Pair u1 u4)
                  codeTriv doAssemblyEqL

      branchesEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 branchesF1 t)
                                              (ap2 Pair codeTriv (ap2 Pair u1 u4)))))
      branchesEqL =
        liftedRuleTransTwo P1 P2 (ap1 branchesF1 t)
          (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
          (ap2 Pair codeTriv (ap2 Pair u1 u4))
          (liftAxiomTwo P1 P2 vStep2)
          (liftedRuleTransTwo P1 P2
             (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap1 doAssemblyF1 t))
             (ap2 Pair codeTriv (ap2 Pair u1 u4))
             (liftAxiomTwo P1 P2 vStep4) vStep5L)

      discPairL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 getDisc t) (ap2 Pair tjY1 tjY2))))
      discPairL = liftedRuleTransTwo P1 P2 (ap1 getDisc t) (ap1 Snd bb) (ap2 Pair tjY1 tjY2)
                    (liftAxiomTwo P1 P2 discEq) ihShapeL

      vStep6L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))
                                          (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t)))))
      vStep6L = liftedCongLTwo P1 P2 IfLf (ap1 getDisc t) (ap2 Pair tjY1 tjY2)
                  (ap1 branchesF1 t) discPairL

      vStep7L : Deriv (P1 imp (P2 imp atomic (eqn (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
                                          (ap2 IfLf (ap2 Pair tjY1 tjY2)
                                                     (ap2 Pair codeTriv (ap2 Pair u1 u4))))))
      vStep7L = liftedCongRTwo P1 P2 IfLf (ap1 branchesF1 t)
                  (ap2 Pair codeTriv (ap2 Pair u1 u4)) (ap2 Pair tjY1 tjY2) branchesEqL

      vStep8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair tjY1 tjY2)
                                              (ap2 Pair codeTriv (ap2 Pair u1 u4)))
                                   (ap2 Pair u1 u4)))
      vStep8 = axIfLfN tjY1 tjY2 codeTriv (ap2 Pair u1 u4)

      verifierEqL : Deriv (P1 imp (P2 imp atomic (eqn (ap1 verifierRTF1 t) (ap2 Pair u1 u4))))
      verifierEqL =
        liftedRuleTransTwo P1 P2 (ap1 verifierRTF1 t)
          (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t)) (ap2 Pair u1 u4)
          (liftAxiomTwo P1 P2 vStep1)
          (liftedRuleTransTwo P1 P2
             (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))
             (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
             (ap2 Pair u1 u4)
             vStep6L
             (liftedRuleTransTwo P1 P2
                (ap2 IfLf (ap2 Pair tjY1 tjY2) (ap1 branchesF1 t))
                (ap2 IfLf (ap2 Pair tjY1 tjY2)
                          (ap2 Pair codeTriv (ap2 Pair u1 u4)))
                (ap2 Pair u1 u4)
                vStep7L (liftAxiomTwo P1 P2 vStep8)))

      i1 : Deriv (atomic (eqn (ap2 body_ruleTrans_v a bb) (ap1 verifierRTF1 t)))
      i1 = axPost verifierRTF1 Pair a bb
  in liftedRuleTransTwo P1 P2 (ap2 body_ruleTrans_v a bb) (ap1 verifierRTF1 t)
       (ap2 Pair u1 u4) (liftAxiomTwo P1 P2 i1) verifierEqL
