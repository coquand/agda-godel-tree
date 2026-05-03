{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleSymVProof
--
-- Evaluation proof for body_ruleSym_v under the "pass" branch
-- hypothesis: Snd bb is Pair-shaped, supplied by the caller as
--   sndB_eq : ap1 Snd bb = ap2 Pair fp sp .
--
-- Conclusion:
--   ap2 body_ruleSym_v a bb = ap2 Pair sp fp     (= the swap).
--
-- Identifier convention: camelCase.  ASCII only.  No postulates,
-- no holes, no with-abstraction.

module BRA.SoundRuleSymVProof where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.EvalHelpers
  using ( liftAxiom ; liftedRuleTrans ; liftedCong1 ; liftedCongL ; liftedCongR )

open import BRA.SoundRuleSymProto
  using ( body_ruleSym_v ; verifierRSF1 ; doSwapF1
        ; getIH ; getSndIH ; getFstIH ; codeTriv )

----------------------------------------------------------------------
-- Closed-Term variant.

body_ruleSym_v_eval_pass :
  (a bb : Term) (fp sp : Term) ->
  Deriv (atomic (eqn (ap1 Snd bb) (ap2 Pair fp sp))) ->
  Deriv (atomic (eqn (ap2 body_ruleSym_v a bb) (ap2 Pair sp fp)))
body_ruleSym_v_eval_pass a bb fp sp sndB_eq =
  let
      t : Term
      t = ap2 Pair a bb

      ----------------------------------------------------------------
      -- Section A: extract  ap1 Snd bb  via Comp Snd Snd applied to t.
      --   ap1 getIH t = Snd(Snd t) = Snd bb  via axComp + axSnd.

      a1 : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd t))))
      a1 = axComp Snd Snd t

      a2 : Deriv (atomic (eqn (ap1 Snd t) bb))
      a2 = axSnd a bb

      a3 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t)) (ap1 Snd bb)))
      a3 = cong1 Snd a2

      ihExtracted : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd bb)))
      ihExtracted = ruleTrans a1 a3

      ihPair : Deriv (atomic (eqn (ap1 getIH t) (ap2 Pair fp sp)))
      ihPair = ruleTrans ihExtracted sndB_eq

      ----------------------------------------------------------------
      -- Section B: extract  ap1 doSwapF1 t = Pair (Snd(Snd bb)) (Fst(Snd bb)),
      -- and then reduce to Pair sp fp using sndB_eq.

      b1 : Deriv (atomic (eqn (ap1 doSwapF1 t)
                              (ap2 Pair (ap1 getSndIH t) (ap1 getFstIH t))))
      b1 = axComp2 Pair getSndIH getFstIH t

      -- ap1 getSndIH t = Snd(Snd(Snd t)) = Snd(Snd bb) = sp via sndB_eq + axSnd.
      b2a : Deriv (atomic (eqn (ap1 getSndIH t)
                                (ap1 Snd (ap1 (Comp Snd Snd) t))))
      b2a = axComp Snd (Comp Snd Snd) t

      b2b : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) t))
                                (ap1 Snd (ap1 Snd bb))))
      b2b = cong1 Snd ihExtracted

      b2c : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                (ap1 Snd (ap2 Pair fp sp))))
      b2c = cong1 Snd sndB_eq

      b2d : Deriv (atomic (eqn (ap1 Snd (ap2 Pair fp sp)) sp))
      b2d = axSnd fp sp

      getSndIHEq : Deriv (atomic (eqn (ap1 getSndIH t) sp))
      getSndIHEq = ruleTrans b2a (ruleTrans b2b (ruleTrans b2c b2d))

      -- ap1 getFstIH t = Fst(Snd(Snd t)) = Fst(Snd bb) = fp via sndB_eq + axFst.
      b3a : Deriv (atomic (eqn (ap1 getFstIH t)
                                (ap1 Fst (ap1 (Comp Snd Snd) t))))
      b3a = axComp Fst (Comp Snd Snd) t

      b3b : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Snd) t))
                                (ap1 Fst (ap1 Snd bb))))
      b3b = cong1 Fst ihExtracted

      b3c : Deriv (atomic (eqn (ap1 Fst (ap1 Snd bb))
                                (ap1 Fst (ap2 Pair fp sp))))
      b3c = cong1 Fst sndB_eq

      b3d : Deriv (atomic (eqn (ap1 Fst (ap2 Pair fp sp)) fp))
      b3d = axFst fp sp

      getFstIHEq : Deriv (atomic (eqn (ap1 getFstIH t) fp))
      getFstIHEq = ruleTrans b3a (ruleTrans b3b (ruleTrans b3c b3d))

      -- Combine: doSwapF1 t = Pair sp fp.
      b4 : Deriv (atomic (eqn (ap2 Pair (ap1 getSndIH t) (ap1 getFstIH t))
                              (ap2 Pair sp (ap1 getFstIH t))))
      b4 = congL Pair (ap1 getFstIH t) getSndIHEq

      b5 : Deriv (atomic (eqn (ap2 Pair sp (ap1 getFstIH t)) (ap2 Pair sp fp)))
      b5 = congR Pair sp getFstIHEq

      doSwapEq : Deriv (atomic (eqn (ap1 doSwapF1 t) (ap2 Pair sp fp)))
      doSwapEq = ruleTrans b1 (ruleTrans b4 b5)

      ----------------------------------------------------------------
      -- Section C: verifierRSF1 t reduces.
      --   verifierRSF1 = Comp2 IfLf getIH (Comp2 Pair (KT codeTriv) doSwapF1)
      --   ap1 verifierRSF1 t
      --     = ap2 IfLf (ap1 getIH t) (ap1 (Comp2 Pair ...) t)
      --     = ap2 IfLf (Pair fp sp) (Pair codeTriv (ap1 doSwapF1 t))
      --     -> via axIfLfN -> ap1 doSwapF1 t = Pair sp fp.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doSwapF1

      c1 : Deriv (atomic (eqn (ap1 verifierRSF1 t)
                              (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      c1 = axComp2 IfLf getIH branchesF1 t

      c2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                              (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doSwapF1 t))))
      c2 = axComp2 Pair (KT codeTriv) doSwapF1 t

      c3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      c3 = axKT (codeFormula (atomic (eqn O O))) t

      c4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doSwapF1 t))
                              (ap2 Pair codeTriv (ap1 doSwapF1 t))))
      c4 = congL Pair (ap1 doSwapF1 t) c3

      c5 : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 doSwapF1 t))
                              (ap2 Pair codeTriv (ap2 Pair sp fp))))
      c5 = congR Pair codeTriv doSwapEq

      branchesEq : Deriv (atomic (eqn (ap1 branchesF1 t)
                                       (ap2 Pair codeTriv (ap2 Pair sp fp))))
      branchesEq = ruleTrans c2 (ruleTrans c4 c5)

      c6 : Deriv (atomic (eqn (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))))
      c6 = congL IfLf (ap1 branchesF1 t) ihPair

      c7 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                              (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair sp fp)))))
      c7 = congR IfLf (ap2 Pair fp sp) branchesEq

      c8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp)
                                         (ap2 Pair codeTriv (ap2 Pair sp fp)))
                              (ap2 Pair sp fp)))
      c8 = axIfLfN fp sp codeTriv (ap2 Pair sp fp)

      verifierEq : Deriv (atomic (eqn (ap1 verifierRSF1 t) (ap2 Pair sp fp)))
      verifierEq = ruleTrans c1 (ruleTrans c6 (ruleTrans c7 c8))

      ----------------------------------------------------------------
      -- Section D: body_ruleSym_v(a, bb) = ap1 verifierRSF1 t  via axPost.

      d1 : Deriv (atomic (eqn (ap2 body_ruleSym_v a bb) (ap1 verifierRSF1 t)))
      d1 = axPost verifierRSF1 Pair a bb

  in ruleTrans d1 verifierEq

----------------------------------------------------------------------
-- Lifted variant: same theorem under an arbitrary auxiliary formula P.

body_ruleSym_v_eval_pass_l :
  (P : Formula) (a bb : Term) (fp sp : Term) ->
  Deriv (P imp atomic (eqn (ap1 Snd bb) (ap2 Pair fp sp))) ->
  Deriv (P imp atomic (eqn (ap2 body_ruleSym_v a bb) (ap2 Pair sp fp)))
body_ruleSym_v_eval_pass_l P a bb fp sp sndB_eqL =
  let
      t : Term
      t = ap2 Pair a bb

      ----------------------------------------------------------------
      -- Section A.

      a1A : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd (ap1 Snd t))))
      a1A = axComp Snd Snd t

      a2A : Deriv (atomic (eqn (ap1 Snd t) bb))
      a2A = axSnd a bb

      a3A : Deriv (atomic (eqn (ap1 Snd (ap1 Snd t)) (ap1 Snd bb)))
      a3A = cong1 Snd a2A

      ihExtracted0 : Deriv (atomic (eqn (ap1 getIH t) (ap1 Snd bb)))
      ihExtracted0 = ruleTrans a1A a3A

      ihExtractedL : Deriv (P imp atomic (eqn (ap1 getIH t) (ap1 Snd bb)))
      ihExtractedL = liftAxiom P ihExtracted0

      ihPairL : Deriv (P imp atomic (eqn (ap1 getIH t) (ap2 Pair fp sp)))
      ihPairL = liftedRuleTrans P (ap1 getIH t) (ap1 Snd bb) (ap2 Pair fp sp)
                  ihExtractedL sndB_eqL

      ----------------------------------------------------------------
      -- Section B.

      b1A : Deriv (atomic (eqn (ap1 doSwapF1 t)
                                (ap2 Pair (ap1 getSndIH t) (ap1 getFstIH t))))
      b1A = axComp2 Pair getSndIH getFstIH t

      b2aA : Deriv (atomic (eqn (ap1 getSndIH t)
                                 (ap1 Snd (ap1 (Comp Snd Snd) t))))
      b2aA = axComp Snd (Comp Snd Snd) t

      b2bA : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) t))
                                 (ap1 Snd (ap1 Snd bb))))
      b2bA = cong1 Snd ihExtracted0

      b2cL : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd bb))
                                       (ap1 Snd (ap2 Pair fp sp))))
      b2cL = liftedCong1 P Snd (ap1 Snd bb) (ap2 Pair fp sp) sndB_eqL

      b2dA : Deriv (atomic (eqn (ap1 Snd (ap2 Pair fp sp)) sp))
      b2dA = axSnd fp sp

      getSndIHEqL : Deriv (P imp atomic (eqn (ap1 getSndIH t) sp))
      getSndIHEqL =
        liftedRuleTrans P (ap1 getSndIH t) (ap1 Snd (ap1 (Comp Snd Snd) t)) sp
          (liftAxiom P b2aA)
          (liftedRuleTrans P (ap1 Snd (ap1 (Comp Snd Snd) t))
             (ap1 Snd (ap1 Snd bb)) sp
             (liftAxiom P b2bA)
             (liftedRuleTrans P (ap1 Snd (ap1 Snd bb))
                (ap1 Snd (ap2 Pair fp sp)) sp
                b2cL (liftAxiom P b2dA)))

      b3aA : Deriv (atomic (eqn (ap1 getFstIH t)
                                 (ap1 Fst (ap1 (Comp Snd Snd) t))))
      b3aA = axComp Fst (Comp Snd Snd) t

      b3bA : Deriv (atomic (eqn (ap1 Fst (ap1 (Comp Snd Snd) t))
                                 (ap1 Fst (ap1 Snd bb))))
      b3bA = cong1 Fst ihExtracted0

      b3cL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Snd bb))
                                       (ap1 Fst (ap2 Pair fp sp))))
      b3cL = liftedCong1 P Fst (ap1 Snd bb) (ap2 Pair fp sp) sndB_eqL

      b3dA : Deriv (atomic (eqn (ap1 Fst (ap2 Pair fp sp)) fp))
      b3dA = axFst fp sp

      getFstIHEqL : Deriv (P imp atomic (eqn (ap1 getFstIH t) fp))
      getFstIHEqL =
        liftedRuleTrans P (ap1 getFstIH t) (ap1 Fst (ap1 (Comp Snd Snd) t)) fp
          (liftAxiom P b3aA)
          (liftedRuleTrans P (ap1 Fst (ap1 (Comp Snd Snd) t))
             (ap1 Fst (ap1 Snd bb)) fp
             (liftAxiom P b3bA)
             (liftedRuleTrans P (ap1 Fst (ap1 Snd bb))
                (ap1 Fst (ap2 Pair fp sp)) fp
                b3cL (liftAxiom P b3dA)))

      b4L : Deriv (P imp atomic (eqn (ap2 Pair (ap1 getSndIH t) (ap1 getFstIH t))
                                       (ap2 Pair sp (ap1 getFstIH t))))
      b4L = liftedCongL P Pair (ap1 getSndIH t) sp (ap1 getFstIH t) getSndIHEqL

      b5L : Deriv (P imp atomic (eqn (ap2 Pair sp (ap1 getFstIH t))
                                       (ap2 Pair sp fp)))
      b5L = liftedCongR P Pair (ap1 getFstIH t) fp sp getFstIHEqL

      doSwapEqL : Deriv (P imp atomic (eqn (ap1 doSwapF1 t) (ap2 Pair sp fp)))
      doSwapEqL =
        liftedRuleTrans P (ap1 doSwapF1 t)
          (ap2 Pair (ap1 getSndIH t) (ap1 getFstIH t)) (ap2 Pair sp fp)
          (liftAxiom P b1A)
          (liftedRuleTrans P (ap2 Pair (ap1 getSndIH t) (ap1 getFstIH t))
             (ap2 Pair sp (ap1 getFstIH t)) (ap2 Pair sp fp)
             b4L b5L)

      ----------------------------------------------------------------
      -- Section C.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) doSwapF1

      c1A : Deriv (atomic (eqn (ap1 verifierRSF1 t)
                                (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))))
      c1A = axComp2 IfLf getIH branchesF1 t

      c2A : Deriv (atomic (eqn (ap1 branchesF1 t)
                                (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doSwapF1 t))))
      c2A = axComp2 Pair (KT codeTriv) doSwapF1 t

      c3A : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      c3A = axKT (codeFormula (atomic (eqn O O))) t

      c4A : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doSwapF1 t))
                                (ap2 Pair codeTriv (ap1 doSwapF1 t))))
      c4A = congL Pair (ap1 doSwapF1 t) c3A

      c5L : Deriv (P imp atomic (eqn (ap2 Pair codeTriv (ap1 doSwapF1 t))
                                       (ap2 Pair codeTriv (ap2 Pair sp fp))))
      c5L = liftedCongR P Pair (ap1 doSwapF1 t) (ap2 Pair sp fp) codeTriv
              doSwapEqL

      branchesEqL : Deriv (P imp atomic (eqn (ap1 branchesF1 t)
                                              (ap2 Pair codeTriv (ap2 Pair sp fp))))
      branchesEqL =
        liftedRuleTrans P (ap1 branchesF1 t)
          (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doSwapF1 t))
          (ap2 Pair codeTriv (ap2 Pair sp fp))
          (liftAxiom P c2A)
          (liftedRuleTrans P
             (ap2 Pair (ap1 (KT codeTriv) t) (ap1 doSwapF1 t))
             (ap2 Pair codeTriv (ap1 doSwapF1 t))
             (ap2 Pair codeTriv (ap2 Pair sp fp))
             (liftAxiom P c4A) c5L)

      c6L : Deriv (P imp atomic (eqn (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
                                       (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))))
      c6L = liftedCongL P IfLf (ap1 getIH t) (ap2 Pair fp sp)
              (ap1 branchesF1 t) ihPairL

      c7L : Deriv (P imp atomic (eqn (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                                       (ap2 IfLf (ap2 Pair fp sp)
                                                  (ap2 Pair codeTriv (ap2 Pair sp fp)))))
      c7L = liftedCongR P IfLf (ap1 branchesF1 t)
              (ap2 Pair codeTriv (ap2 Pair sp fp)) (ap2 Pair fp sp)
              branchesEqL

      c8A : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fp sp)
                                          (ap2 Pair codeTriv (ap2 Pair sp fp)))
                                (ap2 Pair sp fp)))
      c8A = axIfLfN fp sp codeTriv (ap2 Pair sp fp)

      verifierEqL : Deriv (P imp atomic (eqn (ap1 verifierRSF1 t) (ap2 Pair sp fp)))
      verifierEqL =
        liftedRuleTrans P (ap1 verifierRSF1 t)
          (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t)) (ap2 Pair sp fp)
          (liftAxiom P c1A)
          (liftedRuleTrans P
             (ap2 IfLf (ap1 getIH t) (ap1 branchesF1 t))
             (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
             (ap2 Pair sp fp)
             c6L
             (liftedRuleTrans P
                (ap2 IfLf (ap2 Pair fp sp) (ap1 branchesF1 t))
                (ap2 IfLf (ap2 Pair fp sp)
                          (ap2 Pair codeTriv (ap2 Pair sp fp)))
                (ap2 Pair sp fp)
                c7L (liftAxiom P c8A)))

      ----------------------------------------------------------------
      -- Section D.

      d1A : Deriv (atomic (eqn (ap2 body_ruleSym_v a bb) (ap1 verifierRSF1 t)))
      d1A = axPost verifierRSF1 Pair a bb

  in liftedRuleTrans P (ap2 body_ruleSym_v a bb) (ap1 verifierRSF1 t)
       (ap2 Pair sp fp)
       (liftAxiom P d1A) verifierEqL
