{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleInstVProof
--
-- Evaluation proof for body_ruleInst_v under the "pass" branch
-- hypotheses.  Closed-Term version: all witnesses are Term-level.
--
-- Given:
--   * argsExt : ap1 Fst (ap1 Snd a) = argsPair     (closed args extractor).
--   * distH   : ap1 Snd bb = ap2 Pair t1 codeP     (IH distribution; t1 = thmT argsPair
--                                                   in concrete callers but the body never
--                                                   inspects t1, so we keep it abstract).
--   * dh      : codeP = ap2 Pair fstPart sndPart   (inner check: codeP is Pair-shaped).
-- conclude:
--   ap2 body_ruleInst_v a bb = ap2 subT argsPair codeP.
--
-- Identifier convention: camelCase.  Mid-identifier underscores collide
-- with Agda's mixfix grammar.  ASCII only.  No postulates, no holes,
-- no with-abstraction.

module BRA.SoundRuleInstVProof where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.SubT  using (subT)
open import BRA.Thm.EvalHelpers
  using ( liftAxiom ; liftedRuleTrans ; liftedCong1 ; liftedCongL ; liftedCongR )

open import BRA.SoundRuleInstProto
  using ( body_ruleInst_v ; verifyAndRun ; verifierRIF1 ; codeTriv )

----------------------------------------------------------------------
-- codeFormulaPairShape: any reify(codeFormula P) is definitionally a
-- Pair, since codeFormula always returns a non-empty tree (nd _ _).
-- Returns the pair components plus an axRefl-witness.

codeFormulaPairShape : (P : Formula) ->
  Sigma Term (\ fp -> Sigma Term (\ sp ->
    Deriv (atomic (eqn (reify (codeFormula P)) (ap2 Pair fp sp)))))
codeFormulaPairShape (atomic (eqn l r)) =
  mkSigma (reify (code l)) (mkSigma (reify (code r))
    (axRefl (ap2 Pair (reify (code l)) (reify (code r)))))
codeFormulaPairShape (not Q) =
  mkSigma (reify tagNeg) (mkSigma (reify (codeFormula Q))
    (axRefl (ap2 Pair (reify tagNeg) (reify (codeFormula Q)))))
codeFormulaPairShape (Q imp R) =
  mkSigma (reify tagImp)
    (mkSigma (ap2 Pair (reify (codeFormula Q)) (reify (codeFormula R)))
      (axRefl (ap2 Pair (reify tagImp)
                        (ap2 Pair (reify (codeFormula Q))
                                  (reify (codeFormula R))))))

----------------------------------------------------------------------
-- Closed-Term variant.

body_ruleInst_v_eval_pass :
  (a bb : Term) (argsPair t1 codeP fstPart sndPart : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) argsPair)) ->
  Deriv (atomic (eqn (ap1 Snd bb) (ap2 Pair t1 codeP))) ->
  Deriv (atomic (eqn codeP (ap2 Pair fstPart sndPart))) ->
  Deriv (atomic (eqn (ap2 body_ruleInst_v a bb)
                     (ap2 subT argsPair codeP)))
body_ruleInst_v_eval_pass a bb argsPair t1 codeP fstPart sndPart
                          argsExt distH dh =
  let
      ----------------------------------------------------------------
      -- Section A: extract  argsPair  via  Lift (Comp Fst Snd) .
      --   ap2 (Lift (Comp Fst Snd)) a bb
      --     = ap1 (Comp Fst Snd) a       [axLift]
      --     = ap1 Fst (ap1 Snd a)        [axComp]
      --     = argsPair                   [argsExt]

      a1 : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb)
                              (ap1 (Comp Fst Snd) a)))
      a1 = axLift (Comp Fst Snd) a bb

      a2 : Deriv (atomic (eqn (ap1 (Comp Fst Snd) a)
                              (ap1 Fst (ap1 Snd a))))
      a2 = axComp Fst Snd a

      argsExtracted : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb)
                                         argsPair))
      argsExtracted = ruleTrans a1 (ruleTrans a2 argsExt)

      ----------------------------------------------------------------
      -- Section B: extract  codeP  via  Post (Comp Snd (Comp Snd Snd)) Pair .
      --   ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb
      --     = ap1 (Comp Snd (Comp Snd Snd)) (Pair a bb)   [axPost]
      --     = ap1 Snd (ap1 (Comp Snd Snd) (Pair a bb))    [axComp]
      --     = ap1 Snd (ap1 Snd (ap1 Snd (Pair a bb)))     [axComp]
      --     = ap1 Snd (ap1 Snd bb)                        [axSnd]
      --     = ap1 Snd (Pair t1 codeP)                     [distH]
      --     = codeP                                       [axSnd]

      pab : Term
      pab = ap2 Pair a bb

      b1 : Deriv (atomic (eqn (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                              (ap1 (Comp Snd (Comp Snd Snd)) pab)))
      b1 = axPost (Comp Snd (Comp Snd Snd)) Pair a bb

      b2 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd Snd)) pab)
                              (ap1 Snd (ap1 (Comp Snd Snd) pab))))
      b2 = axComp Snd (Comp Snd Snd) pab

      b3a : Deriv (atomic (eqn (ap1 (Comp Snd Snd) pab)
                               (ap1 Snd (ap1 Snd pab))))
      b3a = axComp Snd Snd pab

      b3b : Deriv (atomic (eqn (ap1 Snd pab) bb))
      b3b = axSnd a bb

      b3c : Deriv (atomic (eqn (ap1 Snd (ap1 Snd pab)) (ap1 Snd bb)))
      b3c = cong1 Snd b3b

      b3 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) pab) (ap1 Snd bb)))
      b3 = ruleTrans b3a b3c

      b4 : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) pab))
                              (ap1 Snd (ap1 Snd bb))))
      b4 = cong1 Snd b3

      b5 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                              (ap1 Snd (ap2 Pair t1 codeP))))
      b5 = cong1 Snd distH

      b6 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair t1 codeP)) codeP))
      b6 = axSnd t1 codeP

      thmYHExtracted : Deriv (atomic (eqn (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                                          codeP))
      thmYHExtracted = ruleTrans b1 (ruleTrans b2 (ruleTrans b4 (ruleTrans b5 b6)))

      ----------------------------------------------------------------
      -- Section C: unfold  body_ruleInst_v a bb  via axFan.
      --   body_ruleInst_v = Fan (Lift (Comp Fst Snd))
      --                          (Post (Comp Snd (Comp Snd Snd)) Pair)
      --                          verifyAndRun
      --
      -- ap2 body_ruleInst_v a bb
      --   = ap2 verifyAndRun (ap2 (Lift (Comp Fst Snd)) a bb)
      --                      (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)

      argsExt' : Term
      argsExt' = ap2 (Lift (Comp Fst Snd)) a bb

      thmYHExt' : Term
      thmYHExt' = ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb

      c1 : Deriv (atomic (eqn (ap2 body_ruleInst_v a bb)
                              (ap2 verifyAndRun argsExt' thmYHExt')))
      c1 = axFan (Lift (Comp Fst Snd))
                 (Post (Comp Snd (Comp Snd Snd)) Pair)
                 verifyAndRun a bb

      -- Rewrite verifyAndRun's first arg to argsPair.
      c2 : Deriv (atomic (eqn (ap2 verifyAndRun argsExt' thmYHExt')
                              (ap2 verifyAndRun argsPair thmYHExt')))
      c2 = congL verifyAndRun thmYHExt' argsExtracted

      -- Rewrite verifyAndRun's second arg to codeP.
      c3 : Deriv (atomic (eqn (ap2 verifyAndRun argsPair thmYHExt')
                              (ap2 verifyAndRun argsPair codeP)))
      c3 = congR verifyAndRun argsPair thmYHExtracted

      bodyToVerify : Deriv (atomic (eqn (ap2 body_ruleInst_v a bb)
                                        (ap2 verifyAndRun argsPair codeP)))
      bodyToVerify = ruleTrans c1 (ruleTrans c2 c3)

      ----------------------------------------------------------------
      -- Section D: unfold  verifyAndRun argsPair codeP  via axPost.
      --   verifyAndRun = Post verifierRIF1 Pair
      --   ap2 verifyAndRun argsPair codeP
      --     = ap1 verifierRIF1 (Pair argsPair codeP)
      --
      -- Then unfold verifierRIF1 :
      --   verifierRIF1 = Comp2 IfLf Snd (Comp2 Pair (KT codeTriv) (Comp2 subT Fst Snd))
      --   ap1 verifierRIF1 t'
      --     = ap2 IfLf (ap1 Snd t') (ap1 (Comp2 Pair (KT codeTriv) (Comp2 subT Fst Snd)) t')
      -- where t' = Pair argsPair codeP.

      tprime : Term
      tprime = ap2 Pair argsPair codeP

      d1 : Deriv (atomic (eqn (ap2 verifyAndRun argsPair codeP)
                              (ap1 verifierRIF1 tprime)))
      d1 = axPost verifierRIF1 Pair argsPair codeP

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) (Comp2 subT Fst Snd)

      d2 : Deriv (atomic (eqn (ap1 verifierRIF1 tprime)
                              (ap2 IfLf (ap1 Snd tprime)
                                        (ap1 branchesF1 tprime))))
      d2 = axComp2 IfLf Snd branchesF1 tprime

      ----------------------------------------------------------------
      -- Section E: reduce  ap1 Snd tprime = codeP  (via axSnd) and
      --             ap1 branchesF1 tprime = Pair codeTriv (subT argsPair codeP).

      e1 : Deriv (atomic (eqn (ap1 Snd tprime) codeP))
      e1 = axSnd argsPair codeP

      e2 : Deriv (atomic (eqn (ap1 branchesF1 tprime)
                              (ap2 Pair (ap1 (KT codeTriv) tprime)
                                        (ap1 (Comp2 subT Fst Snd) tprime))))
      e2 = axComp2 Pair (KT codeTriv) (Comp2 subT Fst Snd) tprime

      e3 : Deriv (atomic (eqn (ap1 (KT codeTriv) tprime) codeTriv))
      e3 = axKT (codeFormula (atomic (eqn O O))) tprime

      e4 : Deriv (atomic (eqn (ap1 (Comp2 subT Fst Snd) tprime)
                              (ap2 subT (ap1 Fst tprime) (ap1 Snd tprime))))
      e4 = axComp2 subT Fst Snd tprime

      e5a : Deriv (atomic (eqn (ap1 Fst tprime) argsPair))
      e5a = axFst argsPair codeP

      e5b : Deriv (atomic (eqn (ap2 subT (ap1 Fst tprime) (ap1 Snd tprime))
                               (ap2 subT argsPair (ap1 Snd tprime))))
      e5b = congL subT (ap1 Snd tprime) e5a

      e5c : Deriv (atomic (eqn (ap2 subT argsPair (ap1 Snd tprime))
                               (ap2 subT argsPair codeP)))
      e5c = congR subT argsPair e1

      e5 : Deriv (atomic (eqn (ap1 (Comp2 subT Fst Snd) tprime)
                              (ap2 subT argsPair codeP)))
      e5 = ruleTrans e4 (ruleTrans e5b e5c)

      e6a : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) tprime)
                                          (ap1 (Comp2 subT Fst Snd) tprime))
                               (ap2 Pair codeTriv (ap1 (Comp2 subT Fst Snd) tprime))))
      e6a = congL Pair (ap1 (Comp2 subT Fst Snd) tprime) e3

      e6b : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 (Comp2 subT Fst Snd) tprime))
                               (ap2 Pair codeTriv (ap2 subT argsPair codeP))))
      e6b = congR Pair codeTriv e5

      branchesEval : Deriv (atomic (eqn (ap1 branchesF1 tprime)
                                        (ap2 Pair codeTriv (ap2 subT argsPair codeP))))
      branchesEval = ruleTrans e2 (ruleTrans e6a e6b)

      ----------------------------------------------------------------
      -- Section F: combine  ap1 verifierRIF1 tprime = ap2 IfLf codeP (Pair codeTriv (subT...)).

      f1 : Deriv (atomic (eqn (ap2 IfLf (ap1 Snd tprime) (ap1 branchesF1 tprime))
                              (ap2 IfLf codeP (ap1 branchesF1 tprime))))
      f1 = congL IfLf (ap1 branchesF1 tprime) e1

      f2 : Deriv (atomic (eqn (ap2 IfLf codeP (ap1 branchesF1 tprime))
                              (ap2 IfLf codeP (ap2 Pair codeTriv (ap2 subT argsPair codeP)))))
      f2 = congR IfLf codeP branchesEval

      verifierEvalPre : Deriv (atomic (eqn (ap1 verifierRIF1 tprime)
                                           (ap2 IfLf codeP
                                                (ap2 Pair codeTriv (ap2 subT argsPair codeP)))))
      verifierEvalPre = ruleTrans d2 (ruleTrans f1 f2)

      ----------------------------------------------------------------
      -- Section G: apply dh: codeP = Pair fstPart sndPart, then axIfLfN.

      g1 : Deriv (atomic (eqn (ap2 IfLf codeP
                                    (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
                              (ap2 IfLf (ap2 Pair fstPart sndPart)
                                    (ap2 Pair codeTriv (ap2 subT argsPair codeP)))))
      g1 = congL IfLf (ap2 Pair codeTriv (ap2 subT argsPair codeP)) dh

      g2 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fstPart sndPart)
                                    (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
                              (ap2 subT argsPair codeP)))
      g2 = axIfLfN fstPart sndPart codeTriv (ap2 subT argsPair codeP)

      verifierEval : Deriv (atomic (eqn (ap1 verifierRIF1 tprime)
                                        (ap2 subT argsPair codeP)))
      verifierEval = ruleTrans verifierEvalPre (ruleTrans g1 g2)

      ----------------------------------------------------------------
      -- Section H: chain everything.

      verifyAndRunEval : Deriv (atomic (eqn (ap2 verifyAndRun argsPair codeP)
                                            (ap2 subT argsPair codeP)))
      verifyAndRunEval = ruleTrans d1 verifierEval

  in ruleTrans bodyToVerify verifyAndRunEval

----------------------------------------------------------------------
-- Lifted variant: same theorem under an arbitrary auxiliary formula P.
--
-- Mirrors  body_mp_v_eval_pass_l : every  ruleTrans / cong / axiom  is
-- replaced by its lifted counterpart from BRA.Thm.EvalHelpers; closed
-- sub-derivations get promoted via  liftAxiom P  at the meeting points.

body_ruleInst_v_eval_pass_l :
  (P : Formula) (a bb : Term) (argsPair t1 codeP fstPart sndPart : Term) ->
  Deriv (P imp atomic (eqn (ap1 Fst (ap1 Snd a)) argsPair)) ->
  Deriv (P imp atomic (eqn (ap1 Snd bb)
                            (ap2 Pair t1 codeP))) ->
  Deriv (P imp atomic (eqn codeP (ap2 Pair fstPart sndPart))) ->
  Deriv (P imp atomic (eqn (ap2 body_ruleInst_v a bb)
                            (ap2 subT argsPair codeP)))
body_ruleInst_v_eval_pass_l P a bb argsPair t1 codeP fstPart sndPart
                            argsExtL distHL dhL =
  let
      ----------------------------------------------------------------
      -- Section A.

      a1A : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb)
                                (ap1 (Comp Fst Snd) a)))
      a1A = axLift (Comp Fst Snd) a bb

      a2A : Deriv (atomic (eqn (ap1 (Comp Fst Snd) a)
                                (ap1 Fst (ap1 Snd a))))
      a2A = axComp Fst Snd a

      argsExtractedL : Deriv (P imp atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb)
                                                 argsPair))
      argsExtractedL =
        liftedRuleTrans P (ap2 (Lift (Comp Fst Snd)) a bb) (ap1 (Comp Fst Snd) a) argsPair
          (liftAxiom P a1A)
          (liftedRuleTrans P (ap1 (Comp Fst Snd) a) (ap1 Fst (ap1 Snd a)) argsPair
             (liftAxiom P a2A) argsExtL)

      ----------------------------------------------------------------
      -- Section B.

      pab : Term
      pab = ap2 Pair a bb

      b1A : Deriv (atomic (eqn (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                                (ap1 (Comp Snd (Comp Snd Snd)) pab)))
      b1A = axPost (Comp Snd (Comp Snd Snd)) Pair a bb

      b2A : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd Snd)) pab)
                                (ap1 Snd (ap1 (Comp Snd Snd) pab))))
      b2A = axComp Snd (Comp Snd Snd) pab

      b3aA : Deriv (atomic (eqn (ap1 (Comp Snd Snd) pab)
                                 (ap1 Snd (ap1 Snd pab))))
      b3aA = axComp Snd Snd pab

      b3bA : Deriv (atomic (eqn (ap1 Snd pab) bb))
      b3bA = axSnd a bb

      b3cA : Deriv (atomic (eqn (ap1 Snd (ap1 Snd pab)) (ap1 Snd bb)))
      b3cA = cong1 Snd b3bA

      b3A : Deriv (atomic (eqn (ap1 (Comp Snd Snd) pab) (ap1 Snd bb)))
      b3A = ruleTrans b3aA b3cA

      b4A : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Snd) pab))
                                (ap1 Snd (ap1 Snd bb))))
      b4A = cong1 Snd b3A

      b5L : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd bb))
                                       (ap1 Snd (ap2 Pair t1 codeP))))
      b5L = liftedCong1 P Snd (ap1 Snd bb) (ap2 Pair t1 codeP) distHL

      b6A : Deriv (atomic (eqn (ap1 Snd (ap2 Pair t1 codeP)) codeP))
      b6A = axSnd t1 codeP

      thmYHExtractedL : Deriv (P imp atomic (eqn (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                                                  codeP))
      thmYHExtractedL =
        liftedRuleTrans P (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp Snd (Comp Snd Snd)) pab) codeP
          (liftAxiom P b1A)
          (liftedRuleTrans P (ap1 (Comp Snd (Comp Snd Snd)) pab)
             (ap1 Snd (ap1 (Comp Snd Snd) pab)) codeP
             (liftAxiom P b2A)
             (liftedRuleTrans P (ap1 Snd (ap1 (Comp Snd Snd) pab))
                (ap1 Snd (ap1 Snd bb)) codeP
                (liftAxiom P b4A)
                (liftedRuleTrans P (ap1 Snd (ap1 Snd bb))
                   (ap1 Snd (ap2 Pair t1 codeP)) codeP
                   b5L (liftAxiom P b6A))))

      ----------------------------------------------------------------
      -- Section C.

      argsExt' : Term
      argsExt' = ap2 (Lift (Comp Fst Snd)) a bb

      thmYHExt' : Term
      thmYHExt' = ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb

      c1A : Deriv (atomic (eqn (ap2 body_ruleInst_v a bb)
                                (ap2 verifyAndRun argsExt' thmYHExt')))
      c1A = axFan (Lift (Comp Fst Snd))
                  (Post (Comp Snd (Comp Snd Snd)) Pair)
                  verifyAndRun a bb

      c2L : Deriv (P imp atomic (eqn (ap2 verifyAndRun argsExt' thmYHExt')
                                       (ap2 verifyAndRun argsPair thmYHExt')))
      c2L = liftedCongL P verifyAndRun argsExt' argsPair thmYHExt' argsExtractedL

      c3L : Deriv (P imp atomic (eqn (ap2 verifyAndRun argsPair thmYHExt')
                                       (ap2 verifyAndRun argsPair codeP)))
      c3L = liftedCongR P verifyAndRun thmYHExt' codeP argsPair thmYHExtractedL

      bodyToVerifyL : Deriv (P imp atomic (eqn (ap2 body_ruleInst_v a bb)
                                                (ap2 verifyAndRun argsPair codeP)))
      bodyToVerifyL =
        liftedRuleTrans P (ap2 body_ruleInst_v a bb)
          (ap2 verifyAndRun argsExt' thmYHExt') (ap2 verifyAndRun argsPair codeP)
          (liftAxiom P c1A)
          (liftedRuleTrans P (ap2 verifyAndRun argsExt' thmYHExt')
             (ap2 verifyAndRun argsPair thmYHExt') (ap2 verifyAndRun argsPair codeP)
             c2L c3L)

      ----------------------------------------------------------------
      -- Section D.

      tprime : Term
      tprime = ap2 Pair argsPair codeP

      d1A : Deriv (atomic (eqn (ap2 verifyAndRun argsPair codeP)
                                (ap1 verifierRIF1 tprime)))
      d1A = axPost verifierRIF1 Pair argsPair codeP

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) (Comp2 subT Fst Snd)

      d2A : Deriv (atomic (eqn (ap1 verifierRIF1 tprime)
                                (ap2 IfLf (ap1 Snd tprime)
                                          (ap1 branchesF1 tprime))))
      d2A = axComp2 IfLf Snd branchesF1 tprime

      ----------------------------------------------------------------
      -- Section E.

      e1A : Deriv (atomic (eqn (ap1 Snd tprime) codeP))
      e1A = axSnd argsPair codeP

      e2A : Deriv (atomic (eqn (ap1 branchesF1 tprime)
                                (ap2 Pair (ap1 (KT codeTriv) tprime)
                                          (ap1 (Comp2 subT Fst Snd) tprime))))
      e2A = axComp2 Pair (KT codeTriv) (Comp2 subT Fst Snd) tprime

      e3A : Deriv (atomic (eqn (ap1 (KT codeTriv) tprime) codeTriv))
      e3A = axKT (codeFormula (atomic (eqn O O))) tprime

      e4A : Deriv (atomic (eqn (ap1 (Comp2 subT Fst Snd) tprime)
                                (ap2 subT (ap1 Fst tprime) (ap1 Snd tprime))))
      e4A = axComp2 subT Fst Snd tprime

      e5aA : Deriv (atomic (eqn (ap1 Fst tprime) argsPair))
      e5aA = axFst argsPair codeP

      e5bA : Deriv (atomic (eqn (ap2 subT (ap1 Fst tprime) (ap1 Snd tprime))
                                 (ap2 subT argsPair (ap1 Snd tprime))))
      e5bA = congL subT (ap1 Snd tprime) e5aA

      e5cA : Deriv (atomic (eqn (ap2 subT argsPair (ap1 Snd tprime))
                                 (ap2 subT argsPair codeP)))
      e5cA = congR subT argsPair e1A

      e5A : Deriv (atomic (eqn (ap1 (Comp2 subT Fst Snd) tprime)
                                (ap2 subT argsPair codeP)))
      e5A = ruleTrans e4A (ruleTrans e5bA e5cA)

      e6aA : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) tprime)
                                           (ap1 (Comp2 subT Fst Snd) tprime))
                                 (ap2 Pair codeTriv (ap1 (Comp2 subT Fst Snd) tprime))))
      e6aA = congL Pair (ap1 (Comp2 subT Fst Snd) tprime) e3A

      e6bA : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 (Comp2 subT Fst Snd) tprime))
                                 (ap2 Pair codeTriv (ap2 subT argsPair codeP))))
      e6bA = congR Pair codeTriv e5A

      branchesEvalA : Deriv (atomic (eqn (ap1 branchesF1 tprime)
                                          (ap2 Pair codeTriv (ap2 subT argsPair codeP))))
      branchesEvalA = ruleTrans e2A (ruleTrans e6aA e6bA)

      ----------------------------------------------------------------
      -- Section F.

      f1A : Deriv (atomic (eqn (ap2 IfLf (ap1 Snd tprime) (ap1 branchesF1 tprime))
                                (ap2 IfLf codeP (ap1 branchesF1 tprime))))
      f1A = congL IfLf (ap1 branchesF1 tprime) e1A

      f2A : Deriv (atomic (eqn (ap2 IfLf codeP (ap1 branchesF1 tprime))
                                (ap2 IfLf codeP (ap2 Pair codeTriv (ap2 subT argsPair codeP)))))
      f2A = congR IfLf codeP branchesEvalA

      verifierEvalPreA : Deriv (atomic (eqn (ap1 verifierRIF1 tprime)
                                             (ap2 IfLf codeP
                                                  (ap2 Pair codeTriv (ap2 subT argsPair codeP)))))
      verifierEvalPreA = ruleTrans d2A (ruleTrans f1A f2A)

      ----------------------------------------------------------------
      -- Section G: lifted dh + axIfLfN.

      g1L : Deriv (P imp atomic (eqn (ap2 IfLf codeP
                                            (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
                                       (ap2 IfLf (ap2 Pair fstPart sndPart)
                                            (ap2 Pair codeTriv (ap2 subT argsPair codeP)))))
      g1L = liftedCongL P IfLf codeP (ap2 Pair fstPart sndPart)
              (ap2 Pair codeTriv (ap2 subT argsPair codeP)) dhL

      g2A : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fstPart sndPart)
                                          (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
                                (ap2 subT argsPair codeP)))
      g2A = axIfLfN fstPart sndPart codeTriv (ap2 subT argsPair codeP)

      verifierEvalL : Deriv (P imp atomic (eqn (ap1 verifierRIF1 tprime)
                                                (ap2 subT argsPair codeP)))
      verifierEvalL =
        liftedRuleTrans P (ap1 verifierRIF1 tprime)
          (ap2 IfLf codeP (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
          (ap2 subT argsPair codeP)
          (liftAxiom P verifierEvalPreA)
          (liftedRuleTrans P
             (ap2 IfLf codeP (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
             (ap2 IfLf (ap2 Pair fstPart sndPart)
                  (ap2 Pair codeTriv (ap2 subT argsPair codeP)))
             (ap2 subT argsPair codeP)
             g1L (liftAxiom P g2A))

      ----------------------------------------------------------------
      -- Section H.

      verifyAndRunEvalL : Deriv (P imp atomic (eqn (ap2 verifyAndRun argsPair codeP)
                                                    (ap2 subT argsPair codeP)))
      verifyAndRunEvalL =
        liftedRuleTrans P (ap2 verifyAndRun argsPair codeP)
          (ap1 verifierRIF1 tprime) (ap2 subT argsPair codeP)
          (liftAxiom P d1A) verifierEvalL

  in liftedRuleTrans P (ap2 body_ruleInst_v a bb)
       (ap2 verifyAndRun argsPair codeP) (ap2 subT argsPair codeP)
       bodyToVerifyL verifyAndRunEvalL
