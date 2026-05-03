{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleInst2VProof
--
-- Evaluation proof for body_ruleInst2_v under the "pass" branch
-- hypotheses.  Closed-Term version; no lifted variant needed (the
-- existing dispatcher only has a closed form).
--
-- Hypotheses:
--   * argsExt  : ap2 argsExtractor a bb = argsPair    (closed args extractor)
--   * codepExt : ap2 codepExtractor a bb = codeFP    (codeFP from distH/d_h)
--   * dh       : codeFP = ap2 Pair fstPart sndPart   (Pair-shape of codeFP)
-- Conclusion:
--   ap2 body_ruleInst2_v a bb = ap2 subT2 argsPair codeFP .

module BRA.SoundRuleInst2VProof where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Sb2 using (subT2)

open import BRA.SoundRuleInst2Proto
  using ( body_ruleInst2_v ; argsExtractor ; codepExtractor
        ; verifyAndRun2 ; verifierRI2F1 ; codeTriv )

body_ruleInst2_v_eval_pass :
  (a bb : Term) (argsPair codeFP fstPart sndPart : Term) ->
  Deriv (atomic (eqn (ap2 argsExtractor a bb) argsPair)) ->
  Deriv (atomic (eqn (ap2 codepExtractor a bb) codeFP)) ->
  Deriv (atomic (eqn codeFP (ap2 Pair fstPart sndPart))) ->
  Deriv (atomic (eqn (ap2 body_ruleInst2_v a bb) (ap2 subT2 argsPair codeFP)))
body_ruleInst2_v_eval_pass a bb argsPair codeFP fstPart sndPart
                           argsExt codepExt dh =
  let
      ----------------------------------------------------------------
      -- Section A: unfold body_ruleInst2_v via axFan.

      argsExtT : Term
      argsExtT = ap2 argsExtractor a bb

      codepExtT : Term
      codepExtT = ap2 codepExtractor a bb

      a1 : Deriv (atomic (eqn (ap2 body_ruleInst2_v a bb)
                              (ap2 verifyAndRun2 argsExtT codepExtT)))
      a1 = axFan argsExtractor codepExtractor verifyAndRun2 a bb

      a2 : Deriv (atomic (eqn (ap2 verifyAndRun2 argsExtT codepExtT)
                              (ap2 verifyAndRun2 argsPair codepExtT)))
      a2 = congL verifyAndRun2 codepExtT argsExt

      a3 : Deriv (atomic (eqn (ap2 verifyAndRun2 argsPair codepExtT)
                              (ap2 verifyAndRun2 argsPair codeFP)))
      a3 = congR verifyAndRun2 argsPair codepExt

      bodyToVerify : Deriv (atomic (eqn (ap2 body_ruleInst2_v a bb)
                                         (ap2 verifyAndRun2 argsPair codeFP)))
      bodyToVerify = ruleTrans a1 (ruleTrans a2 a3)

      ----------------------------------------------------------------
      -- Section B: unfold verifyAndRun2 argsPair codeFP via axPost.

      tprime : Term
      tprime = ap2 Pair argsPair codeFP

      b1 : Deriv (atomic (eqn (ap2 verifyAndRun2 argsPair codeFP)
                              (ap1 verifierRI2F1 tprime)))
      b1 = axPost verifierRI2F1 Pair argsPair codeFP

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) (Comp2 subT2 Fst Snd)

      b2 : Deriv (atomic (eqn (ap1 verifierRI2F1 tprime)
                              (ap2 IfLf (ap1 Snd tprime) (ap1 branchesF1 tprime))))
      b2 = axComp2 IfLf Snd branchesF1 tprime

      ----------------------------------------------------------------
      -- Section C: reduce  ap1 Snd tprime = codeFP  and
      --   ap1 branchesF1 tprime = Pair codeTriv (subT2 argsPair codeFP).

      c1 : Deriv (atomic (eqn (ap1 Snd tprime) codeFP))
      c1 = axSnd argsPair codeFP

      c2 : Deriv (atomic (eqn (ap1 branchesF1 tprime)
                              (ap2 Pair (ap1 (KT codeTriv) tprime)
                                        (ap1 (Comp2 subT2 Fst Snd) tprime))))
      c2 = axComp2 Pair (KT codeTriv) (Comp2 subT2 Fst Snd) tprime

      c3 : Deriv (atomic (eqn (ap1 (KT codeTriv) tprime) codeTriv))
      c3 = axKT (codeFormula (atomic (eqn O O))) tprime

      c4 : Deriv (atomic (eqn (ap1 (Comp2 subT2 Fst Snd) tprime)
                              (ap2 subT2 (ap1 Fst tprime) (ap1 Snd tprime))))
      c4 = axComp2 subT2 Fst Snd tprime

      c5a : Deriv (atomic (eqn (ap1 Fst tprime) argsPair))
      c5a = axFst argsPair codeFP

      c5b : Deriv (atomic (eqn (ap2 subT2 (ap1 Fst tprime) (ap1 Snd tprime))
                               (ap2 subT2 argsPair (ap1 Snd tprime))))
      c5b = congL subT2 (ap1 Snd tprime) c5a

      c5c : Deriv (atomic (eqn (ap2 subT2 argsPair (ap1 Snd tprime))
                               (ap2 subT2 argsPair codeFP)))
      c5c = congR subT2 argsPair c1

      c5 : Deriv (atomic (eqn (ap1 (Comp2 subT2 Fst Snd) tprime)
                              (ap2 subT2 argsPair codeFP)))
      c5 = ruleTrans c4 (ruleTrans c5b c5c)

      c6a : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) tprime)
                                          (ap1 (Comp2 subT2 Fst Snd) tprime))
                               (ap2 Pair codeTriv (ap1 (Comp2 subT2 Fst Snd) tprime))))
      c6a = congL Pair (ap1 (Comp2 subT2 Fst Snd) tprime) c3

      c6b : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 (Comp2 subT2 Fst Snd) tprime))
                               (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP))))
      c6b = congR Pair codeTriv c5

      branchesEval : Deriv (atomic (eqn (ap1 branchesF1 tprime)
                                         (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP))))
      branchesEval = ruleTrans c2 (ruleTrans c6a c6b)

      ----------------------------------------------------------------
      -- Section D: assemble verifierRI2F1 tprime via axIfLfN.

      d1 : Deriv (atomic (eqn (ap2 IfLf (ap1 Snd tprime) (ap1 branchesF1 tprime))
                              (ap2 IfLf codeFP (ap1 branchesF1 tprime))))
      d1 = congL IfLf (ap1 branchesF1 tprime) c1

      d2 : Deriv (atomic (eqn (ap2 IfLf codeFP (ap1 branchesF1 tprime))
                              (ap2 IfLf codeFP (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP)))))
      d2 = congR IfLf codeFP branchesEval

      verifierEvalPre : Deriv (atomic (eqn (ap1 verifierRI2F1 tprime)
                                            (ap2 IfLf codeFP
                                                 (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP)))))
      verifierEvalPre = ruleTrans b2 (ruleTrans d1 d2)

      d3 : Deriv (atomic (eqn (ap2 IfLf codeFP
                                    (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP)))
                              (ap2 IfLf (ap2 Pair fstPart sndPart)
                                    (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP)))))
      d3 = congL IfLf (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP)) dh

      d4 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair fstPart sndPart)
                                    (ap2 Pair codeTriv (ap2 subT2 argsPair codeFP)))
                              (ap2 subT2 argsPair codeFP)))
      d4 = axIfLfN fstPart sndPart codeTriv (ap2 subT2 argsPair codeFP)

      verifierEval : Deriv (atomic (eqn (ap1 verifierRI2F1 tprime)
                                         (ap2 subT2 argsPair codeFP)))
      verifierEval = ruleTrans verifierEvalPre (ruleTrans d3 d4)

      verifyAndRunEval : Deriv (atomic (eqn (ap2 verifyAndRun2 argsPair codeFP)
                                             (ap2 subT2 argsPair codeFP)))
      verifyAndRunEval = ruleTrans b1 verifierEval

  in ruleTrans bodyToVerify verifyAndRunEval
