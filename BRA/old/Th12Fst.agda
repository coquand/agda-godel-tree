{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Fst -- schematic Theorem 12 for Fst.
--
-- Df_F1_Fst : Fun1 dispatches on input shape via IfLf:
--   Df_F1_Fst O           = reify encAxFstLf      (lf-case proof code)
--   Df_F1_Fst (Pair x y)  = runtime ruleInst2 proof code with cor x, cor y
--                           at the substituent slots.
--
-- Th12_F1_Fst :
--   Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst (var zero)))
--                       (codeFTeq1Asym Fst (var zero))))
--
-- Construction = fromBaseAndPair on
--    Th12_F1_Fst_at_lf_v2  : at substF zero O P  (lf case)
--    Th12_F1_Fst_at_pair   : at substF zero (Pair v1 v2) P  (Pair case)
-- where  P  is the Theorem 12 statement at  var zero .

module BRA.Th12Fst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor ; stepCor)
open import BRA.SubT         using (subT)
open import BRA.Sb2          using (subT2 ; codedSubstT2 ; subTDef_term2)
open import BRA.CorOfPair    using (corOfPair ; corOfFstPair ; corOfSndPair)
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Tag      using (tagRuleInst2 ; tagAxFst)
open import BRA.Thm.Parts.AxFst    using (encAxFst ; outAxFst)
open import BRA.Thm.Parts.AxFstLf  using (encAxFstLf ; outAxFstLf)
open import BRA.Thm.Parts.RuleInst2 using (encRuleInst2 ; outRuleInst2)
open import BRA.Thm.ThmT     using
  ( thmT
  ; thClosed
  ; thmTDispAxFst
  ; thmTDispAxFstLf
  ; thmTDispRuleInst2_param
  ; tagCode_ruleInst2 )
open import BRA.Thm14CodeFTeqAsym using (codeFTeq1Asym ; mkAp1T ; mkEqT ; mkAp2T)
open import BRA.FromBaseAndPair using (fromBaseAndPair)
open import BRA.Thm.ThmT using (codeF1Th_noVar)

------------------------------------------------------------------------
-- Closed Term constants for the Pair-case proof code.

K1 : Term
K1 = tagCode_ruleInst2

K2 : Term
K2 = reify (code (var zero))

K3 : Term
K3 = reify (code (var (suc zero)))

K4 : Term
K4 = reify (encAxFst (var zero) (var (suc zero)))

lfProofCode : Term
lfProofCode = reify encAxFstLf

------------------------------------------------------------------------
-- ndProofCodeFun1 : Fun1 building the Pair-case runtime proof code.
--
--   ndProofCodeFun1 t = Pair K1 (Pair K2 (Pair K3 (Pair K4
--                          (Pair (ap1 cor (ap1 Fst t))
--                                (ap1 cor (ap1 Snd t)))))) .

ndProofCodeFun1 : Fun1
ndProofCodeFun1 =
  Comp2 Pair (KT K1)
    (Comp2 Pair (KT K2)
      (Comp2 Pair (KT K3)
        (Comp2 Pair (KT K4)
          (Comp2 Pair (Comp cor Fst) (Comp cor Snd)))))

------------------------------------------------------------------------
-- Df_F1_Fst : Fun1 dispatching on input shape.
--
--   Df_F1_Fst t = ap2 IfLf t (ap2 Pair lfProofCode (ndProofCodeFun1 t))
--
-- For t = O           : reduces to lfProofCode (via axIfLfL).
-- For t = Pair v1 v2  : reduces to ndProofCodeFun1 (Pair v1 v2) (axIfLfN).

Df_F1_Fst : Fun1
Df_F1_Fst =
  Comp2 IfLf I
    (Comp2 Pair (KT lfProofCode) ndProofCodeFun1)

------------------------------------------------------------------------
-- ndProofCodeFun1_unfold_pair :
--   ndProofCodeFun1 (Pair v1 v2) =
--     Pair K1 (Pair K2 (Pair K3 (Pair K4
--       (Pair (ap1 cor (ap1 Fst (Pair v1 v2)))
--             (ap1 cor (ap1 Snd (Pair v1 v2)))))))
--
-- Pair structure preserved verbatim; cor's Fst/Snd reductions are NOT
-- applied here.  Done in Th12_F1_Fst_at_pair via cong1 cor + axFst/axSnd.

ndProofCodeFun1_unfold : (t : Term) ->
  Deriv (atomic (eqn (ap1 ndProofCodeFun1 t)
    (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4
       (ap2 Pair (ap1 cor (ap1 Fst t)) (ap1 cor (ap1 Snd t)))))))))
ndProofCodeFun1_unfold t =
  let
    g5 : Fun1
    g5 = Comp2 Pair (Comp cor Fst) (Comp cor Snd)
    g4 : Fun1
    g4 = Comp2 Pair (KT K4) g5
    g3 : Fun1
    g3 = Comp2 Pair (KT K3) g4
    g2 : Fun1
    g2 = Comp2 Pair (KT K2) g3

    -- Step 1: unfold outer Comp2 Pair (KT K1) g2 at t.
    e1 : Deriv (atomic (eqn (ap1 ndProofCodeFun1 t)
                              (ap2 Pair (ap1 (KT K1) t) (ap1 g2 t))))
    e1 = axComp2 Pair (KT K1) g2 t

    -- ktRed for K1.
    eK1 : Deriv (atomic (eqn (ap1 (KT K1) t) K1))
    eK1 = ktRed (natCode tagRuleInst2) t

    -- Unfold g2.
    e2 : Deriv (atomic (eqn (ap1 g2 t)
                              (ap2 Pair (ap1 (KT K2) t) (ap1 g3 t))))
    e2 = axComp2 Pair (KT K2) g3 t

    eK2 : Deriv (atomic (eqn (ap1 (KT K2) t) K2))
    eK2 = ktRed (code (var zero)) t

    -- Unfold g3.
    e3 : Deriv (atomic (eqn (ap1 g3 t)
                              (ap2 Pair (ap1 (KT K3) t) (ap1 g4 t))))
    e3 = axComp2 Pair (KT K3) g4 t

    eK3 : Deriv (atomic (eqn (ap1 (KT K3) t) K3))
    eK3 = ktRed (code (var (suc zero))) t

    -- Unfold g4.
    e4 : Deriv (atomic (eqn (ap1 g4 t)
                              (ap2 Pair (ap1 (KT K4) t) (ap1 g5 t))))
    e4 = axComp2 Pair (KT K4) g5 t

    eK4 : Deriv (atomic (eqn (ap1 (KT K4) t) K4))
    eK4 = ktRed (encAxFst (var zero) (var (suc zero))) t

    -- Unfold g5: ap1 g5 t = Pair (cor (Fst t)) (cor (Snd t)).
    e5 : Deriv (atomic (eqn (ap1 g5 t)
                              (ap2 Pair (ap1 (Comp cor Fst) t)
                                        (ap1 (Comp cor Snd) t))))
    e5 = axComp2 Pair (Comp cor Fst) (Comp cor Snd) t

    eCorFst : Deriv (atomic (eqn (ap1 (Comp cor Fst) t)
                                  (ap1 cor (ap1 Fst t))))
    eCorFst = axComp cor Fst t

    eCorSnd : Deriv (atomic (eqn (ap1 (Comp cor Snd) t)
                                  (ap1 cor (ap1 Snd t))))
    eCorSnd = axComp cor Snd t

    -- Build the chain bottom-up.
    g5_clean : Deriv (atomic (eqn (ap1 g5 t)
                                    (ap2 Pair (ap1 cor (ap1 Fst t))
                                              (ap1 cor (ap1 Snd t)))))
    g5_clean = ruleTrans e5
                 (ruleTrans (congL Pair (ap1 (Comp cor Snd) t) eCorFst)
                            (congR Pair (ap1 cor (ap1 Fst t)) eCorSnd))

    g4_clean : Deriv (atomic (eqn (ap1 g4 t)
                                    (ap2 Pair K4
                                      (ap2 Pair (ap1 cor (ap1 Fst t))
                                                (ap1 cor (ap1 Snd t))))))
    g4_clean = ruleTrans e4
                 (ruleTrans (congL Pair (ap1 g5 t) eK4)
                            (congR Pair K4 g5_clean))

    g3_clean : Deriv (atomic (eqn (ap1 g3 t)
                                    (ap2 Pair K3
                                      (ap2 Pair K4
                                        (ap2 Pair (ap1 cor (ap1 Fst t))
                                                  (ap1 cor (ap1 Snd t)))))))
    g3_clean = ruleTrans e3
                 (ruleTrans (congL Pair (ap1 g4 t) eK3)
                            (congR Pair K3 g4_clean))

    g2_clean : Deriv (atomic (eqn (ap1 g2 t)
                                    (ap2 Pair K2
                                      (ap2 Pair K3
                                        (ap2 Pair K4
                                          (ap2 Pair (ap1 cor (ap1 Fst t))
                                                    (ap1 cor (ap1 Snd t))))))))
    g2_clean = ruleTrans e2
                 (ruleTrans (congL Pair (ap1 g3 t) eK2)
                            (congR Pair K2 g3_clean))

  in ruleTrans e1
       (ruleTrans (congL Pair (ap1 g2 t) eK1)
                  (congR Pair K1 g2_clean))

------------------------------------------------------------------------
-- runtimeTreeAt v1 v2 : the runtime proof code at input (Pair v1 v2).

runtimeTreeAt : Term -> Term -> Term
runtimeTreeAt v1 v2 =
  ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4
    (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair v1 v2)))
              (ap1 cor (ap1 Snd (ap2 Pair v1 v2)))))))

------------------------------------------------------------------------
-- Df_F1_Fst_unfold_pair :
--   Df_F1_Fst (Pair v1 v2) = runtimeTreeAt v1 v2
--
-- The IfLf at Pair input dispatches to Snd of the options Pair, which is
-- ndProofCodeFun1 (Pair v1 v2).  Then ndProofCodeFun1_unfold gives the
-- runtimeTreeAt form.

Df_F1_Fst_unfold_pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 Df_F1_Fst (ap2 Pair v1 v2)) (runtimeTreeAt v1 v2)))
Df_F1_Fst_unfold_pair v1 v2 =
  let
    t : Term
    t = ap2 Pair v1 v2

    options : Fun1
    options = Comp2 Pair (KT lfProofCode) ndProofCodeFun1

    -- Step 1: outer Comp2 IfLf I options unfolds.
    s1 : Deriv (atomic (eqn (ap1 Df_F1_Fst t)
                              (ap2 IfLf (ap1 I t) (ap1 options t))))
    s1 = axComp2 IfLf I options t

    -- Step 2: ap1 I t = t  (axI).
    sI : Deriv (atomic (eqn (ap1 I t) t))
    sI = axI t

    -- Step 3: options unfolds to Pair lfProofCode (ndProofCodeFun1 t).
    sOpt : Deriv (atomic (eqn (ap1 options t)
                                (ap2 Pair (ap1 (KT lfProofCode) t)
                                          (ap1 ndProofCodeFun1 t))))
    sOpt = axComp2 Pair (KT lfProofCode) ndProofCodeFun1 t

    eKlf : Deriv (atomic (eqn (ap1 (KT lfProofCode) t) lfProofCode))
    eKlf = ktRed encAxFstLf t

    sOptClean : Deriv (atomic (eqn (ap1 options t)
                                     (ap2 Pair lfProofCode
                                       (ap1 ndProofCodeFun1 t))))
    sOptClean = ruleTrans sOpt
                  (congL Pair (ap1 ndProofCodeFun1 t) eKlf)

    -- Step 4: ap1 IfLf t (Pair lf nd) = nd  (axIfLfN since t = Pair v1 v2).
    sDispatch : Deriv (atomic (eqn (ap2 IfLf t
                                     (ap2 Pair lfProofCode
                                       (ap1 ndProofCodeFun1 t)))
                                     (ap1 ndProofCodeFun1 t)))
    sDispatch = axIfLfN v1 v2 lfProofCode (ap1 ndProofCodeFun1 t)

    -- Step 5: ndProofCodeFun1 unfolds.
    sUnfold : Deriv (atomic (eqn (ap1 ndProofCodeFun1 t) (runtimeTreeAt v1 v2)))
    sUnfold = ndProofCodeFun1_unfold t

    -- Combine: Df_F1_Fst t -> IfLf t (Pair lfProofCode nd) -> nd -> runtime.
    sCombined : Deriv (atomic (eqn (ap1 Df_F1_Fst t)
                                     (ap2 IfLf t
                                       (ap2 Pair lfProofCode
                                         (ap1 ndProofCodeFun1 t)))))
    sCombined = ruleTrans s1
                  (ruleTrans (congL IfLf (ap1 options t) sI)
                             (congR IfLf t sOptClean))

  in ruleTrans sCombined (ruleTrans sDispatch sUnfold)

------------------------------------------------------------------------
-- Df_F1_Fst_unfold_lf :
--   Df_F1_Fst O = lfProofCode
--
-- IfLf at first arg O takes Fst of the options Pair, which is lfProofCode.

Df_F1_Fst_unfold_lf :
  Deriv (atomic (eqn (ap1 Df_F1_Fst O) lfProofCode))
Df_F1_Fst_unfold_lf =
  let
    t : Term
    t = O

    options : Fun1
    options = Comp2 Pair (KT lfProofCode) ndProofCodeFun1

    s1 : Deriv (atomic (eqn (ap1 Df_F1_Fst t)
                              (ap2 IfLf (ap1 I t) (ap1 options t))))
    s1 = axComp2 IfLf I options t

    sI : Deriv (atomic (eqn (ap1 I t) t))
    sI = axI t

    sOpt : Deriv (atomic (eqn (ap1 options t)
                                (ap2 Pair (ap1 (KT lfProofCode) t)
                                          (ap1 ndProofCodeFun1 t))))
    sOpt = axComp2 Pair (KT lfProofCode) ndProofCodeFun1 t

    eKlf : Deriv (atomic (eqn (ap1 (KT lfProofCode) t) lfProofCode))
    eKlf = ktRed encAxFstLf t

    sOptClean : Deriv (atomic (eqn (ap1 options t)
                                     (ap2 Pair lfProofCode
                                       (ap1 ndProofCodeFun1 t))))
    sOptClean = ruleTrans sOpt
                  (congL Pair (ap1 ndProofCodeFun1 t) eKlf)

    -- IfLf O (Pair lfProofCode _) = lfProofCode by axIfLfL.
    sDispatch : Deriv (atomic (eqn (ap2 IfLf O
                                     (ap2 Pair lfProofCode
                                       (ap1 ndProofCodeFun1 t)))
                                     lfProofCode))
    sDispatch = axIfLfL lfProofCode (ap1 ndProofCodeFun1 t)

    sCombined : Deriv (atomic (eqn (ap1 Df_F1_Fst t)
                                     (ap2 IfLf t
                                       (ap2 Pair lfProofCode
                                         (ap1 ndProofCodeFun1 t)))))
    sCombined = ruleTrans s1
                  (ruleTrans (congL IfLf (ap1 options t) sI)
                             (congR IfLf t sOptClean))

  in ruleTrans sCombined sDispatch

------------------------------------------------------------------------
-- Th12_F1_Fst_at_lf_v2 :
--   Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst O))
--                       (codeFTeq1Asym Fst O)))
--
-- The lf case of schematic Theorem 12 for Fst, using the dispatching
-- Df_F1_Fst.  Df_F1_Fst O = lfProofCode = reify encAxFstLf.  Then
-- thmTDispAxFstLf gives reify outAxFstLf.  Bridge to codeFTeq1Asym Fst O
-- via cor O = O and cor (Fst O) = O.

Th12_F1_Fst_at_lf_v2 :
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst O))
                     (codeFTeq1Asym Fst O)))
Th12_F1_Fst_at_lf_v2 =
  let
    s1 : Deriv (atomic (eqn (ap1 Df_F1_Fst O) lfProofCode))
    s1 = Df_F1_Fst_unfold_lf

    s2 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst O))
                             (ap1 thmT lfProofCode)))
    s2 = cong1 thmT s1

    s3 : Deriv (atomic (eqn (ap1 thmT lfProofCode) (reify outAxFstLf)))
    s3 = thmTDispAxFstLf

    -- Bridge from reify outAxFstLf = mkEqT (mkAp1T (codeF1 Fst) O) O
    -- to codeFTeq1Asym Fst O  = mkEqT (mkAp1T (codeF1 Fst) (cor O)) (cor (Fst O)).

    bridgeInner : Deriv (atomic (eqn O (ap1 cor O)))
    bridgeInner = ruleSym (axRecLf stepCor)

    bridgeRHS : Deriv (atomic (eqn O (ap1 cor (ap1 Fst O))))
    bridgeRHS =
      ruleSym (ruleTrans (cong1 cor axFstLf) (axRecLf stepCor))

    bridgeLHS : Deriv (atomic (eqn (mkAp1T (reify (codeF1 Fst)) O)
                                    (mkAp1T (reify (codeF1 Fst)) (ap1 cor O))))
    bridgeLHS =
      congR Pair (reify tagAp1)
        (congR Pair (reify (codeF1 Fst)) bridgeInner)

    bridgeFull : Deriv (atomic (eqn (mkEqT (mkAp1T (reify (codeF1 Fst)) O) O)
                                     (codeFTeq1Asym Fst O)))
    bridgeFull =
      ruleTrans (congL Pair O bridgeLHS)
                (congR Pair (mkAp1T (reify (codeF1 Fst)) (ap1 cor O)) bridgeRHS)

    s4 : Deriv (atomic (eqn (reify outAxFstLf) (codeFTeq1Asym Fst O)))
    s4 = bridgeFull

  in ruleTrans s2 (ruleTrans s3 s4)

------------------------------------------------------------------------
-- xShape_K4 : the Fst-shape proof for K4 = reify (encAxFst (var 0) (var 1)).
--
-- K4 = ap2 Pair (reify (natCode tagAxFst))
--               (reify (nd (code (var 0)) (code (var 1))))
--    = ap2 Pair (ap2 Pair O (ap2 Pair O O))
--               (ap2 Pair K2 K3)
-- since natCode tagAxFst = natCode (suc (suc zero)) = nd lf (nd lf lf) reified.

xShape_K4 : Sigma Term (\ y' -> Sigma Term (\ x' ->
  Deriv (atomic (eqn (ap1 Fst K4) (ap2 Pair x' y')))))
xShape_K4 =
  mkSigma (ap2 Pair O O) (mkSigma O
    (axFst (ap2 Pair O (ap2 Pair O O)) (ap2 Pair K2 K3)))

------------------------------------------------------------------------
-- Th12_F1_Fst_at_pair : the Pair case of schematic Theorem 12 for Fst.
--
--   Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst (Pair v1 v2)))
--                       (codeFTeq1Asym Fst (Pair v1 v2))))
--
-- Pipeline:
--   (1) Df_F1_Fst_unfold_pair : Df_F1_Fst (Pair v1 v2) = runtimeTreeAt v1 v2.
--   (2) cong1 thmT (1) : thmT(Df_F1_Fst (Pair v1 v2)) = thmT(runtimeTreeAt).
--   (3) thmTDispRuleInst2_param : thmT(runtimeTreeAt) = subT2-form (with
--       cor(Fst..) and cor(Snd..) at substituent slots, K4 unevaluated).
--   (4) thmTDispAxFst (var 0) (var 1) : thmT K4 = reify (outAxFst (var 0) (var 1)).
--   (5) subTDef_term2 : subT2 args codeP = codedSubstT2-form.
--   (6) Agda definitional unfolding of codedSubstT2 on closed outAxFst tree:
--       reduces to reducedT2 (closed expression in cor (Fst..) and cor (Snd..)).
--   (7) Bridge to codeFTeq1Asym Fst (Pair v1 v2) via corOfFstPair, corOfSndPair,
--       and corOfPair (ruleSym).

Th12_F1_Fst_at_pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst (ap2 Pair v1 v2)))
                     (codeFTeq1Asym Fst (ap2 Pair v1 v2))))
Th12_F1_Fst_at_pair v1 v2 =
  let
    pairIn : Term
    pairIn = ap2 Pair v1 v2

    tA : Term
    tA = ap1 cor (ap1 Fst pairIn)

    tB : Term
    tB = ap1 cor (ap1 Snd pairIn)

    runtimeTree : Term
    runtimeTree = runtimeTreeAt v1 v2

    -- (1) Unfold Df_F1_Fst.
    s1 : Deriv (atomic (eqn (ap1 Df_F1_Fst pairIn) runtimeTree))
    s1 = Df_F1_Fst_unfold_pair v1 v2

    -- (2) Push thmT.
    s2 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst pairIn))
                             (ap1 thmT runtimeTree)))
    s2 = cong1 thmT s1

    -- (3) Apply thmTDispRuleInst2_param at xT = K4, tA, tB.
    argsPair : Term
    argsPair = ap2 Pair (ap2 Pair K2 tA) (ap2 Pair K3 tB)

    -- (4) thmT K4 = reify (outAxFst (var 0) (var 1)).
    -- Pair-shape derived from outAxFst x y = codeFormula(...) for the
    -- soundified  thmTDispRuleInst2_param .
    s4 : Deriv (atomic (eqn (ap1 thmT K4) (reify (outAxFst (var zero) (var (suc zero))))))
    s4 = thmTDispAxFst (var zero) (var (suc zero))

    codePfpFst : Term
    codePfpFst = reify (code (ap1 Fst (ap2 Pair (var zero) (var (suc zero)))))
    codePspFst : Term
    codePspFst = reify (code (var zero))

    s3 : Deriv (atomic (eqn (ap1 thmT runtimeTree)
                             (ap2 subT2 argsPair (ap1 thmT K4))))
    s3 = thmTDispRuleInst2_param zero (suc zero) tA tB K4 xShape_K4
                                  codePfpFst codePspFst s4

    s5 : Deriv (atomic (eqn (ap2 subT2 argsPair (ap1 thmT K4))
                             (ap2 subT2 argsPair
                               (reify (outAxFst (var zero) (var (suc zero)))))))
    s5 = congR subT2 argsPair s4

    -- (6) subTDef_term2 reduces subT2 args (reify codeP) to codedSubstT2-form.
    s6 : Deriv (atomic (eqn (ap2 subT2 argsPair
                               (reify (outAxFst (var zero) (var (suc zero)))))
                             (codedSubstT2 tA tB
                               (code (var zero))
                               (code (var (suc zero)))
                               (outAxFst (var zero) (var (suc zero))))))
    s6 = subTDef_term2 zero (suc zero) tA tB
                       (outAxFst (var zero) (var (suc zero)))

    -- (7) Agda definitional unfolding of codedSubstT2 on the closed tree.
    --     The result has cor(Fst..) and cor(Snd..) at variable positions.
    --
    -- outAxFst (var 0) (var 1) = codeFormula (atomic (eqn (Fst (Pair (var 0) (var 1))) (var 0)))
    --                          = nd (code (Fst (Pair (var 0) (var 1)))) (code (var 0))
    --
    -- After codedSubstT2 walk:
    --   - The (code (var 0)) at top-level RHS matches → tA.
    --   - The (code (var 0)) and (code (var 1)) deep inside Pair v1 v2 match → tA, tB.
    --   - All other subtrees are reified as-is (no var-0/var-1 collisions).

    reducedT2 : Term
    reducedT2 = mkEqT
      (mkAp1T (reify (codeF1 Fst))
        (mkAp2T (reify (codeF2 Pair)) tA tB))
      tA

    s7 : Deriv (atomic (eqn (codedSubstT2 tA tB
                               (code (var zero))
                               (code (var (suc zero)))
                               (outAxFst (var zero) (var (suc zero))))
                             reducedT2))
    s7 = axRefl reducedT2

    -- (8) Bridge tA = cor (Fst (Pair v1 v2)) to cor v1 via corOfFstPair.
    --     Bridge tB = cor (Snd (Pair v1 v2)) to cor v2 via corOfSndPair.
    --     Then collapse mkAp2T (codeF2 Pair) (cor v1) (cor v2) to cor (Pair v1 v2)
    --     via ruleSym corOfPair.

    bridgeFst : Deriv (atomic (eqn tA (ap1 cor v1)))
    bridgeFst = corOfFstPair v1 v2

    bridgeSnd : Deriv (atomic (eqn tB (ap1 cor v2)))
    bridgeSnd = corOfSndPair v1 v2

    -- mkAp2T form rewrite:
    --   mkAp2T (codeF2 Pair) tA tB
    --   → mkAp2T (codeF2 Pair) (cor v1) tB         [bridgeFst]
    --   → mkAp2T (codeF2 Pair) (cor v1) (cor v2)   [bridgeSnd]
    --   → cor (Pair v1 v2)                         [ruleSym corOfPair]

    -- mkAp2T g x y = ap2 Pair tagAp2T (ap2 Pair g (ap2 Pair x y)).
    --   So congR Pair (ap2 Pair (codeF2 Pair-Term) tA, then sub) etc.

    pairT : Term
    pairT = reify (codeF2 Pair)

    bridgeMkAp2TA : Deriv (atomic (eqn
      (mkAp2T pairT tA tB)
      (mkAp2T pairT (ap1 cor v1) tB)))
    bridgeMkAp2TA =
      congR Pair (reify tagAp2)
        (congR Pair pairT
          (congL Pair tB bridgeFst))

    bridgeMkAp2TB : Deriv (atomic (eqn
      (mkAp2T pairT (ap1 cor v1) tB)
      (mkAp2T pairT (ap1 cor v1) (ap1 cor v2))))
    bridgeMkAp2TB =
      congR Pair (reify tagAp2)
        (congR Pair pairT
          (congR Pair (ap1 cor v1) bridgeSnd))

    bridgeCorOfPair : Deriv (atomic (eqn
      (mkAp2T pairT (ap1 cor v1) (ap1 cor v2))
      (ap1 cor (ap2 Pair v1 v2))))
    bridgeCorOfPair = ruleSym (corOfPair v1 v2)

    bridgeMkAp2TFull : Deriv (atomic (eqn
      (mkAp2T pairT tA tB)
      (ap1 cor (ap2 Pair v1 v2))))
    bridgeMkAp2TFull =
      ruleTrans bridgeMkAp2TA
                (ruleTrans bridgeMkAp2TB bridgeCorOfPair)

    -- (9) Lift bridgeMkAp2TFull into the LHS slot of reducedT2.
    --   reducedT2 = mkEqT (mkAp1T (codeF1 Fst) (mkAp2T pairT tA tB)) tA
    --   target_LHS = mkEqT (mkAp1T (codeF1 Fst) (cor (Pair v1 v2))) tA
    --   target_RHS = mkEqT (mkAp1T (codeF1 Fst) (cor (Pair v1 v2))) (cor (Fst (Pair v1 v2)))
    --              [no bridge needed for tA → cor(Fst(Pair..)) since tA = cor(Fst(Pair..))]

    bridgeLHS : Deriv (atomic (eqn
      (mkAp1T (reify (codeF1 Fst)) (mkAp2T pairT tA tB))
      (mkAp1T (reify (codeF1 Fst)) (ap1 cor (ap2 Pair v1 v2)))))
    bridgeLHS =
      congR Pair (reify tagAp1)
        (congR Pair (reify (codeF1 Fst)) bridgeMkAp2TFull)

    bridgeFinal : Deriv (atomic (eqn reducedT2 (codeFTeq1Asym Fst (ap2 Pair v1 v2))))
    bridgeFinal = congL Pair tA bridgeLHS

  in ruleTrans s2 (ruleTrans s3 (ruleTrans s5 (ruleTrans s6
       (ruleTrans s7 bridgeFinal))))

------------------------------------------------------------------------
-- Th12_F1_Fst_at : pointwise schematic Theorem 12 for Fst at any input.

Th12_F1_Fst_at_O :
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst O))
                     (codeFTeq1Asym Fst O)))
Th12_F1_Fst_at_O = Th12_F1_Fst_at_lf_v2

Th12_F1_Fst_at_Pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst (ap2 Pair v1 v2)))
                     (codeFTeq1Asym Fst (ap2 Pair v1 v2))))
Th12_F1_Fst_at_Pair = Th12_F1_Fst_at_pair

------------------------------------------------------------------------
-- Schematic packaging via fromBaseAndPair.
--
-- The substF reduction stalls at  substF1 zero O thmT  (thmT is opaque
-- inside ThmT's abstract block).  Bridge via  thClosed .

P_Th12_Fst : Formula
P_Th12_Fst = atomic (eqn (ap1 thmT (ap1 Df_F1_Fst (var zero)))
                          (codeFTeq1Asym Fst (var zero)))

-- Coerce Th12_F1_Fst_at_O to  Deriv (substF zero O P_Th12_Fst)  via thClosed.

baseLf_substF :
  Deriv (substF zero O P_Th12_Fst)
baseLf_substF =
  let
    thEqO : Eq (substF1 zero O thmT) thmT
    thEqO = thClosed zero O

    coerce : Eq (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst O))
                              (codeFTeq1Asym Fst O)))
                (substF zero O P_Th12_Fst)
    coerce = eqCong (\ f -> atomic
                              (eqn (ap1 f (ap1 Df_F1_Fst O))
                                   (codeFTeq1Asym Fst O)))
                    (eqSym thEqO)
  in eqSubst (\ F -> Deriv F) coerce Th12_F1_Fst_at_lf_v2

-- Same for the Pair case.

basePair_substF : (v1Idx v2Idx : Nat) ->
  Deriv (substF zero (ap2 Pair (var v1Idx) (var v2Idx)) P_Th12_Fst)
basePair_substF v1Idx v2Idx =
  let
    pairT : Term
    pairT = ap2 Pair (var v1Idx) (var v2Idx)

    thEqPair : Eq (substF1 zero pairT thmT) thmT
    thEqPair = thClosed zero pairT

    coerce : Eq (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst pairT))
                              (codeFTeq1Asym Fst pairT)))
                (substF zero pairT P_Th12_Fst)
    coerce = eqCong (\ f -> atomic
                              (eqn (ap1 f (ap1 Df_F1_Fst pairT))
                                   (codeFTeq1Asym Fst pairT)))
                    (eqSym thEqPair)
  in eqSubst (\ F -> Deriv F) coerce
              (Th12_F1_Fst_at_pair (var v1Idx) (var v2Idx))

-- Schematic Theorem 12 for Fst:
--   Deriv (P_Th12_Fst)
-- with var 0 free.  Combines the two cases via fromBaseAndPair.

Th12_F1_Fst : Deriv P_Th12_Fst
Th12_F1_Fst =
  fromBaseAndPair P_Th12_Fst (suc (suc zero)) (suc (suc (suc zero)))
    baseLf_substF
    (basePair_substF (suc (suc zero)) (suc (suc (suc zero))))
