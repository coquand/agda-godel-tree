{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Const -- schematic Theorem 12 for Pair (Fun2 case).
--
-- Df_F2_Const : Fun2.  Pair has no shape dispatch (works at any input),
-- so the construction is simpler than Th12Fst: just runtime ruleInst2
-- + axRefl-encoded inner proof code, no IfLf, no fromBaseAndPair.
--
-- Th12_F2_Const : Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_Const (var 0) (var 1)))
--                                    (codeFTeq2Asym Const (var 0) (var 1))))
--
-- Two free variables (var 0, var 1).  Ready for ruleInst at any (a, b).

module BRA.Th12Const where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor ; stepCor)
open import BRA.Sb2          using (subT2 ; codedSubstT2 ; subTDef_term2)
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Tag      using (tagRuleInst2 ; tagAxConst)
open import BRA.Thm.Parts.AxConst   using (encAxConst ; outAxConst)
open import BRA.Thm.Parts.RuleInst2 using (encRuleInst2 ; outRuleInst2)
open import BRA.Thm.ThmT     using
  ( thmT
  ; thClosed
  ; thmTDispAxConst
  ; thmTDispRuleInst2_param
  ; tagCode_ruleInst2 )
open import BRA.Thm14CodeFTeqAsym using (codeFTeq2Asym ; mkAp1T ; mkEqT ; mkAp2T)

------------------------------------------------------------------------
-- Closed Term constants for the runtime proof code.

K1 : Term
K1 = tagCode_ruleInst2

K2 : Term
K2 = reify (code (var zero))

K3 : Term
K3 = reify (code (var (suc zero)))

K4 : Term
K4 = reify (encAxConst (var zero) (var (suc zero)))

------------------------------------------------------------------------
-- ndProofCodeFun1 : Fun1 building the runtime proof code given a Pair input.
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
-- Df_F2_Const : Fun2.  Wraps ndProofCodeFun1 to take two args via
-- Post _ Pair (which constructs the Pair internally before applying).

Df_F2_Const : Fun2
Df_F2_Const = Post ndProofCodeFun1 Pair

------------------------------------------------------------------------
-- ndProofCodeFun1_unfold : ap1 ndProofCodeFun1 t = explicit Pair structure.

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

    e1 : Deriv (atomic (eqn (ap1 ndProofCodeFun1 t)
                              (ap2 Pair (ap1 (KT K1) t) (ap1 g2 t))))
    e1 = axComp2 Pair (KT K1) g2 t

    eK1 : Deriv (atomic (eqn (ap1 (KT K1) t) K1))
    eK1 = ktRed (natCode tagRuleInst2) t

    e2 : Deriv (atomic (eqn (ap1 g2 t)
                              (ap2 Pair (ap1 (KT K2) t) (ap1 g3 t))))
    e2 = axComp2 Pair (KT K2) g3 t

    eK2 : Deriv (atomic (eqn (ap1 (KT K2) t) K2))
    eK2 = ktRed (code (var zero)) t

    e3 : Deriv (atomic (eqn (ap1 g3 t)
                              (ap2 Pair (ap1 (KT K3) t) (ap1 g4 t))))
    e3 = axComp2 Pair (KT K3) g4 t

    eK3 : Deriv (atomic (eqn (ap1 (KT K3) t) K3))
    eK3 = ktRed (code (var (suc zero))) t

    e4 : Deriv (atomic (eqn (ap1 g4 t)
                              (ap2 Pair (ap1 (KT K4) t) (ap1 g5 t))))
    e4 = axComp2 Pair (KT K4) g5 t

    eK4 : Deriv (atomic (eqn (ap1 (KT K4) t) K4))
    eK4 = ktRed (encAxConst (var zero) (var (suc zero))) t

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
-- runtimeTreeAt x v : the runtime proof code at inputs (x, v).
-- Same shape as for Fst, but the cor's are of Fst/Snd of the BUILT pair
-- (Pair x v), which after axFst/axSnd reduce to cor x and cor v.

runtimeTreeAt : Term -> Term -> Term
runtimeTreeAt x v =
  ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4
    (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair x v)))
              (ap1 cor (ap1 Snd (ap2 Pair x v)))))))

------------------------------------------------------------------------
-- Df_F2_Const_unfold : ap2 Df_F2_Const x v = runtimeTreeAt x v.
--
-- Df_F2_Const = Post ndProofCodeFun1 Pair, so axPost reduces
--   ap2 Df_F2_Const x v = ap1 ndProofCodeFun1 (ap2 Pair x v) ,
-- then ndProofCodeFun1_unfold finishes the chain.

Df_F2_Const_unfold : (x v : Term) ->
  Deriv (atomic (eqn (ap2 Df_F2_Const x v) (runtimeTreeAt x v)))
Df_F2_Const_unfold x v =
  let
    pairT : Term
    pairT = ap2 Pair x v

    s1 : Deriv (atomic (eqn (ap2 Df_F2_Const x v)
                             (ap1 ndProofCodeFun1 pairT)))
    s1 = axPost ndProofCodeFun1 Pair x v

    s2 : Deriv (atomic (eqn (ap1 ndProofCodeFun1 pairT) (runtimeTreeAt x v)))
    s2 = ndProofCodeFun1_unfold pairT
  in ruleTrans s1 s2

------------------------------------------------------------------------
-- xShape_K4 : the Fst-shape proof for K4 = reify (encAxRefl (Pair (var 0) (var 1))).
--
-- encAxRefl t = nd (natCode tagAxConst) (code t).
-- tagAxConst = 22, so natCode tagAxConst is a deeply nested (nd lf (nd lf ... )).

xShape_K4 : Sigma Term (\ y' -> Sigma Term (\ x' ->
  Deriv (atomic (eqn (ap1 Fst K4) (ap2 Pair x' y')))))
xShape_K4 = mkSigma _ (mkSigma _ (axFst _ _))

------------------------------------------------------------------------
-- Th12_F2_Const_at_pair : Theorem 12 for Pair at (x, v) for arbitrary Terms.

Th12_F2_Const_at_pair : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_Const x v))
                     (codeFTeq2Asym Const x v)))
Th12_F2_Const_at_pair x v =
  let
    pairT : Term
    pairT = ap2 Pair x v

    -- tA, tB: substituents at the var-0 and var-1 positions of K4.
    -- Using cor (Fst pairT), cor (Snd pairT); bridge to cor x, cor v via axFst/axSnd.
    tA : Term
    tA = ap1 cor (ap1 Fst pairT)

    tB : Term
    tB = ap1 cor (ap1 Snd pairT)

    runtimeTree : Term
    runtimeTree = runtimeTreeAt x v

    -- (1) Unfold Df_F2_Const.
    s1 : Deriv (atomic (eqn (ap2 Df_F2_Const x v) runtimeTree))
    s1 = Df_F2_Const_unfold x v

    s2 : Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_Const x v))
                             (ap1 thmT runtimeTree)))
    s2 = cong1 thmT s1

    -- (2) Apply thmTDispRuleInst2_param.
    argsPair : Term
    argsPair = ap2 Pair (ap2 Pair K2 tA) (ap2 Pair K3 tB)

    s3 : Deriv (atomic (eqn (ap1 thmT runtimeTree)
                             (ap2 subT2 argsPair (ap1 thmT K4))))
    s3 = thmTDispRuleInst2_param zero (suc zero) tA tB K4 xShape_K4

    -- (3) thmT K4 = reify (outAxConst (var 0) (var 1)).
    s4 : Deriv (atomic (eqn (ap1 thmT K4)
                             (reify (outAxConst (var zero) (var (suc zero))))))
    s4 = thmTDispAxConst (var zero) (var (suc zero))

    s5 : Deriv (atomic (eqn (ap2 subT2 argsPair (ap1 thmT K4))
                             (ap2 subT2 argsPair
                               (reify (outAxConst (var zero) (var (suc zero)))))))
    s5 = congR subT2 argsPair s4

    -- (4) subTDef_term2 reduces subT2 args (reify codeP) to codedSubstT2-form.
    s6 : Deriv (atomic (eqn (ap2 subT2 argsPair
                               (reify (outAxConst (var zero) (var (suc zero)))))
                             (codedSubstT2 tA tB
                               (code (var zero))
                               (code (var (suc zero)))
                               (outAxConst (var zero) (var (suc zero))))))
    s6 = subTDef_term2 zero (suc zero) tA tB
                       (outAxConst (var zero) (var (suc zero)))

    -- (5) Agda definitionally reduces codedSubstT2 on the closed outAxConst tree.
    --
    -- outAxConst (var 0) (var 1) = codeFormula (atomic (eqn (Const (var 0) (var 1)) (var 0)))
    --                            = nd (code (Const (var 0) (var 1))) (code (var 0))
    --
    -- After codedSubstT2 walk:
    --   LHS slot: code(Const ...) → mkAp2T (codeF2 Const) tA tB.
    --   RHS slot: code(var 0) match → tA.

    pairT_codeF2 : Term
    pairT_codeF2 = reify (codeF2 Const)

    constCodeT : Term
    constCodeT = mkAp2T pairT_codeF2 tA tB

    reducedT2 : Term
    reducedT2 = mkEqT constCodeT tA

    s7 : Deriv (atomic (eqn (codedSubstT2 tA tB
                               (code (var zero))
                               (code (var (suc zero)))
                               (outAxConst (var zero) (var (suc zero))))
                             reducedT2))
    s7 = axRefl reducedT2

    -- (6) Bridges:
    --     - LHS: rewrite tA, tB substituents in mkAp2T to cor x, cor v.
    --       constCodeT = mkAp2T (codeF2 Const) tA tB
    --                  → mkAp2T (codeF2 Const) (cor x) (cor v)
    --     - RHS: tA = cor (Fst pairT)
    --                  → cor x   (via axFst + cong1 cor)
    --                  → cor (Const x v)   (via axConst ruleSym + cong1 cor)
    --     codeFTeq2Asym Const x v = mkEqT (mkAp2T (codeF2 Const) (cor x) (cor v)) (cor (Const x v))

    bridgeFstX : Deriv (atomic (eqn tA (ap1 cor x)))
    bridgeFstX = cong1 cor (axFst x v)

    bridgeSndV : Deriv (atomic (eqn tB (ap1 cor v)))
    bridgeSndV = cong1 cor (axSnd x v)

    -- LHS bridge (mkAp2T form): convert tA, tB → cor x, cor v.
    bridgeMkAp2TA : Deriv (atomic (eqn constCodeT
                                        (mkAp2T pairT_codeF2 (ap1 cor x) tB)))
    bridgeMkAp2TA =
      congR Pair (reify tagAp2)
        (congR Pair pairT_codeF2
          (congL Pair tB bridgeFstX))

    bridgeMkAp2TB : Deriv (atomic (eqn (mkAp2T pairT_codeF2 (ap1 cor x) tB)
                                        (mkAp2T pairT_codeF2 (ap1 cor x) (ap1 cor v))))
    bridgeMkAp2TB =
      congR Pair (reify tagAp2)
        (congR Pair pairT_codeF2
          (congR Pair (ap1 cor x) bridgeSndV))

    bridgeLHS : Deriv (atomic (eqn constCodeT
                                    (mkAp2T pairT_codeF2 (ap1 cor x) (ap1 cor v))))
    bridgeLHS = ruleTrans bridgeMkAp2TA bridgeMkAp2TB

    -- RHS bridge: tA → cor (Const x v).
    --   tA = cor (Fst pairT) → cor x  (via axFst + cong1 cor)
    --   cor x → cor (Const x v)        (via ruleSym (cong1 cor (axConst x v)))

    bridgeRHS : Deriv (atomic (eqn tA (ap1 cor (ap2 Const x v))))
    bridgeRHS =
      ruleTrans bridgeFstX
                (ruleSym (cong1 cor (axConst x v)))

    -- Combine: reducedT2 = Pair constCodeT tA
    --        → Pair (mkAp2T (codeF2 Const) (cor x) (cor v)) (cor (Const x v))
    --        = codeFTeq2Asym Const x v.
    bridgeFinal : Deriv (atomic (eqn reducedT2 (codeFTeq2Asym Const x v)))
    bridgeFinal =
      ruleTrans (congL Pair tA bridgeLHS)
                (congR Pair (mkAp2T pairT_codeF2 (ap1 cor x) (ap1 cor v)) bridgeRHS)

  in ruleTrans s2 (ruleTrans s3 (ruleTrans s5 (ruleTrans s6
       (ruleTrans s7 bridgeFinal))))

------------------------------------------------------------------------
-- Schematic Theorem 12 for Pair: single Deriv P with var 0, var 1 free.
--
-- No fromBaseAndPair needed (Pair has no shape dispatch); just instantiate
-- the parametric proof at (var zero, var (suc zero)).

P_Th12_Const : Formula
P_Th12_Const = atomic (eqn (ap1 thmT (ap2 Df_F2_Const (var zero) (var (suc zero))))
                           (codeFTeq2Asym Const (var zero) (var (suc zero))))

Th12_F2_Const : Deriv P_Th12_Const
Th12_F2_Const = Th12_F2_Const_at_pair (var zero) (var (suc zero))
