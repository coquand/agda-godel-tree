{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.TreeEq   (Theorem 12 case for g = TreeEq, binary).
--
-- TreeEq's BRA primitives are 4 axioms covering all (x,v) shapes:
--   axTreeEqLL : TreeEq O O = O
--   axTreeEqLN : TreeEq O (Pair a b) = Pair O O
--   axTreeEqNL : TreeEq (Pair a b) O = Pair O O
--   axTreeEqNN : TreeEq (Pair a1 a2) (Pair b1 b2)
--                  = IfLf (TreeEq a1 b1) (Pair (TreeEq a2 b2) (Pair O O))
--
-- The NN case has an IfLf-of-TreeEq RHS whose bridge to the asymmetric
-- target  cor (TreeEq (Pair v1 v2) (Pair v3 v4))  requires cross-pair
-- IHs at (v1, v3) and (v2, v4) PLUS IH-on-IfLf and IH-on-Pair to lift
-- cor through the IfLf/Pair structure.  We parameterise the inner
-- module  Construction  over an externally-provided NN Fun2 and its
-- pointwise correctness, leaving the NN proof to Phase 7 glue.
--
-- LL/LN/NL are concrete (mirror IfLf.agda's LL/L/NL cases).

module BRA.Thm12.Parts.TreeEq where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag
  using (tagAxTreeEqLL ; tagAxTreeEqLN ; tagAxTreeEqNL ; tagAxTreeEqNN)
open import BRA.Thm.ThmT
  using (thmT ; tagCode_axTreeEqLL ; tagCode_axTreeEqLN
       ; tagCode_axTreeEqNL ; tagCode_axTreeEqNN ; thClosed)
open import BRA.Thm12.Param.AxTreeEqLL
  using (parEncAxTreeEqLL ; parOutAxTreeEqLL ; parDispAxTreeEqLL)
open import BRA.Thm12.Param.AxTreeEqLN
  using (parEncAxTreeEqLN ; parOutAxTreeEqLN ; parDispAxTreeEqLN)
open import BRA.Thm12.Param.AxTreeEqNL
  using (parEncAxTreeEqNL ; parOutAxTreeEqNL ; parDispAxTreeEqNL)

------------------------------------------------------------------------
-- The codeFTeq2 spec.

codeFTeq2_TreeEq : Term -> Term -> Term
codeFTeq2_TreeEq x v =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 TreeEq))
                        (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor (ap2 TreeEq x v))

------------------------------------------------------------------------
-- ConstructionBase: parametric over D_TreeEq_NN_fun + closure.
-- Provides D_TreeEq, reductions, bridges, and pointwise correctness for
-- the LL / LN / NL non-recursive cases.  Does NOT depend on the NN
-- pointwise correctness.  The full Construction module below extends
-- this with the NN case (which DOES depend on NN_pt) plus the universal
-- closure proof via nested ruleIndBT.

module ConstructionBase
  (D_TreeEq_NN_fun : Fun2)
  (D_TreeEq_NN_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r D_TreeEq_NN_fun) D_TreeEq_NN_fun)
  where

  ----------------------------------------------------------------------
  -- Building blocks for D_TreeEq.

  private
    fstProj : Fun2
    fstProj = Lift I

    sndProj : Fun2
    sndProj = Post Snd Pair

    caseLLTerm : Term
    caseLLTerm = parEncAxTreeEqLL O

    caseLNFun1 : Fun1
    caseLNFun1 = Comp2 Pair (KT tagCode_axTreeEqLN)
                    (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

    caseLNFun : Fun2
    caseLNFun = Post caseLNFun1 sndProj

    caseNLFun1 : Fun1
    caseNLFun1 = Comp2 Pair (KT tagCode_axTreeEqNL)
                    (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

    caseNLFun : Fun2
    caseNLFun = Lift caseNLFun1

    caseNNFun : Fun2
    caseNNFun = D_TreeEq_NN_fun

    innerLfBranch : Fun2
    innerLfBranch = Fan (Lift (KT caseLLTerm)) caseLNFun Pair

    caseXLfDispatch : Fun2
    caseXLfDispatch = Fan sndProj innerLfBranch IfLf

    innerNdBranch : Fun2
    innerNdBranch = Fan caseNLFun caseNNFun Pair

    caseXNdDispatch : Fun2
    caseXNdDispatch = Fan sndProj innerNdBranch IfLf

    outerInner : Fun2
    outerInner = Fan caseXLfDispatch caseXNdDispatch Pair

  D_TreeEq : Fun2
  D_TreeEq = Fan fstProj outerInner IfLf

  -- D_TreeEq has no free variables (depends only on D_TreeEq_NN_fun
  -- which is assumed closed).  Used to discharge ruleInst-shaped
  -- substitution goals.
  D_TreeEq_closed : (x : Nat) (r : Term) -> Eq (substF2 x r D_TreeEq) D_TreeEq
  D_TreeEq_closed x r = eqCong (\ f -> Fan fstProj (Fan
                                                    (Fan sndProj (Fan (Lift (KT caseLLTerm)) caseLNFun Pair) IfLf)
                                                    (Fan sndProj (Fan caseNLFun f Pair) IfLf)
                                                    Pair) IfLf)
                                {x = substF2 x r D_TreeEq_NN_fun} {y = D_TreeEq_NN_fun}
                                (D_TreeEq_NN_closed x r)

  ----------------------------------------------------------------------
  -- Helpers.

  private
    sndProj_eval : (x v : Term) ->
      Deriv (atomic (eqn (ap2 sndProj x v) v))
    sndProj_eval x v =
      let r1 = axPost Snd Pair x v
          r2 = axSnd x v
      in ruleTrans r1 r2

    fstProj_eval : (x v : Term) ->
      Deriv (atomic (eqn (ap2 fstProj x v) x))
    fstProj_eval x v = ruleTrans (axLift I x v) (axI x)

  ----------------------------------------------------------------------
  -- Reduction at (x = O, v = O).

  D_TreeEq_reduce_OO : Deriv (atomic (eqn (ap2 D_TreeEq O O) caseLLTerm))
  D_TreeEq_reduce_OO =
    let s1 = axFan fstProj outerInner IfLf O O
        fst_O = fstProj_eval O O

        oi1 = axFan caseXLfDispatch caseXNdDispatch Pair O O
        cxlf1 = axFan sndProj innerLfBranch IfLf O O
        snd_OO = sndProj_eval O O

        ilf1 = axFan (Lift (KT caseLLTerm)) caseLNFun Pair O O
        ilf2 : Deriv (atomic (eqn (ap2 (Lift (KT caseLLTerm)) O O) caseLLTerm))
        ilf2 = ruleTrans (axLift (KT caseLLTerm) O O)
                         (axKT (nd (natCode tagAxTreeEqLL) lf) O)
        ilf : Deriv (atomic (eqn (ap2 innerLfBranch O O)
                                  (ap2 Pair caseLLTerm (ap2 caseLNFun O O))))
        ilf = ruleTrans ilf1 (congL Pair (ap2 caseLNFun O O) ilf2)

        cxlf : Deriv (atomic (eqn (ap2 caseXLfDispatch O O) caseLLTerm))
        cxlf =
          let s2 = congL IfLf (ap2 innerLfBranch O O) snd_OO
              s3 = congR IfLf O ilf
              s4 = axIfLfL caseLLTerm (ap2 caseLNFun O O)
          in ruleTrans cxlf1 (ruleTrans s2 (ruleTrans s3 s4))

        oi : Deriv (atomic (eqn (ap2 outerInner O O)
                                (ap2 Pair caseLLTerm (ap2 caseXNdDispatch O O))))
        oi = ruleTrans oi1 (congL Pair (ap2 caseXNdDispatch O O) cxlf)

        s2 = congL IfLf (ap2 outerInner O O) fst_O
        s3 = congR IfLf O oi
        s4 = axIfLfL caseLLTerm (ap2 caseXNdDispatch O O)
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  ----------------------------------------------------------------------
  -- Reduction at (x = O, v = Pair a b).

  D_TreeEq_reduce_LN : (a b : Term) ->
    Deriv (atomic (eqn (ap2 D_TreeEq O (ap2 Pair a b))
                       (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))))
  D_TreeEq_reduce_LN a b =
    let v = ap2 Pair a b

        s1 = axFan fstProj outerInner IfLf O v
        fst_O_v = fstProj_eval O v

        cxlf1 = axFan sndProj innerLfBranch IfLf O v
        snd_O_v = sndProj_eval O v

        ilf1 = axFan (Lift (KT caseLLTerm)) caseLNFun Pair O v
        ilf2 : Deriv (atomic (eqn (ap2 (Lift (KT caseLLTerm)) O v) caseLLTerm))
        ilf2 = ruleTrans (axLift (KT caseLLTerm) O v)
                         (axKT (nd (natCode tagAxTreeEqLL) lf) O)
        ilf : Deriv (atomic (eqn (ap2 innerLfBranch O v)
                                  (ap2 Pair caseLLTerm (ap2 caseLNFun O v))))
        ilf = ruleTrans ilf1 (congL Pair (ap2 caseLNFun O v) ilf2)

        lnf1 = axPost caseLNFun1 sndProj O v
        lnf2 = axComp2 Pair (KT tagCode_axTreeEqLN)
                       (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) v
        lnf3 : Deriv (atomic (eqn (ap1 (KT tagCode_axTreeEqLN) v) tagCode_axTreeEqLN))
        lnf3 = axKT (natCode tagAxTreeEqLN) v
        lnf4a = axComp2 Pair (Comp cor Fst) (Comp cor Snd) v
        lnf4b = axComp cor Fst v
        lnf4c = cong1 cor (axFst a b)
        lnf4 : Deriv (atomic (eqn (ap1 (Comp cor Fst) v) (ap1 cor a)))
        lnf4 = ruleTrans lnf4b lnf4c
        lnf5b = axComp cor Snd v
        lnf5c = cong1 cor (axSnd a b)
        lnf5 : Deriv (atomic (eqn (ap1 (Comp cor Snd) v) (ap1 cor b)))
        lnf5 = ruleTrans lnf5b lnf5c
        lnf6 : Deriv (atomic (eqn (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) v)
                                   (ap2 Pair (ap1 cor a) (ap1 cor b))))
        lnf6 = ruleTrans lnf4a
                (ruleTrans (congL Pair (ap1 (Comp cor Snd) v) lnf4)
                           (congR Pair (ap1 cor a) lnf5))
        lnf_inner : Deriv (atomic (eqn (ap1 caseLNFun1 v)
                                         (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))))
        lnf_inner = ruleTrans lnf2
                      (ruleTrans (congL Pair _ lnf3)
                                 (congR Pair tagCode_axTreeEqLN lnf6))
        lnf : Deriv (atomic (eqn (ap2 caseLNFun O v) (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))))
        lnf = ruleTrans lnf1 (ruleTrans (cong1 caseLNFun1 snd_O_v) lnf_inner)

        cxlf2 = congL IfLf (ap2 innerLfBranch O v) snd_O_v
        ilf' : Deriv (atomic (eqn (ap2 innerLfBranch O v)
                                   (ap2 Pair caseLLTerm (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b)))))
        ilf' = ruleTrans ilf (congR Pair caseLLTerm lnf)
        cxlf3 = congR IfLf v ilf'

        cxlf4 = axIfLfN a b caseLLTerm (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))

        cxlf : Deriv (atomic (eqn (ap2 caseXLfDispatch O v)
                                   (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))))
        cxlf = ruleTrans cxlf1 (ruleTrans cxlf2 (ruleTrans cxlf3 cxlf4))

        oi1 = axFan caseXLfDispatch caseXNdDispatch Pair O v
        oi : Deriv (atomic (eqn (ap2 outerInner O v)
                                (ap2 Pair (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))
                                          (ap2 caseXNdDispatch O v))))
        oi = ruleTrans oi1 (congL Pair (ap2 caseXNdDispatch O v) cxlf)

        s2 = congL IfLf (ap2 outerInner O v) fst_O_v
        s3 = congR IfLf O oi
        s4 = axIfLfL (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b)) (ap2 caseXNdDispatch O v)
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  ----------------------------------------------------------------------
  -- Reduction at (x = Pair p q, v = O).

  D_TreeEq_reduce_NL : (p q : Term) ->
    Deriv (atomic (eqn (ap2 D_TreeEq (ap2 Pair p q) O)
                       (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))))
  D_TreeEq_reduce_NL p q =
    let x = ap2 Pair p q

        s1 = axFan fstProj outerInner IfLf x O
        fst_x_O = fstProj_eval x O

        cxnd1 = axFan sndProj innerNdBranch IfLf x O
        snd_x_O = sndProj_eval x O

        ind1 = axFan caseNLFun caseNNFun Pair x O

        nlf1 = axLift caseNLFun1 x O
        nlf2 = axComp2 Pair (KT tagCode_axTreeEqNL)
                       (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) x
        nlf3 : Deriv (atomic (eqn (ap1 (KT tagCode_axTreeEqNL) x) tagCode_axTreeEqNL))
        nlf3 = axKT (natCode tagAxTreeEqNL) x
        nlf4a = axComp2 Pair (Comp cor Fst) (Comp cor Snd) x
        nlf4b = axComp cor Fst x
        nlf4c = cong1 cor (axFst p q)
        nlf4 : Deriv (atomic (eqn (ap1 (Comp cor Fst) x) (ap1 cor p)))
        nlf4 = ruleTrans nlf4b nlf4c
        nlf5b = axComp cor Snd x
        nlf5c = cong1 cor (axSnd p q)
        nlf5 : Deriv (atomic (eqn (ap1 (Comp cor Snd) x) (ap1 cor q)))
        nlf5 = ruleTrans nlf5b nlf5c
        nlf6 : Deriv (atomic (eqn (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) x)
                                   (ap2 Pair (ap1 cor p) (ap1 cor q))))
        nlf6 = ruleTrans nlf4a
                (ruleTrans (congL Pair (ap1 (Comp cor Snd) x) nlf4)
                           (congR Pair (ap1 cor p) nlf5))
        nlf_inner : Deriv (atomic (eqn (ap1 caseNLFun1 x)
                                         (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))))
        nlf_inner = ruleTrans nlf2
                      (ruleTrans (congL Pair _ nlf3)
                                 (congR Pair tagCode_axTreeEqNL nlf6))
        nlf : Deriv (atomic (eqn (ap2 caseNLFun x O)
                                  (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))))
        nlf = ruleTrans nlf1 nlf_inner

        ind : Deriv (atomic (eqn (ap2 innerNdBranch x O)
                                  (ap2 Pair (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))
                                            (ap2 caseNNFun x O))))
        ind = ruleTrans ind1 (congL Pair (ap2 caseNNFun x O) nlf)

        cxnd2 = congL IfLf (ap2 innerNdBranch x O) snd_x_O
        cxnd3 = congR IfLf O ind
        cxnd4 = axIfLfL (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q)) (ap2 caseNNFun x O)

        cxnd : Deriv (atomic (eqn (ap2 caseXNdDispatch x O)
                                   (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))))
        cxnd = ruleTrans cxnd1 (ruleTrans cxnd2 (ruleTrans cxnd3 cxnd4))

        oi1 = axFan caseXLfDispatch caseXNdDispatch Pair x O
        oi : Deriv (atomic (eqn (ap2 outerInner x O)
                                (ap2 Pair (ap2 caseXLfDispatch x O)
                                          (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q)))))
        oi = ruleTrans oi1 (congR Pair (ap2 caseXLfDispatch x O) cxnd)

        s2 = congL IfLf (ap2 outerInner x O) fst_x_O
        s3 = congR IfLf x oi
        s4 = axIfLfN p q (ap2 caseXLfDispatch x O) (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  ----------------------------------------------------------------------
  -- Reduction at (x = Pair p q, v = Pair a b): dispatches to caseNNFun.

  D_TreeEq_reduce_NN : (p q a b : Term) ->
    Deriv (atomic (eqn (ap2 D_TreeEq (ap2 Pair p q) (ap2 Pair a b))
                       (ap2 D_TreeEq_NN_fun (ap2 Pair p q) (ap2 Pair a b))))
  D_TreeEq_reduce_NN p q a b =
    let x = ap2 Pair p q
        v = ap2 Pair a b

        s1 = axFan fstProj outerInner IfLf x v
        fst_x_v = fstProj_eval x v

        cxnd1 = axFan sndProj innerNdBranch IfLf x v
        snd_x_v = sndProj_eval x v

        ind1 = axFan caseNLFun caseNNFun Pair x v

        cxnd2 = congL IfLf (ap2 innerNdBranch x v) snd_x_v
        cxnd3 = congR IfLf v ind1
        cxnd4 = axIfLfN a b (ap2 caseNLFun x v) (ap2 D_TreeEq_NN_fun x v)

        cxnd : Deriv (atomic (eqn (ap2 caseXNdDispatch x v)
                                   (ap2 D_TreeEq_NN_fun x v)))
        cxnd = ruleTrans cxnd1 (ruleTrans cxnd2 (ruleTrans cxnd3 cxnd4))

        oi1 = axFan caseXLfDispatch caseXNdDispatch Pair x v
        oi : Deriv (atomic (eqn (ap2 outerInner x v)
                                (ap2 Pair (ap2 caseXLfDispatch x v)
                                          (ap2 D_TreeEq_NN_fun x v))))
        oi = ruleTrans oi1 (congR Pair (ap2 caseXLfDispatch x v) cxnd)

        s2 = congL IfLf (ap2 outerInner x v) fst_x_v
        s3 = congR IfLf x oi
        s4 = axIfLfN p q (ap2 caseXLfDispatch x v) (ap2 D_TreeEq_NN_fun x v)
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  ----------------------------------------------------------------------
  -- Bridges.

  private
    corPairUnfold : (a b : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap2 Pair a b))
                          (ap2 Pair (reify tagAp2)
                                    (ap2 Pair (reify (codeF2 Pair))
                                              (ap2 Pair (ap1 cor a) (ap1 cor b))))))
    corPairUnfold a b =
      let recs = ap2 Pair (ap1 cor a) (ap1 cor b)
          orig = ap2 Pair a b
      in ruleTrans (axRecNd O stepCor a b) (stepCorRed orig recs)

  bridgeLL : Deriv (atomic (eqn parOutAxTreeEqLL (codeFTeq2_TreeEq O O)))
  bridgeLL =
    let cor_O = axRecLf O stepCor
        treqLL_eq : Deriv (atomic (eqn (ap2 TreeEq O O) O))
        treqLL_eq = axTreeEqLL
        cor_treqLL : Deriv (atomic (eqn (ap1 cor (ap2 TreeEq O O)) O))
        cor_treqLL = ruleTrans (cong1 cor treqLL_eq) cor_O

        step1 : Deriv (atomic (eqn (ap2 Pair (reify (codeF2 TreeEq)) (ap2 Pair O O))
                                    (ap2 Pair (reify (codeF2 TreeEq))
                                      (ap2 Pair (ap1 cor O) (ap1 cor O)))))
        step1 = congR Pair (reify (codeF2 TreeEq))
                  (ruleTrans (congL Pair O (ruleSym cor_O))
                             (congR Pair (ap1 cor O) (ruleSym cor_O)))

        step2 : Deriv (atomic (eqn (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 TreeEq)) (ap2 Pair O O)))
                                    (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 TreeEq))
                                        (ap2 Pair (ap1 cor O) (ap1 cor O))))))
        step2 = congR Pair (reify tagAp2) step1

        step3 : Deriv (atomic (eqn parOutAxTreeEqLL
                                    (ap2 Pair
                                      (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 TreeEq))
                                          (ap2 Pair (ap1 cor O) (ap1 cor O))))
                                      O)))
        step3 = congL Pair O step2

        step4 : Deriv (atomic (eqn (ap2 Pair
                                      (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 TreeEq))
                                          (ap2 Pair (ap1 cor O) (ap1 cor O))))
                                      O)
                                    (codeFTeq2_TreeEq O O)))
        step4 = congR Pair _ (ruleSym cor_treqLL)
    in ruleTrans step3 step4

  bridgeLN : (a b : Term) ->
    Deriv (atomic (eqn (parOutAxTreeEqLN (ap1 cor a) (ap1 cor b)) (codeFTeq2_TreeEq O (ap2 Pair a b))))
  bridgeLN a b =
    let cor_O = axRecLf O stepCor
        cpu_ab = corPairUnfold a b

        treqLN_eq : Deriv (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
        treqLN_eq = axTreeEqLN a b
        cor_pair_OO_O : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                                            (ap2 Pair (reify tagAp2)
                                              (ap2 Pair (reify (codeF2 Pair))
                                                (ap2 Pair O O)))))
        cor_pair_OO_O =
          ruleTrans (corPairUnfold O O)
            (congR Pair (reify tagAp2)
              (congR Pair (reify (codeF2 Pair))
                (ruleTrans (congL Pair (ap1 cor O) cor_O)
                           (congR Pair O cor_O))))
        cor_treq_eq : Deriv (atomic (eqn (ap1 cor (ap2 TreeEq O (ap2 Pair a b)))
                                         (reify (code (ap2 Pair O O)))))
        cor_treq_eq = ruleTrans (cong1 cor treqLN_eq) cor_pair_OO_O

        step1a : Deriv (atomic (eqn
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                        (ap2 Pair (ap1 cor a) (ap1 cor b))))
                            (ap1 cor (ap2 Pair a b))))
        step1a = ruleSym cpu_ab

        step1b : Deriv (atomic (eqn
                            (ap2 Pair O
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair (ap1 cor a) (ap1 cor b)))))
                            (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))
        step1b = ruleTrans (congL Pair _ (ruleSym cor_O))
                           (congR Pair (ap1 cor O) step1a)

        step1c : Deriv (atomic (eqn
                            (ap2 Pair (reify (codeF2 TreeEq))
                              (ap2 Pair O
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                            (ap2 Pair (ap1 cor a) (ap1 cor b))))))
                            (ap2 Pair (reify (codeF2 TreeEq))
                              (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b))))))
        step1c = congR Pair (reify (codeF2 TreeEq)) step1b

        step1d : Deriv (atomic (eqn
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 TreeEq))
                                (ap2 Pair O
                                  (ap2 Pair (reify tagAp2)
                                    (ap2 Pair (reify (codeF2 Pair))
                                              (ap2 Pair (ap1 cor a) (ap1 cor b)))))))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 TreeEq))
                                (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))))
        step1d = congR Pair (reify tagAp2) step1c

        step1 : Deriv (atomic (eqn (parOutAxTreeEqLN (ap1 cor a) (ap1 cor b))
                                    (ap2 Pair
                                      (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 TreeEq))
                                          (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))
                                      (reify (code (ap2 Pair O O))))))
        step1 = congL Pair (reify (code (ap2 Pair O O))) step1d

        step2 : Deriv (atomic (eqn
                            (ap2 Pair
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 TreeEq))
                                  (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))
                              (reify (code (ap2 Pair O O))))
                            (codeFTeq2_TreeEq O (ap2 Pair a b))))
        step2 = congR Pair _ (ruleSym cor_treq_eq)
    in ruleTrans step1 step2

  bridgeNL : (p q : Term) ->
    Deriv (atomic (eqn (parOutAxTreeEqNL (ap1 cor p) (ap1 cor q)) (codeFTeq2_TreeEq (ap2 Pair p q) O)))
  bridgeNL p q =
    let cor_O = axRecLf O stepCor
        cpu_pq = corPairUnfold p q

        treqNL_eq : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair p q) O) (ap2 Pair O O)))
        treqNL_eq = axTreeEqNL p q
        cor_pair_OO_O : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                                            (ap2 Pair (reify tagAp2)
                                              (ap2 Pair (reify (codeF2 Pair))
                                                (ap2 Pair O O)))))
        cor_pair_OO_O =
          ruleTrans (corPairUnfold O O)
            (congR Pair (reify tagAp2)
              (congR Pair (reify (codeF2 Pair))
                (ruleTrans (congL Pair (ap1 cor O) cor_O)
                           (congR Pair O cor_O))))
        cor_treq_eq : Deriv (atomic (eqn (ap1 cor (ap2 TreeEq (ap2 Pair p q) O))
                                         (reify (code (ap2 Pair O O)))))
        cor_treq_eq = ruleTrans (cong1 cor treqNL_eq) cor_pair_OO_O

        step1a : Deriv (atomic (eqn
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                        (ap2 Pair (ap1 cor p) (ap1 cor q))))
                            (ap1 cor (ap2 Pair p q))))
        step1a = ruleSym cpu_pq

        step1b : Deriv (atomic (eqn
                            (ap2 Pair (ap2 Pair (reify tagAp2)
                                         (ap2 Pair (reify (codeF2 Pair))
                                                   (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                      O)
                            (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O))))
        step1b = ruleTrans (congL Pair O step1a)
                           (congR Pair (ap1 cor (ap2 Pair p q)) (ruleSym cor_O))

        step1c : Deriv (atomic (eqn
                            (ap2 Pair (reify (codeF2 TreeEq))
                              (ap2 Pair (ap2 Pair (reify tagAp2)
                                           (ap2 Pair (reify (codeF2 Pair))
                                                     (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                        O))
                            (ap2 Pair (reify (codeF2 TreeEq))
                              (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O)))))
        step1c = congR Pair (reify (codeF2 TreeEq)) step1b

        step1d : Deriv (atomic (eqn
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 TreeEq))
                                (ap2 Pair (ap2 Pair (reify tagAp2)
                                            (ap2 Pair (reify (codeF2 Pair))
                                                      (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                          O)))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 TreeEq))
                                (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O))))))
        step1d = congR Pair (reify tagAp2) step1c

        step1 = congL Pair (reify (code (ap2 Pair O O))) step1d

        step2 : Deriv (atomic (eqn
                            (ap2 Pair
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 TreeEq))
                                  (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O))))
                              (reify (code (ap2 Pair O O))))
                            (codeFTeq2_TreeEq (ap2 Pair p q) O)))
        step2 = congR Pair _ (ruleSym cor_treq_eq)
    in ruleTrans step1 step2

  ----------------------------------------------------------------------
  -- Pointwise correctness.

  D_correct2_TreeEq_LL : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq O O)) (codeFTeq2_TreeEq O O)))
  D_correct2_TreeEq_LL =
    let r_thmT = cong1 thmT D_TreeEq_reduce_OO
        r_disp = parDispAxTreeEqLL O
    in ruleTrans r_thmT (ruleTrans r_disp bridgeLL)

  D_correct2_TreeEq_LN : (a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq O (ap2 Pair a b))) (codeFTeq2_TreeEq O (ap2 Pair a b))))
  D_correct2_TreeEq_LN a b =
    let r_thmT = cong1 thmT (D_TreeEq_reduce_LN a b)
        r_disp = parDispAxTreeEqLN (ap1 cor a) (ap1 cor b)
        r_bridge = bridgeLN a b
    in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

  D_correct2_TreeEq_NL : (p q : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq (ap2 Pair p q) O)) (codeFTeq2_TreeEq (ap2 Pair p q) O)))
  D_correct2_TreeEq_NL p q =
    let r_thmT = cong1 thmT (D_TreeEq_reduce_NL p q)
        r_disp = parDispAxTreeEqNL (ap1 cor p) (ap1 cor q)
        r_bridge = bridgeNL p q
    in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

------------------------------------------------------------------------
-- Construction: extends ConstructionBase with the NN case + universal
-- proof.  Adds the NN pointwise parameter D_correct2_TreeEq_NN_pt and
-- threads it through the nested ruleIndBT closure.

module Construction
  (D_TreeEq_NN_fun : Fun2)
  (D_TreeEq_NN_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r D_TreeEq_NN_fun) D_TreeEq_NN_fun)
  (D_correct2_TreeEq_NN_pt : (p q a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq_NN_fun (ap2 Pair p q) (ap2 Pair a b)))
                       (codeFTeq2_TreeEq (ap2 Pair p q) (ap2 Pair a b)))))
  where

  open ConstructionBase D_TreeEq_NN_fun D_TreeEq_NN_closed public

  D_correct2_TreeEq_NN : (p q a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq (ap2 Pair p q) (ap2 Pair a b)))
                       (codeFTeq2_TreeEq (ap2 Pair p q) (ap2 Pair a b))))
  D_correct2_TreeEq_NN p q a b =
    let r_thmT = cong1 thmT (D_TreeEq_reduce_NN p q a b)
    in ruleTrans r_thmT (D_correct2_TreeEq_NN_pt p q a b)

  ----------------------------------------------------------------------
  -- Universal proof via nested ruleIndBT.

  private
    v1OuterNat : Nat
    v1OuterNat = suc (suc zero)
    v2OuterNat : Nat
    v2OuterNat = suc (suc (suc zero))
    v1InnerNat : Nat
    v1InnerNat = suc (suc (suc (suc zero)))
    v2InnerNat : Nat
    v2InnerNat = suc (suc (suc (suc (suc zero))))

    vOuterNat : Nat
    vOuterNat = suc zero

    Q_baseO : Formula
    Q_baseO = atomic (eqn (ap1 thmT (ap2 D_TreeEq O (var zero)))
                          (codeFTeq2_TreeEq O (var zero)))

    inner_base_O_proof : Deriv (substF zero O Q_baseO)
    inner_base_O_proof =
      eqSubst (\ DT -> Deriv (atomic (eqn (ap1 (substF1 zero O thmT) (ap2 DT O O))
                                          (codeFTeq2_TreeEq O O))))
              (eqSym (D_TreeEq_closed zero O))
              (eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap2 D_TreeEq O O))
                                                    (codeFTeq2_TreeEq O O))))
                       (eqSym (thClosed zero O))
                       D_correct2_TreeEq_LL)

    inner_step_O_concl : Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
    inner_step_O_concl =
      eqSubst (\ DT -> Deriv (atomic (eqn
                                (ap1 (substF1 zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) thmT)
                                  (ap2 DT O (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                                (codeFTeq2_TreeEq O (ap2 Pair (var v1InnerNat) (var v2InnerNat))))))
              (eqSym (D_TreeEq_closed zero (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                                  (ap1 fT (ap2 D_TreeEq O (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                                  (codeFTeq2_TreeEq O (ap2 Pair (var v1InnerNat) (var v2InnerNat))))))
                       (eqSym (thClosed zero (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                       (D_correct2_TreeEq_LN (var v1InnerNat) (var v2InnerNat)))

    inner_step_O_imp_inner :
      Deriv (substF zero (var v2InnerNat) Q_baseO imp
             substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
    inner_step_O_imp_inner =
      mp (axK (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
              (substF zero (var v2InnerNat) Q_baseO))
         inner_step_O_concl

    inner_step_O_imp :
      Deriv (substF zero (var v1InnerNat) Q_baseO imp
             (substF zero (var v2InnerNat) Q_baseO imp
              substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO))
    inner_step_O_imp =
      mp (axK (substF zero (var v2InnerNat) Q_baseO imp
               substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
              (substF zero (var v1InnerNat) Q_baseO))
         inner_step_O_imp_inner

    univ_x_O : Deriv Q_baseO
    univ_x_O = ruleIndBT Q_baseO v1InnerNat v2InnerNat inner_base_O_proof inner_step_O_imp

    outer_base_proof_unsubst : Deriv (substF zero (var vOuterNat) Q_baseO)
    outer_base_proof_unsubst = ruleInst zero (var vOuterNat) univ_x_O

    P_outer : Formula
    P_outer = atomic (eqn (ap1 thmT (ap2 D_TreeEq (var zero) (var vOuterNat)))
                          (codeFTeq2_TreeEq (var zero) (var vOuterNat)))

    outer_base_proof : Deriv (substF zero O P_outer)
    outer_base_proof =
      eqSubst (\ DT -> Deriv (atomic (eqn
                                (ap1 (substF1 zero O thmT) (ap2 DT O (var vOuterNat)))
                                (codeFTeq2_TreeEq O (var vOuterNat)))))
              (eqSym (D_TreeEq_closed zero O))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                                  (ap1 fT (ap2 D_TreeEq O (var vOuterNat)))
                                  (codeFTeq2_TreeEq O (var vOuterNat)))))
                       (eqSym (thClosed zero O))
                       (eqSubst (\ fT -> Deriv (atomic (eqn
                                            (ap1 fT (ap2 D_TreeEq O (var vOuterNat)))
                                            (codeFTeq2_TreeEq O (var vOuterNat)))))
                                (thClosed zero (var vOuterNat))
                                (eqSubst (\ DT -> Deriv (atomic (eqn
                                            (ap1 (substF1 zero (var vOuterNat) thmT)
                                              (ap2 DT O (var vOuterNat)))
                                            (codeFTeq2_TreeEq O (var vOuterNat)))))
                                         (D_TreeEq_closed zero (var vOuterNat))
                                         outer_base_proof_unsubst)))

    pairOuter : Term
    pairOuter = ap2 Pair (var v1OuterNat) (var v2OuterNat)

    Q_stepP : Formula
    Q_stepP = atomic (eqn (ap1 thmT (ap2 D_TreeEq pairOuter (var zero)))
                          (codeFTeq2_TreeEq pairOuter (var zero)))

    inner_base_P_proof : Deriv (substF zero O Q_stepP)
    inner_base_P_proof =
      eqSubst (\ DT -> Deriv (atomic (eqn
                                (ap1 (substF1 zero O thmT) (ap2 DT pairOuter O))
                                (codeFTeq2_TreeEq pairOuter O))))
              (eqSym (D_TreeEq_closed zero O))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                                  (ap1 fT (ap2 D_TreeEq pairOuter O))
                                  (codeFTeq2_TreeEq pairOuter O))))
                       (eqSym (thClosed zero O))
                       (D_correct2_TreeEq_NL (var v1OuterNat) (var v2OuterNat)))

    inner_step_P_concl : Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
    inner_step_P_concl =
      eqSubst (\ DT -> Deriv (atomic (eqn
                                (ap1 (substF1 zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) thmT)
                                  (ap2 DT pairOuter (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                                (codeFTeq2_TreeEq pairOuter (ap2 Pair (var v1InnerNat) (var v2InnerNat))))))
              (eqSym (D_TreeEq_closed zero (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                                  (ap1 fT (ap2 D_TreeEq pairOuter (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                                  (codeFTeq2_TreeEq pairOuter (ap2 Pair (var v1InnerNat) (var v2InnerNat))))))
                       (eqSym (thClosed zero (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                       (D_correct2_TreeEq_NN (var v1OuterNat) (var v2OuterNat) (var v1InnerNat) (var v2InnerNat)))

    inner_step_P_imp_inner :
      Deriv (substF zero (var v2InnerNat) Q_stepP imp
             substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
    inner_step_P_imp_inner =
      mp (axK (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
              (substF zero (var v2InnerNat) Q_stepP))
         inner_step_P_concl

    inner_step_P_imp :
      Deriv (substF zero (var v1InnerNat) Q_stepP imp
             (substF zero (var v2InnerNat) Q_stepP imp
              substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP))
    inner_step_P_imp =
      mp (axK (substF zero (var v2InnerNat) Q_stepP imp
               substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
              (substF zero (var v1InnerNat) Q_stepP))
         inner_step_P_imp_inner

    univ_x_P : Deriv Q_stepP
    univ_x_P = ruleIndBT Q_stepP v1InnerNat v2InnerNat inner_base_P_proof inner_step_P_imp

    outer_step_concl_unsubst : Deriv (substF zero (var vOuterNat) Q_stepP)
    outer_step_concl_unsubst = ruleInst zero (var vOuterNat) univ_x_P

    outer_step_concl : Deriv (substF zero pairOuter P_outer)
    outer_step_concl =
      eqSubst (\ DT -> Deriv (atomic (eqn
                                (ap1 (substF1 zero pairOuter thmT) (ap2 DT pairOuter (var vOuterNat)))
                                (codeFTeq2_TreeEq pairOuter (var vOuterNat)))))
              (eqSym (D_TreeEq_closed zero pairOuter))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                                  (ap1 fT (ap2 D_TreeEq pairOuter (var vOuterNat)))
                                  (codeFTeq2_TreeEq pairOuter (var vOuterNat)))))
                       (eqSym (thClosed zero pairOuter))
                       (eqSubst (\ fT -> Deriv (atomic (eqn
                                            (ap1 fT (ap2 D_TreeEq pairOuter (var vOuterNat)))
                                            (codeFTeq2_TreeEq pairOuter (var vOuterNat)))))
                                (thClosed zero (var vOuterNat))
                                (eqSubst (\ DT -> Deriv (atomic (eqn
                                            (ap1 (substF1 zero (var vOuterNat) thmT)
                                              (ap2 DT pairOuter (var vOuterNat)))
                                            (codeFTeq2_TreeEq pairOuter (var vOuterNat)))))
                                         (D_TreeEq_closed zero (var vOuterNat))
                                         outer_step_concl_unsubst)))

    outer_step_imp_inner :
      Deriv (substF zero (var v2OuterNat) P_outer imp
             substF zero pairOuter P_outer)
    outer_step_imp_inner =
      mp (axK (substF zero pairOuter P_outer)
              (substF zero (var v2OuterNat) P_outer))
         outer_step_concl

    outer_step_imp :
      Deriv (substF zero (var v1OuterNat) P_outer imp
             (substF zero (var v2OuterNat) P_outer imp
              substF zero pairOuter P_outer))
    outer_step_imp =
      mp (axK (substF zero (var v2OuterNat) P_outer imp
               substF zero pairOuter P_outer)
              (substF zero (var v1OuterNat) P_outer))
         outer_step_imp_inner

  D_correct2_TreeEq_univ : Deriv P_outer
  D_correct2_TreeEq_univ = ruleIndBT P_outer v1OuterNat v2OuterNat outer_base_proof outer_step_imp

  D_correct2_TreeEq : (x v : Term)
    (x_no_var0 : Eq (subst zero x x) x)
    (v_no_var0 : Eq (subst zero x v) v)
    (v_no_var1 : Eq (subst (suc zero) v v) v)
    (x_no_var1 : Eq (subst (suc zero) v x) x) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq x v)) (codeFTeq2_TreeEq x v)))
  D_correct2_TreeEq x v xeq0 veq0 veq1 xeq1 =
    let stage1 : Deriv (substF zero x P_outer)
        stage1 = ruleInst zero x D_correct2_TreeEq_univ

        stage2 : Deriv (substF (suc zero) v (substF zero x P_outer))
        stage2 = ruleInst (suc zero) v stage1

        -- D_TreeEq closure under both substitutions.
        D_TreeEq_closed_outer : Eq (substF2 zero x D_TreeEq) D_TreeEq
        D_TreeEq_closed_outer = D_TreeEq_closed zero x

        D_TreeEq_closed_inner : Eq (substF2 (suc zero) v (substF2 zero x D_TreeEq)) D_TreeEq
        D_TreeEq_closed_inner =
          eqTrans (eqCong (substF2 (suc zero) v) D_TreeEq_closed_outer)
                  (D_TreeEq_closed (suc zero) v)

    in eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap2 D_TreeEq x v)) (codeFTeq2_TreeEq x v))))
         (thClosed (suc zero) v)
         (eqSubst (\ fT -> Deriv (atomic (eqn (ap1 (substF1 (suc zero) v fT) (ap2 D_TreeEq x v))
                                              (codeFTeq2_TreeEq x v))))
           (thClosed zero x)
           (eqSubst (\ xT -> Deriv (atomic (eqn (ap1 (substF1 (suc zero) v (substF1 zero x thmT))
                                                     (ap2 D_TreeEq xT v))
                                                (codeFTeq2_TreeEq xT v))))
             xeq1
             (eqSubst (\ DT -> Deriv (atomic (eqn (ap1 (substF1 (suc zero) v (substF1 zero x thmT))
                                                       (ap2 DT (subst (suc zero) v x) v))
                                                  (codeFTeq2_TreeEq (subst (suc zero) v x) v))))
               D_TreeEq_closed_inner
               stage2)))
