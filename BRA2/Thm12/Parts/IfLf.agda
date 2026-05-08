{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.IfLf   (Theorem 12 case for g = IfLf, binary).
--
-- IfLf is partial: 4 axioms (axIfLfLL/L/NL/N) cover all (x,v) in
-- {O, Pair _ _} x {O, Pair _ _}.  Theorem 12 requires nested
-- ruleIndBT (binary-tree induction on x, then on v).
--
-- D_IfLf : Fun2 dispatches on x first, then on v:
--   ap2 D_IfLf O           O           = parEncAxIfLfLL O
--   ap2 D_IfLf O           (Pair a b) = parEncAxIfLfL (cor a) (cor b)
--   ap2 D_IfLf (Pair p q)  O           = parEncAxIfLfNL (cor p) (cor q)
--   ap2 D_IfLf (Pair p q)  (Pair a b) = parEncAxIfLfN (cor p) (cor q) (cor a) (cor b)

module BRA2.Thm12.Parts.IfLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag
  using (tagAxIfLfL ; tagAxIfLfN ; tagAxIfLfLL ; tagAxIfLfNL)
open import BRA2.Thm.ThmT
  using (thmT ; tagCode_axIfLfL ; tagCode_axIfLfN ; tagCode_axIfLfLL ; tagCode_axIfLfNL ; thClosed)
open import BRA2.Thm12.Param.AxIfLfL
  using (parEncAxIfLfL ; parOutAxIfLfL ; parDispAxIfLfL)
open import BRA2.Thm12.Param.AxIfLfN
  using (parEncAxIfLfN ; parOutAxIfLfN ; parDispAxIfLfN)
open import BRA2.Thm12.Param.AxIfLfLL
  using (parEncAxIfLfLL ; parOutAxIfLfLL ; parDispAxIfLfLL)
open import BRA2.Thm12.Param.AxIfLfNL
  using (parEncAxIfLfNL ; parOutAxIfLfNL ; parDispAxIfLfNL)
open import BRA2.MaxVar
  using (pickFresh ; subst_pickFresh ; pickFresh_natEq_one' ; natEq_refl)

------------------------------------------------------------------------
codeFTeq2_IfLf : Term -> Term -> Term
codeFTeq2_IfLf x v =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor (ap2 IfLf x v))

------------------------------------------------------------------------
-- Building blocks for D_IfLf.

private
  -- Project first arg of Fun2.
  fstProj : Fun2
  fstProj = Lift I

  -- Project second arg of Fun2: ap2 sndProj x v = v.
  sndProj : Fun2
  sndProj = Post Snd Pair

  -- Closed encoded base: parEncAxIfLfLL O (witness for IfLf O O = O).
  caseLLTerm : Term
  caseLLTerm = parEncAxIfLfLL O

  -- Fun1 producing parEncAxIfLfL (cor (Fst v)) (cor (Snd v)) from v.
  caseLNFun1 : Fun1
  caseLNFun1 = Comp2 Pair (KT tagCode_axIfLfL)
                  (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

  -- Fun2 producing parEncAxIfLfL (cor (Fst v)) (cor (Snd v)).
  caseLNFun : Fun2
  caseLNFun = Post caseLNFun1 sndProj

  -- Fun1 producing parEncAxIfLfNL (cor (Fst x)) (cor (Snd x)) from x.
  caseNLFun1 : Fun1
  caseNLFun1 = Comp2 Pair (KT tagCode_axIfLfNL)
                  (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

  caseNLFun : Fun2
  caseNLFun = Lift caseNLFun1

  -- Fun2 producing Pair (cor (Fst v)) (cor (Snd v)) from (x, v).
  corPairOfV : Fun2
  corPairOfV = Post (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) sndProj

  -- Fun2 producing parEncAxIfLfN (cor (Fst x)) (cor (Snd x)) (cor (Fst v)) (cor (Snd v)).
  -- Shape: Pair tagCode_axIfLfN (Pair (cor Fst x) (Pair (cor Snd x) (Pair (cor Fst v) (cor Snd v))))
  caseNNFun : Fun2
  caseNNFun =
    Fan (Lift (KT tagCode_axIfLfN))
        (Fan (Lift (Comp cor Fst))
             (Fan (Lift (Comp cor Snd)) corPairOfV Pair)
             Pair)
        Pair

  -- Inner LF-branch: Pair caseLLTerm caseLNFun-result.
  innerLfBranch : Fun2
  innerLfBranch = Fan (Lift (KT caseLLTerm)) caseLNFun Pair

  -- caseXLfDispatch: when x = O, this is what gets returned (after IfLf's selection).
  -- ap2 caseXLfDispatch x v = IfLf v (Pair caseLLTerm caseLNFun-result).
  caseXLfDispatch : Fun2
  caseXLfDispatch = Fan sndProj innerLfBranch IfLf

  -- Inner ND-branch: Pair caseNLFun-result caseNNFun-result.
  innerNdBranch : Fun2
  innerNdBranch = Fan caseNLFun caseNNFun Pair

  -- caseXNdDispatch: when x = Pair p q, this gets returned.
  -- ap2 caseXNdDispatch x v = IfLf v (Pair caseNLFun-result caseNNFun-result).
  caseXNdDispatch : Fun2
  caseXNdDispatch = Fan sndProj innerNdBranch IfLf

  outerInner : Fun2
  outerInner = Fan caseXLfDispatch caseXNdDispatch Pair

D_IfLf : Fun2
D_IfLf = Fan fstProj outerInner IfLf

------------------------------------------------------------------------
-- Combinator reductions for D_IfLf at the four (x, v) shapes.

-- Helper: ap2 sndProj x v = v.
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

------------------------------------------------------------------------
-- Reduction at (x = O, v = O).

D_IfLf_reduce_OO : Deriv (atomic (eqn (ap2 D_IfLf O O) caseLLTerm))
D_IfLf_reduce_OO =
  let -- ap2 D_IfLf O O = ap2 IfLf (ap2 fstProj O O) (ap2 outerInner O O).
      s1 = axFan fstProj outerInner IfLf O O

      fst_O = fstProj_eval O O  -- ap2 fstProj O O = O

      -- ap2 outerInner O O = ap2 Pair (ap2 caseXLfDispatch O O) (ap2 caseXNdDispatch O O)
      oi1 = axFan caseXLfDispatch caseXNdDispatch Pair O O

      -- ap2 caseXLfDispatch O O = ap2 IfLf (ap2 sndProj O O) (ap2 innerLfBranch O O)
      cxlf1 = axFan sndProj innerLfBranch IfLf O O
      snd_OO = sndProj_eval O O  -- ap2 sndProj O O = O

      -- ap2 innerLfBranch O O = ap2 Pair caseLLTerm (ap2 caseLNFun O O)
      ilf1 = axFan (Lift (KT caseLLTerm)) caseLNFun Pair O O
      ilf2 : Deriv (atomic (eqn (ap2 (Lift (KT caseLLTerm)) O O) caseLLTerm))
      ilf2 = ruleTrans (axLift (KT caseLLTerm) O O)
                       (axKT (nd (natCode tagAxIfLfLL) lf)
                             (valNd (natCode tagAxIfLfLL) lf (natCode_isValue tagAxIfLfLL) valO)
                             O)
      -- caseLLTerm = parEncAxIfLfLL O = ap2 Pair tagCode_axIfLfLL O = reify (nd (natCode tagAxIfLfLL) lf).
      ilf : Deriv (atomic (eqn (ap2 innerLfBranch O O)
                                (ap2 Pair caseLLTerm (ap2 caseLNFun O O))))
      ilf = ruleTrans ilf1 (congL Pair (ap2 caseLNFun O O) ilf2)

      -- After applying axIfLfL: ap2 IfLf O (Pair a b) = a, with a = caseLLTerm.
      cxlf : Deriv (atomic (eqn (ap2 caseXLfDispatch O O) caseLLTerm))
      cxlf =
        let s2 = congL IfLf (ap2 innerLfBranch O O) snd_OO
            s3 = congR IfLf O ilf
            s4 = axIfLfL caseLLTerm (ap2 caseLNFun O O)
        in ruleTrans cxlf1 (ruleTrans s2 (ruleTrans s3 s4))

      -- We don't need to fully evaluate caseXNdDispatch since axIfLfL only uses the FIRST
      -- component of the inner Pair.
      -- Combine: ap2 outerInner O O = Pair caseLLTerm (ap2 caseXNdDispatch O O)
      oi : Deriv (atomic (eqn (ap2 outerInner O O)
                              (ap2 Pair caseLLTerm (ap2 caseXNdDispatch O O))))
      oi = ruleTrans oi1 (congL Pair (ap2 caseXNdDispatch O O) cxlf)

      -- ap2 D_IfLf O O = ap2 IfLf (ap2 fstProj O O) (ap2 outerInner O O)
      --                = ap2 IfLf O (Pair caseLLTerm (ap2 caseXNdDispatch O O))
      --                = caseLLTerm   (axIfLfL)
      s2 = congL IfLf (ap2 outerInner O O) fst_O
      s3 = congR IfLf O oi
      s4 = axIfLfL caseLLTerm (ap2 caseXNdDispatch O O)
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- Reduction at (x = O, v = Pair a b).

D_IfLf_reduce_LN : (a b : Term) ->
  Deriv (atomic (eqn (ap2 D_IfLf O (ap2 Pair a b))
                     (parEncAxIfLfL (ap1 cor a) (ap1 cor b))))
D_IfLf_reduce_LN a b =
  let v = ap2 Pair a b

      s1 = axFan fstProj outerInner IfLf O v
      fst_O_v = fstProj_eval O v  -- ap2 fstProj O v = O

      -- caseXLfDispatch at (O, v) reduces.
      cxlf1 = axFan sndProj innerLfBranch IfLf O v
      snd_O_v = sndProj_eval O v  -- = v

      -- ap2 innerLfBranch O v = ap2 Pair caseLLTerm (ap2 caseLNFun O v)
      ilf1 = axFan (Lift (KT caseLLTerm)) caseLNFun Pair O v
      ilf2 : Deriv (atomic (eqn (ap2 (Lift (KT caseLLTerm)) O v) caseLLTerm))
      ilf2 = ruleTrans (axLift (KT caseLLTerm) O v)
                       (axKT (nd (natCode tagAxIfLfLL) lf) (valNd (natCode tagAxIfLfLL) lf (natCode_isValue tagAxIfLfLL) valO) O)
      ilf : Deriv (atomic (eqn (ap2 innerLfBranch O v)
                                (ap2 Pair caseLLTerm (ap2 caseLNFun O v))))
      ilf = ruleTrans ilf1 (congL Pair (ap2 caseLNFun O v) ilf2)

      -- ap2 caseLNFun O v = ap1 caseLNFun1 (ap2 sndProj O v) = ap1 caseLNFun1 v.
      lnf1 = axPost caseLNFun1 sndProj O v
      -- ap1 caseLNFun1 v = ap2 Pair tagCode_axIfLfL (ap2 Pair (cor (Fst v)) (cor (Snd v)))
      -- where v = Pair a b, so cor (Fst v) = cor a, cor (Snd v) = cor b.
      lnf2 = axComp2 Pair (KT tagCode_axIfLfL)
                     (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) v
      lnf3 : Deriv (atomic (eqn (ap1 (KT tagCode_axIfLfL) v) tagCode_axIfLfL))
      lnf3 = axKT (natCode tagAxIfLfL) (natCode_isValue tagAxIfLfL) v
      lnf4a = axComp2 Pair (Comp cor Fst) (Comp cor Snd) v
      -- ap1 (Comp cor Fst) v = cor (Fst v) = cor a
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
                                       (parEncAxIfLfL (ap1 cor a) (ap1 cor b))))
      lnf_inner = ruleTrans lnf2
                    (ruleTrans (congL Pair _ lnf3)
                               (congR Pair tagCode_axIfLfL lnf6))
      lnf : Deriv (atomic (eqn (ap2 caseLNFun O v) (parEncAxIfLfL (ap1 cor a) (ap1 cor b))))
      lnf = ruleTrans lnf1 (ruleTrans (cong1 caseLNFun1 snd_O_v) lnf_inner)

      -- Combine: caseXLfDispatch at (O, v) = IfLf v (Pair caseLLTerm parEncAxIfLfL_ab).
      cxlf2 = congL IfLf (ap2 innerLfBranch O v) snd_O_v
      ilf' : Deriv (atomic (eqn (ap2 innerLfBranch O v)
                                 (ap2 Pair caseLLTerm (parEncAxIfLfL (ap1 cor a) (ap1 cor b)))))
      ilf' = ruleTrans ilf (congR Pair caseLLTerm lnf)
      cxlf3 = congR IfLf v ilf'

      -- axIfLfN: ap2 IfLf (Pair a b) (Pair u w) = w.
      cxlf4 = axIfLfN a b caseLLTerm (parEncAxIfLfL (ap1 cor a) (ap1 cor b))

      cxlf : Deriv (atomic (eqn (ap2 caseXLfDispatch O v)
                                 (parEncAxIfLfL (ap1 cor a) (ap1 cor b))))
      cxlf = ruleTrans cxlf1 (ruleTrans cxlf2 (ruleTrans cxlf3 cxlf4))

      -- outerInner at (O, v).
      oi1 = axFan caseXLfDispatch caseXNdDispatch Pair O v
      oi : Deriv (atomic (eqn (ap2 outerInner O v)
                              (ap2 Pair (parEncAxIfLfL (ap1 cor a) (ap1 cor b))
                                        (ap2 caseXNdDispatch O v))))
      oi = ruleTrans oi1 (congL Pair (ap2 caseXNdDispatch O v) cxlf)

      s2 = congL IfLf (ap2 outerInner O v) fst_O_v
      s3 = congR IfLf O oi
      s4 = axIfLfL (parEncAxIfLfL (ap1 cor a) (ap1 cor b)) (ap2 caseXNdDispatch O v)
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- Reduction at (x = Pair p q, v = O).

D_IfLf_reduce_NL : (p q : Term) ->
  Deriv (atomic (eqn (ap2 D_IfLf (ap2 Pair p q) O)
                     (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))))
D_IfLf_reduce_NL p q =
  let x = ap2 Pair p q

      s1 = axFan fstProj outerInner IfLf x O
      fst_x_O = fstProj_eval x O  -- = x

      -- caseXNdDispatch at (x, O).
      cxnd1 = axFan sndProj innerNdBranch IfLf x O
      snd_x_O = sndProj_eval x O  -- = O

      -- ap2 innerNdBranch x O = Pair (ap2 caseNLFun x O) (ap2 caseNNFun x O).
      ind1 = axFan caseNLFun caseNNFun Pair x O

      -- ap2 caseNLFun x O = ap1 caseNLFun1 x.
      nlf1 = axLift caseNLFun1 x O
      -- ap1 caseNLFun1 x = parEncAxIfLfNL (cor (Fst x)) (cor (Snd x)) = parEncAxIfLfNL (cor p) (cor q).
      nlf2 = axComp2 Pair (KT tagCode_axIfLfNL)
                     (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) x
      nlf3 : Deriv (atomic (eqn (ap1 (KT tagCode_axIfLfNL) x) tagCode_axIfLfNL))
      nlf3 = axKT (natCode tagAxIfLfNL) (natCode_isValue tagAxIfLfNL) x
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
                                       (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))))
      nlf_inner = ruleTrans nlf2
                    (ruleTrans (congL Pair _ nlf3)
                               (congR Pair tagCode_axIfLfNL nlf6))
      nlf : Deriv (atomic (eqn (ap2 caseNLFun x O)
                                (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))))
      nlf = ruleTrans nlf1 nlf_inner

      ind : Deriv (atomic (eqn (ap2 innerNdBranch x O)
                                (ap2 Pair (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))
                                          (ap2 caseNNFun x O))))
      ind = ruleTrans ind1 (congL Pair (ap2 caseNNFun x O) nlf)

      cxnd2 = congL IfLf (ap2 innerNdBranch x O) snd_x_O
      cxnd3 = congR IfLf O ind

      -- axIfLfL: ap2 IfLf O (Pair u w) = u (FIRST component).
      cxnd4 = axIfLfL (parEncAxIfLfNL (ap1 cor p) (ap1 cor q)) (ap2 caseNNFun x O)

      cxnd : Deriv (atomic (eqn (ap2 caseXNdDispatch x O)
                                 (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))))
      cxnd = ruleTrans cxnd1 (ruleTrans cxnd2 (ruleTrans cxnd3 cxnd4))

      oi1 = axFan caseXLfDispatch caseXNdDispatch Pair x O
      oi : Deriv (atomic (eqn (ap2 outerInner x O)
                              (ap2 Pair (ap2 caseXLfDispatch x O)
                                        (parEncAxIfLfNL (ap1 cor p) (ap1 cor q)))))
      oi = ruleTrans oi1 (congR Pair (ap2 caseXLfDispatch x O) cxnd)

      s2 = congL IfLf (ap2 outerInner x O) fst_x_O
      s3 = congR IfLf x oi
      -- axIfLfN: ap2 IfLf (Pair p q) (Pair u w) = w.
      s4 = axIfLfN p q (ap2 caseXLfDispatch x O) (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- Reduction at (x = Pair p q, v = Pair a b).

D_IfLf_reduce_NN : (p q a b : Term) ->
  Deriv (atomic (eqn (ap2 D_IfLf (ap2 Pair p q) (ap2 Pair a b))
                     (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))))
D_IfLf_reduce_NN p q a b =
  let x = ap2 Pair p q
      v = ap2 Pair a b

      s1 = axFan fstProj outerInner IfLf x v
      fst_x_v = fstProj_eval x v  -- = x

      cxnd1 = axFan sndProj innerNdBranch IfLf x v
      snd_x_v = sndProj_eval x v  -- = v

      ind1 = axFan caseNLFun caseNNFun Pair x v

      -- ap2 caseNNFun x v = parEncAxIfLfN (cor p) (cor q) (cor a) (cor b).
      -- caseNNFun = Fan (Lift (KT tagCode_axIfLfN))
      --                 (Fan (Lift (Comp cor Fst)) (Fan (Lift (Comp cor Snd)) corPairOfV Pair) Pair)
      --                 Pair
      nnf1 = axFan (Lift (KT tagCode_axIfLfN))
                   (Fan (Lift (Comp cor Fst))
                        (Fan (Lift (Comp cor Snd)) corPairOfV Pair)
                        Pair)
                   Pair x v
      nnf2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axIfLfN)) x v) tagCode_axIfLfN))
      nnf2 = ruleTrans (axLift (KT tagCode_axIfLfN) x v)
                       (axKT (natCode tagAxIfLfN) (natCode_isValue tagAxIfLfN) x)
      -- inner Fan layer 1: ap2 (Fan (Lift (Comp cor Fst)) ... Pair) x v
      --   = Pair (cor (Fst x)) (Pair (cor (Snd x)) (Pair (cor (Fst v)) (cor (Snd v))))
      nnf3a = axFan (Lift (Comp cor Fst))
                    (Fan (Lift (Comp cor Snd)) corPairOfV Pair)
                    Pair x v
      nnf3b : Deriv (atomic (eqn (ap2 (Lift (Comp cor Fst)) x v) (ap1 cor p)))
      nnf3b = ruleTrans (axLift (Comp cor Fst) x v)
                        (ruleTrans (axComp cor Fst x) (cong1 cor (axFst p q)))
      -- second component of nnf3a: ap2 (Fan (Lift (Comp cor Snd)) corPairOfV Pair) x v
      --   = Pair (cor (Snd x)) (Pair (cor (Fst v)) (cor (Snd v)))
      nnf4a = axFan (Lift (Comp cor Snd)) corPairOfV Pair x v
      nnf4b : Deriv (atomic (eqn (ap2 (Lift (Comp cor Snd)) x v) (ap1 cor q)))
      nnf4b = ruleTrans (axLift (Comp cor Snd) x v)
                        (ruleTrans (axComp cor Snd x) (cong1 cor (axSnd p q)))
      -- corPairOfV: ap2 (Post (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) sndProj) x v
      --   = ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) (ap2 sndProj x v)
      --   = ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) v
      --   = Pair (cor (Fst v)) (cor (Snd v))   (with v = Pair a b: Pair (cor a) (cor b))
      cpv1 = axPost (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) sndProj x v
      cpv2 = axComp2 Pair (Comp cor Fst) (Comp cor Snd) v
      cpv3a = axComp cor Fst v
      cpv3b = cong1 cor (axFst a b)
      cpv3 : Deriv (atomic (eqn (ap1 (Comp cor Fst) v) (ap1 cor a)))
      cpv3 = ruleTrans cpv3a cpv3b
      cpv4a = axComp cor Snd v
      cpv4b = cong1 cor (axSnd a b)
      cpv4 : Deriv (atomic (eqn (ap1 (Comp cor Snd) v) (ap1 cor b)))
      cpv4 = ruleTrans cpv4a cpv4b
      cpv5 : Deriv (atomic (eqn (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) v)
                                 (ap2 Pair (ap1 cor a) (ap1 cor b))))
      cpv5 = ruleTrans cpv2
              (ruleTrans (congL Pair (ap1 (Comp cor Snd) v) cpv3)
                         (congR Pair (ap1 cor a) cpv4))
      cpv6 : Deriv (atomic (eqn (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) (ap2 sndProj x v))
                                 (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) v)))
      cpv6 = cong1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) snd_x_v
      cpv : Deriv (atomic (eqn (ap2 corPairOfV x v)
                                (ap2 Pair (ap1 cor a) (ap1 cor b))))
      cpv = ruleTrans cpv1 (ruleTrans cpv6 cpv5)

      -- nnf4: snd-comp = Pair (cor q) (Pair (cor a) (cor b)).
      nnf4 : Deriv (atomic (eqn (ap2 (Fan (Lift (Comp cor Snd)) corPairOfV Pair) x v)
                                 (ap2 Pair (ap1 cor q) (ap2 Pair (ap1 cor a) (ap1 cor b)))))
      nnf4 = ruleTrans nnf4a
              (ruleTrans (congL Pair (ap2 corPairOfV x v) nnf4b)
                         (congR Pair (ap1 cor q) cpv))

      nnf3 : Deriv (atomic (eqn (ap2 (Fan (Lift (Comp cor Fst))
                                          (Fan (Lift (Comp cor Snd)) corPairOfV Pair)
                                          Pair) x v)
                                 (ap2 Pair (ap1 cor p)
                                           (ap2 Pair (ap1 cor q)
                                                     (ap2 Pair (ap1 cor a) (ap1 cor b))))))
      nnf3 = ruleTrans nnf3a
              (ruleTrans (congL Pair _ nnf3b)
                         (congR Pair (ap1 cor p) nnf4))

      nnf : Deriv (atomic (eqn (ap2 caseNNFun x v)
                                (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))))
      nnf = ruleTrans nnf1
              (ruleTrans (congL Pair _ nnf2)
                         (congR Pair tagCode_axIfLfN nnf3))

      ind : Deriv (atomic (eqn (ap2 innerNdBranch x v)
                                (ap2 Pair (ap2 caseNLFun x v)
                                          (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b)))))
      ind = ruleTrans ind1 (congR Pair (ap2 caseNLFun x v) nnf)

      cxnd2 = congL IfLf (ap2 innerNdBranch x v) snd_x_v
      cxnd3 = congR IfLf v ind
      -- axIfLfN: ap2 IfLf (Pair a b) (Pair u w) = w.
      cxnd4 = axIfLfN a b (ap2 caseNLFun x v)
                          (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))

      cxnd : Deriv (atomic (eqn (ap2 caseXNdDispatch x v)
                                 (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))))
      cxnd = ruleTrans cxnd1 (ruleTrans cxnd2 (ruleTrans cxnd3 cxnd4))

      oi1 = axFan caseXLfDispatch caseXNdDispatch Pair x v
      oi : Deriv (atomic (eqn (ap2 outerInner x v)
                              (ap2 Pair (ap2 caseXLfDispatch x v)
                                        (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b)))))
      oi = ruleTrans oi1 (congR Pair (ap2 caseXLfDispatch x v) cxnd)

      s2 = congL IfLf (ap2 outerInner x v) fst_x_v
      s3 = congR IfLf x oi
      s4 = axIfLfN p q (ap2 caseXLfDispatch x v)
                       (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- Bridges: each parOutAxIfLf* form to codeFTeq2_IfLf at the corresponding shape.

-- corPairUnfold: cor (Pair x v) = Pair tagAp2 (Pair codeF2Pair (Pair (cor x) (cor v))).
private
  corPairUnfold : (a b : Term) ->
    Deriv (atomic (eqn (ap1 cor (ap2 Pair a b))
                        (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                            (ap2 Pair (ap1 cor a) (ap1 cor b))))))
  corPairUnfold a b =
    let recs = ap2 Pair (ap1 cor a) (ap1 cor b)
        orig = ap2 Pair a b
        origW = ap2 Pair O orig
    in ruleTrans (axRecNd stepCor a b) (stepCorRed origW recs)

-- Bridge at (O, O): parOutAxIfLfLL = codeFTeq2_IfLf O O.
-- parOutAxIfLfLL = reify outAxIfLfLL = reify (codeFormula (atomic (eqn (ap2 IfLf O O) O)))
--                = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair O O))) O
-- codeFTeq2_IfLf O O
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair (cor O) (cor O)))) (cor (IfLf O O))
-- Bridge: O -> cor O via ruleSym axRecLf, and O -> cor (IfLf O O) via ruleSym (cong1 cor axIfLfLL + axRecLf).

bridgeLL : Deriv (atomic (eqn parOutAxIfLfLL (codeFTeq2_IfLf O O)))
bridgeLL =
  let cor_O = axRecLf stepCor
      iflfLL_eq : Deriv (atomic (eqn (ap2 IfLf O O) O))
      iflfLL_eq = axIfLfLL
      cor_iflfLL : Deriv (atomic (eqn (ap1 cor (ap2 IfLf O O)) O))
      cor_iflfLL = ruleTrans (cong1 cor iflfLL_eq) cor_O

      -- LHS rewrite: O slots inside Pair (cor x) (cor v) = Pair O O originally.
      -- Need: Pair (reify (codeF2 IfLf)) (Pair O O)  ->  Pair (reify (codeF2 IfLf)) (Pair (cor O) (cor O))
      step1 : Deriv (atomic (eqn (ap2 Pair (reify (codeF2 IfLf)) (ap2 Pair O O))
                                  (ap2 Pair (reify (codeF2 IfLf))
                                    (ap2 Pair (ap1 cor O) (ap1 cor O)))))
      step1 = congR Pair (reify (codeF2 IfLf))
                (ruleTrans (congL Pair O (ruleSym cor_O))
                           (congR Pair (ap1 cor O) (ruleSym cor_O)))

      step2 : Deriv (atomic (eqn (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 IfLf)) (ap2 Pair O O)))
                                  (ap2 Pair (reify tagAp2)
                                    (ap2 Pair (reify (codeF2 IfLf))
                                      (ap2 Pair (ap1 cor O) (ap1 cor O))))))
      step2 = congR Pair (reify tagAp2) step1

      step3 : Deriv (atomic (eqn parOutAxIfLfLL
                                  (ap2 Pair
                                    (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 IfLf))
                                        (ap2 Pair (ap1 cor O) (ap1 cor O))))
                                    O)))
      step3 = congL Pair O step2

      -- RHS rewrite: O -> cor (IfLf O O).
      step4 : Deriv (atomic (eqn (ap2 Pair
                                    (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 IfLf))
                                        (ap2 Pair (ap1 cor O) (ap1 cor O))))
                                    O)
                                  (codeFTeq2_IfLf O O)))
      step4 = congR Pair _ (ruleSym cor_iflfLL)
  in ruleTrans step3 step4

-- Bridge at (O, Pair a b): parOutAxIfLfL (cor a) (cor b) -> codeFTeq2_IfLf O (Pair a b).
-- parOutAxIfLfL aT bT
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair O (Pair tagAp2 (Pair codeF2Pair (Pair aT bT)))))) aT
-- codeFTeq2_IfLf O (Pair a b)
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair (cor O) (cor (Pair a b))))) (cor (IfLf O (Pair a b)))
-- Bridge:
--   O -> cor O.
--   Pair tagAp2 (Pair codeF2Pair (Pair (cor a) (cor b))) -> cor (Pair a b)  (corPairUnfold reversed).
--   cor a -> cor (IfLf O (Pair a b))   (cong1 cor (ruleSym axIfLfL)).

bridgeLN : (a b : Term) ->
  Deriv (atomic (eqn (parOutAxIfLfL (ap1 cor a) (ap1 cor b)) (codeFTeq2_IfLf O (ap2 Pair a b))))
bridgeLN a b =
  let cor_O = axRecLf stepCor
      cpu = corPairUnfold a b
      iflfL_eq = axIfLfL a b
      cor_iflfL : Deriv (atomic (eqn (ap1 cor (ap2 IfLf O (ap2 Pair a b))) (ap1 cor a)))
      cor_iflfL = cong1 cor iflfL_eq

      -- LHS rewrites.
      step1a : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair (ap1 cor a) (ap1 cor b))))
                          (ap1 cor (ap2 Pair a b))))
      step1a = ruleSym cpu

      -- Slot (cor O) is currently O; rewrite to cor O.
      -- Pair O ((Pair tagAp2 (Pair codeF2Pair (Pair (cor a) (cor b))))
      step1b : Deriv (atomic (eqn
                          (ap2 Pair O (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 Pair))
                                                  (ap2 Pair (ap1 cor a) (ap1 cor b)))))
                          (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))
      step1b = ruleTrans (congL Pair _ (ruleSym cor_O))
                         (congR Pair (ap1 cor O) step1a)

      -- Wrap with codeF2IfLf header.
      step1c : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair O
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair (ap1 cor a) (ap1 cor b))))))
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b))))))
      step1c = congR Pair (reify (codeF2 IfLf)) step1b

      step1d : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 IfLf))
                              (ap2 Pair O
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                            (ap2 Pair (ap1 cor a) (ap1 cor b)))))))
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 IfLf))
                              (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))))
      step1d = congR Pair (reify tagAp2) step1c

      step1 : Deriv (atomic (eqn (parOutAxIfLfL (ap1 cor a) (ap1 cor b))
                                  (ap2 Pair
                                    (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 IfLf))
                                        (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))
                                    (ap1 cor a))))
      step1 = congL Pair (ap1 cor a) step1d

      -- RHS rewrite.
      step2 : Deriv (atomic (eqn
                          (ap2 Pair
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 IfLf))
                                (ap2 Pair (ap1 cor O) (ap1 cor (ap2 Pair a b)))))
                            (ap1 cor a))
                          (codeFTeq2_IfLf O (ap2 Pair a b))))
      step2 = congR Pair _ (ruleSym cor_iflfL)
  in ruleTrans step1 step2

-- Bridge at (Pair p q, O): parOutAxIfLfNL (cor p) (cor q) -> codeFTeq2_IfLf (Pair p q) O.
-- parOutAxIfLfNL pT qT
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair (Pair tagAp2 (Pair codeF2Pair (Pair pT qT))) O))) O
-- codeFTeq2_IfLf (Pair p q) O
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair (cor (Pair p q)) (cor O)))) (cor (IfLf (Pair p q) O))
-- Bridge:
--   Inner LHS slot: Pair tagAp2 (Pair codeF2Pair (Pair pT qT)) -> cor (Pair p q) via corPairUnfold reversed.
--   Slot O on right -> cor O.
--   RHS O -> cor (IfLf (Pair p q) O) via ruleSym (cong1 cor axIfLfNL + axRecLf).

bridgeNL : (p q : Term) ->
  Deriv (atomic (eqn (parOutAxIfLfNL (ap1 cor p) (ap1 cor q)) (codeFTeq2_IfLf (ap2 Pair p q) O)))
bridgeNL p q =
  let cor_O = axRecLf stepCor
      cpu = corPairUnfold p q
      iflfNL_eq : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair p q) O) O))
      iflfNL_eq = axIfLfNL p q
      cor_iflfNL : Deriv (atomic (eqn (ap1 cor (ap2 IfLf (ap2 Pair p q) O)) O))
      cor_iflfNL = ruleTrans (cong1 cor iflfNL_eq) cor_O

      step1a : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair (ap1 cor p) (ap1 cor q))))
                          (ap1 cor (ap2 Pair p q))))
      step1a = ruleSym cpu

      step1b : Deriv (atomic (eqn
                          (ap2 Pair (ap2 Pair (reify tagAp2)
                                       (ap2 Pair (reify (codeF2 Pair))
                                                 (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                    O)
                          (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O))))
      step1b = ruleTrans (congL Pair O step1a)
                         (congR Pair (ap1 cor (ap2 Pair p q)) (ruleSym cor_O))

      step1c : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap2 Pair (reify tagAp2)
                                         (ap2 Pair (reify (codeF2 Pair))
                                                   (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                      O))
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O)))))
      step1c = congR Pair (reify (codeF2 IfLf)) step1b

      step1d : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 IfLf))
                              (ap2 Pair (ap2 Pair (reify tagAp2)
                                          (ap2 Pair (reify (codeF2 Pair))
                                                    (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                        O)))
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 IfLf))
                              (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O))))))
      step1d = congR Pair (reify tagAp2) step1c

      step1 = congL Pair O step1d

      step2 : Deriv (atomic (eqn
                          (ap2 Pair
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 IfLf))
                                (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor O))))
                            O)
                          (codeFTeq2_IfLf (ap2 Pair p q) O)))
      step2 = congR Pair _ (ruleSym cor_iflfNL)
  in ruleTrans step1 step2

-- Bridge at (Pair p q, Pair a b): parOutAxIfLfN (cor p) (cor q) (cor a) (cor b) ->
--                                  codeFTeq2_IfLf (Pair p q) (Pair a b).
-- parOutAxIfLfN pT qT aT bT
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair (Pair tagAp2 (Pair codeF2Pair (Pair pT qT)))
--                                              (Pair tagAp2 (Pair codeF2Pair (Pair aT bT)))))) bT
-- codeFTeq2_IfLf (Pair p q) (Pair a b)
--   = Pair (Pair tagAp2 (Pair codeF2IfLf (Pair (cor (Pair p q)) (cor (Pair a b))))) (cor (IfLf (Pair p q) (Pair a b)))
-- Bridge: corPairUnfold reversed twice + cor (IfLf...) = cor b via cong1 cor (axIfLfN).

bridgeNN : (p q a b : Term) ->
  Deriv (atomic (eqn (parOutAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))
                     (codeFTeq2_IfLf (ap2 Pair p q) (ap2 Pair a b))))
bridgeNN p q a b =
  let cpu_pq = corPairUnfold p q
      cpu_ab = corPairUnfold a b

      iflfN_eq : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair p q) (ap2 Pair a b)) b))
      iflfN_eq = axIfLfN p q a b
      cor_iflfN : Deriv (atomic (eqn (ap1 cor (ap2 IfLf (ap2 Pair p q) (ap2 Pair a b))) (ap1 cor b)))
      cor_iflfN = cong1 cor iflfN_eq

      step1a : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair (ap1 cor p) (ap1 cor q))))
                          (ap1 cor (ap2 Pair p q))))
      step1a = ruleSym cpu_pq

      step1b : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair (ap1 cor a) (ap1 cor b))))
                          (ap1 cor (ap2 Pair a b))))
      step1b = ruleSym cpu_ab

      step1 : Deriv (atomic (eqn
                          (ap2 Pair
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                        (ap2 Pair (ap1 cor p) (ap1 cor q))))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                        (ap2 Pair (ap1 cor a) (ap1 cor b)))))
                          (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor (ap2 Pair a b)))))
      step1 = ruleTrans (congL Pair _ step1a) (congR Pair (ap1 cor (ap2 Pair p q)) step1b)

      step2 : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair (ap1 cor p) (ap1 cor q))))
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair (ap1 cor a) (ap1 cor b))))))
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor (ap2 Pair a b))))))
      step2 = congR Pair (reify (codeF2 IfLf)) step1

      step3 : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 IfLf))
                              (ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                            (ap2 Pair (ap1 cor p) (ap1 cor q))))
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                            (ap2 Pair (ap1 cor a) (ap1 cor b)))))))
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 IfLf))
                              (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor (ap2 Pair a b)))))))
      step3 = congR Pair (reify tagAp2) step2

      step4 = congL Pair (ap1 cor b) step3

      step5 : Deriv (atomic (eqn
                          (ap2 Pair
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 IfLf))
                                (ap2 Pair (ap1 cor (ap2 Pair p q)) (ap1 cor (ap2 Pair a b)))))
                            (ap1 cor b))
                          (codeFTeq2_IfLf (ap2 Pair p q) (ap2 Pair a b))))
      step5 = congR Pair _ (ruleSym cor_iflfN)
  in ruleTrans step4 step5

------------------------------------------------------------------------
-- Pointwise correctness at the four leaf-Pair shapes.

D_correct2_IfLf_LL : Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf O O)) (codeFTeq2_IfLf O O)))
D_correct2_IfLf_LL =
  let r_thmT = cong1 thmT D_IfLf_reduce_OO
      r_disp = parDispAxIfLfLL O
  in ruleTrans r_thmT (ruleTrans r_disp bridgeLL)

D_correct2_IfLf_LN : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf O (ap2 Pair a b))) (codeFTeq2_IfLf O (ap2 Pair a b))))
D_correct2_IfLf_LN a b =
  let r_thmT = cong1 thmT (D_IfLf_reduce_LN a b)
      r_disp = parDispAxIfLfL (ap1 cor a) (ap1 cor b)
      r_bridge = bridgeLN a b
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

D_correct2_IfLf_NL : (p q : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf (ap2 Pair p q) O)) (codeFTeq2_IfLf (ap2 Pair p q) O)))
D_correct2_IfLf_NL p q =
  let r_thmT = cong1 thmT (D_IfLf_reduce_NL p q)
      r_disp = parDispAxIfLfNL (ap1 cor p) (ap1 cor q)
      r_bridge = bridgeNL p q
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

D_correct2_IfLf_NN : (p q a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf (ap2 Pair p q) (ap2 Pair a b)))
                     (codeFTeq2_IfLf (ap2 Pair p q) (ap2 Pair a b))))
D_correct2_IfLf_NN p q a b =
  let r_thmT = cong1 thmT (D_IfLf_reduce_NN p q a b)
      r_disp = parDispAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b)
      r_bridge = bridgeNN p q a b
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

------------------------------------------------------------------------
-- Universal proof via nested ruleIndBT.
--
-- Outer induction on x (var 0); inner induction on v (var 0 of inner formula).
-- Variable assignments:
--   var 0 = x (outer inducting variable)
--   var 1 = v (free during outer, gets inducted on via inner)
--   var 2, var 3 = outer fresh vars for x's children
--   var 4, var 5 = inner fresh vars for v's children

private
  v1OuterNat : Nat
  v1OuterNat = suc (suc zero)            -- var 2
  v2OuterNat : Nat
  v2OuterNat = suc (suc (suc zero))      -- var 3
  v1InnerNat : Nat
  v1InnerNat = suc (suc (suc (suc zero)))           -- var 4
  v2InnerNat : Nat
  v2InnerNat = suc (suc (suc (suc (suc zero))))     -- var 5

  vOuterNat : Nat
  vOuterNat = suc zero                   -- var 1 (= v in outer)

  -- ----- Outer base: x = O. Inner ruleIndBT on v. -----

  Q_baseO : Formula
  Q_baseO = atomic (eqn (ap1 thmT (ap2 D_IfLf O (var zero)))
                        (codeFTeq2_IfLf O (var zero)))

  -- substF zero O Q_baseO => the formula at v = O.
  inner_base_O_proof : Deriv (substF zero O Q_baseO)
  inner_base_O_proof =
    eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap2 D_IfLf O O)) (codeFTeq2_IfLf O O))))
            (eqSym (thClosed zero O))
            D_correct2_IfLf_LL

  inner_step_O_concl : Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
  inner_step_O_concl =
    eqSubst (\ fT -> Deriv (atomic (eqn
                              (ap1 fT (ap2 D_IfLf O (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                              (codeFTeq2_IfLf O (ap2 Pair (var v1InnerNat) (var v2InnerNat))))))
            (eqSym (thClosed zero (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
            (D_correct2_IfLf_LN (var v1InnerNat) (var v2InnerNat))

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

  -- ruleInst zero (var 1): produces Deriv at v_OUTER = var 1.
  outer_base_proof_unsubst : Deriv (substF zero (var vOuterNat) Q_baseO)
  outer_base_proof_unsubst = ruleInst zero (var vOuterNat) univ_x_O

  -- Convert to substF zero O P_outer via eqSubst on thmT.
  P_outer : Formula
  P_outer = atomic (eqn (ap1 thmT (ap2 D_IfLf (var zero) (var vOuterNat)))
                        (codeFTeq2_IfLf (var zero) (var vOuterNat)))

  outer_base_proof : Deriv (substF zero O P_outer)
  outer_base_proof =
    eqSubst (\ fT -> Deriv (atomic (eqn
                              (ap1 fT (ap2 D_IfLf O (var vOuterNat)))
                              (codeFTeq2_IfLf O (var vOuterNat)))))
            (eqSym (thClosed zero O))
            (eqSubst (\ fT -> Deriv (atomic (eqn
                                       (ap1 fT (ap2 D_IfLf O (var vOuterNat)))
                                       (codeFTeq2_IfLf O (var vOuterNat)))))
                     (thClosed zero (var vOuterNat))
                     outer_base_proof_unsubst)

  -- ----- Outer step: x = Pair (var 2) (var 3). Inner ruleIndBT on v. -----

  pairOuter : Term
  pairOuter = ap2 Pair (var v1OuterNat) (var v2OuterNat)

  Q_stepP : Formula
  Q_stepP = atomic (eqn (ap1 thmT (ap2 D_IfLf pairOuter (var zero)))
                        (codeFTeq2_IfLf pairOuter (var zero)))

  inner_base_P_proof : Deriv (substF zero O Q_stepP)
  inner_base_P_proof =
    eqSubst (\ fT -> Deriv (atomic (eqn
                              (ap1 fT (ap2 D_IfLf pairOuter O))
                              (codeFTeq2_IfLf pairOuter O))))
            (eqSym (thClosed zero O))
            (D_correct2_IfLf_NL (var v1OuterNat) (var v2OuterNat))

  inner_step_P_concl : Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
  inner_step_P_concl =
    eqSubst (\ fT -> Deriv (atomic (eqn
                              (ap1 fT (ap2 D_IfLf pairOuter (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
                              (codeFTeq2_IfLf pairOuter (ap2 Pair (var v1InnerNat) (var v2InnerNat))))))
            (eqSym (thClosed zero (ap2 Pair (var v1InnerNat) (var v2InnerNat))))
            (D_correct2_IfLf_NN (var v1OuterNat) (var v2OuterNat) (var v1InnerNat) (var v2InnerNat))

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
    eqSubst (\ fT -> Deriv (atomic (eqn
                              (ap1 fT (ap2 D_IfLf pairOuter (var vOuterNat)))
                              (codeFTeq2_IfLf pairOuter (var vOuterNat)))))
            (eqSym (thClosed zero pairOuter))
            (eqSubst (\ fT -> Deriv (atomic (eqn
                                       (ap1 fT (ap2 D_IfLf pairOuter (var vOuterNat)))
                                       (codeFTeq2_IfLf pairOuter (var vOuterNat)))))
                     (thClosed zero (var vOuterNat))
                     outer_step_concl_unsubst)

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

D_correct2_IfLf_univ : Deriv P_outer
D_correct2_IfLf_univ = ruleIndBT P_outer v1OuterNat v2OuterNat outer_base_proof outer_step_imp

-- Universal Theorem 12 case for IfLf at arbitrary x, v -- no closure
-- argument.  Strategy (BRA/NEXT-SESSION-THM12-IFLF.md):
--
-- Pick k = pickFresh v (k >= 2 and k not in v).  Three ruleInst's:
--   (1) ruleInst zero (var k)   -- rename var 0 (= x slot) to fresh var k
--   (2) ruleInst (suc zero) v   -- substitute v in the v slot
--   (3) ruleInst k x            -- substitute x in the var-k slot
--
-- Step (3)'s recursion through v is harmless because v has no var k
-- (subst_pickFresh).  This avoids the original two-step ruleInst
-- artifact where the second substitution disturbed x.

D_correct2_IfLf : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf x v)) (codeFTeq2_IfLf x v)))
D_correct2_IfLf x v =
  let k : Nat
      k = pickFresh v

      -- Step 1: rename var 0 (= x slot) to var k.
      stage1 : Deriv (substF zero (var k) P_outer)
      stage1 = ruleInst zero (var k) D_correct2_IfLf_univ

      -- Clean substF1 zero (var k) thmT  ->  thmT  via thClosed.
      stage1_clean :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_IfLf (var k) (var (suc zero))))
          (codeFTeq2_IfLf (var k) (var (suc zero)))))
      stage1_clean =
        eqSubst (\ tT -> Deriv (atomic (eqn
                  (ap1 tT (ap2 D_IfLf (var k) (var (suc zero))))
                  (codeFTeq2_IfLf (var k) (var (suc zero))))))
                (thClosed zero (var k))
                stage1

      -- Step 2: substitute v in the v slot.
      stage2 :
        Deriv (substF (suc zero) v (atomic (eqn
          (ap1 thmT (ap2 D_IfLf (var k) (var (suc zero))))
          (codeFTeq2_IfLf (var k) (var (suc zero))))))
      stage2 = ruleInst (suc zero) v stage1_clean

      -- subst (suc zero) v (var k) = var k  because k >= 2, so k != 1.
      eq_kSlot1 : Eq (subst (suc zero) v (var k)) (var k)
      eq_kSlot1 =
        eqCong (\ b -> boolCase b v (var k)) (pickFresh_natEq_one' v)

      -- Clean substF1 (suc zero) v thmT  ->  thmT.
      stage2_thmT :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_IfLf (subst (suc zero) v (var k)) v))
          (codeFTeq2_IfLf (subst (suc zero) v (var k)) v)))
      stage2_thmT =
        eqSubst (\ tT -> Deriv (atomic (eqn
                  (ap1 tT (ap2 D_IfLf (subst (suc zero) v (var k)) v))
                  (codeFTeq2_IfLf (subst (suc zero) v (var k)) v))))
                (thClosed (suc zero) v)
                stage2

      -- Replace (subst (suc zero) v (var k)) by (var k) in the formula.
      stage2_clean :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_IfLf (var k) v))
          (codeFTeq2_IfLf (var k) v)))
      stage2_clean =
        eqSubst (\ Y -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 D_IfLf Y v))
                  (codeFTeq2_IfLf Y v))))
                eq_kSlot1
                stage2_thmT

      -- Step 3: substitute x in the var-k slot.
      stage3 :
        Deriv (substF k x (atomic (eqn
          (ap1 thmT (ap2 D_IfLf (var k) v))
          (codeFTeq2_IfLf (var k) v))))
      stage3 = ruleInst k x stage2_clean

      -- subst k x (var k) = x  because natEq k k = true.
      eq_kk_x : Eq (subst k x (var k)) x
      eq_kk_x =
        eqCong (\ b -> boolCase b x (var k)) (natEq_refl k)

      -- subst k x v = v  because k = pickFresh v is fresh in v.
      eq_kv_v : Eq (subst k x v) v
      eq_kv_v = subst_pickFresh x v

      -- Clean substF1 k x thmT  ->  thmT.
      stage3_thmT :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_IfLf (subst k x (var k)) (subst k x v)))
          (codeFTeq2_IfLf (subst k x (var k)) (subst k x v))))
      stage3_thmT =
        eqSubst (\ tT -> Deriv (atomic (eqn
                  (ap1 tT (ap2 D_IfLf (subst k x (var k)) (subst k x v)))
                  (codeFTeq2_IfLf (subst k x (var k)) (subst k x v)))))
                (thClosed k x)
                stage3

      -- Replace (subst k x (var k)) by x.
      stage3_x :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_IfLf x (subst k x v)))
          (codeFTeq2_IfLf x (subst k x v))))
      stage3_x =
        eqSubst (\ Y -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 D_IfLf Y (subst k x v)))
                  (codeFTeq2_IfLf Y (subst k x v)))))
                eq_kk_x
                stage3_thmT

      -- Replace (subst k x v) by v.
      stage3_xv :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_IfLf x v))
          (codeFTeq2_IfLf x v)))
      stage3_xv =
        eqSubst (\ V -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 D_IfLf x V))
                  (codeFTeq2_IfLf x V))))
                eq_kv_v
                stage3_x
  in stage3_xv
