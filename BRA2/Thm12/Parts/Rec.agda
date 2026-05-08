{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.Rec   (Theorem 12 case for f = Rec z s).
--
-- Rec z s : Fun1 with axRecLf and axRecNd:
--   axRecLf : (Rec z s) O = z
--   axRecNd : (Rec z s) (Pair a b) = s (Pair a b) (Pair (Rec z s a) (Rec z s b))
--
-- The Pair case requires cross-IH on Rec at (a) and (b) plus IH-on-s
-- (a Fun2) to bridge the encoded equation to  cor (Rec z s (Pair a b)) .
-- We parameterise the inner module  Construction  over an externally
-- provided D_Rec_NN_fun : Fun1 and its pointwise correctness, leaving
-- the Pair-case proof to Phase 7 glue.
--
-- O case is concrete (uses parEncAxRecLf bridge).
--
-- D_Rec_zs : Fun1 dispatches on x via IfLf, mirroring Parts/Fst.agda:
--   ap1 D_Rec_zs O           = parEncAxRecLf zT sT
--   ap1 D_Rec_zs (Pair v1 v2) = ap1 D_Rec_NN_fun (Pair v1 v2)
--
-- IMPORTANT (closure issue):  Because z and s are opaque module
-- parameters, Agda cannot reduce  substF1 x r (KT (reify (code z))) ,
-- so the natural ruleIndBT-based universal proof requires explicit
-- closure parameters threading through every reify-of-code occurrence.
-- We therefore expose  D_correct_Rec_zs_O  and  D_correct_Rec_zs_Nd
-- as pointwise proofs and leave the universal closure / ruleIndBT
-- packaging to Phase 7 glue (where z, s are concrete and closure
-- holds definitionally).

module BRA2.Thm12.Parts.Rec where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxRecLf)
open import BRA2.Thm.ThmT using (thmT ; tagCode_axRecLf ; thClosed)
open import BRA2.Thm12.Param.AxRecLf
  using (parEncAxRecLf ; parOutAxRecLf ; parDispAxRecLf)

------------------------------------------------------------------------
-- The codeFTeq1 spec for Rec z s.

codeFTeq1_Rec_zs : (z : Term) (s : Fun2) -> Term -> Term
codeFTeq1_Rec_zs z s x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 (Rec z s))) (ap1 cor x)))
    (ap1 cor (ap1 (Rec z s) x))

------------------------------------------------------------------------
-- Construction module: parametric over the Pair case Fun1.
-- z is taken as a Term whose cor-image equals reify (code z)
-- (z_corLemma); typically z = O (then z_corLemma = axRecLf stepCor).

module Construction
  (z : Term)
  (s : Fun2)
  (z_corLemma : Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))
  (D_Rec_NN_fun : Fun1)
  (D_correct_Rec_NN_pt : (a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_NN_fun (ap2 Pair a b)))
                       (codeFTeq1_Rec_zs z s (ap2 Pair a b)))))
  where

  ----------------------------------------------------------------------
  -- Building blocks for D_Rec_zs.

  private
    zT : Term
    zT = reify (code z)

    sT : Term
    sT = reify (codeF2 s)

    nonleafFun : Fun1
    nonleafFun = D_Rec_NN_fun

    dispatchFun : Fun1
    dispatchFun = Comp2 Pair (KT (parEncAxRecLf zT sT)) nonleafFun

  D_Rec_zs : Fun1
  D_Rec_zs = Comp2 IfLf I dispatchFun

  ----------------------------------------------------------------------
  -- Combinator reduction at x = O.

  D_Rec_zs_reduce_O : Deriv (atomic (eqn (ap1 D_Rec_zs O) (parEncAxRecLf zT sT)))
  D_Rec_zs_reduce_O =
    let s1 : Deriv (atomic (eqn (ap1 D_Rec_zs O)
                                (ap2 IfLf (ap1 I O) (ap1 dispatchFun O))))
        s1 = axComp2 IfLf I dispatchFun O

        s2 : Deriv (atomic (eqn (ap1 I O) O))
        s2 = axI O

        s3 : Deriv (atomic (eqn (ap2 IfLf (ap1 I O) (ap1 dispatchFun O))
                                (ap2 IfLf O (ap1 dispatchFun O))))
        s3 = congL IfLf (ap1 dispatchFun O) s2

        d1 : Deriv (atomic (eqn (ap1 dispatchFun O)
                                (ap2 Pair (ap1 (KT (parEncAxRecLf zT sT)) O)
                                          (ap1 nonleafFun O))))
        d1 = axComp2 Pair (KT (parEncAxRecLf zT sT)) nonleafFun O

        d2 : Deriv (atomic (eqn (ap1 (KT (parEncAxRecLf zT sT)) O) (parEncAxRecLf zT sT)))
        d2 = axKT (nd (natCode tagAxRecLf) (nd (code z) (codeF2 s))) O

        d_final : Deriv (atomic (eqn (ap1 dispatchFun O)
                                     (ap2 Pair (parEncAxRecLf zT sT)
                                               (ap1 nonleafFun O))))
        d_final = ruleTrans d1 (congL Pair (ap1 nonleafFun O) d2)

        s4 : Deriv (atomic (eqn (ap2 IfLf O (ap1 dispatchFun O))
                                (ap2 IfLf O (ap2 Pair (parEncAxRecLf zT sT)
                                                       (ap1 nonleafFun O)))))
        s4 = congR IfLf O d_final

        s5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (parEncAxRecLf zT sT)
                                                       (ap1 nonleafFun O)))
                                (parEncAxRecLf zT sT)))
        s5 = axIfLfL (parEncAxRecLf zT sT) (ap1 nonleafFun O)
    in ruleTrans s1 (ruleTrans s3 (ruleTrans s4 s5))

  ----------------------------------------------------------------------
  -- Combinator reduction at x = Pair a b.

  D_Rec_zs_reduce_Nd : (a b : Term) ->
    Deriv (atomic (eqn (ap1 D_Rec_zs (ap2 Pair a b))
                       (ap1 D_Rec_NN_fun (ap2 Pair a b))))
  D_Rec_zs_reduce_Nd a b =
    let x = ap2 Pair a b
        s1 = axComp2 IfLf I dispatchFun x
        s2 : Deriv (atomic (eqn (ap1 I x) x))
        s2 = axI x

        s3 : Deriv (atomic (eqn (ap2 IfLf (ap1 I x) (ap1 dispatchFun x))
                                (ap2 IfLf x (ap1 dispatchFun x))))
        s3 = congL IfLf (ap1 dispatchFun x) s2

        d1 : Deriv (atomic (eqn (ap1 dispatchFun x)
                                (ap2 Pair (ap1 (KT (parEncAxRecLf zT sT)) x)
                                          (ap1 nonleafFun x))))
        d1 = axComp2 Pair (KT (parEncAxRecLf zT sT)) nonleafFun x

        d2 : Deriv (atomic (eqn (ap1 (KT (parEncAxRecLf zT sT)) x) (parEncAxRecLf zT sT)))
        d2 = axKT (nd (natCode tagAxRecLf) (nd (code z) (codeF2 s))) x

        d_final : Deriv (atomic (eqn (ap1 dispatchFun x)
                                     (ap2 Pair (parEncAxRecLf zT sT)
                                               (ap1 nonleafFun x))))
        d_final = ruleTrans d1 (congL Pair (ap1 nonleafFun x) d2)

        s4 : Deriv (atomic (eqn (ap2 IfLf x (ap1 dispatchFun x))
                                (ap2 IfLf x (ap2 Pair (parEncAxRecLf zT sT)
                                                       (ap1 nonleafFun x)))))
        s4 = congR IfLf x d_final

        s5 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair a b)
                                          (ap2 Pair (parEncAxRecLf zT sT)
                                                    (ap1 nonleafFun x)))
                                (ap1 nonleafFun x)))
        s5 = axIfLfN a b (parEncAxRecLf zT sT) (ap1 nonleafFun x)
    in ruleTrans s1 (ruleTrans s3 (ruleTrans s4 s5))

  ----------------------------------------------------------------------
  -- Bridge at O: parOutAxRecLf zT sT -> codeFTeq1_Rec_zs z s O.

  bridgeO : Deriv (atomic (eqn (parOutAxRecLf zT sT) (codeFTeq1_Rec_zs z s O)))
  bridgeO =
    let cor_O : Deriv (atomic (eqn (ap1 cor O) O))
        cor_O = axRecLf stepCor
        recLf_eq : Deriv (atomic (eqn (ap1 (Rec z s) O) z))
        recLf_eq = axRecLf z s
        cor_recLf_zT : Deriv (atomic (eqn (ap1 cor (ap1 (Rec z s) O)) zT))
        cor_recLf_zT = ruleTrans (cong1 cor recLf_eq) z_corLemma

        step1 : Deriv (atomic (eqn (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                       (ap2 Pair zT sT))
                                              O)
                                    (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                         (ap2 Pair zT sT))
                                              (ap1 cor O))))
        step1 = congR Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                      (ap2 Pair zT sT))
                          (ruleSym cor_O)

        step2 : Deriv (atomic (eqn (ap2 Pair (reify tagAp1)
                                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                          (ap2 Pair zT sT))
                                                O))
                                    (ap2 Pair (reify tagAp1)
                                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                          (ap2 Pair zT sT))
                                                (ap1 cor O)))))
        step2 = congR Pair (reify tagAp1) step1

        step3 : Deriv (atomic (eqn (parOutAxRecLf zT sT)
                                    (ap2 Pair
                                      (ap2 Pair (reify tagAp1)
                                        (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                            (ap2 Pair zT sT))
                                                  (ap1 cor O)))
                                      zT)))
        step3 = congL Pair zT step2

        step4 : Deriv (atomic (eqn (ap2 Pair
                                      (ap2 Pair (reify tagAp1)
                                        (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                            (ap2 Pair zT sT))
                                                  (ap1 cor O)))
                                      zT)
                                    (codeFTeq1_Rec_zs z s O)))
        step4 = congR Pair _ (ruleSym cor_recLf_zT)

    in ruleTrans step3 step4

  ----------------------------------------------------------------------
  -- Pointwise correctness at the two shape cases.

  D_correct_Rec_zs_O : Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs O)) (codeFTeq1_Rec_zs z s O)))
  D_correct_Rec_zs_O =
    let r_thmT = cong1 thmT D_Rec_zs_reduce_O
        r_disp = parDispAxRecLf zT sT
    in ruleTrans r_thmT (ruleTrans r_disp bridgeO)

  D_correct_Rec_zs_Nd : (a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs (ap2 Pair a b)))
                       (codeFTeq1_Rec_zs z s (ap2 Pair a b))))
  D_correct_Rec_zs_Nd a b =
    let r_thmT = cong1 thmT (D_Rec_zs_reduce_Nd a b)
    in ruleTrans r_thmT (D_correct_Rec_NN_pt a b)

  ----------------------------------------------------------------------
  -- Note: a universal proof via ruleIndBT is omitted because the
  -- closure obligation  Eq (substF1 x r D_Rec_zs) D_Rec_zs  cascades
  -- through  reify (code z) ,  reify (codeF2 s) , and  parEncAxRecLf
  -- payloads in ways Agda cannot resolve while  z , s  are opaque
  -- module parameters.  Phase 7 glue, where z and s are concrete,
  -- can derive the universal proof via ruleIndBT using the two
  -- pointwise lemmas above.
