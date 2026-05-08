{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.RecP   (Theorem 12 case for g = RecP s, binary).
--
-- RecP s : Fun2 with axRecPLf and axRecPNd:
--   axRecPLf s p           : ap2 (RecP s) p O = O
--   axRecPNd s p a b       : ap2 (RecP s) p (Pair a b)
--                              = ap2 s (Pair p (Pair a b))
--                                      (Pair (ap2 (RecP s) p a)
--                                            (ap2 (RecP s) p b))
--
-- The Pair case requires cross-IH on RecP at (a) and (b) plus IH-on-s
-- (a Fun2) to bridge the encoded equation to  cor (ap2 (RecP s) p (Pair a b)).
-- We parameterise the inner module  Construction  over an externally
-- provided D2_RecP_NN_fun : Fun2 and its pointwise correctness, leaving
-- the Pair-case proof to Phase 7 glue.
--
-- O case is concrete (uses parEncAxRecPLf bridge).
--
-- D2_RecP_s : Fun2 dispatches on the second argument via IfLf, mirroring
-- Parts/Rec.agda but binary-style:
--   ap2 D2_RecP_s p O           = parEncAxRecPLf sT (ap1 cor p)
--   ap2 D2_RecP_s p (Pair v1 v2) = ap2 D2_RecP_NN_fun p (Pair v1 v2)
--
-- IMPORTANT: We bake  ap1 cor p  into  D2_RecP_s  (not  reify (code p) ),
-- because  p  is a runtime argument here (not a module parameter), so we
-- have no  p_corLemma  available.  Using  cor p  directly matches the
-- spec  codeFTeq2_RecP_s  and avoids extra bridges.
--
-- Universal proof via ruleIndBT is omitted at the parametric layer for
-- the same closure-cascade reason as Parts/Rec.agda.

module BRA2.Thm12.Parts.RecP where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxRecPLf)
open import BRA2.Thm.ThmT using (thmT ; tagCode_axRecPLf)
open import BRA2.Thm12.Param.AxRecPLf
  using (parEncAxRecPLf ; parOutAxRecPLf ; parDispAxRecPLf)

------------------------------------------------------------------------
-- The codeFTeq2 spec for RecP s.

codeFTeq2_RecP_s : (s : Fun2) -> Term -> Term -> Term
codeFTeq2_RecP_s s p x =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 (RecP s)))
                        (ap2 Pair (ap1 cor p) (ap1 cor x))))
    (ap1 cor (ap2 (RecP s) p x))

------------------------------------------------------------------------
-- Construction module: parametric over the Pair case Fun2.

module Construction
  (s : Fun2)
  (D2_RecP_NN_fun : Fun2)
  (D_correct2_RecP_NN_pt : (p a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_RecP_NN_fun p (ap2 Pair a b)))
                       (codeFTeq2_RecP_s s p (ap2 Pair a b)))))
  where

  ----------------------------------------------------------------------
  -- Building blocks for D2_RecP_s.

  private
    sT : Term
    sT = reify (codeF2 s)

    -- ap2 lfPayload p x = ap2 Pair sT (ap1 cor p)
    lfPayload : Fun2
    lfPayload = Fan (Lift (KT sT)) (Lift cor) Pair

    -- ap2 lfPart p x = ap2 Pair tagCode_axRecPLf (ap2 Pair sT (ap1 cor p))
    --                = parEncAxRecPLf sT (ap1 cor p)
    lfPart : Fun2
    lfPart = Fan (Lift (KT tagCode_axRecPLf)) lfPayload Pair

    -- ap2 dispatchFun p x = ap2 Pair (ap2 lfPart p x) (ap2 D2_RecP_NN_fun p x)
    dispatchFun : Fun2
    dispatchFun = Fan lfPart D2_RecP_NN_fun Pair

  D2_RecP_s : Fun2
  D2_RecP_s = Fan (Post Snd Pair) dispatchFun IfLf

  ----------------------------------------------------------------------
  -- Helper reductions.

  private
    -- ap2 (Post Snd Pair) p x = x
    postSndPair_eval : (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Post Snd Pair) p x) x))
    postSndPair_eval p x =
      let e1 : Deriv (atomic (eqn (ap2 (Post Snd Pair) p x)
                                   (ap1 Snd (ap2 Pair p x))))
          e1 = axPost Snd Pair p x
          e2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair p x)) x))
          e2 = axSnd p x
      in ruleTrans e1 e2

    -- ap2 (Lift (KT (reify v))) p x = reify v
    liftKTtree_eval : (v : Tree) (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Lift (KT (reify v))) p x) (reify v)))
    liftKTtree_eval v p x =
      ruleTrans (axLift (KT (reify v)) p x) (axKT v p)

    -- helper: lift cor through (Lift cor)
    liftCor_eval : (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Lift cor) p x) (ap1 cor p)))
    liftCor_eval p x = axLift cor p x

  ----------------------------------------------------------------------
  -- Reduction at x = O:
  --   ap2 D2_RecP_s p O = parEncAxRecPLf sT (ap1 cor p)

  D2_RecP_s_reduce_O : (p : Term) ->
    Deriv (atomic (eqn (ap2 D2_RecP_s p O)
                       (parEncAxRecPLf sT (ap1 cor p))))
  D2_RecP_s_reduce_O p =
    let -- Step A: unfold Fan
        a1 : Deriv (atomic (eqn (ap2 D2_RecP_s p O)
                                 (ap2 IfLf (ap2 (Post Snd Pair) p O)
                                            (ap2 dispatchFun p O))))
        a1 = axFan (Post Snd Pair) dispatchFun IfLf p O

        -- Step B: rewrite first arg of IfLf to O (= second input directly)
        a2 : Deriv (atomic (eqn (ap2 (Post Snd Pair) p O) O))
        a2 = postSndPair_eval p O

        a3 : Deriv (atomic (eqn (ap2 IfLf (ap2 (Post Snd Pair) p O)
                                          (ap2 dispatchFun p O))
                                 (ap2 IfLf O (ap2 dispatchFun p O))))
        a3 = congL IfLf (ap2 dispatchFun p O) a2

        -- Step C: unfold dispatchFun
        c1 : Deriv (atomic (eqn (ap2 dispatchFun p O)
                                 (ap2 Pair (ap2 lfPart p O)
                                            (ap2 D2_RecP_NN_fun p O))))
        c1 = axFan lfPart D2_RecP_NN_fun Pair p O

        -- Step C': unfold lfPart at p, O
        d1 : Deriv (atomic (eqn (ap2 lfPart p O)
                                 (ap2 Pair (ap2 (Lift (KT tagCode_axRecPLf)) p O)
                                            (ap2 lfPayload p O))))
        d1 = axFan (Lift (KT tagCode_axRecPLf)) lfPayload Pair p O

        d2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axRecPLf)) p O)
                                 tagCode_axRecPLf))
        d2 = liftKTtree_eval (natCode tagAxRecPLf) p O

        -- Step D: unfold lfPayload at p, O
        e1 : Deriv (atomic (eqn (ap2 lfPayload p O)
                                 (ap2 Pair (ap2 (Lift (KT sT)) p O)
                                            (ap2 (Lift cor) p O))))
        e1 = axFan (Lift (KT sT)) (Lift cor) Pair p O

        e2 : Deriv (atomic (eqn (ap2 (Lift (KT sT)) p O) sT))
        e2 = liftKTtree_eval (codeF2 s) p O

        e3 : Deriv (atomic (eqn (ap2 (Lift cor) p O) (ap1 cor p)))
        e3 = liftCor_eval p O

        e4 : Deriv (atomic (eqn (ap2 lfPayload p O)
                                 (ap2 Pair sT (ap1 cor p))))
        e4 = ruleTrans e1
              (ruleTrans (congL Pair (ap2 (Lift cor) p O) e2)
                         (congR Pair sT e3))

        d3 : Deriv (atomic (eqn (ap2 lfPart p O)
                                 (ap2 Pair tagCode_axRecPLf (ap2 Pair sT (ap1 cor p)))))
        d3 = ruleTrans d1
              (ruleTrans (congL Pair (ap2 lfPayload p O) d2)
                         (congR Pair tagCode_axRecPLf e4))

        -- d3 conclusion is exactly  parEncAxRecPLf sT (ap1 cor p) .

        c2 : Deriv (atomic (eqn (ap2 dispatchFun p O)
                                 (ap2 Pair (parEncAxRecPLf sT (ap1 cor p))
                                            (ap2 D2_RecP_NN_fun p O))))
        c2 = ruleTrans c1
              (congL Pair (ap2 D2_RecP_NN_fun p O) d3)

        -- Step E: rewrite IfLf RHS via c2, then apply axIfLfL
        a4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 dispatchFun p O))
                                 (ap2 IfLf O (ap2 Pair
                                                  (parEncAxRecPLf sT (ap1 cor p))
                                                  (ap2 D2_RecP_NN_fun p O)))))
        a4 = congR IfLf O c2

        a5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair
                                                  (parEncAxRecPLf sT (ap1 cor p))
                                                  (ap2 D2_RecP_NN_fun p O)))
                                 (parEncAxRecPLf sT (ap1 cor p))))
        a5 = axIfLfL (parEncAxRecPLf sT (ap1 cor p))
                     (ap2 D2_RecP_NN_fun p O)

    in ruleTrans a1 (ruleTrans a3 (ruleTrans a4 a5))

  ----------------------------------------------------------------------
  -- Reduction at x = Pair v1 v2:
  --   ap2 D2_RecP_s p (Pair v1 v2) = ap2 D2_RecP_NN_fun p (Pair v1 v2)

  D2_RecP_s_reduce_Nd : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 D2_RecP_s p (ap2 Pair v1 v2))
                       (ap2 D2_RecP_NN_fun p (ap2 Pair v1 v2))))
  D2_RecP_s_reduce_Nd p v1 v2 =
    let x = ap2 Pair v1 v2

        a1 : Deriv (atomic (eqn (ap2 D2_RecP_s p x)
                                 (ap2 IfLf (ap2 (Post Snd Pair) p x)
                                            (ap2 dispatchFun p x))))
        a1 = axFan (Post Snd Pair) dispatchFun IfLf p x

        a2 : Deriv (atomic (eqn (ap2 (Post Snd Pair) p x) x))
        a2 = postSndPair_eval p x

        a3 : Deriv (atomic (eqn (ap2 IfLf (ap2 (Post Snd Pair) p x)
                                          (ap2 dispatchFun p x))
                                 (ap2 IfLf x (ap2 dispatchFun p x))))
        a3 = congL IfLf (ap2 dispatchFun p x) a2

        c1 : Deriv (atomic (eqn (ap2 dispatchFun p x)
                                 (ap2 Pair (ap2 lfPart p x)
                                            (ap2 D2_RecP_NN_fun p x))))
        c1 = axFan lfPart D2_RecP_NN_fun Pair p x

        a4 : Deriv (atomic (eqn (ap2 IfLf x (ap2 dispatchFun p x))
                                 (ap2 IfLf x (ap2 Pair (ap2 lfPart p x)
                                                        (ap2 D2_RecP_NN_fun p x)))))
        a4 = congR IfLf x c1

        a5 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair v1 v2)
                                          (ap2 Pair (ap2 lfPart p x)
                                                     (ap2 D2_RecP_NN_fun p x)))
                                 (ap2 D2_RecP_NN_fun p x)))
        a5 = axIfLfN v1 v2 (ap2 lfPart p x) (ap2 D2_RecP_NN_fun p x)

    in ruleTrans a1 (ruleTrans a3 (ruleTrans a4 a5))

  ----------------------------------------------------------------------
  -- Bridge at O: parOutAxRecPLf sT (ap1 cor p) -> codeFTeq2_RecP_s s p O.

  bridgeO : (p : Term) ->
    Deriv (atomic (eqn (parOutAxRecPLf sT (ap1 cor p))
                       (codeFTeq2_RecP_s s p O)))
  bridgeO p =
    let cor_O : Deriv (atomic (eqn (ap1 cor O) O))
        cor_O = axRecLf stepCor

        recPLf_eq : Deriv (atomic (eqn (ap2 (RecP s) p O) O))
        recPLf_eq = axRecPLf s p

        cor_recPLf : Deriv (atomic (eqn (ap1 cor (ap2 (RecP s) p O))
                                         (ap1 cor O)))
        cor_recPLf = cong1 cor recPLf_eq

        cor_recPLf_O : Deriv (atomic (eqn (ap1 cor (ap2 (RecP s) p O)) O))
        cor_recPLf_O = ruleTrans cor_recPLf cor_O

        -- parOutAxRecPLf sT (ap1 cor p) =
        --   Pair (Pair (reify tagAp2)
        --              (Pair (Pair (reify K_rPV) sT)
        --                    (Pair (ap1 cor p) O)))
        --        O
        -- where (Pair (reify K_rPV) sT) = reify (codeF2 (RecP s)).
        -- codeFTeq2_RecP_s s p O =
        --   Pair (Pair (reify tagAp2)
        --              (Pair (reify (codeF2 (RecP s)))
        --                    (Pair (ap1 cor p) (ap1 cor O))))
        --        (ap1 cor (ap2 (RecP s) p O))
        --
        -- The "reify (codeF2 (RecP s))" reduces structurally to the same
        -- expression, so we only bridge:
        --   O <-> ap1 cor O      via  ruleSym cor_O
        --   O <-> ap1 cor (ap2 (RecP s) p O)   via  ruleSym cor_recPLf_O

        -- The inner pair where O is replaced by  ap1 cor O .
        step1 : Deriv (atomic (eqn
                  (ap2 Pair (ap1 cor p) O)
                  (ap2 Pair (ap1 cor p) (ap1 cor O))))
        step1 = congR Pair (ap1 cor p) (ruleSym cor_O)

        step2 : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF2 (RecP s)))
                            (ap2 Pair (ap1 cor p) O))
                  (ap2 Pair (reify (codeF2 (RecP s)))
                            (ap2 Pair (ap1 cor p) (ap1 cor O)))))
        step2 = congR Pair (reify (codeF2 (RecP s))) step1

        step3 : Deriv (atomic (eqn
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 (RecP s)))
                                      (ap2 Pair (ap1 cor p) O)))
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 (RecP s)))
                                      (ap2 Pair (ap1 cor p) (ap1 cor O))))))
        step3 = congR Pair (reify tagAp2) step2

        -- The outer Pair: replace O by ap1 cor (ap2 (RecP s) p O).
        step4 : Deriv (atomic (eqn
                  (parOutAxRecPLf sT (ap1 cor p))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 (RecP s)))
                                        (ap2 Pair (ap1 cor p) (ap1 cor O))))
                    O)))
        step4 = congL Pair O step3

        step5 : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 (RecP s)))
                                        (ap2 Pair (ap1 cor p) (ap1 cor O))))
                    O)
                  (codeFTeq2_RecP_s s p O)))
        step5 = congR Pair _ (ruleSym cor_recPLf_O)

    in ruleTrans step4 step5

  ----------------------------------------------------------------------
  -- Pointwise correctness at the two shape cases.

  D_correct2_RecP_s_O : (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_RecP_s p O))
                       (codeFTeq2_RecP_s s p O)))
  D_correct2_RecP_s_O p =
    let r_thmT = cong1 thmT (D2_RecP_s_reduce_O p)
        r_disp = parDispAxRecPLf sT (ap1 cor p)
    in ruleTrans r_thmT (ruleTrans r_disp (bridgeO p))

  D_correct2_RecP_s_Nd : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_RecP_s p (ap2 Pair v1 v2)))
                       (codeFTeq2_RecP_s s p (ap2 Pair v1 v2))))
  D_correct2_RecP_s_Nd p v1 v2 =
    let r_thmT = cong1 thmT (D2_RecP_s_reduce_Nd p v1 v2)
    in ruleTrans r_thmT (D_correct2_RecP_NN_pt p v1 v2)

  ----------------------------------------------------------------------
  -- Note: a universal proof via ruleIndBT is omitted because the
  -- closure obligation  Eq (substF2 x r D2_RecP_s) D2_RecP_s  cascades
  -- through  reify (codeF2 s)  in ways Agda cannot resolve while  s  is
  -- an opaque module parameter.  Phase 7 glue, where  s  is concrete,
  -- can derive the universal proof via ruleIndBT using the two
  -- pointwise lemmas above.
