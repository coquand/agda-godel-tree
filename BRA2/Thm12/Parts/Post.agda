{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.Post
--
-- Theorem 12 case for g = Post f h : Fun2 (post-composition).
-- Recursive in f : Fun1 and h : Fun2.
--
-- Encoded chain:
--   D2_(Post f h) a b = encRuleTrans
--                         (parEncAxPost f h (cor a) (cor b))    -- (Post f h)(num a, num b) = f(h(num a, num b))
--                         (encRuleTrans
--                            (parEncCong1 f (D2_h a b))           -- f(h(num a, num b)) = f(num(h a b))
--                            (Df (h a b)))                        -- f(num(h a b)) = num(f(h a b))
-- + bridge cor(f(h a b)) -> cor((Post f h)(a, b)) via cong1 cor + axPost + ruleSym.

module BRA2.Thm12.Parts.Post where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxPost ; tagCong1 ; tagRuleTrans)
open import BRA2.Thm.ThmT
  using (thmT ; tagCode_axPost ; tagCode_ruleTrans ; tagCode_cong1)
open import BRA2.Thm12.Param.AxPost
  using (parDispAxPost ; parEncAxPost ; parOutAxPost)
open import BRA2.Thm12.Param.Cong1
  using (parDispCong1 ; parEncCong1 ; parOutCong1)
open import BRA2.Thm12.Param.RuleTrans
  using (parDispRuleTrans ; parEncRuleTrans)

module PostCase
  (f : Fun1)
  (h : Fun2)
  (Df : Fun1)
  (D2_h : Fun2)
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  (D_correct_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
  where

  -- Sub-combinators of D2_(Post f h).
  private
    -- Produces parEncAxPost f h (cor a) (cor b).
    axPost_part : Fun2
    axPost_part =
      Fan (Lift (KT tagCode_axPost))
          (Fan (Lift (KT (reify (codeF1 f))))
               (Fan (Lift (KT (reify (codeF2 h))))
                    (Fan (Lift cor) (Post cor (Post Snd Pair)) Pair)
                    Pair)
               Pair)
          Pair

    -- Produces parEncCong1 f (D2_h a b) = Pair tagCode_cong1 (Pair codeF1f (D2_h a b)).
    cong1_part : Fun2
    cong1_part =
      Fan (Lift (KT tagCode_cong1))
          (Fan (Lift (KT (reify (codeF1 f)))) D2_h Pair)
          Pair

    -- Inner ruleTrans: parEncRuleTrans cong1_part (Df ∘ h).  As Fun2:
    --   ap2 inner_rt a b = Pair tagCode_ruleTrans (Pair (cong1_part a b) (Df (h a b)))
    df_after_h : Fun2
    df_after_h = Post Df h

    inner_rt : Fun2
    inner_rt =
      Fan (Lift (KT tagCode_ruleTrans))
          (Fan cong1_part df_after_h Pair)
          Pair

  D2_Post_fh : Fun2
  D2_Post_fh =
    Fan (Lift (KT tagCode_ruleTrans))
        (Fan axPost_part inner_rt Pair)
        Pair

  codeFTeq2_Post : Term -> Term -> Term
  codeFTeq2_Post a b =
    ap2 Pair
      (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 (Post f h)))
                          (ap2 Pair (ap1 cor a) (ap1 cor b))))
      (ap1 cor (ap2 (Post f h) a b))

  ----------------------------------------------------------------------
  -- Combinator reduction.

  private
    -- helper: ap2 (Post cor (Post Snd Pair)) a b = cor b
    corOnSnd : (a b : Term) ->
      Deriv (atomic (eqn (ap2 (Post cor (Post Snd Pair)) a b) (ap1 cor b)))
    corOnSnd a b =
      ruleTrans (axPost cor (Post Snd Pair) a b)
                (cong1 cor (ruleTrans (axPost Snd Pair a b) (axSnd a b)))

  axPostPart_reduce : (a b : Term) ->
    Deriv (atomic (eqn (ap2 axPost_part a b)
                       (parEncAxPost f h (ap1 cor a) (ap1 cor b))))
  axPostPart_reduce a b =
    let codeF1f_T = reify (codeF1 f)
        codeF2h_T = reify (codeF2 h)
        innerCor : Fun2
        innerCor = Fan (Lift cor) (Post cor (Post Snd Pair)) Pair
        innerH : Fun2
        innerH = Fan (Lift (KT codeF2h_T)) innerCor Pair
        innerF : Fun2
        innerF = Fan (Lift (KT codeF1f_T)) innerH Pair
        outerP : Fun2
        outerP = Fan (Lift (KT tagCode_axPost)) innerF Pair

        -- Reduce step by step.
        s1 = axFan (Lift (KT tagCode_axPost)) innerF Pair a b
        s2a = axLift (KT tagCode_axPost) a b
        s2b = axKT (natCode tagAxPost) (natCode_isValue tagAxPost) a
        s2 = ruleTrans s2a s2b

        sInner = axFan (Lift (KT codeF1f_T)) innerH Pair a b
        sInnerL = ruleTrans (axLift (KT codeF1f_T) a b) (axKT (codeF1 f) (codeF1_isValue f) a)

        sH = axFan (Lift (KT codeF2h_T)) innerCor Pair a b
        sHL = ruleTrans (axLift (KT codeF2h_T) a b) (axKT (codeF2 h) (codeF2_isValue h) a)

        sCor = axFan (Lift cor) (Post cor (Post Snd Pair)) Pair a b
        sCorL = axLift cor a b
        sCorR = corOnSnd a b

        innerCorOut : Term
        innerCorOut = ap2 Pair (ap1 cor a) (ap1 cor b)

        sCorTo : Deriv (atomic (eqn (ap2 innerCor a b) innerCorOut))
        sCorTo = ruleTrans sCor
                   (ruleTrans (congL Pair (ap2 (Post cor (Post Snd Pair)) a b) sCorL)
                              (congR Pair (ap1 cor a) sCorR))

        innerHOut : Term
        innerHOut = ap2 Pair codeF2h_T innerCorOut

        sHTo : Deriv (atomic (eqn (ap2 innerH a b) innerHOut))
        sHTo = ruleTrans sH
                  (ruleTrans (congL Pair (ap2 innerCor a b) sHL)
                             (congR Pair codeF2h_T sCorTo))

        innerFOut : Term
        innerFOut = ap2 Pair codeF1f_T innerHOut

        sInnerTo : Deriv (atomic (eqn (ap2 innerF a b) innerFOut))
        sInnerTo = ruleTrans sInner
                     (ruleTrans (congL Pair (ap2 innerH a b) sInnerL)
                                (congR Pair codeF1f_T sHTo))
    in ruleTrans s1
         (ruleTrans (congL Pair (ap2 innerF a b) s2)
                    (congR Pair tagCode_axPost sInnerTo))

  cong1Part_reduce : (a b : Term) ->
    Deriv (atomic (eqn (ap2 cong1_part a b)
                       (parEncCong1 f (ap2 D2_h a b))))
  cong1Part_reduce a b =
    let codeF1f_T = reify (codeF1 f)
        innerKf : Fun2
        innerKf = Fan (Lift (KT codeF1f_T)) D2_h Pair

        s1 = axFan (Lift (KT tagCode_cong1)) innerKf Pair a b
        s2 = ruleTrans (axLift (KT tagCode_cong1) a b)
                       (axKT (natCode tagCong1) (natCode_isValue tagCong1) a)

        sInner = axFan (Lift (KT codeF1f_T)) D2_h Pair a b
        sInnerL = ruleTrans (axLift (KT codeF1f_T) a b) (axKT (codeF1 f) (codeF1_isValue f) a)
        sInnerTo : Deriv (atomic (eqn (ap2 innerKf a b)
                                       (ap2 Pair codeF1f_T (ap2 D2_h a b))))
        sInnerTo = ruleTrans sInner
                     (congL Pair (ap2 D2_h a b) sInnerL)
    in ruleTrans s1
         (ruleTrans (congL Pair (ap2 innerKf a b) s2)
                    (congR Pair tagCode_cong1 sInnerTo))

  innerRT_reduce : (a b : Term) ->
    Deriv (atomic (eqn (ap2 inner_rt a b)
                       (parEncRuleTrans (parEncCong1 f (ap2 D2_h a b))
                                         (ap1 Df (ap2 h a b)))))
  innerRT_reduce a b =
    let s1 = axFan (Lift (KT tagCode_ruleTrans))
                   (Fan cong1_part df_after_h Pair) Pair a b
        s2 = ruleTrans (axLift (KT tagCode_ruleTrans) a b)
                       (axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) a)

        sInner = axFan cong1_part df_after_h Pair a b
        sCong1 = cong1Part_reduce a b
        sDf : Deriv (atomic (eqn (ap2 df_after_h a b) (ap1 Df (ap2 h a b))))
        sDf = axPost Df h a b
        sInnerTo : Deriv (atomic (eqn (ap2 (Fan cong1_part df_after_h Pair) a b)
                                        (ap2 Pair (parEncCong1 f (ap2 D2_h a b))
                                                   (ap1 Df (ap2 h a b)))))
        sInnerTo = ruleTrans sInner
                     (ruleTrans (congL Pair (ap2 df_after_h a b) sCong1)
                                (congR Pair (parEncCong1 f (ap2 D2_h a b)) sDf))
    in ruleTrans s1
         (ruleTrans (congL Pair (ap2 (Fan cong1_part df_after_h Pair) a b) s2)
                    (congR Pair tagCode_ruleTrans sInnerTo))

  D2_Post_reduce : (a b : Term) ->
    Deriv (atomic (eqn (ap2 D2_Post_fh a b)
                       (parEncRuleTrans
                          (parEncAxPost f h (ap1 cor a) (ap1 cor b))
                          (parEncRuleTrans
                            (parEncCong1 f (ap2 D2_h a b))
                            (ap1 Df (ap2 h a b))))))
  D2_Post_reduce a b =
    let s1 = axFan (Lift (KT tagCode_ruleTrans))
                   (Fan axPost_part inner_rt Pair) Pair a b
        s2 = ruleTrans (axLift (KT tagCode_ruleTrans) a b)
                       (axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) a)
        sInner = axFan axPost_part inner_rt Pair a b
        sAx = axPostPart_reduce a b
        sIRT = innerRT_reduce a b
        innerOut : Term
        innerOut = ap2 Pair (parEncAxPost f h (ap1 cor a) (ap1 cor b))
                              (parEncRuleTrans
                                (parEncCong1 f (ap2 D2_h a b))
                                (ap1 Df (ap2 h a b)))
        sInnerTo : Deriv (atomic (eqn (ap2 (Fan axPost_part inner_rt Pair) a b) innerOut))
        sInnerTo = ruleTrans sInner
                     (ruleTrans (congL Pair (ap2 inner_rt a b) sAx)
                                (congR Pair (parEncAxPost f h (ap1 cor a) (ap1 cor b)) sIRT))
    in ruleTrans s1
         (ruleTrans (congL Pair _ s2)
                    (congR Pair tagCode_ruleTrans sInnerTo))

  ----------------------------------------------------------------------
  -- D_correct2_Post_fh .

  D_correct2_Post_fh : (a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_Post_fh a b)) (codeFTeq2_Post a b)))
  D_correct2_Post_fh a b =
    let cf  = reify (codeF1 f)
        ch  = reify (codeF2 h)

        u1_y1 : Term
        u1_y1 = ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Post I IfLf))))
                                       (ap2 Pair cf ch))
                            (ap2 Pair (ap1 cor a) (ap1 cor b)))
        u2_y1 : Term
        u2_y1 = ap2 Pair (reify tagAp1)
                  (ap2 Pair cf
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair ch (ap2 Pair (ap1 cor a) (ap1 cor b)))))

        d_y1 : Deriv (atomic (eqn (ap1 thmT (parEncAxPost f h (ap1 cor a) (ap1 cor b)))
                                    (ap2 Pair u1_y1 u2_y1)))
        d_y1 = parDispAxPost f h (ap1 cor a) (ap1 cor b)

        u1_Dh : Term
        u1_Dh = ap2 Pair (reify tagAp2)
                  (ap2 Pair ch (ap2 Pair (ap1 cor a) (ap1 cor b)))
        u2_Dh : Term
        u2_Dh = ap1 cor (ap2 h a b)

        d_Dh : Deriv (atomic (eqn (ap1 thmT (ap2 D2_h a b))
                                   (ap2 Pair u1_Dh u2_Dh)))
        d_Dh = D_correct_h a b

        u1_cong : Term
        u1_cong = ap2 Pair (reify tagAp1) (ap2 Pair cf u1_Dh)
        u2_cong : Term
        u2_cong = ap2 Pair (reify tagAp1) (ap2 Pair cf u2_Dh)

        d_cong : Deriv (atomic (eqn (ap1 thmT (parEncCong1 f (ap2 D2_h a b)))
                                     (ap2 Pair u1_cong u2_cong)))
        d_cong = parDispCong1 f (ap2 D2_h a b) u1_Dh u2_Dh d_Dh

        u1_Df : Term
        u1_Df = ap2 Pair (reify tagAp1) (ap2 Pair cf (ap1 cor (ap2 h a b)))
        u2_Df : Term
        u2_Df = ap1 cor (ap1 f (ap2 h a b))

        d_Df : Deriv (atomic (eqn (ap1 thmT (ap1 Df (ap2 h a b)))
                                   (ap2 Pair u1_Df u2_Df)))
        d_Df = D_correct_f (ap2 h a b)

        cong_shape : Deriv (atomic (eqn (ap1 Fst (parEncCong1 f (ap2 D2_h a b)))
                                          (ap2 Pair O _)))
        cong_shape = axFst tagCode_cong1 _

        d_inner_rt : Deriv (atomic (eqn (ap1 thmT
                              (parEncRuleTrans (parEncCong1 f (ap2 D2_h a b))
                                                (ap1 Df (ap2 h a b))))
                              (ap2 Pair u1_cong u2_Df)))
        d_inner_rt = parDispRuleTrans
                       (parEncCong1 f (ap2 D2_h a b))
                       (ap1 Df (ap2 h a b))
                       u1_cong u2_cong u1_Df u2_Df
                       _ _
                       cong_shape d_cong d_Df

        axPost_shape : Deriv (atomic (eqn (ap1 Fst (parEncAxPost f h (ap1 cor a) (ap1 cor b)))
                                            (ap2 Pair O _)))
        axPost_shape = axFst tagCode_axPost _

        d_outer_rt : Deriv (atomic (eqn (ap1 thmT
                              (parEncRuleTrans
                                (parEncAxPost f h (ap1 cor a) (ap1 cor b))
                                (parEncRuleTrans
                                  (parEncCong1 f (ap2 D2_h a b))
                                  (ap1 Df (ap2 h a b)))))
                              (ap2 Pair u1_y1 u2_Df)))
        d_outer_rt = parDispRuleTrans
                       (parEncAxPost f h (ap1 cor a) (ap1 cor b))
                       (parEncRuleTrans
                          (parEncCong1 f (ap2 D2_h a b))
                          (ap1 Df (ap2 h a b)))
                       u1_y1 u2_y1 u1_cong u2_Df
                       _ _
                       axPost_shape d_y1 d_inner_rt

        red = D2_Post_reduce a b

        thmT_red : Deriv (atomic (eqn
                    (ap1 thmT (ap2 D2_Post_fh a b))
                    (ap1 thmT (parEncRuleTrans
                                (parEncAxPost f h (ap1 cor a) (ap1 cor b))
                                (parEncRuleTrans
                                  (parEncCong1 f (ap2 D2_h a b))
                                  (ap1 Df (ap2 h a b)))))))
        thmT_red = cong1 thmT red

        sym_bridge : Deriv (atomic (eqn (ap1 cor (ap1 f (ap2 h a b)))
                                         (ap1 cor (ap2 (Post f h) a b))))
        sym_bridge = ruleSym (cong1 cor (axPost f h a b))

        bridge : Deriv (atomic (eqn (ap2 Pair u1_y1 u2_Df) (codeFTeq2_Post a b)))
        bridge = congR Pair u1_y1 sym_bridge

    in ruleTrans thmT_red (ruleTrans d_outer_rt bridge)
