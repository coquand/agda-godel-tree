{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.Comp
--
-- Theorem 12 case for f = Comp f' g (Fun1 composition).  Recursive in
-- both subcombinators f' and g, taking their D's and D_correct's as IH
-- parameters.
--
-- Encoded proof tree (asymmetric):
--   D_(Comp f' g) a = encRuleTrans
--                       (parEncAxComp f' g (cor a))               -- (Comp f' g)(num a) = f'(g(num a))
--                       (encRuleTrans
--                          (parEncCong1 f' (D_g a))                 -- f'(g(num a)) = f'(num(g a))
--                          (D_f' (g a)))                            -- f'(num(g a)) = num(f'(g a))
-- + final bridge cor(f'(g a)) -> cor((Comp f' g) a) via cong1 cor + axComp + ruleSym.

module BRA2.Thm12.Parts.Comp where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxComp ; tagAxLift ; tagCong1 ; tagRuleTrans)
open import BRA2.Thm.ThmT
  using (thmT ; tagCode_axComp ; tagCode_ruleTrans ; tagCode_cong1)
open import BRA2.Thm12.Param.AxComp
  using (parDispAxComp ; parEncAxComp ; parOutAxComp)
open import BRA2.Thm12.Param.Cong1
  using (parDispCong1 ; parEncCong1 ; parOutCong1)
open import BRA2.Thm12.Param.RuleTrans
  using (parDispRuleTrans ; parEncRuleTrans)

module CompCase
  (f' g : Fun1)
  (Df' Dg : Fun1)
  (D_correct_f' : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df' x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f')) (ap1 cor x)))
         (ap1 cor (ap1 f' x))))))
  (D_correct_g : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Dg x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 g)) (ap1 cor x)))
         (ap1 cor (ap1 g x))))))
  where

  -- Sub-combinators of D_(Comp f' g) when applied to x.
  private
    -- Produces parEncAxComp f' g (cor x) when applied to x.
    axComp_part : Fun1
    axComp_part =
      Comp2 Pair (KT tagCode_axComp)
        (Comp2 Pair (KT (reify (codeF1 f')))
          (Comp2 Pair (KT (reify (codeF1 g))) cor))

    -- Produces parEncCong1 f' (Dg x) when applied to x.
    cong1_part : Fun1
    cong1_part =
      Comp2 Pair (KT tagCode_cong1)
        (Comp2 Pair (KT (reify (codeF1 f'))) Dg)

    -- Inner ruleTrans: Comp2 Pair cong1_part (Comp Df' g)
    --   ap1 inner_rt x = Pair (parEncCong1 f' (Dg x)) (Df' (g x)).
    inner_rt : Fun1
    inner_rt =
      Comp2 Pair (KT tagCode_ruleTrans)
        (Comp2 Pair cong1_part (Comp Df' g))

  D_Comp_f'g : Fun1
  D_Comp_f'g =
    Comp2 Pair (KT tagCode_ruleTrans)
      (Comp2 Pair axComp_part inner_rt)

  codeFTeq1_Comp : Term -> Term
  codeFTeq1_Comp x =
    ap2 Pair
      (ap2 Pair (reify tagAp1)
                (ap2 Pair (reify (codeF1 (Comp f' g))) (ap1 cor x)))
      (ap1 cor (ap1 (Comp f' g) x))

  ----------------------------------------------------------------------
  -- Combinator reduction:
  --   ap1 D_Comp_f'g x = parEncRuleTrans (parEncAxComp f' g (cor x)) (innerRT x)
  -- where innerRT x = parEncRuleTrans (parEncCong1 f' (Dg x)) (Df' (g x))

  axCompPart_reduce : (x : Term) ->
    Deriv (atomic (eqn (ap1 axComp_part x) (parEncAxComp f' g (ap1 cor x))))
  axCompPart_reduce x =
    let s1 = axComp2 Pair (KT tagCode_axComp)
                          (Comp2 Pair (KT (reify (codeF1 f')))
                            (Comp2 Pair (KT (reify (codeF1 g))) cor)) x
        s2 = axKT (natCode tagAxComp) (natCode_isValue tagAxComp) x
        s3 = axComp2 Pair (KT (reify (codeF1 f')))
                          (Comp2 Pair (KT (reify (codeF1 g))) cor) x
        s4 = axKT (codeF1 f') (codeF1_isValue f') x
        s5 = axComp2 Pair (KT (reify (codeF1 g))) cor x
        s6 = axKT (codeF1 g) (codeF1_isValue g) x
        innerInner : Term
        innerInner = ap2 Pair (reify (codeF1 g)) (ap1 cor x)
        rInner = ruleTrans s5 (congL Pair (ap1 cor x) s6)
        innerOuter : Term
        innerOuter = ap2 Pair (reify (codeF1 f')) innerInner
        rOuter = ruleTrans s3 (ruleTrans (congL Pair _ s4) (congR Pair (reify (codeF1 f')) rInner))
    in ruleTrans s1 (ruleTrans (congL Pair _ s2) (congR Pair tagCode_axComp rOuter))

  cong1Part_reduce : (x : Term) ->
    Deriv (atomic (eqn (ap1 cong1_part x) (parEncCong1 f' (ap1 Dg x))))
  cong1Part_reduce x =
    let s1 = axComp2 Pair (KT tagCode_cong1)
                          (Comp2 Pair (KT (reify (codeF1 f'))) Dg) x
        s2 = axKT (natCode tagCong1) (natCode_isValue tagCong1) x
        s3 = axComp2 Pair (KT (reify (codeF1 f'))) Dg x
        s4 = axKT (codeF1 f') (codeF1_isValue f') x
        rInner = ruleTrans s3 (congL Pair (ap1 Dg x) s4)
    in ruleTrans s1 (ruleTrans (congL Pair _ s2) (congR Pair tagCode_cong1 rInner))

  innerRT_reduce : (x : Term) ->
    Deriv (atomic (eqn (ap1 inner_rt x)
              (parEncRuleTrans (parEncCong1 f' (ap1 Dg x)) (ap1 Df' (ap1 g x)))))
  innerRT_reduce x =
    let s1 = axComp2 Pair (KT tagCode_ruleTrans)
                          (Comp2 Pair cong1_part (Comp Df' g)) x
        s2 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
        s3 = axComp2 Pair cong1_part (Comp Df' g) x
        s4 = cong1Part_reduce x
        s5 = axComp Df' g x
        rInner = ruleTrans s3
                   (ruleTrans (congL Pair (ap1 (Comp Df' g) x) s4)
                              (congR Pair (parEncCong1 f' (ap1 Dg x)) s5))
    in ruleTrans s1 (ruleTrans (congL Pair _ s2) (congR Pair tagCode_ruleTrans rInner))

  D_Comp_reduce : (x : Term) ->
    Deriv (atomic (eqn (ap1 D_Comp_f'g x)
              (parEncRuleTrans (parEncAxComp f' g (ap1 cor x))
                (parEncRuleTrans (parEncCong1 f' (ap1 Dg x))
                                 (ap1 Df' (ap1 g x))))))
  D_Comp_reduce x =
    let s1 = axComp2 Pair (KT tagCode_ruleTrans)
                          (Comp2 Pair axComp_part inner_rt) x
        s2 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
        s3 = axComp2 Pair axComp_part inner_rt x
        s4 = axCompPart_reduce x
        s5 = innerRT_reduce x
        rInner = ruleTrans s3
                   (ruleTrans (congL Pair _ s4)
                              (congR Pair (parEncAxComp f' g (ap1 cor x)) s5))
    in ruleTrans s1 (ruleTrans (congL Pair _ s2) (congR Pair tagCode_ruleTrans rInner))

  ----------------------------------------------------------------------
  -- D_correct_Comp_f'g .

  -- Helper for parDispRuleTrans's shape requirement: head of any
  -- parEnc* term is tagCode_X = reify(natCode (suc N)) which has Pair
  -- shape, so Fst gives (Pair O ...).

  D_correct_Comp_f'g : (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_Comp_f'g x)) (codeFTeq1_Comp x)))
  D_correct_Comp_f'g x =
    let cf  = reify (codeF1 f')
        cg  = reify (codeF1 g)
        K2  = reify (leftT (codeF1 (Comp I I)))

        -- y1 = parEncAxComp f' g (cor x). image:
        u1_y1 : Term
        u1_y1 = ap2 Pair (reify tagAp1)
                  (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) (ap1 cor x))
        u2_y1 : Term
        u2_y1 = ap2 Pair (reify tagAp1)
                  (ap2 Pair cf (ap2 Pair (reify tagAp1) (ap2 Pair cg (ap1 cor x))))
        d1_y1 : Deriv (atomic (eqn (ap1 thmT (parEncAxComp f' g (ap1 cor x)))
                                    (ap2 Pair u1_y1 u2_y1)))
        d1_y1 = parDispAxComp f' g (ap1 cor x)

        -- D_g x's image: codeFTeq1_g x.
        u1_Dg : Term
        u1_Dg = ap2 Pair (reify tagAp1) (ap2 Pair cg (ap1 cor x))
        u2_Dg : Term
        u2_Dg = ap1 cor (ap1 g x)
        d_Dg : Deriv (atomic (eqn (ap1 thmT (ap1 Dg x))
                                   (ap2 Pair u1_Dg u2_Dg)))
        d_Dg = D_correct_g x

        -- parEncCong1 f' (Dg x)'s image: parOutCong1 f' u1_Dg u2_Dg.
        u1_cong : Term
        u1_cong = ap2 Pair (reify tagAp1) (ap2 Pair cf u1_Dg)
        u2_cong : Term
        u2_cong = ap2 Pair (reify tagAp1) (ap2 Pair cf u2_Dg)
        d_cong : Deriv (atomic (eqn (ap1 thmT (parEncCong1 f' (ap1 Dg x)))
                                     (ap2 Pair u1_cong u2_cong)))
        d_cong = parDispCong1 f' (ap1 Dg x) u1_Dg u2_Dg d_Dg

        -- D_f' (g x)'s image: codeFTeq1_f' (g x).
        u1_Df : Term
        u1_Df = ap2 Pair (reify tagAp1) (ap2 Pair cf (ap1 cor (ap1 g x)))
        u2_Df : Term
        u2_Df = ap1 cor (ap1 f' (ap1 g x))
        d_Df : Deriv (atomic (eqn (ap1 thmT (ap1 Df' (ap1 g x)))
                                    (ap2 Pair u1_Df u2_Df)))
        d_Df = D_correct_f' (ap1 g x)

        -- Inner ruleTrans: y2 = parEncRuleTrans (parEncCong1 f' (Dg x)) (Df' (g x))
        -- image: Pair u1_cong u2_Df.
        -- Fst-shape proof for parEncCong1: Fst (Pair tagCode_cong1 ...) = tagCode_cong1.
        cong_shape : Deriv (atomic (eqn (ap1 Fst (parEncCong1 f' (ap1 Dg x)))
                                          tagCode_cong1))
        cong_shape = axFst tagCode_cong1 _

        d_inner_rt : Deriv (atomic (eqn (ap1 thmT (parEncRuleTrans
                              (parEncCong1 f' (ap1 Dg x)) (ap1 Df' (ap1 g x))))
                              (ap2 Pair u1_cong u2_Df)))
        d_inner_rt = parDispRuleTrans
                       (parEncCong1 f' (ap1 Dg x))
                       (ap1 Df' (ap1 g x))
                       u1_cong u2_cong u1_Df u2_Df
                       _ _
                       cong_shape d_cong d_Df

        -- Outer ruleTrans: y = parEncRuleTrans y1 y2.  image: Pair u1_y1 u2_Df.
        axComp_shape : Deriv (atomic (eqn (ap1 Fst (parEncAxComp f' g (ap1 cor x)))
                                            (ap2 Pair O (reify (natCode (suc (suc (suc (suc zero))))))))) -- tagAxComp = 5, prev = 4
        axComp_shape = axFst tagCode_axComp _

        d_outer_rt : Deriv (atomic (eqn (ap1 thmT (parEncRuleTrans
                              (parEncAxComp f' g (ap1 cor x))
                              (parEncRuleTrans
                                (parEncCong1 f' (ap1 Dg x))
                                (ap1 Df' (ap1 g x)))))
                              (ap2 Pair u1_y1 u2_Df)))
        d_outer_rt = parDispRuleTrans
                       (parEncAxComp f' g (ap1 cor x))
                       (parEncRuleTrans
                          (parEncCong1 f' (ap1 Dg x))
                          (ap1 Df' (ap1 g x)))
                       u1_y1 u2_y1 u1_cong u2_Df
                       _ _
                       axComp_shape d1_y1 d_inner_rt

        -- Combinator reduction of D_Comp_f'g.
        red = D_Comp_reduce x

        thmT_red : Deriv (atomic (eqn
                    (ap1 thmT (ap1 D_Comp_f'g x))
                    (ap1 thmT (parEncRuleTrans
                                (parEncAxComp f' g (ap1 cor x))
                                (parEncRuleTrans
                                  (parEncCong1 f' (ap1 Dg x))
                                  (ap1 Df' (ap1 g x)))))))
        thmT_red = cong1 thmT red

        -- Bridge: u2_Df = cor(f'(g x)) -> cor((Comp f' g) x).
        sym_bridge : Deriv (atomic (eqn (ap1 cor (ap1 f' (ap1 g x)))
                                          (ap1 cor (ap1 (Comp f' g) x))))
        sym_bridge = ruleSym (cong1 cor (axComp f' g x))

        bridge : Deriv (atomic (eqn (ap2 Pair u1_y1 u2_Df) (codeFTeq1_Comp x)))
        bridge = congR Pair u1_y1 sym_bridge

    in ruleTrans thmT_red (ruleTrans d_outer_rt bridge)
