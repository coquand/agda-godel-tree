{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.Comp2
--
-- Theorem 12 case for f = Comp2 h f' g (Fun1 with Fun2 + 2 Fun1 subs).
-- Recursive: takes D_f', D_g (Fun1 IH) and D2_h (Fun2 IH).
--
-- Encoded chain (Guard's pattern):
--   D_(Comp2 h f' g) x = encRuleTrans y1 (encRuleTrans y2a (encRuleTrans y2b y2c))
--     y1  = parEncAxComp2 h f' g (cor x)            -- (Comp2 h f' g)(num x) = h(f' num x, g num x)
--     y2a = parEncCongL h (D_f' x) (encoded g num x) -- h(f' num x, g num x) = h(num(f' x), g num x)
--     y2b = parEncCongR h (D_g x) (cor (f' x))       -- h(num(f' x), g num x) = h(num(f' x), num(g x))
--     y2c = D2_h (f' x) (g x)                        -- h(num(f' x), num(g x)) = num(h(f' x, g x))
-- Then bridge: cor(h(f' x, g x)) -> cor((Comp2 h f' g) x) via cong1 cor + axComp2 + ruleSym.

module BRA2.Thm12.Parts.Comp2 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagRuleTrans)
open import BRA2.Thm.ThmT
  using (thmT ; tagCode_ruleTrans)
open import BRA2.Thm12.Param.AxComp2
  using (parDispAxComp2 ; parEncAxComp2)
open import BRA2.Thm12.Param.CongL
  using (parDispCongL ; parEncCongL)
open import BRA2.Thm12.Param.CongR
  using (parDispCongR ; parEncCongR)
open import BRA2.Thm12.Param.RuleTrans
  using (parDispRuleTrans ; parEncRuleTrans)

module Comp2Case
  (h : Fun2)
  (f' g : Fun1)
  (D2_h : Fun2)
  (Df' Dg : Fun1)
  (D_correct_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
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

  ----------------------------------------------------------------------
  -- The asymmetric encoded equation.

  codeFTeq1_Comp2 : Term -> Term
  codeFTeq1_Comp2 x =
    ap2 Pair
      (ap2 Pair (reify tagAp1)
                (ap2 Pair (reify (codeF1 (Comp2 h f' g))) (ap1 cor x)))
      (ap1 cor (ap1 (Comp2 h f' g) x))

  ----------------------------------------------------------------------
  -- D_Comp2_hfg : Fun1 .
  --
  -- Built modularly from sub-encoders.  Each is a Fun1 producing the
  -- corresponding encoded sub-witness.

  private
    cF2h : Term
    cF2h = reify (codeF2 h)
    cF1f : Term
    cF1f = reify (codeF1 f')
    cF1g : Term
    cF1g = reify (codeF1 g)

    -- y1 builder: ap1 y1_part x = parEncAxComp2 h f' g (cor x).
    y1_part : Fun1
    y1_part =
      Comp2 Pair (KT (BRA2.Thm.ThmT.tagCode_axComp2))
        (Comp2 Pair (KT cF2h)
          (Comp2 Pair (KT cF1f)
            (Comp2 Pair (KT cF1g) cor)))

    -- enc_g_num: ap1 enc_g_num x = Pair tagAp1 (Pair codeF1g (cor x))
    --            = "encoded g num x".
    enc_g_num : Fun1
    enc_g_num = Comp2 Pair (KT (reify tagAp1))
                  (Comp2 Pair (KT cF1g) cor)

    -- y2a builder: ap1 y2a_part x = parEncCongL h (Df' x) (enc_g_num x)
    --   = Pair tagCode_congL (Pair (Pair codeF2h (enc_g_num x)) (Df' x))
    -- New layout (Finding 1): closed pair (codeF2h, xT) inner, open IH y_h_T outer.
    y2a_part : Fun1
    y2a_part =
      Comp2 Pair (KT (BRA2.Thm.ThmT.tagCode_congL))
        (Comp2 Pair
          (Comp2 Pair (KT cF2h) enc_g_num)
          Df')

    -- corF': ap1 corF' x = cor (f' x).
    corF' : Fun1
    corF' = Comp cor f'

    -- y2b builder: ap1 y2b_part x = parEncCongR h (Dg x) (cor (f' x))
    --   = Pair tagCode_congR (Pair (Pair codeF2h (cor (f' x))) (Dg x)).
    y2b_part : Fun1
    y2b_part =
      Comp2 Pair (KT (BRA2.Thm.ThmT.tagCode_congR))
        (Comp2 Pair
          (Comp2 Pair (KT cF2h) corF')
          Dg)

    -- y2c builder: ap1 y2c_part x = D2_h (f' x) (g x).
    y2c_part : Fun1
    y2c_part = Comp2 D2_h f' g

    -- inner_rt2 : produces Pair tagCode_ruleTrans (Pair y2b y2c).
    inner_rt2 : Fun1
    inner_rt2 =
      Comp2 Pair (KT tagCode_ruleTrans)
        (Comp2 Pair y2b_part y2c_part)

    -- inner_rt1 : produces Pair tagCode_ruleTrans (Pair y2a (inner_rt2)).
    inner_rt1 : Fun1
    inner_rt1 =
      Comp2 Pair (KT tagCode_ruleTrans)
        (Comp2 Pair y2a_part inner_rt2)

  D_Comp2_hfg : Fun1
  D_Comp2_hfg =
    Comp2 Pair (KT tagCode_ruleTrans)
      (Comp2 Pair y1_part inner_rt1)

  ----------------------------------------------------------------------
  -- D_correct_Comp2_hfg .
  --
  -- We won't write a separate D_Comp2_reduce; we proceed directly.

  D_correct_Comp2_hfg : (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_Comp2_hfg x)) (codeFTeq1_Comp2 x)))
  D_correct_Comp2_hfg x =
    let -- ====================================================================
        -- Combinator reductions: each sub-builder reduces to its parEnc form.

        red_y1 : Deriv (atomic (eqn (ap1 y1_part x)
                                     (parEncAxComp2 h f' g (ap1 cor x))))
        red_y1 =
          let -- y1_part = Comp2 Pair (KT tagCode_axComp2) (...) etc.
              -- Reduce step by step using axComp2 + axKT chain.
              s1 = axComp2 Pair (KT (BRA2.Thm.ThmT.tagCode_axComp2))
                                (Comp2 Pair (KT cF2h)
                                  (Comp2 Pair (KT cF1f)
                                    (Comp2 Pair (KT cF1g) cor))) x
              s2 = axKT (natCode (BRA2.Thm.Tag.tagAxComp2)) (natCode_isValue (BRA2.Thm.Tag.tagAxComp2)) x
              s3 = axComp2 Pair (KT cF2h)
                                (Comp2 Pair (KT cF1f)
                                  (Comp2 Pair (KT cF1g) cor)) x
              s4 = axKT (codeF2 h) (codeF2_isValue h) x
              s5 = axComp2 Pair (KT cF1f) (Comp2 Pair (KT cF1g) cor) x
              s6 = axKT (codeF1 f') (codeF1_isValue f') x
              s7 = axComp2 Pair (KT cF1g) cor x
              s8 = axKT (codeF1 g) (codeF1_isValue g) x

              ri3 : Deriv (atomic (eqn
                          (ap1 (Comp2 Pair (KT cF1g) cor) x)
                          (ap2 Pair cF1g (ap1 cor x))))
              ri3 = ruleTrans s7 (congL Pair (ap1 cor x) s8)

              ri2 : Deriv (atomic (eqn
                          (ap1 (Comp2 Pair (KT cF1f) (Comp2 Pair (KT cF1g) cor)) x)
                          (ap2 Pair cF1f (ap2 Pair cF1g (ap1 cor x)))))
              ri2 = ruleTrans s5
                      (ruleTrans (congL Pair _ s6)
                                 (congR Pair cF1f ri3))

              ri1 : Deriv (atomic (eqn
                          (ap1 (Comp2 Pair (KT cF2h)
                                  (Comp2 Pair (KT cF1f)
                                    (Comp2 Pair (KT cF1g) cor))) x)
                          (ap2 Pair cF2h (ap2 Pair cF1f (ap2 Pair cF1g (ap1 cor x))))))
              ri1 = ruleTrans s3
                      (ruleTrans (congL Pair _ s4)
                                 (congR Pair cF2h ri2))
          in ruleTrans s1
                (ruleTrans (congL Pair _ s2)
                           (congR Pair (BRA2.Thm.ThmT.tagCode_axComp2) ri1))

        red_enc_g_num : Deriv (atomic (eqn (ap1 enc_g_num x)
                                             (ap2 Pair (reify tagAp1)
                                                       (ap2 Pair cF1g (ap1 cor x)))))
        red_enc_g_num =
          let s1 = axComp2 Pair (KT (reify tagAp1)) (Comp2 Pair (KT cF1g) cor) x
              s2 = axKT lf valO x  -- tagAp1 = nd lf (nd lf lf), reify = Pair O (Pair O O); but axKT takes v, so axKT (reify^-1 ...) — hmm
                              -- Use axKT with appropriate Tree; the actual Tree behind tagAp1 is `nd lf (nd lf lf)`.
                              -- We need axKT (nd lf (nd lf lf)) x.
              -- Re-derive: simpler to write directly.
              s2' = axKT tagAp1 tagAp1_isValue x
              s3 = axComp2 Pair (KT cF1g) cor x
              s4 = axKT (codeF1 g) (codeF1_isValue g) x
              ri = ruleTrans s3 (congL Pair (ap1 cor x) s4)
          in ruleTrans s1
               (ruleTrans (congL Pair _ s2')
                          (congR Pair (reify tagAp1) ri))

        red_y2a : Deriv (atomic (eqn (ap1 y2a_part x)
                                       (parEncCongL h (ap1 Df' x)
                                          (ap2 Pair (reify tagAp1)
                                                    (ap2 Pair cF1g (ap1 cor x))))))
        red_y2a =
          let s1 = axComp2 Pair (KT (BRA2.Thm.ThmT.tagCode_congL))
                                (Comp2 Pair
                                  (Comp2 Pair (KT cF2h) enc_g_num)
                                  Df') x
              s2 = axKT (natCode (BRA2.Thm.Tag.tagCongL)) (natCode_isValue (BRA2.Thm.Tag.tagCongL)) x
              s3 = axComp2 Pair (Comp2 Pair (KT cF2h) enc_g_num) Df' x
              s4 = axComp2 Pair (KT cF2h) enc_g_num x
              s5 = axKT (codeF2 h) (codeF2_isValue h) x
              -- ap1 (Comp2 Pair (KT cF2h) enc_g_num) x = Pair cF2h (enc_g_num x)
              ri_inner = ruleTrans s4
                           (ruleTrans (congL Pair (ap1 enc_g_num x) s5)
                                      (congR Pair cF2h red_enc_g_num))
              ri2 = ruleTrans s3 (congL Pair (ap1 Df' x) ri_inner)
          in ruleTrans s1
               (ruleTrans (congL Pair _ s2)
                          (congR Pair (BRA2.Thm.ThmT.tagCode_congL) ri2))

        red_y2b : Deriv (atomic (eqn (ap1 y2b_part x)
                                       (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))))
        red_y2b =
          let s1 = axComp2 Pair (KT (BRA2.Thm.ThmT.tagCode_congR))
                                (Comp2 Pair
                                  (Comp2 Pair (KT cF2h) corF')
                                  Dg) x
              s2 = axKT (natCode (BRA2.Thm.Tag.tagCongR)) (natCode_isValue (BRA2.Thm.Tag.tagCongR)) x
              s3 = axComp2 Pair (Comp2 Pair (KT cF2h) corF') Dg x
              s4 = axComp2 Pair (KT cF2h) corF' x
              s5 = axKT (codeF2 h) (codeF2_isValue h) x
              s6 = axComp cor f' x
              -- ap1 (Comp2 Pair (KT cF2h) corF') x = Pair cF2h (cor (f' x))
              ri_inner = ruleTrans s4
                           (ruleTrans (congL Pair (ap1 corF' x) s5)
                                      (congR Pair cF2h s6))
              ri2 = ruleTrans s3 (congL Pair (ap1 Dg x) ri_inner)
          in ruleTrans s1
               (ruleTrans (congL Pair _ s2)
                          (congR Pair (BRA2.Thm.ThmT.tagCode_congR) ri2))

        red_y2c : Deriv (atomic (eqn (ap1 y2c_part x) (ap2 D2_h (ap1 f' x) (ap1 g x))))
        red_y2c = axComp2 D2_h f' g x

        -- ====================================================================
        -- Main chain: thmT(D_Comp2_hfg x) = chain via parDispRuleTrans...

        -- y1's image (parDispAxComp2):
        u1_y1 : Term
        u1_y1 = ap2 Pair (reify tagAp1)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp2 IfLf I I))))
                                       (ap2 Pair cF2h (ap2 Pair cF1f cF1g)))
                            (ap1 cor x))
        u2_y1 : Term
        u2_y1 = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h
                    (ap2 Pair (ap2 Pair (reify tagAp1)
                                         (ap2 Pair cF1f (ap1 cor x)))
                              (ap2 Pair (reify tagAp1)
                                         (ap2 Pair cF1g (ap1 cor x)))))

        d_y1 : Deriv (atomic (eqn (ap1 thmT (parEncAxComp2 h f' g (ap1 cor x)))
                                    (ap2 Pair u1_y1 u2_y1)))
        d_y1 = parDispAxComp2 h f' g (ap1 cor x)

        -- D_f' x's image:
        u1_Df : Term
        u1_Df = ap2 Pair (reify tagAp1) (ap2 Pair cF1f (ap1 cor x))
        u2_Df : Term
        u2_Df = ap1 cor (ap1 f' x)

        d_Df : Deriv (atomic (eqn (ap1 thmT (ap1 Df' x))
                                    (ap2 Pair u1_Df u2_Df)))
        d_Df = D_correct_f' x

        -- y2a's image (parDispCongL h (D_f' x) ENC_GUM):
        ENC_GUM : Term
        ENC_GUM = ap2 Pair (reify tagAp1) (ap2 Pair cF1g (ap1 cor x))

        u1_y2a : Term
        u1_y2a = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair u1_Df ENC_GUM))
        u2_y2a : Term
        u2_y2a = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair u2_Df ENC_GUM))

        d_y2a : Deriv (atomic (eqn (ap1 thmT (parEncCongL h (ap1 Df' x) ENC_GUM))
                                     (ap2 Pair u1_y2a u2_y2a)))
        d_y2a = parDispCongL h (ap1 Df' x) ENC_GUM u1_Df u2_Df d_Df

        -- D_g x's image:
        u1_Dg : Term
        u1_Dg = ap2 Pair (reify tagAp1) (ap2 Pair cF1g (ap1 cor x))
        u2_Dg : Term
        u2_Dg = ap1 cor (ap1 g x)

        d_Dg : Deriv (atomic (eqn (ap1 thmT (ap1 Dg x))
                                    (ap2 Pair u1_Dg u2_Dg)))
        d_Dg = D_correct_g x

        -- y2b's image (parDispCongR h (D_g x) (cor(f' x))):
        u1_y2b : Term
        u1_y2b = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair (ap1 cor (ap1 f' x)) u1_Dg))
        u2_y2b : Term
        u2_y2b = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair (ap1 cor (ap1 f' x)) u2_Dg))

        d_y2b : Deriv (atomic (eqn
                  (ap1 thmT (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x))))
                  (ap2 Pair u1_y2b u2_y2b)))
        d_y2b = parDispCongR h (ap1 Dg x) (ap1 cor (ap1 f' x))
                              u1_Dg u2_Dg d_Dg

        -- D2_h (f' x) (g x)'s image:
        u1_D2h : Term
        u1_D2h = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair (ap1 cor (ap1 f' x)) (ap1 cor (ap1 g x))))
        u2_D2h : Term
        u2_D2h = ap1 cor (ap2 h (ap1 f' x) (ap1 g x))

        d_D2h : Deriv (atomic (eqn (ap1 thmT (ap2 D2_h (ap1 f' x) (ap1 g x)))
                                     (ap2 Pair u1_D2h u2_D2h)))
        d_D2h = D_correct_h (ap1 f' x) (ap1 g x)

        -- ====================================================================
        -- Three nested ruleTrans to combine: parDispRuleTrans calls.

        y2b_shape : Deriv (atomic (eqn (ap1 Fst (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x))))
                                         (ap2 Pair O _)))
        y2b_shape = axFst (BRA2.Thm.ThmT.tagCode_congR) _

        d_inner_rt2 : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                          (ap2 D2_h (ap1 f' x) (ap1 g x))))
              (ap2 Pair u1_y2b u2_D2h)))
        d_inner_rt2 = parDispRuleTrans
                        (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                        (ap2 D2_h (ap1 f' x) (ap1 g x))
                        u1_y2b u2_y2b u1_D2h u2_D2h
                        _ _
                        y2b_shape d_y2b d_D2h

        y2a_shape : Deriv (atomic (eqn (ap1 Fst (parEncCongL h (ap1 Df' x) ENC_GUM))
                                         (ap2 Pair O _)))
        y2a_shape = axFst (BRA2.Thm.ThmT.tagCode_congL) _

        d_inner_rt1 : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncCongL h (ap1 Df' x) ENC_GUM)
                          (parEncRuleTrans
                            (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                            (ap2 D2_h (ap1 f' x) (ap1 g x)))))
              (ap2 Pair u1_y2a u2_D2h)))
        d_inner_rt1 = parDispRuleTrans
                        (parEncCongL h (ap1 Df' x) ENC_GUM)
                        (parEncRuleTrans
                          (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                          (ap2 D2_h (ap1 f' x) (ap1 g x)))
                        u1_y2a u2_y2a u1_y2b u2_D2h
                        _ _
                        y2a_shape d_y2a d_inner_rt2

        y1_shape : Deriv (atomic (eqn (ap1 Fst (parEncAxComp2 h f' g (ap1 cor x)))
                                        (ap2 Pair O _)))
        y1_shape = axFst (BRA2.Thm.ThmT.tagCode_axComp2) _

        d_outer : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncAxComp2 h f' g (ap1 cor x))
                          (parEncRuleTrans
                            (parEncCongL h (ap1 Df' x) ENC_GUM)
                            (parEncRuleTrans
                              (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                              (ap2 D2_h (ap1 f' x) (ap1 g x))))))
              (ap2 Pair u1_y1 u2_D2h)))
        d_outer = parDispRuleTrans
                    (parEncAxComp2 h f' g (ap1 cor x))
                    (parEncRuleTrans
                      (parEncCongL h (ap1 Df' x) ENC_GUM)
                      (parEncRuleTrans
                        (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                        (ap2 D2_h (ap1 f' x) (ap1 g x))))
                    u1_y1 u2_y1 u1_y2a u2_D2h
                    _ _
                    y1_shape d_y1 d_inner_rt1

        -- ====================================================================
        -- Combinator reduction of D_Comp2_hfg.

        red_inner_rt2 : Deriv (atomic (eqn (ap1 inner_rt2 x)
              (parEncRuleTrans
                (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                (ap2 D2_h (ap1 f' x) (ap1 g x)))))
        red_inner_rt2 =
          let s1 = axComp2 Pair (KT tagCode_ruleTrans)
                                (Comp2 Pair y2b_part y2c_part) x
              s2 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
              s3 = axComp2 Pair y2b_part y2c_part x
              ri = ruleTrans s3
                      (ruleTrans (congL Pair (ap1 y2c_part x) red_y2b)
                                 (congR Pair _ red_y2c))
          in ruleTrans s1 (ruleTrans (congL Pair _ s2)
                                     (congR Pair tagCode_ruleTrans ri))

        red_inner_rt1 : Deriv (atomic (eqn (ap1 inner_rt1 x)
              (parEncRuleTrans
                (parEncCongL h (ap1 Df' x) ENC_GUM)
                (parEncRuleTrans
                  (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                  (ap2 D2_h (ap1 f' x) (ap1 g x))))))
        red_inner_rt1 =
          let s1 = axComp2 Pair (KT tagCode_ruleTrans)
                                (Comp2 Pair y2a_part inner_rt2) x
              s2 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
              s3 = axComp2 Pair y2a_part inner_rt2 x
              ri = ruleTrans s3
                      (ruleTrans (congL Pair (ap1 inner_rt2 x) red_y2a)
                                 (congR Pair _ red_inner_rt2))
          in ruleTrans s1 (ruleTrans (congL Pair _ s2)
                                     (congR Pair tagCode_ruleTrans ri))

        red_full : Deriv (atomic (eqn (ap1 D_Comp2_hfg x)
              (parEncRuleTrans
                (parEncAxComp2 h f' g (ap1 cor x))
                (parEncRuleTrans
                  (parEncCongL h (ap1 Df' x) ENC_GUM)
                  (parEncRuleTrans
                    (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                    (ap2 D2_h (ap1 f' x) (ap1 g x)))))))
        red_full =
          let s1 = axComp2 Pair (KT tagCode_ruleTrans)
                                (Comp2 Pair y1_part inner_rt1) x
              s2 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
              s3 = axComp2 Pair y1_part inner_rt1 x
              ri = ruleTrans s3
                      (ruleTrans (congL Pair (ap1 inner_rt1 x) red_y1)
                                 (congR Pair _ red_inner_rt1))
          in ruleTrans s1 (ruleTrans (congL Pair _ s2)
                                     (congR Pair tagCode_ruleTrans ri))

        thmT_red : Deriv (atomic (eqn
              (ap1 thmT (ap1 D_Comp2_hfg x))
              (ap1 thmT (parEncRuleTrans
                          (parEncAxComp2 h f' g (ap1 cor x))
                          (parEncRuleTrans
                            (parEncCongL h (ap1 Df' x) ENC_GUM)
                            (parEncRuleTrans
                              (parEncCongR h (ap1 Dg x) (ap1 cor (ap1 f' x)))
                              (ap2 D2_h (ap1 f' x) (ap1 g x))))))))
        thmT_red = cong1 thmT red_full

        -- Bridge: u2_D2h = cor(h(f' x, g x)) -> cor((Comp2 h f' g) x).
        sym_bridge : Deriv (atomic (eqn (ap1 cor (ap2 h (ap1 f' x) (ap1 g x)))
                                          (ap1 cor (ap1 (Comp2 h f' g) x))))
        sym_bridge = ruleSym (cong1 cor (axComp2 h f' g x))

        bridge : Deriv (atomic (eqn (ap2 Pair u1_y1 u2_D2h) (codeFTeq1_Comp2 x)))
        bridge = congR Pair u1_y1 sym_bridge

    in ruleTrans thmT_red (ruleTrans d_outer bridge)
