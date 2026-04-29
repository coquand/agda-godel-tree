{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.Fan
--
-- Theorem 12 case for g = Fan h1 h2 h (Fun2 with 3 Fun2 sub-args).
-- Recursive: takes D2_h1, D2_h2, D2_h (Fun2 IHs) and shape hypotheses
-- for D2_h1, D2_h2 (used as y1 of inner parDispRuleTrans calls).
--
-- BRA equation behind: ap2 (Fan h1 h2 h) a b = ap2 h (ap2 h1 a b) (ap2 h2 a b).
--
-- Encoded chain (Guard's pattern):
--   D2_(Fan h1 h2 h) x v = encRT y1 (encRT y2a (encRT y2b y2c))
--     y1  = parEncAxFan h1 h2 h (cor x) (cor v)
--               -- (Fan h1 h2 h)(num x, num v) = h(h1 num x v, h2 num x v)
--     y2a = parEncCongL h (D2_h1 x v) ENC_H2NUM
--               -- h(h1 num x v, h2 num x v) = h(num(h1 x v), h2 num x v)
--     y2b = parEncCongR h (D2_h2 x v) (cor (h1 x v))
--               -- h(num(h1 x v), h2 num x v) = h(num(h1 x v), num(h2 x v))
--     y2c = D2_h (h1 x v) (h2 x v)
--               -- h(num(h1 x v), num(h2 x v)) = num(h(h1 x v, h2 x v))
-- Bridge: cor(h(h1 x v, h2 x v)) -> cor((Fan h1 h2 h) x v) via cong1 cor + axFan + ruleSym.

module BRA.Thm12.Parts.Fan where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagRuleTrans)
open import BRA.Thm.ThmT
  using (thmT ; tagCode_ruleTrans)
open import BRA.Thm12.Param.AxFan
  using (parDispAxFan ; parEncAxFan)
open import BRA.Thm12.Param.CongL
  using (parDispCongL ; parEncCongL)
open import BRA.Thm12.Param.CongR
  using (parDispCongR ; parEncCongR)
open import BRA.Thm12.Param.RuleTrans
  using (parDispRuleTrans ; parEncRuleTrans)

module FanCase
  (h1 h2 h : Fun2)
  (D2_h1 D2_h2 D2_h : Fun2)
  (D_correct_h1 : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h1 x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h1))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h1 x v))))))
  (D_correct_h2 : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h2 x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h2))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h2 x v))))))
  (D_correct_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
  (D2_h1_shape : (x v : Term) ->
     Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst (ap2 D2_h1 x v)) (ap2 Pair x' y'))))))
  (D2_h2_shape : (x v : Term) ->
     Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst (ap2 D2_h2 x v)) (ap2 Pair x' y'))))))
  where

  ----------------------------------------------------------------------
  -- The asymmetric encoded equation (matches the Fun2 IH form).

  codeFTeq2_Fan : Term -> Term -> Term
  codeFTeq2_Fan x v =
    ap2 Pair
      (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 (Fan h1 h2 h)))
                          (ap2 Pair (ap1 cor x) (ap1 cor v))))
      (ap1 cor (ap2 (Fan h1 h2 h) x v))

  ----------------------------------------------------------------------
  -- D2_Fan_h1h2h : Fun2 .
  --
  -- Built from sub-builders.  Each is a Fun2 of (x, v) producing the
  -- corresponding encoded sub-witness.

  private
    cF2h1 : Term
    cF2h1 = reify (codeF2 h1)
    cF2h2 : Term
    cF2h2 = reify (codeF2 h2)
    cF2h  : Term
    cF2h  = reify (codeF2 h)

    -- corLeft : Fun2 producing cor of LEFT arg.  ap2 corLeft x v = ap1 cor x.
    corLeft : Fun2
    corLeft = Lift cor

    -- corRight : Fun2 producing cor of RIGHT arg.  ap2 corRight x v = ap1 cor v.
    corRight : Fun2
    corRight = Post cor (Post Snd Pair)

    -- pair_corxv : ap2 pair_corxv x v = Pair (cor x) (cor v).
    pair_corxv : Fun2
    pair_corxv = Fan corLeft corRight Pair

    -- y1_part : Fun2.
    --   ap2 y1_part x v = parEncAxFan h1 h2 h (cor x) (cor v)
    --                   = Pair tagCode_axFan
    --                       (Pair cF2h1 (Pair cF2h2 (Pair cF2h (Pair (cor x) (cor v))))).
    y1_inner4 : Fun2
    y1_inner4 = Fan (Lift (KT cF2h)) pair_corxv Pair

    y1_inner3 : Fun2
    y1_inner3 = Fan (Lift (KT cF2h2)) y1_inner4 Pair

    y1_inner2 : Fun2
    y1_inner2 = Fan (Lift (KT cF2h1)) y1_inner3 Pair

    y1_part : Fun2
    y1_part = Fan (Lift (KT BRA.Thm.ThmT.tagCode_axFan)) y1_inner2 Pair

    -- enc_h2_num : ap2 enc_h2_num x v = Pair tagAp2 (Pair cF2h2 (Pair (cor x) (cor v))).
    enc_h2_num_inner : Fun2
    enc_h2_num_inner = Fan (Lift (KT cF2h2)) pair_corxv Pair

    enc_h2_num : Fun2
    enc_h2_num = Fan (Lift (KT (reify tagAp2))) enc_h2_num_inner Pair

    -- y2a_part : Fun2.
    --   ap2 y2a_part x v = parEncCongL h (D2_h1 x v) (enc_h2_num x v)
    --                    = Pair tagCode_congL (Pair cF2h (Pair (D2_h1 x v) (enc_h2_num x v))).
    y2a_inner3 : Fun2
    y2a_inner3 = Fan D2_h1 enc_h2_num Pair

    y2a_inner2 : Fun2
    y2a_inner2 = Fan (Lift (KT cF2h)) y2a_inner3 Pair

    y2a_part : Fun2
    y2a_part = Fan (Lift (KT BRA.Thm.ThmT.tagCode_congL)) y2a_inner2 Pair

    -- corF1_h1 : ap2 corF1_h1 x v = cor (ap2 h1 x v).
    corF1_h1 : Fun2
    corF1_h1 = Post cor h1

    -- y2b_part : Fun2.
    --   ap2 y2b_part x v = parEncCongR h (D2_h2 x v) (cor (h1 x v))
    --                    = Pair tagCode_congR (Pair cF2h (Pair (D2_h2 x v) (cor (h1 x v)))).
    y2b_inner3 : Fun2
    y2b_inner3 = Fan D2_h2 corF1_h1 Pair

    y2b_inner2 : Fun2
    y2b_inner2 = Fan (Lift (KT cF2h)) y2b_inner3 Pair

    y2b_part : Fun2
    y2b_part = Fan (Lift (KT BRA.Thm.ThmT.tagCode_congR)) y2b_inner2 Pair

    -- y2c_part : Fun2.
    --   ap2 y2c_part x v = ap2 D2_h (ap2 h1 x v) (ap2 h2 x v).
    y2c_part : Fun2
    y2c_part = Fan h1 h2 D2_h

    -- inner_rt2 : ap2 inner_rt2 x v = parEncRuleTrans (y2b x v) (y2c x v).
    inner_rt2_pair : Fun2
    inner_rt2_pair = Fan y2b_part y2c_part Pair

    inner_rt2 : Fun2
    inner_rt2 = Fan (Lift (KT tagCode_ruleTrans)) inner_rt2_pair Pair

    -- inner_rt1 : ap2 inner_rt1 x v = parEncRuleTrans (y2a x v) (inner_rt2 x v).
    inner_rt1_pair : Fun2
    inner_rt1_pair = Fan y2a_part inner_rt2 Pair

    inner_rt1 : Fun2
    inner_rt1 = Fan (Lift (KT tagCode_ruleTrans)) inner_rt1_pair Pair

  D2_Fan_h1h2h : Fun2
  D2_Fan_h1h2h =
    Fan (Lift (KT tagCode_ruleTrans))
        (Fan y1_part inner_rt1 Pair)
        Pair

  ----------------------------------------------------------------------
  -- D_correct2_Fan_h1h2h .

  D_correct2_Fan_h1h2h : (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_Fan_h1h2h x v)) (codeFTeq2_Fan x v)))
  D_correct2_Fan_h1h2h x v =
    let -- ====================================================================
        -- Sub-builder reductions: each Fun2 sub-builder reduces via Fan/Lift/KT.

        -- pair_corxv reduces to Pair (cor x) (cor v).
        red_corLeft : Deriv (atomic (eqn (ap2 corLeft x v) (ap1 cor x)))
        red_corLeft = axLift cor x v

        red_corRight_a : Deriv (atomic (eqn (ap2 corRight x v)
                                             (ap1 cor (ap2 (Post Snd Pair) x v))))
        red_corRight_a = axPost cor (Post Snd Pair) x v
        red_corRight_b : Deriv (atomic (eqn (ap2 (Post Snd Pair) x v) v))
        red_corRight_b = ruleTrans (axPost Snd Pair x v) (axSnd x v)
        red_corRight : Deriv (atomic (eqn (ap2 corRight x v) (ap1 cor v)))
        red_corRight = ruleTrans red_corRight_a (cong1 cor red_corRight_b)

        red_pair_corxv : Deriv (atomic (eqn (ap2 pair_corxv x v)
                                              (ap2 Pair (ap1 cor x) (ap1 cor v))))
        red_pair_corxv =
          ruleTrans (axFan corLeft corRight Pair x v)
            (ruleTrans (congL Pair (ap2 corRight x v) red_corLeft)
                       (congR Pair (ap1 cor x) red_corRight))

        -- y1_inner4 reduces to Pair cF2h (Pair (cor x) (cor v)).
        red_y1_inner4 : Deriv (atomic (eqn (ap2 y1_inner4 x v)
                          (ap2 Pair cF2h (ap2 Pair (ap1 cor x) (ap1 cor v)))))
        red_y1_inner4 =
          let s1 = axFan (Lift (KT cF2h)) pair_corxv Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT cF2h)) x v) cF2h))
              s2 = ruleTrans (axLift (KT cF2h) x v) (axKT (codeF2 h) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 pair_corxv x v) s2)
                          (congR Pair cF2h red_pair_corxv))

        red_y1_inner3 : Deriv (atomic (eqn (ap2 y1_inner3 x v)
                          (ap2 Pair cF2h2
                            (ap2 Pair cF2h (ap2 Pair (ap1 cor x) (ap1 cor v))))))
        red_y1_inner3 =
          let s1 = axFan (Lift (KT cF2h2)) y1_inner4 Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT cF2h2)) x v) cF2h2))
              s2 = ruleTrans (axLift (KT cF2h2) x v) (axKT (codeF2 h2) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y1_inner4 x v) s2)
                          (congR Pair cF2h2 red_y1_inner4))

        red_y1_inner2 : Deriv (atomic (eqn (ap2 y1_inner2 x v)
                          (ap2 Pair cF2h1
                            (ap2 Pair cF2h2
                              (ap2 Pair cF2h (ap2 Pair (ap1 cor x) (ap1 cor v)))))))
        red_y1_inner2 =
          let s1 = axFan (Lift (KT cF2h1)) y1_inner3 Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT cF2h1)) x v) cF2h1))
              s2 = ruleTrans (axLift (KT cF2h1) x v) (axKT (codeF2 h1) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y1_inner3 x v) s2)
                          (congR Pair cF2h1 red_y1_inner3))

        red_y1 : Deriv (atomic (eqn (ap2 y1_part x v)
                                      (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v))))
        red_y1 =
          let s1 = axFan (Lift (KT BRA.Thm.ThmT.tagCode_axFan)) y1_inner2 Pair x v
              s2 : Deriv (atomic (eqn
                          (ap2 (Lift (KT BRA.Thm.ThmT.tagCode_axFan)) x v)
                          BRA.Thm.ThmT.tagCode_axFan))
              s2 = ruleTrans (axLift (KT BRA.Thm.ThmT.tagCode_axFan) x v)
                             (axKT (natCode BRA.Thm.Tag.tagAxFan) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y1_inner2 x v) s2)
                          (congR Pair BRA.Thm.ThmT.tagCode_axFan red_y1_inner2))

        -- enc_h2_num reduces to Pair tagAp2 (Pair cF2h2 (Pair (cor x) (cor v))).
        red_enc_h2_num_inner : Deriv (atomic (eqn (ap2 enc_h2_num_inner x v)
                                  (ap2 Pair cF2h2
                                    (ap2 Pair (ap1 cor x) (ap1 cor v)))))
        red_enc_h2_num_inner =
          let s1 = axFan (Lift (KT cF2h2)) pair_corxv Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT cF2h2)) x v) cF2h2))
              s2 = ruleTrans (axLift (KT cF2h2) x v) (axKT (codeF2 h2) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 pair_corxv x v) s2)
                          (congR Pair cF2h2 red_pair_corxv))

        red_enc_h2_num : Deriv (atomic (eqn (ap2 enc_h2_num x v)
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair cF2h2
                              (ap2 Pair (ap1 cor x) (ap1 cor v))))))
        red_enc_h2_num =
          let s1 = axFan (Lift (KT (reify tagAp2))) enc_h2_num_inner Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT (reify tagAp2))) x v)
                                       (reify tagAp2)))
              s2 = ruleTrans (axLift (KT (reify tagAp2)) x v) (axKT tagAp2 x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 enc_h2_num_inner x v) s2)
                          (congR Pair (reify tagAp2) red_enc_h2_num_inner))

        -- y2a_inner3 reduces to Pair (D2_h1 x v) (enc_h2_num x v).
        red_y2a_inner3 : Deriv (atomic (eqn (ap2 y2a_inner3 x v)
                          (ap2 Pair (ap2 D2_h1 x v)
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair cF2h2
                                (ap2 Pair (ap1 cor x) (ap1 cor v)))))))
        red_y2a_inner3 =
          let s1 = axFan D2_h1 enc_h2_num Pair x v
          in ruleTrans s1 (congR Pair (ap2 D2_h1 x v) red_enc_h2_num)

        red_y2a_inner2 : Deriv (atomic (eqn (ap2 y2a_inner2 x v)
                          (ap2 Pair cF2h
                            (ap2 Pair (ap2 D2_h1 x v)
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair cF2h2
                                  (ap2 Pair (ap1 cor x) (ap1 cor v))))))))
        red_y2a_inner2 =
          let s1 = axFan (Lift (KT cF2h)) y2a_inner3 Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT cF2h)) x v) cF2h))
              s2 = ruleTrans (axLift (KT cF2h) x v) (axKT (codeF2 h) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y2a_inner3 x v) s2)
                          (congR Pair cF2h red_y2a_inner3))

        red_y2a : Deriv (atomic (eqn (ap2 y2a_part x v)
                          (parEncCongL h (ap2 D2_h1 x v)
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair cF2h2
                                (ap2 Pair (ap1 cor x) (ap1 cor v)))))))
        red_y2a =
          let s1 = axFan (Lift (KT BRA.Thm.ThmT.tagCode_congL)) y2a_inner2 Pair x v
              s2 : Deriv (atomic (eqn
                          (ap2 (Lift (KT BRA.Thm.ThmT.tagCode_congL)) x v)
                          BRA.Thm.ThmT.tagCode_congL))
              s2 = ruleTrans (axLift (KT BRA.Thm.ThmT.tagCode_congL) x v)
                             (axKT (natCode BRA.Thm.Tag.tagCongL) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y2a_inner2 x v) s2)
                          (congR Pair BRA.Thm.ThmT.tagCode_congL red_y2a_inner2))

        -- corF1_h1 reduces to cor (h1 x v).
        red_corF1_h1 : Deriv (atomic (eqn (ap2 corF1_h1 x v) (ap1 cor (ap2 h1 x v))))
        red_corF1_h1 = axPost cor h1 x v

        -- y2b_inner3 reduces to Pair (D2_h2 x v) (cor (h1 x v)).
        red_y2b_inner3 : Deriv (atomic (eqn (ap2 y2b_inner3 x v)
                          (ap2 Pair (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))))
        red_y2b_inner3 =
          let s1 = axFan D2_h2 corF1_h1 Pair x v
          in ruleTrans s1 (congR Pair (ap2 D2_h2 x v) red_corF1_h1)

        red_y2b_inner2 : Deriv (atomic (eqn (ap2 y2b_inner2 x v)
                          (ap2 Pair cF2h
                            (ap2 Pair (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v))))))
        red_y2b_inner2 =
          let s1 = axFan (Lift (KT cF2h)) y2b_inner3 Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT cF2h)) x v) cF2h))
              s2 = ruleTrans (axLift (KT cF2h) x v) (axKT (codeF2 h) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y2b_inner3 x v) s2)
                          (congR Pair cF2h red_y2b_inner3))

        red_y2b : Deriv (atomic (eqn (ap2 y2b_part x v)
                          (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))))
        red_y2b =
          let s1 = axFan (Lift (KT BRA.Thm.ThmT.tagCode_congR)) y2b_inner2 Pair x v
              s2 : Deriv (atomic (eqn
                          (ap2 (Lift (KT BRA.Thm.ThmT.tagCode_congR)) x v)
                          BRA.Thm.ThmT.tagCode_congR))
              s2 = ruleTrans (axLift (KT BRA.Thm.ThmT.tagCode_congR) x v)
                             (axKT (natCode BRA.Thm.Tag.tagCongR) x)
          in ruleTrans s1
               (ruleTrans (congL Pair (ap2 y2b_inner2 x v) s2)
                          (congR Pair BRA.Thm.ThmT.tagCode_congR red_y2b_inner2))

        -- y2c reduces via axFan: ap2 (Fan h1 h2 D2_h) x v = ap2 D2_h (h1 x v) (h2 x v).
        red_y2c : Deriv (atomic (eqn (ap2 y2c_part x v)
                                       (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))))
        red_y2c = axFan h1 h2 D2_h x v

        -- ====================================================================
        -- Main chain: parDispRuleTrans calls.

        -- y1's image (parDispAxFan):
        u1_y1 : Term
        u1_y1 = ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Fan IfLf IfLf IfLf))))
                                       (ap2 Pair cF2h1 (ap2 Pair cF2h2 cF2h)))
                            (ap2 Pair (ap1 cor x) (ap1 cor v)))
        u2_y1 : Term
        u2_y1 = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h
                    (ap2 Pair (ap2 Pair (reify tagAp2)
                                         (ap2 Pair cF2h1 (ap2 Pair (ap1 cor x) (ap1 cor v))))
                              (ap2 Pair (reify tagAp2)
                                         (ap2 Pair cF2h2 (ap2 Pair (ap1 cor x) (ap1 cor v))))))

        d_y1 : Deriv (atomic (eqn (ap1 thmT (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v)))
                                    (ap2 Pair u1_y1 u2_y1)))
        d_y1 = parDispAxFan h1 h2 h (ap1 cor x) (ap1 cor v)

        -- D_h1 image:
        u1_Dh1 : Term
        u1_Dh1 = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h1 (ap2 Pair (ap1 cor x) (ap1 cor v)))
        u2_Dh1 : Term
        u2_Dh1 = ap1 cor (ap2 h1 x v)

        d_Dh1 : Deriv (atomic (eqn (ap1 thmT (ap2 D2_h1 x v))
                                    (ap2 Pair u1_Dh1 u2_Dh1)))
        d_Dh1 = D_correct_h1 x v

        -- ENC_H2NUM = encoded h2(cor x, cor v).
        ENC_H2NUM : Term
        ENC_H2NUM = ap2 Pair (reify tagAp2)
                      (ap2 Pair cF2h2 (ap2 Pair (ap1 cor x) (ap1 cor v)))

        -- y2a's image (parDispCongL):
        u1_y2a : Term
        u1_y2a = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair u1_Dh1 ENC_H2NUM))
        u2_y2a : Term
        u2_y2a = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair u2_Dh1 ENC_H2NUM))

        d_Dh1_shape = snd (snd (D2_h1_shape x v))

        d_y2a : Deriv (atomic (eqn
                  (ap1 thmT (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM))
                  (ap2 Pair u1_y2a u2_y2a)))
        d_y2a = parDispCongL h (ap2 D2_h1 x v) ENC_H2NUM
                              u1_Dh1 u2_Dh1 _ _ d_Dh1_shape d_Dh1

        -- D_h2 image:
        u1_Dh2 : Term
        u1_Dh2 = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h2 (ap2 Pair (ap1 cor x) (ap1 cor v)))
        u2_Dh2 : Term
        u2_Dh2 = ap1 cor (ap2 h2 x v)

        d_Dh2 : Deriv (atomic (eqn (ap1 thmT (ap2 D2_h2 x v))
                                    (ap2 Pair u1_Dh2 u2_Dh2)))
        d_Dh2 = D_correct_h2 x v

        -- y2b's image (parDispCongR with xT = cor (h1 x v)):
        u1_y2b : Term
        u1_y2b = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair (ap1 cor (ap2 h1 x v)) u1_Dh2))
        u2_y2b : Term
        u2_y2b = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h (ap2 Pair (ap1 cor (ap2 h1 x v)) u2_Dh2))

        d_Dh2_shape = snd (snd (D2_h2_shape x v))

        d_y2b : Deriv (atomic (eqn
                  (ap1 thmT (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v))))
                  (ap2 Pair u1_y2b u2_y2b)))
        d_y2b = parDispCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v))
                              u1_Dh2 u2_Dh2 _ _ d_Dh2_shape d_Dh2

        -- D2_h applied at (h1 x v, h2 x v):
        u1_D2h : Term
        u1_D2h = ap2 Pair (reify tagAp2)
                  (ap2 Pair cF2h
                    (ap2 Pair (ap1 cor (ap2 h1 x v)) (ap1 cor (ap2 h2 x v))))
        u2_D2h : Term
        u2_D2h = ap1 cor (ap2 h (ap2 h1 x v) (ap2 h2 x v))

        d_D2h : Deriv (atomic (eqn (ap1 thmT (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v)))
                                    (ap2 Pair u1_D2h u2_D2h)))
        d_D2h = D_correct_h (ap2 h1 x v) (ap2 h2 x v)

        -- ====================================================================
        -- Three nested parDispRuleTrans calls.

        y2b_shape : Deriv (atomic (eqn
                      (ap1 Fst (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v))))
                      (ap2 Pair O _)))
        y2b_shape = axFst BRA.Thm.ThmT.tagCode_congR _

        d_inner_rt2 : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                          (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))))
              (ap2 Pair u1_y2b u2_D2h)))
        d_inner_rt2 = parDispRuleTrans
                        (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                        (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))
                        u1_y2b u2_y2b u1_D2h u2_D2h
                        _ _
                        y2b_shape d_y2b d_D2h

        y2a_shape : Deriv (atomic (eqn
                      (ap1 Fst (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM))
                      (ap2 Pair O _)))
        y2a_shape = axFst BRA.Thm.ThmT.tagCode_congL _

        d_inner_rt1 : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                          (parEncRuleTrans
                            (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                            (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v)))))
              (ap2 Pair u1_y2a u2_D2h)))
        d_inner_rt1 = parDispRuleTrans
                        (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                        (parEncRuleTrans
                          (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                          (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v)))
                        u1_y2a u2_y2a u1_y2b u2_D2h
                        _ _
                        y2a_shape d_y2a d_inner_rt2

        y1_shape : Deriv (atomic (eqn
                      (ap1 Fst (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v)))
                      (ap2 Pair O _)))
        y1_shape = axFst BRA.Thm.ThmT.tagCode_axFan _

        d_outer : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v))
                          (parEncRuleTrans
                            (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                            (parEncRuleTrans
                              (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                              (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))))))
              (ap2 Pair u1_y1 u2_D2h)))
        d_outer = parDispRuleTrans
                    (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v))
                    (parEncRuleTrans
                      (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                      (parEncRuleTrans
                        (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                        (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))))
                    u1_y1 u2_y1 u1_y2a u2_D2h
                    _ _
                    y1_shape d_y1 d_inner_rt1

        -- ====================================================================
        -- Combinator reduction of D2_Fan_h1h2h.

        red_inner_rt2 : Deriv (atomic (eqn (ap2 inner_rt2 x v)
              (parEncRuleTrans
                (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v)))))
        red_inner_rt2 =
          let s1 = axFan (Lift (KT tagCode_ruleTrans)) inner_rt2_pair Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) x v)
                                       tagCode_ruleTrans))
              s2 = ruleTrans (axLift (KT tagCode_ruleTrans) x v)
                             (axKT (natCode tagRuleTrans) x)
              s3 = axFan y2b_part y2c_part Pair x v
              ri = ruleTrans s3
                      (ruleTrans (congL Pair (ap2 y2c_part x v) red_y2b)
                                 (congR Pair _ red_y2c))
          in ruleTrans s1 (ruleTrans (congL Pair _ s2)
                                     (congR Pair tagCode_ruleTrans ri))

        red_inner_rt1 : Deriv (atomic (eqn (ap2 inner_rt1 x v)
              (parEncRuleTrans
                (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                (parEncRuleTrans
                  (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                  (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))))))
        red_inner_rt1 =
          let s1 = axFan (Lift (KT tagCode_ruleTrans)) inner_rt1_pair Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) x v)
                                       tagCode_ruleTrans))
              s2 = ruleTrans (axLift (KT tagCode_ruleTrans) x v)
                             (axKT (natCode tagRuleTrans) x)
              s3 = axFan y2a_part inner_rt2 Pair x v
              ri = ruleTrans s3
                      (ruleTrans (congL Pair (ap2 inner_rt2 x v) red_y2a)
                                 (congR Pair _ red_inner_rt2))
          in ruleTrans s1 (ruleTrans (congL Pair _ s2)
                                     (congR Pair tagCode_ruleTrans ri))

        red_full : Deriv (atomic (eqn (ap2 D2_Fan_h1h2h x v)
              (parEncRuleTrans
                (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v))
                (parEncRuleTrans
                  (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                  (parEncRuleTrans
                    (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                    (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v)))))))
        red_full =
          let s1 = axFan (Lift (KT tagCode_ruleTrans))
                         (Fan y1_part inner_rt1 Pair) Pair x v
              s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) x v)
                                       tagCode_ruleTrans))
              s2 = ruleTrans (axLift (KT tagCode_ruleTrans) x v)
                             (axKT (natCode tagRuleTrans) x)
              s3 = axFan y1_part inner_rt1 Pair x v
              ri = ruleTrans s3
                      (ruleTrans (congL Pair (ap2 inner_rt1 x v) red_y1)
                                 (congR Pair _ red_inner_rt1))
          in ruleTrans s1 (ruleTrans (congL Pair _ s2)
                                     (congR Pair tagCode_ruleTrans ri))

        thmT_red : Deriv (atomic (eqn
              (ap1 thmT (ap2 D2_Fan_h1h2h x v))
              (ap1 thmT (parEncRuleTrans
                          (parEncAxFan h1 h2 h (ap1 cor x) (ap1 cor v))
                          (parEncRuleTrans
                            (parEncCongL h (ap2 D2_h1 x v) ENC_H2NUM)
                            (parEncRuleTrans
                              (parEncCongR h (ap2 D2_h2 x v) (ap1 cor (ap2 h1 x v)))
                              (ap2 D2_h (ap2 h1 x v) (ap2 h2 x v))))))))
        thmT_red = cong1 thmT red_full

        -- Bridge: u2_D2h = cor(h(h1 x v, h2 x v)) -> cor((Fan h1 h2 h) x v).
        sym_bridge : Deriv (atomic (eqn (ap1 cor (ap2 h (ap2 h1 x v) (ap2 h2 x v)))
                                          (ap1 cor (ap2 (Fan h1 h2 h) x v))))
        sym_bridge = ruleSym (cong1 cor (axFan h1 h2 h x v))

        bridge : Deriv (atomic (eqn (ap2 Pair u1_y1 u2_D2h) (codeFTeq2_Fan x v)))
        bridge = congR Pair u1_y1 sym_bridge

    in ruleTrans thmT_red (ruleTrans d_outer bridge)
