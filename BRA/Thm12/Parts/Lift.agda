{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.Lift
--
-- Theorem 12 case for g = Lift f : Fun2 (recursive in f : Fun1).
--
-- BRA equation behind: (Lift f)(num a, num b) = num((Lift f)(a, b)).
-- Reduces via axLift + IH on f, threaded through ruleTrans.
--
-- Proof tree pi_(Lift f)(a, b):
--   ruleTrans
--     (axLift f (cor a) (cor b))         -- (Lift f)(num a, num b) = f(num a)
--     (D_correct_f hypothesis at a)        -- f(num a) = num(f a)
-- + bridge cor(f a) -> cor((Lift f)(a, b)) via cong1 cor + axLift + ruleSym.
--
-- Encoded form: encRuleTrans (parEncAxLift f (cor a) (cor b)) (D_f a).
-- Then th-image bridges to codeFTeq2_Lift via congR Pair on the RHS slot.
--
-- Takes  D_f : Fun1  and  D_correct_f : ...  as IH parameters (per the
-- planning doc's recursive-Parts pattern).  The glue file BRA/Thm12.agda
-- instantiates with the recursively-built D f.

module BRA.Thm12.Parts.Lift where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxLift ; tagRuleTrans)
open import BRA.Thm.ThmT using (thmT ; tagCode_axLift ; tagCode_ruleTrans)
open import BRA.Thm12.Param.AxLift
  using (parDispAxLift ; parEncAxLift ; parOutAxLift)
open import BRA.Thm12.Param.RuleTrans
  using (parDispRuleTrans ; parEncRuleTrans)

module LiftCase
  (f : Fun1)
  (Df : Fun1)
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  where

  ----------------------------------------------------------------------
  -- D2_Lift_f : Fun2.
  --
  -- ap2 D2_Lift_f a b =
  --   parEncRuleTrans (parEncAxLift f (cor a) (cor b)) (Df a)
  -- = Pair tagCode_ruleTrans (Pair (parEncAxLift f (cor a) (cor b)) (Df a))
  --
  -- As Fun2, built using Comp2 Pair, KT, Comp, etc.

  -- Helper: parEncAxLift f as a Fun2 of (a, b) via cor on each arg.
  --   ap2 lift_part_f a b = parEncAxLift f (cor a) (cor b)
  private
    lift_part : Fun2
    lift_part =
      Fan (Lift (KT tagCode_axLift))
          (Fan (Lift (KT (reify (codeF1 f))))
               (Fan (Lift cor) (Post cor (Post Snd Pair)) Pair)
               Pair)
          Pair

    -- Helper: Df applied to first arg only (drop second).
    --   ap2 df_first a b = ap1 Df a
    df_first : Fun2
    df_first = Lift Df

  D2_Lift_f : Fun2
  D2_Lift_f =
    Fan (Lift (KT tagCode_ruleTrans))
        (Fan lift_part df_first Pair)
        Pair

  codeFTeq2_Lift : Term -> Term -> Term
  codeFTeq2_Lift a b =
    ap2 Pair
      (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 (Lift f)))
                          (ap2 Pair (ap1 cor a) (ap1 cor b))))
      (ap1 cor (ap2 (Lift f) a b))

  ----------------------------------------------------------------------
  -- Combinator reduction:
  --   ap2 D2_Lift_f a b = parEncRuleTrans (parEncAxLift f (cor a) (cor b)) (Df a)

  D2_Lift_reduce : (a b : Term) ->
    Deriv (atomic (eqn
      (ap2 D2_Lift_f a b)
      (parEncRuleTrans (parEncAxLift f (ap1 cor a) (ap1 cor b))
                       (ap1 Df a))))
  D2_Lift_reduce a b =
    let -- Outer Fan unfolds.
        s1 : Deriv (atomic (eqn (ap2 D2_Lift_f a b)
                (ap2 Pair (ap2 (Lift (KT tagCode_ruleTrans)) a b)
                          (ap2 (Fan lift_part df_first Pair) a b))))
        s1 = axFan (Lift (KT tagCode_ruleTrans))
                   (Fan lift_part df_first Pair) Pair a b

        -- Lift KT reduces to constant.
        s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) a b)
                                 tagCode_ruleTrans))
        s2 = ruleTrans (axLift (KT tagCode_ruleTrans) a b)
                       (axKT (natCode tagRuleTrans) a)

        -- Inner Fan unfolds.
        s3 : Deriv (atomic (eqn (ap2 (Fan lift_part df_first Pair) a b)
                (ap2 Pair (ap2 lift_part a b) (ap2 df_first a b))))
        s3 = axFan lift_part df_first Pair a b

        -- ap2 df_first a b = ap1 Df a (via axLift).
        s4 : Deriv (atomic (eqn (ap2 df_first a b) (ap1 Df a)))
        s4 = axLift Df a b

        -- ap2 lift_part a b reduces step by step.
        -- lift_part = Fan (Lift (KT tagCode_axLift))
        --                 (Fan (Lift (KT codeF1f)) (Fan (Lift cor) (Post cor (Post Snd Pair)) Pair) Pair)
        --                 Pair
        codeF1f_T : Term
        codeF1f_T = reify (codeF1 f)

        inner1 : Fun2
        inner1 = Fan (Lift cor) (Post cor (Post Snd Pair)) Pair

        inner2 : Fun2
        inner2 = Fan (Lift (KT codeF1f_T)) inner1 Pair

        l1 : Deriv (atomic (eqn (ap2 lift_part a b)
                (ap2 Pair (ap2 (Lift (KT tagCode_axLift)) a b)
                          (ap2 inner2 a b))))
        l1 = axFan (Lift (KT tagCode_axLift)) inner2 Pair a b

        l2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axLift)) a b)
                                 tagCode_axLift))
        l2 = ruleTrans (axLift (KT tagCode_axLift) a b)
                       (axKT (natCode tagAxLift) a)

        l3 : Deriv (atomic (eqn (ap2 inner2 a b)
                (ap2 Pair (ap2 (Lift (KT codeF1f_T)) a b)
                          (ap2 inner1 a b))))
        l3 = axFan (Lift (KT codeF1f_T)) inner1 Pair a b

        l4 : Deriv (atomic (eqn (ap2 (Lift (KT codeF1f_T)) a b) codeF1f_T))
        l4 = ruleTrans (axLift (KT codeF1f_T) a b) (axKT (codeF1 f) a)

        l5 : Deriv (atomic (eqn (ap2 inner1 a b)
                (ap2 Pair (ap2 (Lift cor) a b) (ap2 (Post cor (Post Snd Pair)) a b))))
        l5 = axFan (Lift cor) (Post cor (Post Snd Pair)) Pair a b

        l6 : Deriv (atomic (eqn (ap2 (Lift cor) a b) (ap1 cor a)))
        l6 = axLift cor a b

        l7a : Deriv (atomic (eqn (ap2 (Post cor (Post Snd Pair)) a b)
                                  (ap1 cor (ap2 (Post Snd Pair) a b))))
        l7a = axPost cor (Post Snd Pair) a b
        l7b : Deriv (atomic (eqn (ap2 (Post Snd Pair) a b) b))
        l7b = ruleTrans (axPost Snd Pair a b) (axSnd a b)
        l7  : Deriv (atomic (eqn (ap2 (Post cor (Post Snd Pair)) a b) (ap1 cor b)))
        l7  = ruleTrans l7a (cong1 cor l7b)

        innerInner : Term
        innerInner = ap2 Pair (ap1 cor a) (ap1 cor b)

        l5_to : Deriv (atomic (eqn (ap2 inner1 a b) innerInner))
        l5_to = ruleTrans l5
                  (ruleTrans (congL Pair (ap2 (Post cor (Post Snd Pair)) a b) l6)
                             (congR Pair (ap1 cor a) l7))

        innerOuter : Term
        innerOuter = ap2 Pair codeF1f_T innerInner

        l3_to : Deriv (atomic (eqn (ap2 inner2 a b) innerOuter))
        l3_to = ruleTrans l3
                  (ruleTrans (congL Pair (ap2 inner1 a b) l4)
                             (congR Pair codeF1f_T l5_to))

        liftPartFull : Term
        liftPartFull = ap2 Pair tagCode_axLift innerOuter

        l1_to : Deriv (atomic (eqn (ap2 lift_part a b) liftPartFull))
        l1_to = ruleTrans l1
                  (ruleTrans (congL Pair (ap2 inner2 a b) l2)
                             (congR Pair tagCode_axLift l3_to))

        innerFan_to : Deriv (atomic (eqn (ap2 (Fan lift_part df_first Pair) a b)
                                          (ap2 Pair liftPartFull (ap1 Df a))))
        innerFan_to = ruleTrans s3
                        (ruleTrans (congL Pair (ap2 df_first a b) l1_to)
                                   (congR Pair liftPartFull s4))

        finalRHS : Term
        finalRHS = ap2 Pair tagCode_ruleTrans
                     (ap2 Pair liftPartFull (ap1 Df a))
    in ruleTrans s1
         (ruleTrans (congL Pair (ap2 (Fan lift_part df_first Pair) a b) s2)
                    (congR Pair tagCode_ruleTrans innerFan_to))

  ----------------------------------------------------------------------
  -- D_correct2_Lift_f .

  -- Shape proof: Fst (parEncAxLift f (cor a) (cor b)) = Pair O (rest).
  -- parEncAxLift f xT yT = Pair tagCode_axLift (...). tagCode_axLift =
  -- reify (natCode tagAxLift) = ap2 Pair O (reify (natCode (tagAxLift - 1))).
  -- So Fst of (Pair tagCode_axLift _) = tagCode_axLift = Pair O ...

  private
    fstShape : (a b : Term) ->
      Deriv (atomic (eqn (ap1 Fst (parEncAxLift f (ap1 cor a) (ap1 cor b)))
                          (ap2 Pair O (reify (natCode (suc (suc (suc (suc (suc (suc zero))))))))))) -- = reify (natCode (tagAxLift - 1))
    fstShape a b = axFst tagCode_axLift _

  D_correct2_Lift_f : (a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_Lift_f a b)) (codeFTeq2_Lift a b)))
  D_correct2_Lift_f a b =
    let codeF1f_T = reify (codeF1 f)

        -- y1 image (axLift dispatch):
        --   Pair (Pair tagAp2 (Pair (Pair K2 codeF1f) (Pair cor a cor b)))
        --        (Pair tagAp1 (Pair codeF1f cor a))
        u1 : Term
        u1 = ap2 Pair (reify tagAp2)
               (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Lift I)))) codeF1f_T)
                         (ap2 Pair (ap1 cor a) (ap1 cor b)))
        u2 : Term
        u2 = ap2 Pair (reify tagAp1) (ap2 Pair codeF1f_T (ap1 cor a))

        d1 : Deriv (atomic (eqn (ap1 thmT (parEncAxLift f (ap1 cor a) (ap1 cor b)))
                                 (ap2 Pair u1 u2)))
        d1 = parDispAxLift f (ap1 cor a) (ap1 cor b)

        -- y2 image (D_correct_f at substituent a):
        --   codeFTeq1 f a = Pair (Pair tagAp1 (Pair codeF1f (cor a))) (cor (f a))
        --   So y2's LHS u3 = Pair tagAp1 (Pair codeF1f (cor a)) = u2  (chain match!)
        --   y2's RHS u4 = cor (f a)
        u3 : Term
        u3 = u2  -- by construction of codeFTeq1 f a

        u4 : Term
        u4 = ap1 cor (ap1 f a)

        d2 : Deriv (atomic (eqn (ap1 thmT (ap1 Df a)) (ap2 Pair u3 u4)))
        d2 = D_correct_f a

        -- ruleTrans dispatch combines d1, d2 to produce Pair u1 u4.
        shape = fstShape a b

        d_rt : Deriv (atomic (eqn
                  (ap1 thmT (parEncRuleTrans
                              (parEncAxLift f (ap1 cor a) (ap1 cor b))
                              (ap1 Df a)))
                  (ap2 Pair u1 u4)))
        d_rt = parDispRuleTrans
                 (parEncAxLift f (ap1 cor a) (ap1 cor b))
                 (ap1 Df a)
                 u1 u2 u3 u4
                 _ _
                 shape d1 d2

        -- Combinator reduction.
        red = D2_Lift_reduce a b

        thmT_red : Deriv (atomic (eqn
                    (ap1 thmT (ap2 D2_Lift_f a b))
                    (ap1 thmT (parEncRuleTrans
                                 (parEncAxLift f (ap1 cor a) (ap1 cor b))
                                 (ap1 Df a)))))
        thmT_red = cong1 thmT red

        -- Bridge: u4 = cor (f a) -> cor ((Lift f)(a, b))
        sym_bridge : Deriv (atomic (eqn (ap1 cor (ap1 f a))
                                         (ap1 cor (ap2 (Lift f) a b))))
        sym_bridge = ruleSym (cong1 cor (axLift f a b))

        bridge : Deriv (atomic (eqn (ap2 Pair u1 u4) (codeFTeq2_Lift a b)))
        bridge = congR Pair u1 sym_bridge

    in ruleTrans thmT_red (ruleTrans d_rt bridge)
