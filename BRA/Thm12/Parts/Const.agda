{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.Const
--
-- Theorem 12 case for g = Const : Fun2 (the constant-first projection).
--
-- Goal: build  D2_Const : Fun2  such that for every Term x, v,
--     ap1 thmT (ap2 D2_Const x v)  =  codeFTeq2_Const x v
-- where codeFTeq2_Const x v  encodes Guard's "Const(num x, num v) = num(Const x v)" :
--     Pair (Pair tagAp2 (Pair (codeF2 Const) (Pair (cor x) (cor v)))) (cor (Const x v))
--
-- Strategy:
--   1. D2_Const  =  Fan (Lift (KT tagCode_axConst))
--                       (Fan (Lift cor) (Post cor (Post Snd Pair)) Pair)
--                       Pair.
--   2. parDispAxConst (cor x) (cor v)  reduces the dispatch.
--   3. Bridge: parOutAxConst (cor x) (cor v) -> codeFTeq2_Const x v
--      differs only in the RHS slot (cor x vs cor (Const x v)).
--      Provable from  ruleSym (cong1 cor (axConst x v)).

module BRA.Thm12.Parts.Const where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxConst)
open import BRA.Thm.ThmT using (thmT ; tagCode_axConst)
open import BRA.Thm12.Param.AxConst
  using (parDispAxConst ; parEncAxConst ; parOutAxConst)

------------------------------------------------------------------------
-- D2_Const : Fun2 .
--
--  ap2 D2_Const x v  reduces to  Pair tagCode_axConst (Pair (cor x) (cor v))
--  = parEncAxConst (cor x) (cor v).

-- "Drop-first" Fun2: ap2 dropFst a b = b, via  axPost + axSnd.
private
  dropFst : Fun2
  dropFst = Post Snd Pair

D2_Const : Fun2
D2_Const =
  Fan (Lift (KT tagCode_axConst))
      (Fan (Lift cor) (Post cor dropFst) Pair)
      Pair

------------------------------------------------------------------------
-- The asymmetric encoded equation.

codeFTeq2_Const : Term -> Term -> Term
codeFTeq2_Const x v =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 Const))
                        (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor (ap2 Const x v))

------------------------------------------------------------------------
-- Combinator reduction:
--   ap2 D2_Const x v = parEncAxConst (cor x) (cor v).

D2_Const_reduce : (x v : Term) ->
  Deriv (atomic (eqn (ap2 D2_Const x v)
                     (parEncAxConst (ap1 cor x) (ap1 cor v))))
D2_Const_reduce x v =
  let s1 : Deriv (atomic (eqn (ap2 D2_Const x v)
              (ap2 Pair (ap2 (Lift (KT tagCode_axConst)) x v)
                        (ap2 (Fan (Lift cor) (Post cor dropFst) Pair) x v))))
      s1 = axFan (Lift (KT tagCode_axConst))
                 (Fan (Lift cor) (Post cor dropFst) Pair) Pair x v

      s2a : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axConst)) x v)
                               (ap1 (KT tagCode_axConst) x)))
      s2a = axLift (KT tagCode_axConst) x v
      s2b : Deriv (atomic (eqn (ap1 (KT tagCode_axConst) x) tagCode_axConst))
      s2b = axKT (natCode tagAxConst) x
      s2  : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axConst)) x v) tagCode_axConst))
      s2  = ruleTrans s2a s2b

      s3 : Deriv (atomic (eqn (ap2 (Fan (Lift cor) (Post cor dropFst) Pair) x v)
              (ap2 Pair (ap2 (Lift cor) x v) (ap2 (Post cor dropFst) x v))))
      s3 = axFan (Lift cor) (Post cor dropFst) Pair x v

      s4 : Deriv (atomic (eqn (ap2 (Lift cor) x v) (ap1 cor x)))
      s4 = axLift cor x v

      -- ap2 (Post cor dropFst) x v = cor (dropFst x v) = cor v.
      s5a : Deriv (atomic (eqn (ap2 (Post cor dropFst) x v)
                                (ap1 cor (ap2 dropFst x v))))
      s5a = axPost cor dropFst x v
      s5b : Deriv (atomic (eqn (ap2 dropFst x v) v))
      s5b = ruleTrans (axPost Snd Pair x v) (axSnd x v)
      s5  : Deriv (atomic (eqn (ap2 (Post cor dropFst) x v) (ap1 cor v)))
      s5  = ruleTrans s5a (cong1 cor s5b)

      r3 : Deriv (atomic (eqn (ap2 (Fan (Lift cor) (Post cor dropFst) Pair) x v)
              (ap2 Pair (ap1 cor x) (ap1 cor v))))
      r3 = ruleTrans s3
             (ruleTrans (congL Pair (ap2 (Post cor dropFst) x v) s4)
                        (congR Pair (ap1 cor x) s5))

      r1 : Deriv (atomic (eqn (ap2 D2_Const x v)
              (ap2 Pair tagCode_axConst (ap2 Pair (ap1 cor x) (ap1 cor v)))))
      r1 = ruleTrans s1
             (ruleTrans (congL Pair (ap2 (Fan (Lift cor) (Post cor dropFst) Pair) x v) s2)
                        (congR Pair tagCode_axConst r3))
  in r1

------------------------------------------------------------------------
-- Bridge:  parOutAxConst (cor x) (cor v) = codeFTeq2_Const x v .

bridgePair : (x v : Term) ->
  Deriv (atomic (eqn (parOutAxConst (ap1 cor x) (ap1 cor v))
                     (codeFTeq2_Const x v)))
bridgePair x v =
  let pairLhs : Term
      pairLhs = ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 Const))
                            (ap2 Pair (ap1 cor x) (ap1 cor v)))

      sym_bridge : Deriv (atomic (eqn (ap1 cor x) (ap1 cor (ap2 Const x v))))
      sym_bridge = ruleSym (cong1 cor (axConst x v))
  in congR Pair pairLhs sym_bridge

------------------------------------------------------------------------
-- D_correct2_Const .

D_correct2_Const : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2_Const x v)) (codeFTeq2_Const x v)))
D_correct2_Const x v =
  let r_red = D2_Const_reduce x v

      r_thmT : Deriv (atomic (eqn (ap1 thmT (ap2 D2_Const x v))
                                   (ap1 thmT (parEncAxConst (ap1 cor x) (ap1 cor v)))))
      r_thmT = cong1 thmT r_red

      r_disp = parDispAxConst (ap1 cor x) (ap1 cor v)

      r_bridge = bridgePair x v
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)
