{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Z -- schematic Theorem 12 at f := Z (the constant-zero functor).
--
-- Mirrors BRA.Th12I exactly, with three substitutions:
--   * encAxI (var 0)  -> encAxZ (var 0)
--   * thmTDispAxI     -> thmTDispAxZ
--   * cong1 cor (axI x) bridge -> a 2-step bridge through  axZ x  and
--                                  axRecLf O stepCor  (since
--                                  cor (ap1 Z x) = cor O = O).
--
-- No postulates, no holes.

module BRA.Th12Z where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor ; stepCor)
open import BRA.SubT
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Tag      using (tagAxKT ; tagRuleInst)
open import BRA.Thm.Parts.AxKT using (encAxZ ; outAxZ)
open import BRA.Thm.ThmT     using
  ( thmT
  ; thmTDispAxZ
  ; thmTDispRuleInst_param
  ; tagCode_ruleInst )
open import BRA.Thm14CodeFTeqAsym using (codeFTeq1Asym ; mkAp1T ; mkEqT)
open import BRA.Th12I        using (codedSubstT ; subTDef_term)

------------------------------------------------------------------------
-- Closed Term constants for Df_F1_Z's runtime proof code.

T1 : Term
T1 = tagCode_ruleInst

T2 : Term
T2 = reify (code (var zero))

T3_Z : Term
T3_Z = reify (encAxZ (var zero))

------------------------------------------------------------------------
-- Df_F1_Z : Fun1
--
-- ap1 Df_F1_Z x = ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3_Z (ap1 cor x)))

Df_F1_Z : Fun1
Df_F1_Z = Comp2 Pair
            (KT T1)
            (Comp2 Pair
              (KT T2)
              (Comp2 Pair
                (KT T3_Z)
                cor))

------------------------------------------------------------------------
-- Df_F1_Z_unfold : same template as Df_F1_I_unfold (4 axComp2 + 3 ktRed).

Df_F1_Z_unfold : (x : Term) ->
  Deriv (atomic (eqn (ap1 Df_F1_Z x)
                     (ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3_Z (ap1 cor x))))))
Df_F1_Z_unfold x =
  let
    inner3 : Fun1
    inner3 = Comp2 Pair (KT T3_Z) cor

    inner2 : Fun1
    inner2 = Comp2 Pair (KT T2) inner3

    s1 : Deriv (atomic (eqn (ap1 Df_F1_Z x)
                            (ap2 Pair (ap1 (KT T1) x) (ap1 inner2 x))))
    s1 = axComp2 Pair (KT T1) inner2 x

    s2_kt1 : Deriv (atomic (eqn (ap1 (KT T1) x) T1))
    s2_kt1 = ktRed (natCode tagRuleInst) x

    s3 : Deriv (atomic (eqn (ap1 inner2 x)
                            (ap2 Pair (ap1 (KT T2) x) (ap1 inner3 x))))
    s3 = axComp2 Pair (KT T2) inner3 x

    s4_kt2 : Deriv (atomic (eqn (ap1 (KT T2) x) T2))
    s4_kt2 = ktRed (code (var zero)) x

    s5 : Deriv (atomic (eqn (ap1 inner3 x)
                            (ap2 Pair (ap1 (KT T3_Z) x) (ap1 cor x))))
    s5 = axComp2 Pair (KT T3_Z) cor x

    s6_kt3 : Deriv (atomic (eqn (ap1 (KT T3_Z) x) T3_Z))
    s6_kt3 = ktRed (encAxZ (var zero)) x

    inner3_simp : Deriv (atomic (eqn (ap1 inner3 x)
                                      (ap2 Pair T3_Z (ap1 cor x))))
    inner3_simp = ruleTrans s5 (congL Pair (ap1 cor x) s6_kt3)

    inner2_step1 : Deriv (atomic (eqn (ap1 inner2 x)
                                       (ap2 Pair T2 (ap1 inner3 x))))
    inner2_step1 = ruleTrans s3 (congL Pair (ap1 inner3 x) s4_kt2)

    inner2_step2 : Deriv (atomic (eqn (ap2 Pair T2 (ap1 inner3 x))
                                       (ap2 Pair T2 (ap2 Pair T3_Z (ap1 cor x)))))
    inner2_step2 = congR Pair T2 inner3_simp

    inner2_simp : Deriv (atomic (eqn (ap1 inner2 x)
                                      (ap2 Pair T2 (ap2 Pair T3_Z (ap1 cor x)))))
    inner2_simp = ruleTrans inner2_step1 inner2_step2

    s_kt1 : Deriv (atomic (eqn (ap1 Df_F1_Z x)
                                (ap2 Pair T1 (ap1 inner2 x))))
    s_kt1 = ruleTrans s1 (congL Pair (ap1 inner2 x) s2_kt1)

    s_final : Deriv (atomic (eqn (ap2 Pair T1 (ap1 inner2 x))
                                  (ap2 Pair T1 (ap2 Pair T2
                                    (ap2 Pair T3_Z (ap1 cor x))))))
    s_final = congR Pair T1 inner2_simp
  in ruleTrans s_kt1 s_final

------------------------------------------------------------------------
-- xShape for thmTDispRuleInst_param at xT = T3_Z.
--
-- T3_Z = reify (nd (natCode tagAxKT) (nd (codeF1 Z) (code (var zero))))
--      = ap2 Pair (reify (natCode tagAxKT)) (reify (nd (codeF1 Z) (code (var zero))))
-- reify (natCode tagAxKT) is itself ap2 Pair-shaped (since tagAxKT is suc-form).
-- We let Agda infer x', y' via underscores.

xShape_F1_Z : Sigma Term (\ y' -> Sigma Term (\ x' ->
  Deriv (atomic (eqn (ap1 Fst T3_Z) (ap2 Pair x' y')))))
xShape_F1_Z = mkSigma _ (mkSigma _ (axFst _ _))

------------------------------------------------------------------------
-- Df_F1_Z_dispatch : runtime substitution bridge via thmTDispRuleInst_param.

Df_F1_Z_dispatch : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3_Z (ap1 cor x)))))
    (ap2 subT (ap2 Pair T2 (ap1 cor x)) (ap1 thmT T3_Z))))
Df_F1_Z_dispatch x =
  thmTDispRuleInst_param zero (ap1 cor x) T3_Z xShape_F1_Z

------------------------------------------------------------------------
-- Df_F1_Z_axZ_thmT :  thmT T3_Z = reify (outAxZ (var zero)) .

Df_F1_Z_axZ_thmT : Deriv (atomic (eqn (ap1 thmT T3_Z)
                                       (reify (outAxZ (var zero)))))
Df_F1_Z_axZ_thmT = thmTDispAxZ (var zero)

------------------------------------------------------------------------
-- Df_F1_Z_runtime : the runtime bridge result.

Df_F1_Z_runtime : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap1 Df_F1_Z x))
    (ap2 subT (ap2 Pair T2 (ap1 cor x)) (reify (outAxZ (var zero))))))
Df_F1_Z_runtime x =
  let
    runtimeTree : Term
    runtimeTree = ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3_Z (ap1 cor x)))

    s1 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Z x))
                             (ap1 thmT runtimeTree)))
    s1 = cong1 thmT (Df_F1_Z_unfold x)

    s2 : Deriv (atomic (eqn (ap1 thmT runtimeTree)
                             (ap2 subT (ap2 Pair T2 (ap1 cor x))
                                       (ap1 thmT T3_Z))))
    s2 = Df_F1_Z_dispatch x

    s3 : Deriv (atomic (eqn (ap2 subT (ap2 Pair T2 (ap1 cor x))
                                       (ap1 thmT T3_Z))
                             (ap2 subT (ap2 Pair T2 (ap1 cor x))
                                       (reify (outAxZ (var zero))))))
    s3 = congR subT (ap2 Pair T2 (ap1 cor x)) Df_F1_Z_axZ_thmT
  in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Th12_F1_Z_at_var0 :  schematic Theorem 12 for f := Z .
--
--   Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Z (var zero)))
--                       (codeFTeq1Asym Z (var zero))))
--
-- Bridge from Df_F1_Z_runtime's subT-form to codeFTeq1Asym Z (var 0):
--   (1) subTDef_term reduces subT-form to codedSubstT-form.
--   (2) codedSubstT unfolds definitionally on closed outAxZ (var 0)
--       to  mkEqT (mkAp1T (reify (codeF1 Z)) (cor x)) O .
--   (3) Bridge RHS slot from  O  to  ap1 cor (ap1 Z x)  via:
--         axZ x        :  ap1 Z x = O
--         cong1 cor    :  ap1 cor (ap1 Z x) = ap1 cor O
--         axRecLf O stepCor :  ap1 cor O = O
--         (ruleSym to flip direction)

Th12_F1_Z_at_var0 :
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Z (var zero)))
                     (codeFTeq1Asym Z (var zero))))
Th12_F1_Z_at_var0 =
  let
    x : Term
    x = var zero

    runtimeRHS : Term
    runtimeRHS = ap2 subT (ap2 Pair T2 (ap1 cor x)) (reify (outAxZ x))

    -- (1) Runtime bridge.
    step1 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Z x)) runtimeRHS))
    step1 = Df_F1_Z_runtime x

    -- (2) subTDef_term: subT-form = codedSubstT-form.
    step2 : Deriv (atomic (eqn runtimeRHS
                                (codedSubstT (ap1 cor x) (code (var zero))
                                              (outAxZ x))))
    step2 = subTDef_term zero (ap1 cor x) (outAxZ x)

    reducedT : Term
    reducedT = mkEqT (mkAp1T (reify (codeF1 Z)) (ap1 cor x)) O

    -- (3) codedSubstT-form reduces definitionally to reducedT.
    step3 : Deriv (atomic (eqn (codedSubstT (ap1 cor x) (code (var zero))
                                              (outAxZ x))
                                reducedT))
    step3 = axRefl reducedT

    -- (4) Bridge RHS slot from  O  to  ap1 cor (ap1 Z x) .
    --   axZ x              :  ap1 Z x = O
    --   cong1 cor          :  ap1 cor (ap1 Z x) = ap1 cor O
    --   axRecLf O stepCor  :  ap1 cor O = O
    --   ruleTrans          :  ap1 cor (ap1 Z x) = O
    --   ruleSym            :  O = ap1 cor (ap1 Z x)

    bridgeR : Deriv (atomic (eqn O (ap1 cor (ap1 Z x))))
    bridgeR =
      ruleSym (ruleTrans (cong1 cor (axZ x))
                          (axRecLf O stepCor))

    step4 : Deriv (atomic (eqn reducedT
                                (codeFTeq1Asym Z x)))
    step4 = congR Pair (mkAp1T (reify (codeF1 Z)) (ap1 cor x)) bridgeR

  in ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))

------------------------------------------------------------------------
-- Schematic Theorem 12 for Z, in the form used by Theorem 14.
-- Aliased for uniformity with Th12_F1_Fst, Th12_F1_Snd, Th12_F1_I.

P_Th12_Z : Formula
P_Th12_Z = atomic (eqn (ap1 thmT (ap1 Df_F1_Z (var zero)))
                        (codeFTeq1Asym Z (var zero)))

Th12_F1_Z : Deriv P_Th12_Z
Th12_F1_Z = Th12_F1_Z_at_var0
