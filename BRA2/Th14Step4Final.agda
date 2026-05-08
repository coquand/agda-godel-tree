{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th14Step4Final
--
-- K_part_l: Phase C step 4 in fully canonicalized form.
--
-- Builds on  step4_l_neg  (Th14Step4Canonical) which delivers
--   PrAtX x imp atomic (eqn (thmT (K_part x))
--                            (Pair (reify tagNeg)
--                                  (subT (vc1, cor x) (reify (codeFormula inner_eq)))))
-- where inner_eq = atomic (eqn (thmT (var 1)) (sub (reify j) (reify j))).
--
-- Stage K canonicalizes the inner subT.  Architecture is identical to
-- step3's Stage A/B/C: subT_codeFormula_atomic + leaf preservation
-- bridges (no codedSubst in goal types, fast typecheck).
--
-- Result:  K_part_l : (x : Term) -> Deriv (PrAtX x imp atomic
--   (eqn (thmT (K_part x))
--        (Pair (reify tagNeg) (Pair (encoded_th_x_at x) encoded_sub_ii)))).
--
-- ASCII only.  No postulates, no holes, no with-abstraction, no dot
-- patterns.

module BRA2.Th14Step4Final where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor      using (cor)
open import BRA2.Sub      using (sub)
open import BRA2.SubT     using (subT)
open import BRA2.Thm.ThmT using (thmT ; codedSubstT_code_thmT_var1)

open import BRA2.Thm.EvalHelpers
  using (liftAxiom ; liftedRuleTrans)

open import BRA2.Thm14SubLemma using (thmTSubLemma)
open import BRA2.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)
open import BRA2.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA2.GoedelII using (i ; cG ; G ; G_norm ; G_unfold ; j ; j_isValue ; PrAtX)

open import BRA2.Th14SubTPushthrough
  using (subT_codeFormula_atomic ; subT_node_match)

open import BRA2.Th14SubTLeaf
  using ( subT_preserves_via_meta ; subT_preserves_codeReify
        ; subT_to_meta
        ; codedSubstT_code_ap2_reify_reify)

open import BRA2.SbParam using (codedSubstT)

import BRA2.Th14Step4Canonical

----------------------------------------------------------------------
-- Convenience.

private
  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

  encoded_th_x_at : Term -> Term
  encoded_th_x_at x = ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 thmT)) (ap1 cor x))

  encoded_sub_ii : Term
  encoded_sub_ii = reify (code (ap2 sub i i))

----------------------------------------------------------------------
-- The Th14Step4Final module proper.

module Th14Step4Final
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub using (K_part)
  open BRA2.Th14Step4Canonical.Th14Step4Canonical r12_th r12_sub
    using (step4_l_neg ; inner_eq)

  --------------------------------------------------------------------
  -- Stage K bridges.  Distribute  subT (vc1, cor x)  through
  -- reify (codeFormula inner_eq) using the existing Pushthrough
  -- + Aux 1 / Aux 2 helpers.

  private
    vc1corx : Term -> Term
    vc1corx x = ap2 Pair varCode1T (ap1 cor x)

    -- subT (vc1, cor x) (reify (code (var 1))) = cor x.   (MATCH)
    bK_v1_match : (x : Term) ->
      Deriv (atomic (eqn (ap2 subT (vc1corx x) (reify (code (var (suc zero)))))
                          (ap1 cor x)))
    bK_v1_match x = subT_node_match (suc zero) (ap1 cor x)

    -- subT (vc1, cor x) (reify tagAp1) = reify tagAp1.  (closed eval, refl)
    bK_tagAp1 : (x : Term) ->
      Deriv (atomic (eqn (ap2 subT (vc1corx x) (reify tagAp1)) (reify tagAp1)))
    bK_tagAp1 x = subT_preserves_via_meta (suc zero) (ap1 cor x) tagAp1 tagAp1_isValue refl

    -- subT (vc1, cor x) (reify (code (sub i i))) = reify (code (sub i i)) = encoded_sub_ii.
    -- Uses codedSubstT_code_ap2_reify_reify (g = sub, ja = jb = j).
    bK_subII : (x : Term) ->
      Deriv (atomic (eqn (ap2 subT (vc1corx x) encoded_sub_ii) encoded_sub_ii))
    bK_subII x =
      let
          codeF2_sub_eq : Eq (codedSubstT (ap1 cor x) (code (var (suc zero))) (codeF2 sub))
                             (reify (codeF2 sub))
          codeF2_sub_eq = refl

          treeEq_codeF2_sub_false : Eq (treeEq tagVar (codeF2 sub)) false
          treeEq_codeF2_sub_false = refl

          meta_eq : Eq (codedSubstT (ap1 cor x) (code (var (suc zero))) (code (ap2 sub i i)))
                       (reify (code (ap2 sub i i)))
          meta_eq = codedSubstT_code_ap2_reify_reify (ap1 cor x) (suc zero) sub
                      j j_isValue j j_isValue codeF2_sub_eq treeEq_codeF2_sub_false
      in subT_preserves_via_meta (suc zero) (ap1 cor x) (code (ap2 sub i i))
                                 (code_isValue (ap2 sub i i)) meta_eq

  --------------------------------------------------------------------
  -- stage_K_left:  subT (vc1, cor x) (reify (code (ap1 thmT (var 1))))
  --                  = encoded_th_x_at x.
  --
  -- Uses the dedicated  codedSubstT_code_thmT_var1  lemma (proved
  -- inside Thm.ThmT 's abstract block where thmT unfolds) +
  -- subT_preserves_via_meta.

  stage_K_left : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc1corx x) (reify (code (ap1 thmT (var (suc zero))))))
                        (encoded_th_x_at x)))
  stage_K_left x =
    subT_to_meta (suc zero) (ap1 cor x)
      (code (ap1 thmT (var (suc zero))))
      (code_isValue (ap1 thmT (var (suc zero))))
      (encoded_th_x_at x)
      (codedSubstT_code_thmT_var1 (ap1 cor x))

  --------------------------------------------------------------------
  -- stage_K: distribute subT (vc1, cor x) through reify (codeFormula inner_eq).
  --
  -- inner_eq = atomic (eqn (ap1 thmT (var 1)) (ap2 sub (reify j) (reify j)))
  -- = atomic (eqn (ap1 thmT (var 1)) (ap2 sub i i))   [since i = reify j]
  --
  -- Distribute via subT_codeFormula_atomic + stage_K_left + bK_subII.

  stage_K : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc1corx x) (reify (codeFormula inner_eq)))
                        (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
  stage_K x =
    let
        p : Term
        p = vc1corx x

        s1 : Deriv (atomic (eqn (ap2 subT p (reify (codeFormula inner_eq)))
                                 (ap2 Pair (ap2 subT p (reify (code (ap1 thmT (var (suc zero))))))
                                            (ap2 subT p (reify (code (ap2 sub i i)))))))
        s1 = subT_codeFormula_atomic (suc zero) (ap1 cor x)
                (ap1 thmT (var (suc zero))) (ap2 sub i i)

        s2 : Deriv (atomic (eqn
          (ap2 Pair (ap2 subT p (reify (code (ap1 thmT (var (suc zero))))))
                     (ap2 subT p (reify (code (ap2 sub i i)))))
          (ap2 Pair (encoded_th_x_at x)
                     (ap2 subT p (reify (code (ap2 sub i i)))))))
        s2 = congL Pair (ap2 subT p (reify (code (ap2 sub i i)))) (stage_K_left x)

        s3 : Deriv (atomic (eqn
          (ap2 Pair (encoded_th_x_at x)
                     (ap2 subT p (reify (code (ap2 sub i i)))))
          (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
        s3 = congR Pair (encoded_th_x_at x) (bK_subII x)

    in ruleTrans s1 (ruleTrans s2 s3)

  --------------------------------------------------------------------
  -- K_part_l: compose step4_l_neg + stage_K to get the full canonicalized form.

  K_part_l : (x : Term) ->
    Deriv (PrAtX x imp
            atomic (eqn (ap1 thmT (ap1 K_part x))
                        (ap2 Pair (reify tagNeg)
                          (ap2 Pair (encoded_th_x_at x) encoded_sub_ii))))
  K_part_l x =
    let
        P : Formula
        P = PrAtX x

        p : Term
        p = vc1corx x

        -- step4_l_neg gives:
        --   P imp ... = Pair (reify tagNeg) (subT p (reify (codeFormula inner_eq)))
        sa : Deriv (P imp atomic (eqn (ap1 thmT (ap1 K_part x))
                                       (ap2 Pair (reify tagNeg)
                                                  (ap2 subT p (reify (codeFormula inner_eq))))))
        sa = step4_l_neg x

        -- stage_K (closed): subT p (reify (codeFormula inner_eq)) =
        --   Pair (encoded_th_x_at x) encoded_sub_ii.
        sb_closed : Deriv (atomic (eqn
          (ap2 Pair (reify tagNeg) (ap2 subT p (reify (codeFormula inner_eq))))
          (ap2 Pair (reify tagNeg) (ap2 Pair (encoded_th_x_at x) encoded_sub_ii))))
        sb_closed = congR Pair (reify tagNeg) (stage_K x)

        sb_lifted : Deriv (P imp atomic (eqn
          (ap2 Pair (reify tagNeg) (ap2 subT p (reify (codeFormula inner_eq))))
          (ap2 Pair (reify tagNeg) (ap2 Pair (encoded_th_x_at x) encoded_sub_ii))))
        sb_lifted = liftAxiom P sb_closed

    in liftedRuleTrans P
         (ap1 thmT (ap1 K_part x))
         (ap2 Pair (reify tagNeg) (ap2 subT p (reify (codeFormula inner_eq))))
         (ap2 Pair (reify tagNeg) (ap2 Pair (encoded_th_x_at x) encoded_sub_ii))
         sa sb_lifted
