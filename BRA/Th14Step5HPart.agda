{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14Step5HPart
--
-- h_part_canon + h_part_l for Phase C step 5.
--
-- Architecture: same as step3 (Th14Step3 + Th14Step3Canon).
--   * h_part_canon: distribute the 2-deep subT through reify (codeFormula
--     t'_formula) using subT_codeFormula_imp / subT_codeFormula_neg /
--     subT_codeFormula_atomic + leaf bridges.
--   * h_part_l: chain h_part_pre + h_part_canon + 2 mp dispatches
--     (h_part_thxLayer + h_part), then liftAxiom (PrAtX x).
--
-- Result:  h_part_l : (x : Term) ->
--   Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 h_part x)) target_h))
-- where target_h = encoded "(thmT(cor x) = sub(i,i)) imp ...
--   ((thmT(cor x) ≠ sub(i,i)) imp (0 = 1))" .
--
-- ASCII only.  No postulates, no holes.

module BRA.Th14Step5HPart where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Sub      using (sub)
open import BRA.SubT     using (subT)
open import BRA.StepReduce using (ktRed)
open import BRA.Thm.Tag  using (tagMp ; tagAxContrapos)

open import BRA.Thm.ThmT using
  ( thmT ; tagCode_ruleInst ; tagCode_mp
  ; thmTDispMp_param )

open import BRA.Thm.EvalHelpers using (liftAxiom)

open import BRA.Thm14SubLemma using (thmTSubLemma)
open import BRA.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)
open import BRA.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA.Th14SubTPushthrough
  using (subT_codeFormula_imp ; subT_codeFormula_neg
       ; subT_codeFormula_atomic ; subT_node_match)

open import BRA.Th14SubTLeaf
  using ( sub_v0_v1 ; sub_v0_v2 ; sub_v1_v0 ; sub_v1_v2
        ; subT_preserves_codeReify
        ; subT_preserves_via_meta
        ; codedSubstT_code_ap2_reify_reify)

open import BRA.SbParam using (codedSubstT)

open import BRA.Thm14Numerals using (t'_formula)
open import BRA.GoedelII using (cG ; G ; i ; j ; PrAtX)

import BRA.Th14StepHPre
import BRA.Th14HUnfolds

----------------------------------------------------------------------
-- Constants and substituent terms.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

  encoded_sub_ii : Term
  encoded_sub_ii = reify (code (ap2 sub i i))

  encoded_th_x_at : Term -> Term
  encoded_th_x_at x = ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 thmT)) (ap1 cor x))

----------------------------------------------------------------------
-- t'_formula's pieces.

private
  x0 : Term
  x0 = var zero

  x1 : Term
  x1 = var (suc zero)

  -- t'_formula = eq01 imp ((not eq01) imp bot)
  -- where eq01 = atomic (eqn x0 x1) ; bot = atomic (eqn O (ap2 Pair O O)).

  eq01' : Formula
  eq01' = atomic (eqn x0 x1)

  -- bot from BRA.Thm11Abstract = atomic (eqn O (ap2 Pair O O)).
  -- We use `bot_local` to avoid pulling the abstract module.
  bot_local : Formula
  bot_local = atomic (eqn O (ap2 Pair O O))

----------------------------------------------------------------------
-- Stage A': substitute var 1 -> sub i i in t'_formula.
--
-- F'_a = (atomic (eqn x0 (sub i i))) imp ((not (atomic (eqn x0 (sub i i)))) imp bot)

F'_a_eq01 : Formula
F'_a_eq01 = atomic (eqn x0 (ap2 sub i i))

F'_a : Formula
F'_a = F'_a_eq01 imp ((not F'_a_eq01) imp bot_local)

----------------------------------------------------------------------
-- Stage A' bridges (vc1, encoded_sub_ii).

private
  vc1sub : Term
  vc1sub = ap2 Pair varCode1T encoded_sub_ii

  -- subT vc1 varCode0T = varCode0T.
  bA'_v0 : Deriv (atomic (eqn (ap2 subT vc1sub varCode0T) varCode0T))
  bA'_v0 = sub_v1_v0 encoded_sub_ii

  -- subT vc1 varCode1T = encoded_sub_ii (MATCH).
  bA'_v1 : Deriv (atomic (eqn (ap2 subT vc1sub varCode1T) encoded_sub_ii))
  bA'_v1 = subT_node_match (suc zero) encoded_sub_ii

  -- subT vc1 (reify (code O)) = reify (code O) (= reify lf = O).
  bA'_codeO : Deriv (atomic (eqn (ap2 subT vc1sub (reify (code O))) (reify (code O))))
  bA'_codeO = subT_preserves_via_meta (suc zero) encoded_sub_ii (code O) refl

  -- subT vc1 (reify (code falseT)) = reify (code falseT). falseT = ap2 Pair O O.
  bA'_codeFalse : Deriv (atomic (eqn (ap2 subT vc1sub (reify (code (ap2 Pair O O))))
                                       (reify (code (ap2 Pair O O)))))
  bA'_codeFalse = subT_preserves_via_meta (suc zero) encoded_sub_ii (code (ap2 Pair O O)) refl

----------------------------------------------------------------------
-- Stage A' eq01 distribution.

stageH_A_eq01 :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula eq01')))
                      (reify (codeFormula F'_a_eq01))))
stageH_A_eq01 =
  let
      s1 = subT_codeFormula_atomic (suc zero) encoded_sub_ii x0 x1

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc1sub (reify (code x0)))
                                          (ap2 subT vc1sub (reify (code x1))))
                               (ap2 Pair varCode0T (ap2 subT vc1sub (reify (code x1))))))
      s2 = congL Pair (ap2 subT vc1sub (reify (code x1))) bA'_v0

      s3 : Deriv (atomic (eqn (ap2 Pair varCode0T (ap2 subT vc1sub (reify (code x1))))
                               (ap2 Pair varCode0T encoded_sub_ii)))
      s3 = congR Pair varCode0T bA'_v1
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A' (not eq01) -> not F'_a_eq01.

stageH_A_neg :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula (not eq01'))))
                      (reify (codeFormula (not F'_a_eq01)))))
stageH_A_neg =
  let
      s1 = subT_codeFormula_neg (suc zero) encoded_sub_ii eq01'

      s2 : Deriv (atomic (eqn
        (ap2 Pair (reify tagNeg) (ap2 subT vc1sub (reify (codeFormula eq01'))))
        (ap2 Pair (reify tagNeg) (reify (codeFormula F'_a_eq01)))))
      s2 = congR Pair (reify tagNeg) stageH_A_eq01
  in ruleTrans s1 s2

----------------------------------------------------------------------
-- Stage A' bot preservation.

stageH_A_bot :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula bot_local)))
                      (reify (codeFormula bot_local))))
stageH_A_bot =
  let
      s1 = subT_codeFormula_atomic (suc zero) encoded_sub_ii O (ap2 Pair O O)

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc1sub (reify (code O)))
                                          (ap2 subT vc1sub (reify (code (ap2 Pair O O)))))
                               (ap2 Pair (reify (code O))
                                          (ap2 subT vc1sub (reify (code (ap2 Pair O O)))))))
      s2 = congL Pair (ap2 subT vc1sub (reify (code (ap2 Pair O O)))) bA'_codeO

      s3 : Deriv (atomic (eqn (ap2 Pair (reify (code O))
                                          (ap2 subT vc1sub (reify (code (ap2 Pair O O)))))
                               (ap2 Pair (reify (code O)) (reify (code (ap2 Pair O O))))))
      s3 = congR Pair (reify (code O)) bA'_codeFalse
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A' (not eq01) imp bot.

stageH_A_neg_imp_bot :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula ((not eq01') imp bot_local))))
                      (reify (codeFormula ((not F'_a_eq01) imp bot_local)))))
stageH_A_neg_imp_bot =
  let
      s1 = subT_codeFormula_imp (suc zero) encoded_sub_ii (not eq01') bot_local

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT vc1sub (reify (codeFormula bot_local))) stageH_A_neg)

      s3 = congR Pair (reify tagImp)
             (congR Pair (reify (codeFormula (not F'_a_eq01))) stageH_A_bot)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A' top-level.

stageH_A :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula t'_formula)))
                      (reify (codeFormula F'_a))))
stageH_A =
  let
      s1 = subT_codeFormula_imp (suc zero) encoded_sub_ii eq01' ((not eq01') imp bot_local)

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT vc1sub (reify (codeFormula ((not eq01') imp bot_local))))
                         stageH_A_eq01)

      s3 = congR Pair (reify tagImp)
             (congR Pair (reify (codeFormula F'_a_eq01)) stageH_A_neg_imp_bot)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B': substitute var 0 -> encoded_th_x_at x in F'_a.
--
-- F'_a's eq01 has v0 free.  After substitution, the encoding has
-- encoded_th_x_at x at v0 leaves.

target_h_eq01 : Term -> Term
target_h_eq01 x = ap2 Pair (encoded_th_x_at x) encoded_sub_ii

target_h : Term -> Term
target_h x =
  ap2 Pair (reify tagImp)
    (ap2 Pair (target_h_eq01 x)
       (ap2 Pair (reify tagImp)
          (ap2 Pair (ap2 Pair (reify tagNeg) (target_h_eq01 x))
                    (reify (codeFormula bot_local)))))

----------------------------------------------------------------------
-- Stage B' bridges (vc0, encoded_th_x_at x).

private
  vc0sub : Term -> Term
  vc0sub x = ap2 Pair varCode0T (encoded_th_x_at x)

  -- subT vc0 varCode0T = encoded_th_x_at x (MATCH).
  bB'_v0 : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) varCode0T) (encoded_th_x_at x)))
  bB'_v0 x = subT_node_match zero (encoded_th_x_at x)

  -- subT vc0 encoded_sub_ii = encoded_sub_ii (preservation; ap2 sub i i closed).
  bB'_subII : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) encoded_sub_ii) encoded_sub_ii))
  bB'_subII x =
    let
        codeF2_sub_eq : Eq (codedSubstT (encoded_th_x_at x) (code (var zero)) (codeF2 sub))
                           (reify (codeF2 sub))
        codeF2_sub_eq = refl

        treeEq_codeF2_sub_false : Eq (treeEq tagVar (codeF2 sub)) false
        treeEq_codeF2_sub_false = refl

        meta_eq : Eq (codedSubstT (encoded_th_x_at x) (code (var zero)) (code (ap2 sub i i)))
                     (reify (code (ap2 sub i i)))
        meta_eq = codedSubstT_code_ap2_reify_reify (encoded_th_x_at x) zero sub
                    j j codeF2_sub_eq treeEq_codeF2_sub_false
    in subT_preserves_via_meta zero (encoded_th_x_at x) (code (ap2 sub i i)) meta_eq

  -- bot preservation: subT vc0 (reify (codeFormula bot)) = reify (codeFormula bot).
  bB'_bot : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula bot_local)))
                        (reify (codeFormula bot_local))))
  bB'_bot x = subT_preserves_via_meta zero (encoded_th_x_at x) (codeFormula bot_local) refl

----------------------------------------------------------------------
-- Stage B' eq01 distribution.

stageH_B_eq01 : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula F'_a_eq01)))
                      (target_h_eq01 x)))
stageH_B_eq01 x =
  let
      s1 = subT_codeFormula_atomic zero (encoded_th_x_at x) x0 (ap2 sub i i)

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT (vc0sub x) (reify (code x0)))
                                          (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))))
                               (ap2 Pair (encoded_th_x_at x)
                                          (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))))))
      s2 = congL Pair (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))) (bB'_v0 x)

      s3 : Deriv (atomic (eqn (ap2 Pair (encoded_th_x_at x)
                                          (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))))
                               (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
      s3 = congR Pair (encoded_th_x_at x) (bB'_subII x)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B' neg.

stageH_B_neg : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula (not F'_a_eq01))))
                      (ap2 Pair (reify tagNeg) (target_h_eq01 x))))
stageH_B_neg x =
  let
      s1 = subT_codeFormula_neg zero (encoded_th_x_at x) F'_a_eq01

      s2 : Deriv (atomic (eqn
        (ap2 Pair (reify tagNeg) (ap2 subT (vc0sub x) (reify (codeFormula F'_a_eq01))))
        (ap2 Pair (reify tagNeg) (target_h_eq01 x))))
      s2 = congR Pair (reify tagNeg) (stageH_B_eq01 x)
  in ruleTrans s1 s2

----------------------------------------------------------------------
-- Stage B' (not F'_a_eq01) imp bot.

stageH_B_neg_imp_bot : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula ((not F'_a_eq01) imp bot_local))))
                      (ap2 Pair (reify tagImp)
                         (ap2 Pair (ap2 Pair (reify tagNeg) (target_h_eq01 x))
                                   (reify (codeFormula bot_local))))))
stageH_B_neg_imp_bot x =
  let
      s1 = subT_codeFormula_imp zero (encoded_th_x_at x) (not F'_a_eq01) bot_local

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT (vc0sub x) (reify (codeFormula bot_local))) (stageH_B_neg x))

      s3 = congR Pair (reify tagImp)
             (congR Pair (ap2 Pair (reify tagNeg) (target_h_eq01 x)) (bB'_bot x))
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B' top-level.

stageH_B : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula F'_a))) (target_h x)))
stageH_B x =
  let
      s1 = subT_codeFormula_imp zero (encoded_th_x_at x) F'_a_eq01 ((not F'_a_eq01) imp bot_local)

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT (vc0sub x) (reify (codeFormula ((not F'_a_eq01) imp bot_local))))
                         (stageH_B_eq01 x))

      s3 = congR Pair (reify tagImp)
             (congR Pair (target_h_eq01 x) (stageH_B_neg_imp_bot x))
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- h_part_canon: chain Stage A' + Stage B' with congR bridges.

h_part_canon : (x : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (vc0sub x)
       (ap2 subT vc1sub (reify (codeFormula t'_formula))))
    (target_h x)))
h_part_canon x =
  let
      bridge_a : Deriv (atomic (eqn
        (ap2 subT (vc0sub x)
           (ap2 subT vc1sub (reify (codeFormula t'_formula))))
        (ap2 subT (vc0sub x) (reify (codeFormula F'_a)))))
      bridge_a = congR subT (vc0sub x) stageH_A
  in ruleTrans bridge_a (stageH_B x)

----------------------------------------------------------------------
-- The Th14Step5HPart module proper, parametric in r12_th, r12_sub.

module Th14Step5HPart
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub using (h_part_skel)

  open BRA.Th14StepHPre.Th14StepHPre r12_th r12_sub
    using (h_part_pre)

  --------------------------------------------------------------------
  -- h_part_skel_l : the encoded ex-falso form, lifted under PrAtX x.
  --
  -- Combines h_part_pre + h_part_canon to get
  --   thmT(h_part_skel x) = target_h x
  -- (an unconditional equation), then liftAxiom under PrAtX x.

  h_part_skel_l : (x : Term) ->
    Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 h_part_skel x)) (target_h x)))
  h_part_skel_l x =
    liftAxiom (PrAtX x) (ruleTrans (h_part_pre x) (h_part_canon x))
