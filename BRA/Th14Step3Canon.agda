{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14Step3Canon
--
-- Phase C step 3 canonicalization (Stage A).
--
-- Architecture: subT-commutes-with-formula-encoding-constructors.
-- Stage A is a short Deriv chain over  subT_codeFormula_imp  /
-- subT_codeFormula_atomic  /  leaf preservation lemmas (Aux 1, Aux 2).
-- No  codedSubst / codedSubstT  appears in any goal type.
--
-- ASCII only.  No postulates, no holes, no with-abstraction, no dot
-- patterns.

module BRA.Th14Step3Canon where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Sub      using (sub)
open import BRA.SubT     using (subT)
open import BRA.Thm.ThmT using (thmT)

open import BRA.Th14SubTPushthrough
  using (subT_codeFormula_imp ; subT_codeFormula_atomic
       ; subT_node_match)

open import BRA.SbParam using (codedSubstT)
open import BRA.Th14SubTLeaf
  using ( sub_v0_v1 ; sub_v0_v2 ; sub_v1_v0 ; sub_v1_v2
        ; sub_v2_v0 ; sub_v2_v1
        ; subT_preserves_codeReify
        ; subT_preserves_via_meta
        ; codedSubstT_code_ap2_reify_reify)

open import BRA.Thm14Numerals using (t_formula)
open import BRA.GoedelII using (cG ; G ; i ; j)

----------------------------------------------------------------------
-- Constants and substituent terms.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

  varCode2T : Term
  varCode2T = reify (code (var (suc (suc zero))))

  sub_ii_subst : Term
  sub_ii_subst = reify (code (reify (codeFormula G)))

  encoded_sub_ii : Term
  encoded_sub_ii = reify (code (ap2 sub i i))

  encoded_th_x_at : Term -> Term
  encoded_th_x_at x = ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 thmT)) (ap1 cor x))

----------------------------------------------------------------------
-- t_formula's pieces.

private
  x0 : Term
  x0 = var zero

  x1 : Term
  x1 = var (suc zero)

  x2 : Term
  x2 = var (suc (suc zero))

  eq02 : Formula
  eq02 = atomic (eqn x0 x2)

  eq12 : Formula
  eq12 = atomic (eqn x1 x2)

  eq01 : Formula
  eq01 = atomic (eqn x0 x1)

  -- Sanity: t_formula = eq02 imp (eq12 imp eq01).  Definitional.
  -- (Imported t_formula has this shape.)

----------------------------------------------------------------------
-- Stage A target: F_a (substitute var 2 -> cG in t_formula).

F_a_eq02 : Formula
F_a_eq02 = atomic (eqn x0 cG)

F_a_eq12 : Formula
F_a_eq12 = atomic (eqn x1 cG)

F_a_eq01 : Formula
F_a_eq01 = atomic (eqn x0 x1)

F_a : Formula
F_a = F_a_eq02 imp (F_a_eq12 imp F_a_eq01)

----------------------------------------------------------------------
-- Stage A bridges.
--
-- Each bridge says:  subT (vc2_pair sub_ii_subst) (reify (codeFormula F_part))
--                      = reify (codeFormula (F_part [var 2 -> cG]))
-- for each F_part in {eq02, eq12, eq01, eq12 imp eq01, t_formula}.

private
  vc2sub : Term
  vc2sub = ap2 Pair varCode2T sub_ii_subst

  -- Leaf bridges: subT (vc2, sub_ii_subst) varCode_k.

  bA_v0 : Deriv (atomic (eqn (ap2 subT vc2sub varCode0T) varCode0T))
  bA_v0 = sub_v2_v0 sub_ii_subst

  bA_v1 : Deriv (atomic (eqn (ap2 subT vc2sub varCode1T) varCode1T))
  bA_v1 = sub_v2_v1 sub_ii_subst

  bA_v2 : Deriv (atomic (eqn (ap2 subT vc2sub varCode2T) sub_ii_subst))
  bA_v2 = subT_node_match (suc (suc zero)) sub_ii_subst

----------------------------------------------------------------------
-- Stage A: distribute eq02.
-- subT (vc2sub) (reify (codeFormula (atomic (eqn x0 x2))))
--   = reify (codeFormula (atomic (eqn x0 cG)))   = reify (codeFormula F_a_eq02)

stageA_eq02 :
  Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula eq02)))
                      (reify (codeFormula F_a_eq02))))
stageA_eq02 =
  let
      s1 : Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula eq02)))
                               (ap2 Pair (ap2 subT vc2sub (reify (code x0)))
                                          (ap2 subT vc2sub (reify (code x2))))))
      s1 = subT_codeFormula_atomic (suc (suc zero)) sub_ii_subst x0 x2

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc2sub (reify (code x0)))
                                          (ap2 subT vc2sub (reify (code x2))))
                               (ap2 Pair varCode0T (ap2 subT vc2sub (reify (code x2))))))
      s2 = congL Pair (ap2 subT vc2sub (reify (code x2))) bA_v0

      s3 : Deriv (atomic (eqn (ap2 Pair varCode0T (ap2 subT vc2sub (reify (code x2))))
                               (ap2 Pair varCode0T sub_ii_subst)))
      s3 = congR Pair varCode0T bA_v2

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A: distribute eq12.

stageA_eq12 :
  Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula eq12)))
                      (reify (codeFormula F_a_eq12))))
stageA_eq12 =
  let
      s1 = subT_codeFormula_atomic (suc (suc zero)) sub_ii_subst x1 x2

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc2sub (reify (code x1)))
                                          (ap2 subT vc2sub (reify (code x2))))
                               (ap2 Pair varCode1T (ap2 subT vc2sub (reify (code x2))))))
      s2 = congL Pair (ap2 subT vc2sub (reify (code x2))) bA_v1

      s3 : Deriv (atomic (eqn (ap2 Pair varCode1T (ap2 subT vc2sub (reify (code x2))))
                               (ap2 Pair varCode1T sub_ii_subst)))
      s3 = congR Pair varCode1T bA_v2

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A: distribute eq01 (no var 2 inside, so unchanged).

stageA_eq01 :
  Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula eq01)))
                      (reify (codeFormula F_a_eq01))))
stageA_eq01 =
  let
      s1 = subT_codeFormula_atomic (suc (suc zero)) sub_ii_subst x0 x1

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc2sub (reify (code x0)))
                                          (ap2 subT vc2sub (reify (code x1))))
                               (ap2 Pair varCode0T (ap2 subT vc2sub (reify (code x1))))))
      s2 = congL Pair (ap2 subT vc2sub (reify (code x1))) bA_v0

      s3 : Deriv (atomic (eqn (ap2 Pair varCode0T (ap2 subT vc2sub (reify (code x1))))
                               (ap2 Pair varCode0T varCode1T)))
      s3 = congR Pair varCode0T bA_v1

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A: distribute (eq12 imp eq01).

stageA_eq12_imp_eq01 :
  Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula (eq12 imp eq01))))
                      (reify (codeFormula (F_a_eq12 imp F_a_eq01)))))
stageA_eq12_imp_eq01 =
  let
      s1 : Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula (eq12 imp eq01))))
                               (ap2 Pair (reify tagImp)
                                  (ap2 Pair (ap2 subT vc2sub (reify (codeFormula eq12)))
                                            (ap2 subT vc2sub (reify (codeFormula eq01)))))))
      s1 = subT_codeFormula_imp (suc (suc zero)) sub_ii_subst eq12 eq01

      s2 : Deriv (atomic (eqn
        (ap2 Pair (reify tagImp)
           (ap2 Pair (ap2 subT vc2sub (reify (codeFormula eq12)))
                     (ap2 subT vc2sub (reify (codeFormula eq01)))))
        (ap2 Pair (reify tagImp)
           (ap2 Pair (reify (codeFormula F_a_eq12))
                     (ap2 subT vc2sub (reify (codeFormula eq01)))))))
      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT vc2sub (reify (codeFormula eq01))) stageA_eq12)

      s3 : Deriv (atomic (eqn
        (ap2 Pair (reify tagImp)
           (ap2 Pair (reify (codeFormula F_a_eq12))
                     (ap2 subT vc2sub (reify (codeFormula eq01)))))
        (ap2 Pair (reify tagImp)
           (ap2 Pair (reify (codeFormula F_a_eq12))
                     (reify (codeFormula F_a_eq01))))))
      s3 = congR Pair (reify tagImp)
             (congR Pair (reify (codeFormula F_a_eq12)) stageA_eq01)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage A: top-level (subT applied to t_formula).

stageA :
  Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula t_formula)))
                      (reify (codeFormula F_a))))
stageA =
  let
      s1 : Deriv (atomic (eqn (ap2 subT vc2sub (reify (codeFormula t_formula)))
                               (ap2 Pair (reify tagImp)
                                  (ap2 Pair (ap2 subT vc2sub (reify (codeFormula eq02)))
                                            (ap2 subT vc2sub (reify (codeFormula (eq12 imp eq01))))))))
      s1 = subT_codeFormula_imp (suc (suc zero)) sub_ii_subst eq02 (eq12 imp eq01)

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT vc2sub (reify (codeFormula (eq12 imp eq01)))) stageA_eq02)

      s3 = congR Pair (reify tagImp)
             (congR Pair (reify (codeFormula F_a_eq02)) stageA_eq12_imp_eq01)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B: substitute var 1 -> sub i i in F_a.
--
-- F_b = (atomic (eqn x0 cG)) imp ((atomic (eqn (ap2 sub i i) cG)) imp (atomic (eqn x0 (ap2 sub i i))))

F_b_eq02 : Formula
F_b_eq02 = atomic (eqn x0 cG)

F_b_eq12 : Formula
F_b_eq12 = atomic (eqn (ap2 sub i i) cG)

F_b_eq01 : Formula
F_b_eq01 = atomic (eqn x0 (ap2 sub i i))

F_b : Formula
F_b = F_b_eq02 imp (F_b_eq12 imp F_b_eq01)

----------------------------------------------------------------------
-- Stage B bridges.

private
  vc1sub : Term
  vc1sub = ap2 Pair varCode1T encoded_sub_ii

  -- Leaf bridges for vc1.

  bB_v0 : Deriv (atomic (eqn (ap2 subT vc1sub varCode0T) varCode0T))
  bB_v0 = sub_v1_v0 encoded_sub_ii

  -- subT vc1 varCode1T = encoded_sub_ii (MATCH).
  bB_v1 : Deriv (atomic (eqn (ap2 subT vc1sub varCode1T) encoded_sub_ii))
  bB_v1 = subT_node_match (suc zero) encoded_sub_ii

  -- subT vc1 (reify (code cG)) = reify (code cG)  (passthrough; cG = reify (codeFormula G)).
  bB_cG : Deriv (atomic (eqn (ap2 subT vc1sub (reify (code cG))) (reify (code cG))))
  bB_cG = subT_preserves_codeReify (suc zero) encoded_sub_ii (codeFormula G)

----------------------------------------------------------------------
-- Stage B: distribute F_a_eq02 (= atomic (eqn x0 cG)).
--
-- subT (vc1, encoded_sub_ii) (reify (codeFormula (atomic (eqn x0 cG))))
--   = reify (codeFormula (atomic (eqn x0 cG)))     -- preserved (no var 1 inside)

stageB_eq02 :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula F_a_eq02)))
                      (reify (codeFormula F_b_eq02))))
stageB_eq02 =
  let
      s1 = subT_codeFormula_atomic (suc zero) encoded_sub_ii x0 cG

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc1sub (reify (code x0)))
                                          (ap2 subT vc1sub (reify (code cG))))
                               (ap2 Pair varCode0T (ap2 subT vc1sub (reify (code cG))))))
      s2 = congL Pair (ap2 subT vc1sub (reify (code cG))) bB_v0

      s3 : Deriv (atomic (eqn (ap2 Pair varCode0T (ap2 subT vc1sub (reify (code cG))))
                               (ap2 Pair varCode0T (reify (code cG)))))
      s3 = congR Pair varCode0T bB_cG

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B: distribute F_a_eq12 (= atomic (eqn x1 cG)) -> F_b_eq12.

stageB_eq12 :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula F_a_eq12)))
                      (reify (codeFormula F_b_eq12))))
stageB_eq12 =
  let
      s1 = subT_codeFormula_atomic (suc zero) encoded_sub_ii x1 cG

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc1sub (reify (code x1)))
                                          (ap2 subT vc1sub (reify (code cG))))
                               (ap2 Pair encoded_sub_ii (ap2 subT vc1sub (reify (code cG))))))
      s2 = congL Pair (ap2 subT vc1sub (reify (code cG))) bB_v1

      s3 : Deriv (atomic (eqn (ap2 Pair encoded_sub_ii (ap2 subT vc1sub (reify (code cG))))
                               (ap2 Pair encoded_sub_ii (reify (code cG)))))
      s3 = congR Pair encoded_sub_ii bB_cG

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B: distribute F_a_eq01 (= atomic (eqn x0 x1)) -> F_b_eq01.

stageB_eq01 :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula F_a_eq01)))
                      (reify (codeFormula F_b_eq01))))
stageB_eq01 =
  let
      s1 = subT_codeFormula_atomic (suc zero) encoded_sub_ii x0 x1

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT vc1sub (reify (code x0)))
                                          (ap2 subT vc1sub (reify (code x1))))
                               (ap2 Pair varCode0T (ap2 subT vc1sub (reify (code x1))))))
      s2 = congL Pair (ap2 subT vc1sub (reify (code x1))) bB_v0

      s3 : Deriv (atomic (eqn (ap2 Pair varCode0T (ap2 subT vc1sub (reify (code x1))))
                               (ap2 Pair varCode0T encoded_sub_ii)))
      s3 = congR Pair varCode0T bB_v1

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B: distribute (F_a_eq12 imp F_a_eq01) -> (F_b_eq12 imp F_b_eq01).

stageB_eq12_imp_eq01 :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula (F_a_eq12 imp F_a_eq01))))
                      (reify (codeFormula (F_b_eq12 imp F_b_eq01)))))
stageB_eq12_imp_eq01 =
  let
      s1 = subT_codeFormula_imp (suc zero) encoded_sub_ii F_a_eq12 F_a_eq01

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT vc1sub (reify (codeFormula F_a_eq01))) stageB_eq12)

      s3 = congR Pair (reify tagImp)
             (congR Pair (reify (codeFormula F_b_eq12)) stageB_eq01)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage B: top-level.

stageB :
  Deriv (atomic (eqn (ap2 subT vc1sub (reify (codeFormula F_a)))
                      (reify (codeFormula F_b))))
stageB =
  let
      s1 = subT_codeFormula_imp (suc zero) encoded_sub_ii F_a_eq02 (F_a_eq12 imp F_a_eq01)

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT vc1sub (reify (codeFormula (F_a_eq12 imp F_a_eq01))))
                         stageB_eq02)

      s3 = congR Pair (reify tagImp)
             (congR Pair (reify (codeFormula F_b_eq02)) stageB_eq12_imp_eq01)
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage C: substitute var 0 -> encoded_th_x_at x in F_b.
--
-- The substituent encoded_th_x_at x is a Term parametric in x.  It
-- contains  cor x  at the deepest leaf, but as a substituent it
-- appears only at MATCH positions (var 0 leaves), never as TreeEq
-- input or as a target subterm.

-- Stage C target form (parametric in x).  Encoded mixed-form Pair.

target_c : Term -> Term
target_c x =
  ap2 Pair (reify tagImp)
    (ap2 Pair (ap2 Pair (encoded_th_x_at x) (reify (code cG)))
       (ap2 Pair (reify tagImp)
          (ap2 Pair (ap2 Pair encoded_sub_ii (reify (code cG)))
                    (ap2 Pair (encoded_th_x_at x) encoded_sub_ii))))

----------------------------------------------------------------------
-- Stage C bridges.

private
  vc0sub : Term -> Term
  vc0sub x = ap2 Pair varCode0T (encoded_th_x_at x)

  -- subT vc0 varCode0T = encoded_th_x_at x (MATCH).
  bC_v0 : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) varCode0T) (encoded_th_x_at x)))
  bC_v0 x = subT_node_match zero (encoded_th_x_at x)

  -- subT vc0 varCode1T = varCode1T.
  bC_v1 : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) varCode1T) varCode1T))
  bC_v1 x = sub_v0_v1 (encoded_th_x_at x)

  -- subT vc0 (reify (code cG)) = reify (code cG).
  bC_cG : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (code cG))) (reify (code cG))))
  bC_cG x = subT_preserves_codeReify zero (encoded_th_x_at x) (codeFormula G)

  -- subT vc0 (reify (code (sub i i))) = reify (code (sub i i)) = encoded_sub_ii.
  -- Uses codedSubstT_code_ap2_reify_reify with g = sub, ja = jb = j (since i = reify j).
  -- The two side-conditions (codeF2 sub preservation, treeEq tagVar (codeF2 sub) = false)
  -- are `refl` since codeF2 sub is a closed concrete tree.
  bC_subII : (x : Term) ->
    Deriv (atomic (eqn (ap2 subT (vc0sub x) encoded_sub_ii) encoded_sub_ii))
  bC_subII x =
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
        -- i = reify j (definitionally).
    in subT_preserves_via_meta zero (encoded_th_x_at x) (code (ap2 sub i i)) meta_eq

----------------------------------------------------------------------
-- Stage C: distribute F_b_eq02 (= atomic (eqn x0 cG)) -> Pair (encoded_th_x_at x) (reify (code cG)).

stageC_eq02 : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula F_b_eq02)))
                      (ap2 Pair (encoded_th_x_at x) (reify (code cG)))))
stageC_eq02 x =
  let
      s1 = subT_codeFormula_atomic zero (encoded_th_x_at x) x0 cG

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT (vc0sub x) (reify (code x0)))
                                          (ap2 subT (vc0sub x) (reify (code cG))))
                               (ap2 Pair (encoded_th_x_at x) (ap2 subT (vc0sub x) (reify (code cG))))))
      s2 = congL Pair (ap2 subT (vc0sub x) (reify (code cG))) (bC_v0 x)

      s3 : Deriv (atomic (eqn (ap2 Pair (encoded_th_x_at x) (ap2 subT (vc0sub x) (reify (code cG))))
                               (ap2 Pair (encoded_th_x_at x) (reify (code cG)))))
      s3 = congR Pair (encoded_th_x_at x) (bC_cG x)

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage C: distribute F_b_eq12 (= atomic (eqn (sub i i) cG))
-- -> Pair encoded_sub_ii (reify (code cG)).

stageC_eq12 : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula F_b_eq12)))
                      (ap2 Pair encoded_sub_ii (reify (code cG)))))
stageC_eq12 x =
  let
      s1 = subT_codeFormula_atomic zero (encoded_th_x_at x) (ap2 sub i i) cG

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT (vc0sub x) (reify (code (ap2 sub i i))))
                                          (ap2 subT (vc0sub x) (reify (code cG))))
                               (ap2 Pair encoded_sub_ii (ap2 subT (vc0sub x) (reify (code cG))))))
      s2 = congL Pair (ap2 subT (vc0sub x) (reify (code cG))) (bC_subII x)

      s3 : Deriv (atomic (eqn (ap2 Pair encoded_sub_ii (ap2 subT (vc0sub x) (reify (code cG))))
                               (ap2 Pair encoded_sub_ii (reify (code cG)))))
      s3 = congR Pair encoded_sub_ii (bC_cG x)

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage C: distribute F_b_eq01 (= atomic (eqn x0 (sub i i)))
-- -> Pair (encoded_th_x_at x) encoded_sub_ii.

stageC_eq01 : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula F_b_eq01)))
                      (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
stageC_eq01 x =
  let
      s1 = subT_codeFormula_atomic zero (encoded_th_x_at x) x0 (ap2 sub i i)

      s2 : Deriv (atomic (eqn (ap2 Pair (ap2 subT (vc0sub x) (reify (code x0)))
                                          (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))))
                               (ap2 Pair (encoded_th_x_at x) (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))))))
      s2 = congL Pair (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))) (bC_v0 x)

      s3 : Deriv (atomic (eqn (ap2 Pair (encoded_th_x_at x) (ap2 subT (vc0sub x) (reify (code (ap2 sub i i)))))
                               (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
      s3 = congR Pair (encoded_th_x_at x) (bC_subII x)

  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage C: distribute (F_b_eq12 imp F_b_eq01).

stageC_eq12_imp_eq01 : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula (F_b_eq12 imp F_b_eq01))))
                      (ap2 Pair (reify tagImp)
                         (ap2 Pair (ap2 Pair encoded_sub_ii (reify (code cG)))
                                   (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))))
stageC_eq12_imp_eq01 x =
  let
      s1 = subT_codeFormula_imp zero (encoded_th_x_at x) F_b_eq12 F_b_eq01

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT (vc0sub x) (reify (codeFormula F_b_eq01))) (stageC_eq12 x))

      s3 = congR Pair (reify tagImp)
             (congR Pair (ap2 Pair encoded_sub_ii (reify (code cG))) (stageC_eq01 x))
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- Stage C: top-level.

stageC : (x : Term) ->
  Deriv (atomic (eqn (ap2 subT (vc0sub x) (reify (codeFormula F_b)))
                      (target_c x)))
stageC x =
  let
      s1 = subT_codeFormula_imp zero (encoded_th_x_at x) F_b_eq02 (F_b_eq12 imp F_b_eq01)

      s2 = congR Pair (reify tagImp)
             (congL Pair (ap2 subT (vc0sub x) (reify (codeFormula (F_b_eq12 imp F_b_eq01))))
                         (stageC_eq02 x))

      s3 = congR Pair (reify tagImp)
             (congR Pair (ap2 Pair (encoded_th_x_at x) (reify (code cG))) (stageC_eq12_imp_eq01 x))
  in ruleTrans s1 (ruleTrans s2 s3)

----------------------------------------------------------------------
-- step3_canon: chain Stage A + Stage B + Stage C with congR bridges.

step3_canon : (x : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (vc0sub x)
       (ap2 subT vc1sub
          (ap2 subT vc2sub (reify (codeFormula t_formula)))))
    (target_c x)))
step3_canon x =
  let
      bridge_a : Deriv (atomic (eqn
        (ap2 subT (vc0sub x)
           (ap2 subT vc1sub
              (ap2 subT vc2sub (reify (codeFormula t_formula)))))
        (ap2 subT (vc0sub x)
           (ap2 subT vc1sub (reify (codeFormula F_a))))))
      bridge_a = congR subT (vc0sub x) (congR subT vc1sub stageA)

      bridge_b : Deriv (atomic (eqn
        (ap2 subT (vc0sub x)
           (ap2 subT vc1sub (reify (codeFormula F_a))))
        (ap2 subT (vc0sub x) (reify (codeFormula F_b)))))
      bridge_b = congR subT (vc0sub x) stageB

      stageC_x : Deriv (atomic (eqn
        (ap2 subT (vc0sub x) (reify (codeFormula F_b)))
        (target_c x)))
      stageC_x = stageC x

  in ruleTrans bridge_a (ruleTrans bridge_b stageC_x)
