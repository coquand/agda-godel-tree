{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th14Step4Canonical
--
-- Phase C step 4 canonicalization (NEXT-SESSION-PHASE-C-CONTINUE.md (C2)):
-- bridges  step4_l 's RHS  subT (Pair varCode1T (cor x)) cG  through
-- the cG -> reify (codeFormula G_norm) bridge (via the meta-equation
-- G_unfold ) and through  subT_codeFormula_neg  (Th14SubTPushthrough)
-- to expose the outer  tagNeg  head explicitly.
--
-- The exposed  tagNeg  head is what  step5_l 's outer mp dispatch
-- (thmTDispMp_param at constr5 layer) needs to identify the negated
-- branch of the encoded  not (atomic (eqn ...))  formula.
--
-- The result form is:
--
--   step4_l_neg : (x : Term) ->
--     Deriv (PrAtX x imp atomic (eqn
--       (ap1 thmT (ap1 K_part x))
--       (ap2 Pair (reify tagNeg)
--                  (ap2 subT (ap2 Pair varCode1T (ap1 cor x))
--                            (reify (codeFormula <inner_atomic>))))))
--
-- where  <inner_atomic>  is  atomic (eqn (ap1 thmT (var 1))
--                                          (ap2 sub (reify j) (reify j)))
-- (= the inner equation of  G_norm , Definition of which uses  j
-- abstract from BRA2.Thm11Diagonal).
--
-- Further canonicalization through  subT_codeFormula_atomic  on the
-- inner equation (to expose code(thmT(var 1)) and code(ap2 sub ...))
-- is left to the next layer (step5_l in BRA2.Th14Step5).
--
-- ASCII only.  No postulates, no holes, no with-abstraction, no dot
-- patterns.

module BRA2.Th14Step4Canonical where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor      using (cor)
open import BRA2.Sub      using (sub)
open import BRA2.SubT     using (subT)

open import BRA2.Thm.ThmT using (thmT)

open import BRA2.Thm.EvalHelpers
  using (liftAxiom ; liftedRuleTrans)

open import BRA2.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA2.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA2.GoedelII using (i ; cG ; G ; G_norm ; G_unfold ; j ; PrAtX)

import BRA2.Th14Step4

open import BRA2.Th14SubTPushthrough using (subT_codeFormula_neg)

----------------------------------------------------------------------
-- Convenience.

private
  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

----------------------------------------------------------------------
-- The Th14Step4Canonical module proper.  Parametric in r12_th, r12_sub
-- so it can refer to  K_part  and chain  step4_l .

module Th14Step4Canonical
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub using (K_part)

  open BRA2.Th14Step4.Th14Step4 r12_th r12_sub using (step4_l)

  --------------------------------------------------------------------
  -- The inner equation of  G_norm .  This is  atomic (eqn (ap1 thmT
  -- (var 1)) (ap2 sub (reify j) (reify j)))  --  Definition 12 's
  -- "th(x_1) != sub(i,i)"  's inner  th(x_1) = sub(i,i) .

  -- G_norm = not (atomic (eqn (ap1 thmT (var 1)) (ap2 sub (reify j) (reify j))))
  -- (per  BRA2.Thm11Diagonal.G_norm 's definition).
  inner_eq : Formula
  inner_eq = atomic (eqn (ap1 thmT (var (suc zero)))
                          (ap2 sub (reify j) (reify j)))

  -- G_norm = not inner_eq , by Agda definitional equality.  We assert
  -- this as a refl-witnessed Eq so we can transport later.
  G_norm_unfold : Eq G_norm (not inner_eq)
  G_norm_unfold = refl

  --------------------------------------------------------------------
  -- cG meta-equality bridge: cG  =  reify (codeFormula (not inner_eq)) .
  --
  -- Three steps:
  --   * G_unfold      : Eq G G_norm
  --   * eqCong codeFormula : Eq (codeFormula G) (codeFormula G_norm)
  --   * eqCong reify       : Eq cG (reify (codeFormula G_norm))
  --   * G_norm_unfold      : Eq G_norm (not inner_eq) -- transport via eqCong.

  cG_to_neg_form : Eq cG (reify (codeFormula (not inner_eq)))
  cG_to_neg_form =
    let
        -- Eq G G_norm.
        e1 : Eq G G_norm
        e1 = G_unfold

        -- Eq G (not inner_eq).
        e2 : Eq G (not inner_eq)
        e2 = eqTrans e1 G_norm_unfold

        -- Eq (codeFormula G) (codeFormula (not inner_eq)).
        e3 : Eq (codeFormula G) (codeFormula (not inner_eq))
        e3 = eqCong codeFormula e2
    in eqCong reify e3

  --------------------------------------------------------------------
  -- step4_l_neg : the canonicalized step 4 with  tagNeg  head exposed.
  --
  -- Construction:
  --   * step4_l x : ... = subT (Pair varCode1T (cor x)) cG
  --   * eqSubst with cG_to_neg_form: ... = subT (Pair varCode1T (cor x)) (reify (codeFormula (not inner_eq)))
  --   * subT_codeFormula_neg lifted under PrAtX x: bridges to
  --       Pair tagNeg (subT (Pair varCode1T (cor x)) (reify (codeFormula inner_eq)))

  step4_l_neg : (x : Term) ->
    Deriv (PrAtX x imp
            atomic (eqn (ap1 thmT (ap1 K_part x))
                        (ap2 Pair (reify tagNeg)
                          (ap2 subT (ap2 Pair varCode1T (ap1 cor x))
                                    (reify (codeFormula inner_eq))))))
  step4_l_neg x =
    let
        P : Formula
        P = PrAtX x

        p_subst : Term
        p_subst = ap2 Pair varCode1T (ap1 cor x)

        -- step4_l x: PrAtX x imp ... = subT p_subst cG
        sa : Deriv (P imp atomic (eqn (ap1 thmT (ap1 K_part x))
                                       (ap2 subT p_subst cG)))
        sa = step4_l x

        -- Transport cG -> reify (codeFormula (not inner_eq)) via
        -- cG_to_neg_form (meta-equation).  Use eqSubst to apply at the
        -- Deriv level.
        sb : Deriv (P imp atomic (eqn (ap1 thmT (ap1 K_part x))
                                       (ap2 subT p_subst
                                             (reify (codeFormula (not inner_eq))))))
        sb =
          eqSubst
            (\ T -> Deriv (P imp atomic (eqn (ap1 thmT (ap1 K_part x))
                                               (ap2 subT p_subst T))))
            cG_to_neg_form
            sa

        -- subT_codeFormula_neg  (closed): subT(p_subst)(reify (codeFormula (not P_)))
        --   = Pair tagNeg (subT(p_subst)(reify (codeFormula P_)))
        sc_closed :
          Deriv (atomic (eqn
            (ap2 subT p_subst (reify (codeFormula (not inner_eq))))
            (ap2 Pair (reify tagNeg)
                      (ap2 subT p_subst (reify (codeFormula inner_eq))))))
        sc_closed = subT_codeFormula_neg (suc zero) (ap1 cor x) inner_eq

        -- Lift sc_closed under P.
        sc_lifted :
          Deriv (P imp atomic (eqn
            (ap2 subT p_subst (reify (codeFormula (not inner_eq))))
            (ap2 Pair (reify tagNeg)
                      (ap2 subT p_subst (reify (codeFormula inner_eq))))))
        sc_lifted = liftAxiom P sc_closed

    in liftedRuleTrans P
         (ap1 thmT (ap1 K_part x))
         (ap2 subT p_subst (reify (codeFormula (not inner_eq))))
         (ap2 Pair (reify tagNeg)
                   (ap2 subT p_subst (reify (codeFormula inner_eq))))
         sb sc_lifted
