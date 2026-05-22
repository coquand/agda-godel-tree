{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14GodelII -- Goedel's Second Incompleteness Theorem for
-- BRA , Guard 1963 Theorem 14 (p. 17) final assembly .
--
-- Statement :
--
--     godelII : Deriv ConSchema -> Deriv falseF
--
-- where
--
--     ConSchema = neg (eqF (ap1 thmT (var 0)) (codeFormula falseF))
--
-- Argument (closing on Step 5 of Thm 14) :
--
--   (1) step5 (var 1)  :  imp (P_x (var 1))  (eqF (thmT (big_term (var 1))) codeFalse)
--                       =  imp (eqF (thmT (var 1)) j)
--                              (eqF (thmT (big_term (var 1))) codeFalse) .
--   (2) ruleInst 0 (big_term (var 1)) on Con :
--          Deriv (substF 0 (big_term (var 1)) ConSchema)
--        ≡ Deriv (neg (eqF (ap1 thmT (big_term (var 1))) codeFalse))
--        (bridge via Closed codeFalse + definitional substT 0 ... (var 0) = big_term (var 1)) .
--   (3) Apply axContrapos + mp twice :
--          Deriv (neg (eqF (thmT (var 1)) j)) .
--   (4) Bridge to Thm14F's G via predicate-Leibniz  BRA3.Substitutivity.substF_cong
--       at  k = 2 , a = j , b = ap2 sub i i , Phi = neg (eqF (thmT (var 1)) (var 2)) :
--          imp (substF 2 j Phi)         (substF 2 (ap2 sub i i) Phi)
--        = imp (neg (eqF (thmT (var 1)) j))
--              (neg (eqF (thmT (var 1)) (ap2 sub i i)))
--        = imp (neg P_x var 1) G .
--       Apply mp on (3) :  Deriv G .
--   (5) godelI_at_subform G d_G  :  Deriv falseF .  Same shape as
--        BRA4.GoedelI.godelI but using Thm14F's sub-form  diag_term_eq
--        instead of BRA4.Diagonal 's sbf-form .

module BRA4.Thm.Thm14GodelII where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFormula ; falseF ; codeFalse )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Encode            using ( encode )
open import BRA4.Sub               using ( sub )
open import BRA4.ThmTCompleteRec   using ( thmT_complete_rec )
open import BRA4.Thm.Thm14F
  using ( i ; iNat ; j ; G ; F ; H ; diag_inst ; diag_term_eq
        ; sub_ii_eq_j )
open import BRA4.Thm.Thm14Step1    using ( P_x )
open import BRA4.Thm.Thm14Step5    using ( big_term ; step5 )

open import BRA3.Contrapositive    using ( axExFalso ; axContrapos )
open import BRA3.Substitutivity    using ( substF_cong )
open import BRA3.Dispatch
  using ( closed_O ; closed_ap1 ; closed_ap2 ; closed_natCode ; closedAt )

------------------------------------------------------------------------
-- The target falseF formula and consistency schema .

P_false : Formula
P_false = falseF

ConSchema : Formula
ConSchema = neg (eqF (ap1 thmT (var zero)) codeFalse)

------------------------------------------------------------------------
-- Closedness of codeFalse .
--
--   codeFalse  =  codeFormula falseF
--              =  ap2 Pair (natCode tag_eq)
--                  (ap2 Pair (codeTerm O) (codeTerm (ap1 s O)))
--              =  ap2 Pair (natCode tag_eq)
--                  (ap2 Pair O
--                    (ap2 Pair (natCode tag_ap1)
--                      (ap2 Pair (natCode tag_s) O))) .
--
-- All leaves are  O  or  natCode  -- closed .

closed_codeFalse : Closed codeFalse
closed_codeFalse =
  closed_ap2 Pair (natCode tag_eq)
    (ap2 Pair O
      (ap2 Pair (natCode tag_ap1)
        (ap2 Pair (natCode tag_s) O)))
    (closed_natCode tag_eq)
    (closed_ap2 Pair O
       (ap2 Pair (natCode tag_ap1)
         (ap2 Pair (natCode tag_s) O))
       closed_O
       (closed_ap2 Pair (natCode tag_ap1)
          (ap2 Pair (natCode tag_s) O)
          (closed_natCode tag_ap1)
          (closed_ap2 Pair (natCode tag_s) O
             (closed_natCode tag_s)
             closed_O)))

------------------------------------------------------------------------
-- Closedness of  i  (= natCode iNat ) and  ap2 sub i i .

closed_i : Closed i
closed_i = closed_natCode iNat

closed_sub_ii : Closed (ap2 sub i i)
closed_sub_ii = closed_ap2 sub i i closed_i closed_i

------------------------------------------------------------------------
-- godelI_subform : same as BRA4.GoedelI.godelI but for Thm14F 's G
--  (which uses  ap2 sub i i  in place of  Diagonal 's sbf-form ) .

godelI_subform : Deriv G -> Deriv P_false
godelI_subform d =
  let
    y : Term
    y = encode d

    eq1 : Deriv (eqF (ap1 thmT y) (codeFormula G))
    eq1 = thmT_complete_rec d

    diag_sym : Deriv (eqF (codeFormula G) (ap2 sub i i))
    diag_sym = ruleSym diag_term_eq

    eq2 : Deriv (eqF (ap1 thmT y) (ap2 sub i i))
    eq2 = ruleTrans eq1 diag_sym

    d_subst1 : Deriv (substF (suc zero) y G)
    d_subst1 = ruleInst (suc zero) y d

    -- substF 1 y G  evaluates Agda-definitionally to
    --   neg (atomic (eqn (ap1 thmT y) (substT 1 y (ap2 sub i i))))
    -- via natEq 1 1 = true on the var-1 slot inside ap1 thmT.

    subst_sub_ii_eq : Eq (substT (suc zero) y (ap2 sub i i)) (ap2 sub i i)
    subst_sub_ii_eq = closedAt closed_sub_ii (suc zero) y

    d_inst_neg : Deriv (neg (atomic (eqn (ap1 thmT y) (ap2 sub i i))))
    d_inst_neg =
      eqSubst (\ z -> Deriv (neg (atomic (eqn (ap1 thmT y) z))))
              subst_sub_ii_eq
              d_subst1

    eq_form : Formula
    eq_form = atomic (eqn (ap1 thmT y) (ap2 sub i i))

    exFalso_imp : Deriv (imp eq_form (imp (neg eq_form) P_false))
    exFalso_imp = axExFalso eq_form P_false

    step_after_eq : Deriv (imp (neg eq_form) P_false)
    step_after_eq = mp exFalso_imp eq2

    result : Deriv P_false
    result = mp step_after_eq d_inst_neg
  in result

------------------------------------------------------------------------
-- The bridge predicate  Phi  used by  substF_cong .
--
--   Phi  =  neg (eqF (ap1 thmT (var 1)) (var 2))
--
-- Then:
--   substF 2 j         Phi  =  neg (eqF (ap1 thmT (var 1)) j)         (definitional)
--   substF 2 (sub i i) Phi  =  neg (eqF (ap1 thmT (var 1)) (sub i i))  = G

Phi : Formula
Phi = neg (eqF (ap1 thmT (var (suc zero))) (var (suc (suc zero))))

------------------------------------------------------------------------
-- GOEDEL II.

godelII : Deriv ConSchema -> Deriv P_false
godelII d_con =
  let
    --------------------------------------------------------------------
    -- (1) Step 5 at x = var 1 .

    step5_v1 :
      Deriv (imp (eqF (ap1 thmT (var (suc zero))) j)
                  (eqF (ap1 thmT (big_term (var (suc zero)))) codeFalse))
    step5_v1 = step5 (var (suc zero))

    --------------------------------------------------------------------
    -- (2) ruleInst 0 (big_term (var 1)) on Con  +  closed-bridge for codeFalse .
    --
    -- substF 0 (big_term (var 1)) ConSchema
    --   = neg (eqF (substT 0 (big_term (var 1)) (ap1 thmT (var 0)))
    --               (substT 0 (big_term (var 1)) codeFalse))
    --   = neg (eqF (ap1 thmT (big_term (var 1)))   [substT 0 t (var 0) = t definitionally]
    --               (substT 0 (big_term (var 1)) codeFalse))
    -- Bridge:  substT 0 (big_term (var 1)) codeFalse = codeFalse  via Closed.

    d_con_inst : Deriv (substF zero (big_term (var (suc zero))) ConSchema)
    d_con_inst = ruleInst zero (big_term (var (suc zero))) d_con

    subst_codeFalse_eq :
      Eq (substT zero (big_term (var (suc zero))) codeFalse) codeFalse
    subst_codeFalse_eq = closedAt closed_codeFalse zero (big_term (var (suc zero)))

    neg_thmT_bigterm_codeFalse :
      Deriv (neg (eqF (ap1 thmT (big_term (var (suc zero)))) codeFalse))
    neg_thmT_bigterm_codeFalse =
      eqSubst (\ z -> Deriv (neg (eqF (ap1 thmT (big_term (var (suc zero)))) z)))
              subst_codeFalse_eq
              d_con_inst

    --------------------------------------------------------------------
    -- (3) axContrapos + mp + mp  ->  Deriv (neg (eqF (thmT (var 1)) j)) .

    A_form : Formula
    A_form = eqF (ap1 thmT (var (suc zero))) j

    B_form : Formula
    B_form = eqF (ap1 thmT (big_term (var (suc zero)))) codeFalse

    contra : Deriv (imp (imp A_form B_form) (imp (neg B_form) (neg A_form)))
    contra = axContrapos A_form B_form

    contra_at_step5 : Deriv (imp (neg B_form) (neg A_form))
    contra_at_step5 = mp contra step5_v1

    neg_A : Deriv (neg A_form)
    neg_A = mp contra_at_step5 neg_thmT_bigterm_codeFalse

    --------------------------------------------------------------------
    -- (4) substF_cong  Phi  bridge :  Deriv (imp (neg A_form) G) .

    sub_ii_eq_j_rev : Deriv (eqF j (ap2 sub i i))
    sub_ii_eq_j_rev = ruleSym sub_ii_eq_j

    bridge :
      Deriv (imp (substF (suc (suc zero)) j Phi)
                  (substF (suc (suc zero)) (ap2 sub i i) Phi))
    bridge = substF_cong (suc (suc zero)) j (ap2 sub i i) sub_ii_eq_j_rev Phi

    -- substF 2 j Phi reduces definitionally to neg A_form .
    -- substF 2 (ap2 sub i i) Phi reduces definitionally to G .

    d_G : Deriv G
    d_G = mp bridge neg_A

    --------------------------------------------------------------------
    -- (5) godelI_subform .

  in godelI_subform d_G
