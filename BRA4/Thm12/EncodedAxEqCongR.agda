{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqCongR -- encoded  ax_eqCongR  instance via single
-- 3-variable simultaneous sb-wrap on axN7.
--
-- Schema axN7 :  (v0 = v1)  >  (g(v2, v0) = g(v2, v1)) ,  extra = codeFun2 g .
--
-- Goal (universal in g : Fun2, tA tB tC : Term ; no Closed) :
--
--   encodedAxEqCongR_Term g tA tB tC
--     = encoded( (tA = tB)  >  (g(tC, tA) = g(tC, tB)) )

module BRA4.Thm12.EncodedAxEqCongR where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun2 )
open import BRA4.SbContract3
open import BRA4.SbT3              using ( sbt3 )
open import BRA4.SbF3              using ( sbf3 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb3         using ( thmT_at_sb3 )
open import BRA4.ThmTAtAx7         using ( thmT_at_axN7 )

open SbContract3 sbContract3

------------------------------------------------------------------------
-- Constants and helpers.

private
  N7 : Nat
  N7 = suc (suc (suc (suc (suc (suc (suc zero))))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 Pair (natCode tag_var) (natCode (suc (suc zero)))

  cEq01 : Term
  cEq01 = ap2 Pair (natCode tag_eq) (ap2 Pair cV0 cV1)

  cAp2_g_at : Term -> Term -> Term -> Term
  cAp2_g_at gT viT vjT =
    ap2 Pair (natCode tag_ap2) (ap2 Pair gT (ap2 Pair viT vjT))

  outputRHS7 : Term -> Term
  outputRHS7 gT =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair cEq01
        (ap2 Pair (natCode tag_eq)
          (ap2 Pair (cAp2_g_at gT cV2 cV0) (cAp2_g_at gT cV2 cV1))))

  packAx7_codeF2 : Fun2 -> Term
  packAx7_codeF2 g =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N7) (codeFun2 g))

  spec3_at : Term -> Term -> Term -> Term
  spec3_at tA tB tC = spec3T zero (suc zero) (suc (suc zero)) tA tB tC

------------------------------------------------------------------------
-- Df_axEqCongR : Fun2 -> Term -> Term -> Term -> Term.

Df_axEqCongR : Fun2 -> Term -> Term -> Term -> Term
Df_axEqCongR g tA tB tC =
  ap2 Pair (natCode tag_sb3)
    (ap2 Pair (spec3_at tA tB tC) (packAx7_codeF2 g))

------------------------------------------------------------------------
-- The target encoded formula.

encodedAxEqCongR_Term : Fun2 -> Term -> Term -> Term -> Term
encodedAxEqCongR_Term g tA tB tC =
  ap2 Pair (natCode tag_imp)
    (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB))
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g) (ap2 Pair tC tA)))
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g) (ap2 Pair tC tB))))))

------------------------------------------------------------------------
-- sbf3-cascade lemma.

private
  sbf3_step :
    (g : Fun2) (tA tB tC : Term) ->
    Deriv (eqF (ap2 sbf3 (spec3_at tA tB tC) (outputRHS7 (codeFun2 g)))
                (encodedAxEqCongR_Term g tA tB tC))
  sbf3_step g tA tB tC =
    let sp : Term
        sp = spec3_at tA tB tC

        e_cV0 : Deriv (eqF (ap2 sbt3 sp cV0) tA)
        e_cV0 = sbt3_at_var_match_one zero (suc zero) (suc (suc zero)) tA tB tC

        e_cV1 : Deriv (eqF (ap2 sbt3 sp cV1) tB)
        e_cV1 = sbt3_at_var_match_two zero (suc zero) (suc (suc zero)) tA tB tC refl

        e_cV2 : Deriv (eqF (ap2 sbt3 sp cV2) tC)
        e_cV2 = sbt3_at_var_match_three zero (suc zero) (suc (suc zero)) tA tB tC refl refl

        -- (a) sbf3 sp cEq01 = Pair tag_eq (Pair tA tB).
        e_eq01_atomic :
          Deriv (eqF (ap2 sbf3 sp cEq01)
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair (ap2 sbt3 sp cV0) (ap2 sbt3 sp cV1))))
        e_eq01_atomic =
          sbf3_at_atomic zero (suc zero) (suc (suc zero)) tA tB tC cV0 cV1

        e_eq01_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV0) (ap2 sbt3 sp cV1))
                      (ap2 Pair tA tB))
        e_eq01_inner =
          ruleTrans (congL Pair (ap2 sbt3 sp cV1) e_cV0)
                    (congR Pair tA e_cV1)

        e_eq01 :
          Deriv (eqF (ap2 sbf3 sp cEq01)
                      (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB)))
        e_eq01 =
          ruleTrans e_eq01_atomic
            (congR Pair (natCode tag_eq) e_eq01_inner)

        -- (b) sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV0).
        e_lhs_step :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV0))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt3 sp cV2)
                            (ap2 sbt3 sp cV0)))))
        e_lhs_step =
          sbt3_at_ap2 zero (suc zero) (suc (suc zero)) tA tB tC g cV2 cV0

        e_lhs_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV2) (ap2 sbt3 sp cV0))
                      (ap2 Pair tC tA))
        e_lhs_inner =
          ruleTrans (congL Pair (ap2 sbt3 sp cV0) e_cV2)
                    (congR Pair tC e_cV0)

        e_lhs :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV0))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g) (ap2 Pair tC tA))))
        e_lhs =
          ruleTrans e_lhs_step
            (congR Pair (natCode tag_ap2)
              (congR Pair (codeFun2 g) e_lhs_inner))

        -- sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV1).
        e_rhs_step :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV1))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt3 sp cV2)
                            (ap2 sbt3 sp cV1)))))
        e_rhs_step =
          sbt3_at_ap2 zero (suc zero) (suc (suc zero)) tA tB tC g cV2 cV1

        e_rhs_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV2) (ap2 sbt3 sp cV1))
                      (ap2 Pair tC tB))
        e_rhs_inner =
          ruleTrans (congL Pair (ap2 sbt3 sp cV1) e_cV2)
                    (congR Pair tC e_cV1)

        e_rhs :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV1))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g) (ap2 Pair tC tB))))
        e_rhs =
          ruleTrans e_rhs_step
            (congR Pair (natCode tag_ap2)
              (congR Pair (codeFun2 g) e_rhs_inner))

        -- (c) sbf3 sp on the consequent.
        e_eq_consAtomic :
          Deriv (eqF
            (ap2 sbf3 sp
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair (cAp2_g_at (codeFun2 g) cV2 cV0)
                          (cAp2_g_at (codeFun2 g) cV2 cV1))))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair
                (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV0))
                (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV1)))))
        e_eq_consAtomic =
          sbf3_at_atomic zero (suc zero) (suc (suc zero)) tA tB tC
            (cAp2_g_at (codeFun2 g) cV2 cV0)
            (cAp2_g_at (codeFun2 g) cV2 cV1)

        e_eq_consInner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV0))
                       (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV1)))
            (ap2 Pair
              (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tC tA)))
              (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tC tB)))))
        e_eq_consInner =
          ruleTrans
            (congL Pair (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV2 cV1)) e_lhs)
            (congR Pair
              (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tC tA)))
              e_rhs)

        e_eq_cons :
          Deriv (eqF
            (ap2 sbf3 sp
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair (cAp2_g_at (codeFun2 g) cV2 cV0)
                          (cAp2_g_at (codeFun2 g) cV2 cV1))))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair
                (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tC tA)))
                (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tC tB))))))
        e_eq_cons =
          ruleTrans e_eq_consAtomic
            (congR Pair (natCode tag_eq) e_eq_consInner)

        -- (d) sbf3_at_imp.
        ant : Term
        ant = cEq01

        cons : Term
        cons =
          ap2 Pair (natCode tag_eq)
            (ap2 Pair (cAp2_g_at (codeFun2 g) cV2 cV0)
                      (cAp2_g_at (codeFun2 g) cV2 cV1))

        e_imp :
          Deriv (eqF (ap2 sbf3 sp (outputRHS7 (codeFun2 g)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair (ap2 sbf3 sp ant) (ap2 sbf3 sp cons))))
        e_imp =
          sbf3_at_imp zero (suc zero) (suc (suc zero)) tA tB tC ant cons

        e_imp_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbf3 sp ant) (ap2 sbf3 sp cons))
            (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB))
                       (ap2 Pair (natCode tag_eq)
                         (ap2 Pair
                           (ap2 Pair (natCode tag_ap2)
                             (ap2 Pair (codeFun2 g) (ap2 Pair tC tA)))
                           (ap2 Pair (natCode tag_ap2)
                             (ap2 Pair (codeFun2 g) (ap2 Pair tC tB)))))))
        e_imp_inner =
          ruleTrans (congL Pair (ap2 sbf3 sp cons) e_eq01)
                    (congR Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB)) e_eq_cons)

    in ruleTrans e_imp (congR Pair (natCode tag_imp) e_imp_inner)

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqCongR :
  (g : Fun2) (tA tB tC : Term) ->
  Deriv (eqF (ap1 thmT (Df_axEqCongR g tA tB tC))
              (encodedAxEqCongR_Term g tA tB tC))
encodedAxEqCongR g tA tB tC =
  let sp : Term
      sp = spec3_at tA tB tC

      pa : Term
      pa = packAx7_codeF2 g

      e_at_sb3 :
        Deriv (eqF (ap1 thmT (Df_axEqCongR g tA tB tC))
                    (ap2 sbf3 sp (ap1 thmT pa)))
      e_at_sb3 = thmT_at_sb3 sp pa

      e_axN7 :
        Deriv (eqF (ap1 thmT pa) (outputRHS7 (codeFun2 g)))
      e_axN7 = thmT_at_axN7 (codeFun2 g)

      e_lift_axN7 :
        Deriv (eqF (ap2 sbf3 sp (ap1 thmT pa))
                    (ap2 sbf3 sp (outputRHS7 (codeFun2 g))))
      e_lift_axN7 = congR sbf3 sp e_axN7

      e_sbf3 :
        Deriv (eqF (ap2 sbf3 sp (outputRHS7 (codeFun2 g)))
                    (encodedAxEqCongR_Term g tA tB tC))
      e_sbf3 = sbf3_step g tA tB tC

  in ruleTrans e_at_sb3
       (ruleTrans e_lift_axN7 e_sbf3)
