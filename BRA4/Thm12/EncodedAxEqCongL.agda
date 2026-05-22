{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqCongL -- encoded  ax_eqCongL  instance via single
-- 3-variable simultaneous sb-wrap on axN6.
--
-- Goal (universal in g : Fun2, tA tB tC : Term ; no Closed) :
--
--   Df_axEqCongL : Fun2 -> Term -> Term -> Term -> Term
--   encodedAxEqCongL :
--     (g : Fun2) (tA tB tC : Term) ->
--     Deriv (eqF (ap1 thmT (Df_axEqCongL g tA tB tC))
--                 (encodedAxEqCongL_Term g tA tB tC))
--
-- where  encodedAxEqCongL_Term g tA tB tC  is the encoded form of
--   "(tA = tB) > (g(tA, tC) = g(tB, tC))".  ( tC is the substituent
-- name; using lowercase  t-  prefix to avoid clashing with the BRA
-- combinator  C  which is the composition operator.)
--
-- Construction.  Df_axEqCongL g tA tB tC = pi tag_sb3 (pi spec3 packAx6_codeF2 g)
-- with spec3 = spec3T 0 1 2 tA tB tC.
--
-- thmT walks the wrap :
--   thmT (Df_axEqCongL g tA tB tC)
--     = sbf3 spec3 (thmT (packAx 6 (codeFun2 g)))      [thmT_at_sb3]
--     = sbf3 spec3 (outputRHS6 (codeFun2 g))           [thmT_at_axN6]
--     = encodedAxEqCongL_Term g tA tB tC               [sbf3 cascade]

module BRA4.Thm12.EncodedAxEqCongL where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun2 )
open import BRA4.SbContract3
open import BRA4.SbT3              using ( sbt3 )
open import BRA4.SbF3              using ( sbf3 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb3         using ( thmT_at_sb3 )
open import BRA4.ThmTAtAx6         using ( thmT_at_axN6 )

open SbContract3 sbContract3

------------------------------------------------------------------------
-- Constants and helpers.

private
  N6 : Nat
  N6 = suc (suc (suc (suc (suc (suc zero)))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 Pair (natCode tag_var) (natCode (suc (suc zero)))

  cEq01 : Term
  cEq01 = ap2 Pair (natCode tag_eq) (ap2 Pair cV0 cV1)

  -- code(ap2 g vi vj) = pi tag_ap2 (pi gT (pi vi vj))
  cAp2_g_at : Term -> Term -> Term -> Term
  cAp2_g_at gT viT vjT =
    ap2 Pair (natCode tag_ap2) (ap2 Pair gT (ap2 Pair viT vjT))

  outputRHS6 : Term -> Term
  outputRHS6 gT =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair cEq01
        (ap2 Pair (natCode tag_eq)
          (ap2 Pair (cAp2_g_at gT cV0 cV2) (cAp2_g_at gT cV1 cV2))))

  packAx6_codeF2 : Fun2 -> Term
  packAx6_codeF2 g =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N6) (codeFun2 g))

  spec3_at : Term -> Term -> Term -> Term
  spec3_at tA tB tC = spec3T zero (suc zero) (suc (suc zero)) tA tB tC

------------------------------------------------------------------------
-- Df_axEqCongL : Fun2 -> Term -> Term -> Term -> Term.

Df_axEqCongL : Fun2 -> Term -> Term -> Term -> Term
Df_axEqCongL g tA tB tC =
  ap2 Pair (natCode tag_sb3)
    (ap2 Pair (spec3_at tA tB tC) (packAx6_codeF2 g))

------------------------------------------------------------------------
-- The target encoded formula.

encodedAxEqCongL_Term : Fun2 -> Term -> Term -> Term -> Term
encodedAxEqCongL_Term g tA tB tC =
  ap2 Pair (natCode tag_imp)
    (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB))
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g) (ap2 Pair tA tC)))
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g) (ap2 Pair tB tC))))))

------------------------------------------------------------------------
-- sbf3-cascade lemma.

private
  sbf3_step :
    (g : Fun2) (tA tB tC : Term) ->
    Deriv (eqF (ap2 sbf3 (spec3_at tA tB tC) (outputRHS6 (codeFun2 g)))
                (encodedAxEqCongL_Term g tA tB tC))
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

        -- (b) sbt3 sp (cAp2_g_at (codeFun2 g) cV0 cV2).
        e_lhs_step :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV0 cV2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt3 sp cV0)
                            (ap2 sbt3 sp cV2)))))
        e_lhs_step =
          sbt3_at_ap2 zero (suc zero) (suc (suc zero)) tA tB tC g cV0 cV2

        e_lhs_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV0) (ap2 sbt3 sp cV2))
                      (ap2 Pair tA tC))
        e_lhs_inner =
          ruleTrans (congL Pair (ap2 sbt3 sp cV2) e_cV0)
                    (congR Pair tA e_cV2)

        e_lhs :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV0 cV2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g) (ap2 Pair tA tC))))
        e_lhs =
          ruleTrans e_lhs_step
            (congR Pair (natCode tag_ap2)
              (congR Pair (codeFun2 g) e_lhs_inner))

        -- sbt3 sp (cAp2_g_at (codeFun2 g) cV1 cV2).
        e_rhs_step :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV1 cV2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt3 sp cV1)
                            (ap2 sbt3 sp cV2)))))
        e_rhs_step =
          sbt3_at_ap2 zero (suc zero) (suc (suc zero)) tA tB tC g cV1 cV2

        e_rhs_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV1) (ap2 sbt3 sp cV2))
                      (ap2 Pair tB tC))
        e_rhs_inner =
          ruleTrans (congL Pair (ap2 sbt3 sp cV2) e_cV1)
                    (congR Pair tB e_cV2)

        e_rhs :
          Deriv (eqF (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV1 cV2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g) (ap2 Pair tB tC))))
        e_rhs =
          ruleTrans e_rhs_step
            (congR Pair (natCode tag_ap2)
              (congR Pair (codeFun2 g) e_rhs_inner))

        -- (c) sbf3 sp (Pair tag_eq (Pair (cAp2_g_at (codeFun2 g) cV0 cV2)
        --                                (cAp2_g_at (codeFun2 g) cV1 cV2))) .
        e_eq_consAtomic :
          Deriv (eqF
            (ap2 sbf3 sp
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair (cAp2_g_at (codeFun2 g) cV0 cV2)
                          (cAp2_g_at (codeFun2 g) cV1 cV2))))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair
                (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV0 cV2))
                (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV1 cV2)))))
        e_eq_consAtomic =
          sbf3_at_atomic zero (suc zero) (suc (suc zero)) tA tB tC
            (cAp2_g_at (codeFun2 g) cV0 cV2)
            (cAp2_g_at (codeFun2 g) cV1 cV2)

        e_eq_consInner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV0 cV2))
                       (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV1 cV2)))
            (ap2 Pair
              (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tA tC)))
              (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tB tC)))))
        e_eq_consInner =
          ruleTrans
            (congL Pair (ap2 sbt3 sp (cAp2_g_at (codeFun2 g) cV1 cV2)) e_lhs)
            (congR Pair
              (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tA tC)))
              e_rhs)

        e_eq_cons :
          Deriv (eqF
            (ap2 sbf3 sp
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair (cAp2_g_at (codeFun2 g) cV0 cV2)
                          (cAp2_g_at (codeFun2 g) cV1 cV2))))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair
                (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tA tC)))
                (ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair tB tC))))))
        e_eq_cons =
          ruleTrans e_eq_consAtomic
            (congR Pair (natCode tag_eq) e_eq_consInner)

        -- (d) sbf3_at_imp.
        ant : Term
        ant = cEq01

        cons : Term
        cons =
          ap2 Pair (natCode tag_eq)
            (ap2 Pair (cAp2_g_at (codeFun2 g) cV0 cV2)
                      (cAp2_g_at (codeFun2 g) cV1 cV2))

        e_imp :
          Deriv (eqF (ap2 sbf3 sp (outputRHS6 (codeFun2 g)))
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
                             (ap2 Pair (codeFun2 g) (ap2 Pair tA tC)))
                           (ap2 Pair (natCode tag_ap2)
                             (ap2 Pair (codeFun2 g) (ap2 Pair tB tC)))))))
        e_imp_inner =
          ruleTrans (congL Pair (ap2 sbf3 sp cons) e_eq01)
                    (congR Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB)) e_eq_cons)

    in ruleTrans e_imp (congR Pair (natCode tag_imp) e_imp_inner)

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqCongL :
  (g : Fun2) (tA tB tC : Term) ->
  Deriv (eqF (ap1 thmT (Df_axEqCongL g tA tB tC))
              (encodedAxEqCongL_Term g tA tB tC))
encodedAxEqCongL g tA tB tC =
  let sp : Term
      sp = spec3_at tA tB tC

      pa : Term
      pa = packAx6_codeF2 g

      e_at_sb3 :
        Deriv (eqF (ap1 thmT (Df_axEqCongL g tA tB tC))
                    (ap2 sbf3 sp (ap1 thmT pa)))
      e_at_sb3 = thmT_at_sb3 sp pa

      e_axN6 :
        Deriv (eqF (ap1 thmT pa) (outputRHS6 (codeFun2 g)))
      e_axN6 = thmT_at_axN6 (codeFun2 g)

      e_lift_axN6 :
        Deriv (eqF (ap2 sbf3 sp (ap1 thmT pa))
                    (ap2 sbf3 sp (outputRHS6 (codeFun2 g))))
      e_lift_axN6 = congR sbf3 sp e_axN6

      e_sbf3 :
        Deriv (eqF (ap2 sbf3 sp (outputRHS6 (codeFun2 g)))
                    (encodedAxEqCongL_Term g tA tB tC))
      e_sbf3 = sbf3_step g tA tB tC

  in ruleTrans e_at_sb3
       (ruleTrans e_lift_axN6 e_sbf3)
