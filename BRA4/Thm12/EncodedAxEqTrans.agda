{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqTrans -- encoded  ax_eqTrans  instance via single
-- 3-variable simultaneous sb-wrap on axN4.
--
-- Schema axN4 :  (v0 = v1)  >  (v0 = v2)  >  (v1 = v2) .  No  extra .
--
-- Goal (universal in tA tB tC : Term ; no Closed) :
--
--   encodedAxEqTrans_Term tA tB tC
--     = encoded( (tA = tB)  >  (tA = tC)  >  (tB = tC) )

module BRA4.Thm12.EncodedAxEqTrans where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFormula ; codeTerm )
open import BRA4.SbContract3
open import BRA4.SbT3              using ( sbt3 )
open import BRA4.SbF3              using ( sbf3 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb3         using ( thmT_at_sb3 )
open import BRA4.ThmTAtAx4         using ( thmT_at_axN4 )

open SbContract3 sbContract3

------------------------------------------------------------------------
-- Constants and helpers.

private
  N4 : Nat
  N4 = suc (suc (suc (suc zero)))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 Pair (natCode tag_var) (natCode (suc (suc zero)))

  -- The packed axiom Term  packAx 4 O .  (axN4 has no functor arg, so
  -- the "extra" slot is filled with the dummy  O .)
  packAx4 : Term
  packAx4 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N4) O)

  spec3_at : Term -> Term -> Term -> Term
  spec3_at tA tB tC = spec3T zero (suc zero) (suc (suc zero)) tA tB tC

  -- The outputRHS form is the codeFormula of the axN4 schema (a fixed
  -- closed-form Term independent of  extra ).
  outputRHS4_concrete : Term
  outputRHS4_concrete =
    codeFormula (imp (atomic (eqn (var zero) (var (suc zero))))
                      (imp (atomic (eqn (var zero) (var (suc (suc zero)))))
                           (atomic (eqn (var (suc zero)) (var (suc (suc zero)))))))

  -- Spelt out as explicit Pair structure (= outputRHS4_concrete , by
  -- codeFormula's defining equations).
  cEq01 : Term
  cEq01 = ap2 Pair (natCode tag_eq) (ap2 Pair cV0 cV1)

  cEq02 : Term
  cEq02 = ap2 Pair (natCode tag_eq) (ap2 Pair cV0 cV2)

  cEq12 : Term
  cEq12 = ap2 Pair (natCode tag_eq) (ap2 Pair cV1 cV2)

  outputRHS4_pair : Term
  outputRHS4_pair =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair cEq01
        (ap2 Pair (natCode tag_imp)
          (ap2 Pair cEq02 cEq12)))

------------------------------------------------------------------------
-- Df_axEqTrans : Term -> Term -> Term -> Term.

Df_axEqTrans : Term -> Term -> Term -> Term
Df_axEqTrans tA tB tC =
  ap2 Pair (natCode tag_sb3)
    (ap2 Pair (spec3_at tA tB tC) packAx4)

------------------------------------------------------------------------
-- The target encoded formula.

encodedAxEqTrans_Term : Term -> Term -> Term -> Term
encodedAxEqTrans_Term tA tB tC =
  ap2 Pair (natCode tag_imp)
    (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB))
              (ap2 Pair (natCode tag_imp)
                (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tC))
                          (ap2 Pair (natCode tag_eq) (ap2 Pair tB tC)))))

------------------------------------------------------------------------
-- sbf3-cascade lemma.

private
  sbf3_step :
    (tA tB tC : Term) ->
    Deriv (eqF (ap2 sbf3 (spec3_at tA tB tC) outputRHS4_pair)
                (encodedAxEqTrans_Term tA tB tC))
  sbf3_step tA tB tC =
    let sp : Term
        sp = spec3_at tA tB tC

        e_cV0 : Deriv (eqF (ap2 sbt3 sp cV0) tA)
        e_cV0 = sbt3_at_var_match_one zero (suc zero) (suc (suc zero)) tA tB tC

        e_cV1 : Deriv (eqF (ap2 sbt3 sp cV1) tB)
        e_cV1 = sbt3_at_var_match_two zero (suc zero) (suc (suc zero)) tA tB tC refl

        e_cV2 : Deriv (eqF (ap2 sbt3 sp cV2) tC)
        e_cV2 = sbt3_at_var_match_three zero (suc zero) (suc (suc zero)) tA tB tC refl refl

        -- sbf3 sp on each cEqij  via sbf3_at_atomic + sbt3 var matches.
        sbf3_at_cEq01 :
          Deriv (eqF (ap2 sbf3 sp cEq01)
                      (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB)))
        sbf3_at_cEq01 =
          let e1 = sbf3_at_atomic zero (suc zero) (suc (suc zero)) tA tB tC cV0 cV1
              e2 = congL Pair (ap2 sbt3 sp cV1) e_cV0
              e3 = congR Pair tA e_cV1
              e_inner :
                Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV0) (ap2 sbt3 sp cV1))
                            (ap2 Pair tA tB))
              e_inner = ruleTrans e2 e3
          in ruleTrans e1 (congR Pair (natCode tag_eq) e_inner)

        sbf3_at_cEq02 :
          Deriv (eqF (ap2 sbf3 sp cEq02)
                      (ap2 Pair (natCode tag_eq) (ap2 Pair tA tC)))
        sbf3_at_cEq02 =
          let e1 = sbf3_at_atomic zero (suc zero) (suc (suc zero)) tA tB tC cV0 cV2
              e2 = congL Pair (ap2 sbt3 sp cV2) e_cV0
              e3 = congR Pair tA e_cV2
              e_inner :
                Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV0) (ap2 sbt3 sp cV2))
                            (ap2 Pair tA tC))
              e_inner = ruleTrans e2 e3
          in ruleTrans e1 (congR Pair (natCode tag_eq) e_inner)

        sbf3_at_cEq12 :
          Deriv (eqF (ap2 sbf3 sp cEq12)
                      (ap2 Pair (natCode tag_eq) (ap2 Pair tB tC)))
        sbf3_at_cEq12 =
          let e1 = sbf3_at_atomic zero (suc zero) (suc (suc zero)) tA tB tC cV1 cV2
              e2 = congL Pair (ap2 sbt3 sp cV2) e_cV1
              e3 = congR Pair tB e_cV2
              e_inner :
                Deriv (eqF (ap2 Pair (ap2 sbt3 sp cV1) (ap2 sbt3 sp cV2))
                            (ap2 Pair tB tC))
              e_inner = ruleTrans e2 e3
          in ruleTrans e1 (congR Pair (natCode tag_eq) e_inner)

        -- Inner imp : sbf3 sp (Pair tag_imp (Pair cEq02 cEq12)).
        e_inner_imp :
          Deriv (eqF (ap2 sbf3 sp
                       (ap2 Pair (natCode tag_imp) (ap2 Pair cEq02 cEq12)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair (ap2 sbf3 sp cEq02) (ap2 sbf3 sp cEq12))))
        e_inner_imp =
          sbf3_at_imp zero (suc zero) (suc (suc zero)) tA tB tC cEq02 cEq12

        e_inner_imp_eval :
          Deriv (eqF
            (ap2 Pair (ap2 sbf3 sp cEq02) (ap2 sbf3 sp cEq12))
            (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tC))
                       (ap2 Pair (natCode tag_eq) (ap2 Pair tB tC))))
        e_inner_imp_eval =
          ruleTrans (congL Pair (ap2 sbf3 sp cEq12) sbf3_at_cEq02)
                    (congR Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tC))
                                sbf3_at_cEq12)

        e_inner_imp_final :
          Deriv (eqF (ap2 sbf3 sp
                       (ap2 Pair (natCode tag_imp) (ap2 Pair cEq02 cEq12)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tC))
                                   (ap2 Pair (natCode tag_eq) (ap2 Pair tB tC)))))
        e_inner_imp_final =
          ruleTrans e_inner_imp
            (congR Pair (natCode tag_imp) e_inner_imp_eval)

        -- Outer imp : sbf3 sp outputRHS4_pair.
        e_outer_imp :
          Deriv (eqF (ap2 sbf3 sp outputRHS4_pair)
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair (ap2 sbf3 sp cEq01)
                                   (ap2 sbf3 sp
                                     (ap2 Pair (natCode tag_imp)
                                       (ap2 Pair cEq02 cEq12))))))
        e_outer_imp =
          sbf3_at_imp zero (suc zero) (suc (suc zero)) tA tB tC
            cEq01 (ap2 Pair (natCode tag_imp) (ap2 Pair cEq02 cEq12))

        e_outer_imp_eval :
          Deriv (eqF
            (ap2 Pair (ap2 sbf3 sp cEq01)
                       (ap2 sbf3 sp
                         (ap2 Pair (natCode tag_imp) (ap2 Pair cEq02 cEq12))))
            (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB))
                       (ap2 Pair (natCode tag_imp)
                         (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tC))
                                    (ap2 Pair (natCode tag_eq) (ap2 Pair tB tC))))))
        e_outer_imp_eval =
          ruleTrans
            (congL Pair (ap2 sbf3 sp (ap2 Pair (natCode tag_imp) (ap2 Pair cEq02 cEq12)))
                        sbf3_at_cEq01)
            (congR Pair (ap2 Pair (natCode tag_eq) (ap2 Pair tA tB))
                        e_inner_imp_final)

    in ruleTrans e_outer_imp
         (congR Pair (natCode tag_imp) e_outer_imp_eval)

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqTrans :
  (tA tB tC : Term) ->
  Deriv (eqF (ap1 thmT (Df_axEqTrans tA tB tC))
              (encodedAxEqTrans_Term tA tB tC))
encodedAxEqTrans tA tB tC =
  let sp : Term
      sp = spec3_at tA tB tC

      e_at_sb3 :
        Deriv (eqF (ap1 thmT (Df_axEqTrans tA tB tC))
                    (ap2 sbf3 sp (ap1 thmT packAx4)))
      e_at_sb3 = thmT_at_sb3 sp packAx4

      e_axN4 :
        Deriv (eqF (ap1 thmT packAx4) outputRHS4_pair)
      e_axN4 = thmT_at_axN4 O

      e_lift_axN4 :
        Deriv (eqF (ap2 sbf3 sp (ap1 thmT packAx4))
                    (ap2 sbf3 sp outputRHS4_pair))
      e_lift_axN4 = congR sbf3 sp e_axN4

      e_sbf3 :
        Deriv (eqF (ap2 sbf3 sp outputRHS4_pair)
                    (encodedAxEqTrans_Term tA tB tC))
      e_sbf3 = sbf3_step tA tB tC

  in ruleTrans e_at_sb3
       (ruleTrans e_lift_axN4 e_sbf3)
