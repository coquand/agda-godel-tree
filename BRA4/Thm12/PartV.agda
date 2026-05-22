{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartV -- Theorem 12, case  g = v  (second-projection Fun2).
--
-- Goal :
--   thm12_v : (X Y : Term) ->
--     Deriv (eqF (ap1 thmT (Df_v X Y)) (codeFTeq2 v X Y))
--
-- Construction.  Df_v X Y = sb2-wrap of  packAx 3 O  with substituents
--  (X' := num X, Y' := num Y)  at  v0 / v1  (k1 = 0, k2 = 1) :
--
--   Df_v X Y
--     = Pair tag_sb2
--         (Pair (Pair (Pair (natCode 0) (num X)) (Pair (natCode 1) (num Y)))
--               (Pair (natCode tag_ax) (Pair (natCode 3) O)))
--
-- Then thmT walks the wrap :
--   thmT (Df_v X Y)  =sb2=  sbf2 spec2 (thmT (packAx 3 O))
--                    =axN3=  sbf2 spec2 (codeFormula (atomic (eqn (v (var 0) (var 1)) (var 1))))
--                    =sbf2 cascade=
--                            Pair tag_eq (Pair (encV(num X, num Y)) (num Y))
-- where  encV(A, B) = Pair tag_ap2 (Pair (codeFun2 v) (Pair A B)) .
--
-- Bridge RHS slot  num Y  ->  num (v X Y)  via cong1 num (ruleSym (ax_v X Y)).
--
-- No  Closed  premise.  The substituents  num X , num Y  are plopped
-- into the two var-positions by  sbt2_at_var_match_one / _two  and are
-- not walked further.

module BRA4.Thm12.PartV where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun2 ; codeFormula )
open import BRA4.Num               using ( num )
open import BRA4.SbContract2
open import BRA4.SbT2              using ( sbt2 )
open import BRA4.SbF2              using ( sbf2 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb2         using ( thmT_at_sb2 )
open import BRA4.ThmTAtAx3         using ( thmT_at_axN3 )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq2 )

open SbContract2 sbContract2

------------------------------------------------------------------------
-- Constants and helpers.

private
  N3 : Nat
  N3 = suc (suc (suc zero))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  packAx3_O : Term
  packAx3_O =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N3) O)

  spec2_at : Term -> Term -> Term
  spec2_at X Y =
    ap2 Pair (ap2 Pair (natCode zero) X)
             (ap2 Pair (natCode (suc zero)) Y)

  -- The codeFormula output of thmT_at_axN3 expands definitionally to :
  --   Pair tag_eq (Pair codeV0V1 cV1)
  -- where  codeV0V1 = Pair tag_ap2 (Pair (codeFun2 v) (Pair cV0 cV1)).
  codeV0V1 : Term
  codeV0V1 =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 v) (ap2 Pair cV0 cV1))

  outputRHS3 : Term
  outputRHS3 =
    ap2 Pair (natCode tag_eq) (ap2 Pair codeV0V1 cV1)

  -- The "schema codeFormula" form returned by thmT_at_axN3 .  Definitionally
  -- equal to outputRHS3 by codeFormula's recursive expansion.
  outputRHS3_codeF : Term
  outputRHS3_codeF =
    codeFormula (atomic (eqn (ap2 v (var zero) (var (suc zero))) (var (suc zero))))

  -- codeFun2 v evaluates to natCode tag_v ; both forms coincide definitionally.

------------------------------------------------------------------------
-- Df_v : Term -> Term -> Term.

Df_v : Term -> Term -> Term
Df_v X Y =
  ap2 Pair (natCode tag_sb2)
    (ap2 Pair (spec2_at (ap1 num X) (ap1 num Y)) packAx3_O)

------------------------------------------------------------------------
-- sbf2-cascade lemma :
--   sbf2 spec2_XY  outputRHS3  =  Pair tag_eq (Pair (encV (num X) (num Y)) (num Y)) .

private
  encV : Term -> Term -> Term
  encV A B =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 v) (ap2 Pair A B))

  sbf2_step :
    (X Y : Term) ->
    Deriv (eqF (ap2 sbf2 (spec2_at (ap1 num X) (ap1 num Y)) outputRHS3)
                (ap2 Pair (natCode tag_eq)
                  (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y))))
  sbf2_step X Y =
    let sp : Term
        sp = spec2_at (ap1 num X) (ap1 num Y)

        -- sbt2 sp cV0 = num X via sbt2_at_var_match_one.
        e_cV0 : Deriv (eqF (ap2 sbt2 sp cV0) (ap1 num X))
        e_cV0 = sbt2_at_var_match_one zero (suc zero) (ap1 num X) (ap1 num Y)

        -- sbt2 sp cV1 = num Y via sbt2_at_var_match_two ; needs Eq (natEq 0 1) false.
        e_cV1 : Deriv (eqF (ap2 sbt2 sp cV1) (ap1 num Y))
        e_cV1 = sbt2_at_var_match_two zero (suc zero)
                  (ap1 num X) (ap1 num Y) refl

        -- (a) sbf2_at_atomic at ca = codeV0V1 , cb = cV1 .
        e_atomic :
          Deriv (eqF (ap2 sbf2 sp outputRHS3)
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt2 sp codeV0V1)
                          (ap2 sbt2 sp cV1))))
        e_atomic = sbf2_at_atomic zero (suc zero)
                    (ap1 num X) (ap1 num Y) codeV0V1 cV1

        -- (b) sbt2 sp codeV0V1 via sbt2_at_ap2 with g=v , ca=cV0 , cb=cV1.
        e_ca_step :
          Deriv (eqF (ap2 sbt2 sp codeV0V1)
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 v)
                          (ap2 Pair
                            (ap2 sbt2 sp cV0)
                            (ap2 sbt2 sp cV1)))))
        e_ca_step = sbt2_at_ap2 zero (suc zero)
                     (ap1 num X) (ap1 num Y) v cV0 cV1

        e_ca_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1))
                      (ap2 Pair (ap1 num X) (ap1 num Y)))
        e_ca_inner =
          ruleTrans (congL Pair (ap2 sbt2 sp cV1) e_cV0)
                    (congR Pair (ap1 num X) e_cV1)

        e_ca :
          Deriv (eqF (ap2 sbt2 sp codeV0V1) (encV (ap1 num X) (ap1 num Y)))
        e_ca =
          ruleTrans e_ca_step
            (congR Pair (natCode tag_ap2)
              (congR Pair (codeFun2 v) e_ca_inner))

        -- (c) Combine ca / cb evaluations inside the Pair-eq output.
        e_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt2 sp codeV0V1) (ap2 sbt2 sp cV1))
            (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y)))
        e_inner =
          ruleTrans (congL Pair (ap2 sbt2 sp cV1) e_ca)
                    (congR Pair (encV (ap1 num X) (ap1 num Y)) e_cV1)

        e_outer :
          Deriv (eqF
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt2 sp codeV0V1) (ap2 sbt2 sp cV1)))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y))))
        e_outer = congR Pair (natCode tag_eq) e_inner

    in ruleTrans e_atomic e_outer

------------------------------------------------------------------------
-- The main theorem.

thm12_v :
  (X Y : Term) ->
  Deriv (eqF (ap1 thmT (Df_v X Y)) (codeFTeq2 v X Y))
thm12_v X Y =
  let
    sp : Term
    sp = spec2_at (ap1 num X) (ap1 num Y)

    -- (a)  thmT (Df_v X Y) =Deriv= sbf2 sp (thmT packAx3_O)  via thmT_at_sb2 .
    e_at_sb2 :
      Deriv (eqF (ap1 thmT (Df_v X Y))
                  (ap2 sbf2 sp (ap1 thmT packAx3_O)))
    e_at_sb2 = thmT_at_sb2 sp packAx3_O

    -- (b)  thmT packAx3_O =Deriv= outputRHS3  via thmT_at_axN3 O .
    -- (outputRHS3_codeF = codeFormula (...) definitionally equals outputRHS3.)
    e_axN3 :
      Deriv (eqF (ap1 thmT packAx3_O) outputRHS3)
    e_axN3 = thmT_at_axN3 O

    e_lift_axN3 :
      Deriv (eqF (ap2 sbf2 sp (ap1 thmT packAx3_O))
                  (ap2 sbf2 sp outputRHS3))
    e_lift_axN3 = congR sbf2 sp e_axN3

    -- (c)  sbf2 sp outputRHS3  =Deriv= Pair tag_eq (Pair (encV (num X) (num Y)) (num Y)) .
    e_sbf2 :
      Deriv (eqF (ap2 sbf2 sp outputRHS3)
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y))))
    e_sbf2 = sbf2_step X Y

    e_cascade :
      Deriv (eqF (ap1 thmT (Df_v X Y))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y))))
    e_cascade =
      ruleTrans e_at_sb2
        (ruleTrans e_lift_axN3 e_sbf2)

    -- (d)  Bridge RHS slot  num Y  ->  num (v X Y)  via cong1 num (ruleSym (ax_v X Y)).
    axV_eq : Deriv (eqF (ap2 v X Y) Y)
    axV_eq = ax_v X Y

    rhs_bridge :
      Deriv (eqF (ap1 num Y) (ap1 num (ap2 v X Y)))
    rhs_bridge = cong1 num (ruleSym axV_eq)

    -- (e)  Lift through outer Pair layers.
    e_inner_pair :
      Deriv (eqF
        (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y))
        (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num (ap2 v X Y))))
    e_inner_pair = congR Pair (encV (ap1 num X) (ap1 num Y)) rhs_bridge

    e_outer_pair :
      Deriv (eqF
        (ap2 Pair (natCode tag_eq) (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y)))
        (ap2 Pair (natCode tag_eq) (ap2 Pair (encV (ap1 num X) (ap1 num Y))
                                              (ap1 num (ap2 v X Y)))))
    e_outer_pair = congR Pair (natCode tag_eq) e_inner_pair

    -- The RHS of e_outer_pair is definitionally codeFTeq2 v X Y .
    -- ( codeFTeq2 v X Y  unfolds to  Pair tag_eq (Pair (encV (num X) (num Y))
    --                                                  (num (v X Y))) . )

  in ruleTrans e_cascade e_outer_pair
