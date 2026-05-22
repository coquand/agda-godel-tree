{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartU -- Theorem 12, case  f = u  (identity functor).
--
-- Goal :
--   thm12_u : (X : Term) ->
--     Deriv (eqF (ap1 thmT (ap1 Df_u X)) (codeFTeq1 u X))
--
-- Construction.  Df_u X = encode_sb 0 (ap1 num X) (packAx 2 O) :
--   ap1 Df_u X
--     =Deriv= Pair tag_sb (Pair (Pair tag_0 (num X)) (Pair tag_ax (Pair tag_2 O)))
--   ( i.e. the sb-wrap of the axN2 schema with substituent  num X  at var 0 )
--
-- Then thmT walks the wrap :
--   thmT (Df_u X)  =sb=  sbf spec (thmT (packAx 2 O))
--                  =axN2=  sbf spec (codeFormula (atomic (eqn (u v0) v0)))
--                  =sbf_at_atomic + sbt closures=
--                          Pair tag_eq (Pair codeU(num X) (num X))
-- where codeU(num X) = Pair tag_ap1 (Pair (codeFun1 u) (num X)).
--
-- Bridge RHS slot (num X) to (num (u X)) via cong1 num (ruleSym (ax_u X)).
--
-- No  Closed  premise.  The substituent  num X  is plopped into the two
-- var-0 positions by  sbt_at_var_match  and is NOT walked further
-- (because only one sb-wrap layer is involved).

module BRA4.Thm12.PartU where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFormula )
open import BRA4.Num               using ( num )
open import BRA4.SbContract
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx2         using ( thmT_at_axN2 )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 )

------------------------------------------------------------------------
-- Open the contract to access closure equations.

open SbContract sbContract

------------------------------------------------------------------------
-- Df_u : Fun1 such that  ap1 Df_u X  is the sb-encoded "ax_u (num X)".
--
--   Df_u = C Pair (constN tag_sb)
--            (C Pair (C Pair (constN 0) num)
--                    constPackAx2_O)
--
-- where  constPackAx2_O : Fun1  returns the constant Term  packAx 2 O .

private
  constPackAx2_O : Fun1
  constPackAx2_O =
    C Pair (constN tag_ax)
      (C Pair (constN (suc (suc zero))) (constN zero))

Df_u : Fun1
Df_u =
  C Pair (constN tag_sb)
    (C Pair (C Pair (constN zero) num) constPackAx2_O)

------------------------------------------------------------------------
-- Target shape:  ap1 Df_u X  =Deriv=  encDfu X .

private
  packAx2_O : Term
  packAx2_O =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode (suc (suc zero))) O)

  encDfu : Term -> Term
  encDfu X =
    ap2 Pair (natCode tag_sb)
      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X))
                packAx2_O)

------------------------------------------------------------------------
-- Step 1 : Df_u unfolding.

private
  constPackAx2_O_eq :
    (X : Term) -> Deriv (eqF (ap1 constPackAx2_O X) packAx2_O)
  constPackAx2_O_eq X =
    let e1 :
          Deriv (eqF (ap1 constPackAx2_O X)
                      (ap2 Pair (ap1 (constN tag_ax) X)
                                  (ap1 (C Pair (constN (suc (suc zero))) (constN zero)) X)))
        e1 = ax_C Pair (constN tag_ax)
                      (C Pair (constN (suc (suc zero))) (constN zero))
                      X

        e2 :
          Deriv (eqF (ap1 (C Pair (constN (suc (suc zero))) (constN zero)) X)
                      (ap2 Pair (ap1 (constN (suc (suc zero))) X)
                                  (ap1 (constN zero) X)))
        e2 = ax_C Pair (constN (suc (suc zero))) (constN zero) X

        e3 :
          Deriv (eqF (ap1 (C Pair (constN (suc (suc zero))) (constN zero)) X)
                      (ap2 Pair (natCode (suc (suc zero))) (natCode zero)))
        e3 = ruleTrans e2
               (ruleTrans (congL Pair (ap1 (constN zero) X)
                                   (constN_eq (suc (suc zero)) X))
                          (congR Pair (natCode (suc (suc zero)))
                                   (constN_eq zero X)))

        -- natCode zero  =  O  (definitional).
        e4 :
          Deriv (eqF (ap1 (C Pair (constN (suc (suc zero))) (constN zero)) X)
                      (ap2 Pair (natCode (suc (suc zero))) O))
        e4 = e3

        cN_ax : Deriv (eqF (ap1 (constN tag_ax) X) (natCode tag_ax))
        cN_ax = constN_eq tag_ax X
    in ruleTrans e1
         (ruleTrans (congL Pair
                       (ap1 (C Pair (constN (suc (suc zero))) (constN zero)) X)
                       cN_ax)
                    (congR Pair (natCode tag_ax) e4))

  Df_u_unfold :
    (X : Term) -> Deriv (eqF (ap1 Df_u X) (encDfu X))
  Df_u_unfold X =
    let e1 :
          Deriv (eqF (ap1 Df_u X)
                      (ap2 Pair (ap1 (constN tag_sb) X)
                                  (ap1 (C Pair (C Pair (constN zero) num)
                                                constPackAx2_O) X)))
        e1 = ax_C Pair (constN tag_sb)
                      (C Pair (C Pair (constN zero) num) constPackAx2_O) X

        e2 :
          Deriv (eqF (ap1 (C Pair (C Pair (constN zero) num) constPackAx2_O) X)
                      (ap2 Pair (ap1 (C Pair (constN zero) num) X)
                                  (ap1 constPackAx2_O X)))
        e2 = ax_C Pair (C Pair (constN zero) num) constPackAx2_O X

        e3 :
          Deriv (eqF (ap1 (C Pair (constN zero) num) X)
                      (ap2 Pair (ap1 (constN zero) X) (ap1 num X)))
        e3 = ax_C Pair (constN zero) num X

        e3' :
          Deriv (eqF (ap1 (C Pair (constN zero) num) X)
                      (ap2 Pair (natCode zero) (ap1 num X)))
        e3' = ruleTrans e3 (congL Pair (ap1 num X) (constN_eq zero X))

        e2' :
          Deriv (eqF (ap1 (C Pair (C Pair (constN zero) num) constPackAx2_O) X)
                      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X)) packAx2_O))
        e2' = ruleTrans e2
                (ruleTrans (congL Pair (ap1 constPackAx2_O X) e3')
                           (congR Pair (ap2 Pair (natCode zero) (ap1 num X))
                                       (constPackAx2_O_eq X)))

        cN_sb : Deriv (eqF (ap1 (constN tag_sb) X) (natCode tag_sb))
        cN_sb = constN_eq tag_sb X
    in ruleTrans e1
         (ruleTrans (congL Pair
                       (ap1 (C Pair (C Pair (constN zero) num) constPackAx2_O) X)
                       cN_sb)
                    (congR Pair (natCode tag_sb) e2'))

------------------------------------------------------------------------
-- Step 2 : thmT cascade on  encDfu X .

private
  spec_at : Term -> Term
  spec_at X = ap2 Pair (natCode zero) (ap1 num X)

  -- codeFormula (atomic (eqn (ap1 u (var 0)) (var 0))) :
  -- the schema codeFormula axN2.
  axN2_form : Term
  axN2_form = codeFormula (atomic (eqn (ap1 u (var zero)) (var zero)))

  -- Decomposed form.  axN2_form definitionally equals
  --   Pair tag_eq (Pair codeAU codeV0)
  -- with codeAU = Pair tag_ap1 (Pair tag_u codeV0), codeV0 = Pair tag_var (natCode 0).
  codeV0 : Term
  codeV0 = ap2 Pair (natCode tag_var) (natCode zero)

  codeAU : Term
  codeAU = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 u) codeV0)

------------------------------------------------------------------------
-- Step 3 :  sbf spec (codeFormula axN2)  =Deriv=  Pair tag_eq (Pair codeU(numX) (numX)) .

private
  -- codeU(num X)  in the asymmetric encoding.
  codeU_numX : Term -> Term
  codeU_numX X = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 u) (ap1 num X))

  sbf_step :
    (X : Term) ->
    Deriv (eqF (ap2 sbf (spec_at X) axN2_form)
                (ap2 Pair (natCode tag_eq)
                  (ap2 Pair (codeU_numX X) (ap1 num X))))
  sbf_step X =
    let sp : Term
        sp = spec_at X

        -- sbf_at_atomic at k=0, S=(num X), ca=codeAU, cb=codeV0.
        e_atomic :
          Deriv (eqF (ap2 sbf sp axN2_form)
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt sp codeAU)
                          (ap2 sbt sp codeV0))))
        e_atomic = sbf_at_atomic zero (ap1 num X) codeAU codeV0

        -- sbt sp codeV0 = num X  via  sbt_at_var_match 0 (num X) .
        e_cb : Deriv (eqF (ap2 sbt sp codeV0) (ap1 num X))
        e_cb = sbt_at_var_match zero (ap1 num X)

        -- sbt sp codeAU = Pair tag_ap1 (Pair tag_u (num X))
        --   via sbt_at_ap1 0 (num X) u codeV0 + cong on inner with e_cb.
        e_ca_step1 :
          Deriv (eqF (ap2 sbt sp codeAU)
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 u) (ap2 sbt sp codeV0))))
        e_ca_step1 = sbt_at_ap1 zero (ap1 num X) u codeV0

        e_ca :
          Deriv (eqF (ap2 sbt sp codeAU) (codeU_numX X))
        e_ca = ruleTrans e_ca_step1
                 (congR Pair (natCode tag_ap1)
                   (congR Pair (codeFun1 u) e_cb))

        -- Combine the two sbt-results inside the Pair-eq output.
        e_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt sp codeAU) (ap2 sbt sp codeV0))
            (ap2 Pair (codeU_numX X) (ap1 num X)))
        e_inner =
          ruleTrans (congL Pair (ap2 sbt sp codeV0) e_ca)
                    (congR Pair (codeU_numX X) e_cb)

        e_outer :
          Deriv (eqF
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt sp codeAU) (ap2 sbt sp codeV0)))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (codeU_numX X) (ap1 num X))))
        e_outer = congR Pair (natCode tag_eq) e_inner
    in ruleTrans e_atomic e_outer

------------------------------------------------------------------------
-- Step 4 : main theorem.

thm12_u :
  (X : Term) ->
  Deriv (eqF (ap1 thmT (ap1 Df_u X)) (codeFTeq1 u X))
thm12_u X =
  let
    sp : Term
    sp = spec_at X

    -- (a)  ap1 Df_u X  =Deriv=  encDfu X .
    e_unfold : Deriv (eqF (ap1 Df_u X) (encDfu X))
    e_unfold = Df_u_unfold X

    e_thmT_unfold :
      Deriv (eqF (ap1 thmT (ap1 Df_u X)) (ap1 thmT (encDfu X)))
    e_thmT_unfold = cong1 thmT e_unfold

    -- (b)  thmT (encDfu X)  =Deriv=  sbf sp (thmT (packAx 2 O))   via  thmT_at_sb sp packAx2_O .
    e_at_sb :
      Deriv (eqF (ap1 thmT (encDfu X)) (ap2 sbf sp (ap1 thmT packAx2_O)))
    e_at_sb = thmT_at_sb sp packAx2_O

    -- (c)  thmT (packAx 2 O)  =Deriv=  codeFormula axN2  via  thmT_at_axN2 O .
    e_axN2 :
      Deriv (eqF (ap1 thmT packAx2_O) axN2_form)
    e_axN2 = thmT_at_axN2 O

    e_lift_axN2 :
      Deriv (eqF (ap2 sbf sp (ap1 thmT packAx2_O)) (ap2 sbf sp axN2_form))
    e_lift_axN2 = congR sbf sp e_axN2

    -- (d)  sbf sp axN2_form  =Deriv=  Pair tag_eq (Pair codeU(numX) (numX))   via  sbf_step .
    e_sbf : Deriv (eqF (ap2 sbf sp axN2_form)
                        (ap2 Pair (natCode tag_eq)
                          (ap2 Pair (codeU_numX X) (ap1 num X))))
    e_sbf = sbf_step X

    -- Chain (a)+(b)+(c)+(d) :
    e_cascade :
      Deriv (eqF (ap1 thmT (ap1 Df_u X))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair (codeU_numX X) (ap1 num X))))
    e_cascade =
      ruleTrans e_thmT_unfold
        (ruleTrans e_at_sb
          (ruleTrans e_lift_axN2 e_sbf))

    -- (e)  Bridge RHS slot :  num X  =Deriv=  num (u X) .
    rhs_bridge :
      Deriv (eqF (ap1 num X) (ap1 num (ap1 u X)))
    rhs_bridge = cong1 num (ruleSym (ax_u X))

    -- (f)  Lift through outer  Pair  layers.
    e_inner_pair :
      Deriv (eqF
        (ap2 Pair (codeU_numX X) (ap1 num X))
        (ap2 Pair (codeU_numX X) (ap1 num (ap1 u X))))
    e_inner_pair = congR Pair (codeU_numX X) rhs_bridge

    e_outer_pair :
      Deriv (eqF
        (ap2 Pair (natCode tag_eq) (ap2 Pair (codeU_numX X) (ap1 num X)))
        (ap2 Pair (natCode tag_eq) (ap2 Pair (codeU_numX X) (ap1 num (ap1 u X)))))
    e_outer_pair = congR Pair (natCode tag_eq) e_inner_pair

  in ruleTrans e_cascade e_outer_pair
