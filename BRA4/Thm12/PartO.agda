{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartO -- Theorem 12, case  f = o  (zero functor).
--
-- Goal :
--   thm12_o : (X : Term) ->
--     Deriv (eqF (ap1 thmT (ap1 Df_o X)) (codeFTeq1 o X))
--
-- Construction.  Df_o X = encode_sb 0 (ap1 num X) (packAx 1 O) :
--   ap1 Df_o X
--     =Deriv= Pair tag_sb (Pair (Pair tag_0 (num X)) (Pair tag_ax (Pair tag_1 O)))
--
-- Then thmT walks the wrap :
--   thmT (Df_o X)  =sb=  sbf spec (thmT (packAx 1 O))
--                  =axN1=  sbf spec (codeFormula (atomic (eqn (o v0) O)))
--                  =sbf_at_atomic + sbt closures + sbt_at_O=
--                          Pair tag_eq (Pair codeO(num X) O)
-- where codeO(num X) = Pair tag_ap1 (Pair (codeFun1 o) (num X)).
--
-- Bridge RHS slot O to (num (o X)) via :
--   num (o X)  =Deriv=  num O   via  cong1 num (ax_o X)
--   num O      =Deriv=  O       via  num_at_O
-- So  num (o X) =Deriv= O , and ruleSym gives  O =Deriv= num (o X) .

module BRA4.Thm12.PartO where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFormula )
open import BRA4.Num               using ( num ; num_at_O )
open import BRA4.SbContract
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx1         using ( thmT_at_axN1 )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 )

open SbContract sbContract

------------------------------------------------------------------------
-- Df_o : Fun1 .  Built exactly like Df_u but at packAx 1 .

private
  constPackAx1_O : Fun1
  constPackAx1_O =
    C Pair (constN tag_ax)
      (C Pair (constN (suc zero)) (constN zero))

Df_o : Fun1
Df_o =
  C Pair (constN tag_sb)
    (C Pair (C Pair (constN zero) num) constPackAx1_O)

------------------------------------------------------------------------
-- Target shape:  ap1 Df_o X  =Deriv=  encDfo X .

private
  packAx1_O : Term
  packAx1_O =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode (suc zero)) O)

  encDfo : Term -> Term
  encDfo X =
    ap2 Pair (natCode tag_sb)
      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X))
                packAx1_O)

------------------------------------------------------------------------
-- Step 1 : Df_o unfolding.

private
  constPackAx1_O_eq :
    (X : Term) -> Deriv (eqF (ap1 constPackAx1_O X) packAx1_O)
  constPackAx1_O_eq X =
    let e1 :
          Deriv (eqF (ap1 constPackAx1_O X)
                      (ap2 Pair (ap1 (constN tag_ax) X)
                                  (ap1 (C Pair (constN (suc zero)) (constN zero)) X)))
        e1 = ax_C Pair (constN tag_ax)
                      (C Pair (constN (suc zero)) (constN zero))
                      X

        e2 :
          Deriv (eqF (ap1 (C Pair (constN (suc zero)) (constN zero)) X)
                      (ap2 Pair (natCode (suc zero)) (natCode zero)))
        e2 = ruleTrans (ax_C Pair (constN (suc zero)) (constN zero) X)
               (ruleTrans (congL Pair (ap1 (constN zero) X)
                                   (constN_eq (suc zero) X))
                          (congR Pair (natCode (suc zero))
                                   (constN_eq zero X)))

        cN_ax : Deriv (eqF (ap1 (constN tag_ax) X) (natCode tag_ax))
        cN_ax = constN_eq tag_ax X
    in ruleTrans e1
         (ruleTrans (congL Pair
                       (ap1 (C Pair (constN (suc zero)) (constN zero)) X)
                       cN_ax)
                    (congR Pair (natCode tag_ax) e2))

  Df_o_unfold :
    (X : Term) -> Deriv (eqF (ap1 Df_o X) (encDfo X))
  Df_o_unfold X =
    let e1 :
          Deriv (eqF (ap1 Df_o X)
                      (ap2 Pair (ap1 (constN tag_sb) X)
                                  (ap1 (C Pair (C Pair (constN zero) num)
                                                constPackAx1_O) X)))
        e1 = ax_C Pair (constN tag_sb)
                      (C Pair (C Pair (constN zero) num) constPackAx1_O) X

        e3 :
          Deriv (eqF (ap1 (C Pair (constN zero) num) X)
                      (ap2 Pair (natCode zero) (ap1 num X)))
        e3 = ruleTrans (ax_C Pair (constN zero) num X)
               (congL Pair (ap1 num X) (constN_eq zero X))

        e2' :
          Deriv (eqF (ap1 (C Pair (C Pair (constN zero) num) constPackAx1_O) X)
                      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X)) packAx1_O))
        e2' = ruleTrans (ax_C Pair (C Pair (constN zero) num) constPackAx1_O X)
                (ruleTrans (congL Pair (ap1 constPackAx1_O X) e3)
                           (congR Pair (ap2 Pair (natCode zero) (ap1 num X))
                                       (constPackAx1_O_eq X)))

        cN_sb : Deriv (eqF (ap1 (constN tag_sb) X) (natCode tag_sb))
        cN_sb = constN_eq tag_sb X
    in ruleTrans e1
         (ruleTrans (congL Pair
                       (ap1 (C Pair (C Pair (constN zero) num) constPackAx1_O) X)
                       cN_sb)
                    (congR Pair (natCode tag_sb) e2'))

------------------------------------------------------------------------
-- Step 2 : sbf spec (codeFormula axN1)  =Deriv=  Pair tag_eq (Pair codeO(numX) O) .

private
  spec_at : Term -> Term
  spec_at X = ap2 Pair (natCode zero) (ap1 num X)

  axN1_form : Term
  axN1_form = codeFormula (atomic (eqn (ap1 o (var zero)) O))

  codeV0 : Term
  codeV0 = ap2 Pair (natCode tag_var) (natCode zero)

  codeAO : Term
  codeAO = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 o) codeV0)

  codeO_numX : Term -> Term
  codeO_numX X = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 o) (ap1 num X))

  sbf_step :
    (X : Term) ->
    Deriv (eqF (ap2 sbf (spec_at X) axN1_form)
                (ap2 Pair (natCode tag_eq)
                  (ap2 Pair (codeO_numX X) O)))
  sbf_step X =
    let sp : Term
        sp = spec_at X

        -- sbf_at_atomic at k=0, S=(num X), ca=codeAO, cb=O.
        e_atomic :
          Deriv (eqF (ap2 sbf sp axN1_form)
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair (ap2 sbt sp codeAO) (ap2 sbt sp O))))
        e_atomic = sbf_at_atomic zero (ap1 num X) codeAO O

        -- sbt sp O = O via sbt_at_O.
        e_cb : Deriv (eqF (ap2 sbt sp O) O)
        e_cb = sbt_at_O sp

        -- sbt sp codeV0 = num X via sbt_at_var_match.
        e_v0 : Deriv (eqF (ap2 sbt sp codeV0) (ap1 num X))
        e_v0 = sbt_at_var_match zero (ap1 num X)

        -- sbt sp codeAO = codeO(num X) via sbt_at_ap1 + e_v0.
        e_ca_step1 :
          Deriv (eqF (ap2 sbt sp codeAO)
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 o) (ap2 sbt sp codeV0))))
        e_ca_step1 = sbt_at_ap1 zero (ap1 num X) o codeV0

        e_ca :
          Deriv (eqF (ap2 sbt sp codeAO) (codeO_numX X))
        e_ca = ruleTrans e_ca_step1
                 (congR Pair (natCode tag_ap1)
                   (congR Pair (codeFun1 o) e_v0))

        e_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt sp codeAO) (ap2 sbt sp O))
            (ap2 Pair (codeO_numX X) O))
        e_inner =
          ruleTrans (congL Pair (ap2 sbt sp O) e_ca)
                    (congR Pair (codeO_numX X) e_cb)

        e_outer :
          Deriv (eqF
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt sp codeAO) (ap2 sbt sp O)))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (codeO_numX X) O)))
        e_outer = congR Pair (natCode tag_eq) e_inner
    in ruleTrans e_atomic e_outer

------------------------------------------------------------------------
-- Step 3 : main theorem.

thm12_o :
  (X : Term) ->
  Deriv (eqF (ap1 thmT (ap1 Df_o X)) (codeFTeq1 o X))
thm12_o X =
  let
    sp : Term
    sp = spec_at X

    -- (a) Df_o X =Deriv= encDfo X.
    e_unfold : Deriv (eqF (ap1 Df_o X) (encDfo X))
    e_unfold = Df_o_unfold X

    e_thmT_unfold :
      Deriv (eqF (ap1 thmT (ap1 Df_o X)) (ap1 thmT (encDfo X)))
    e_thmT_unfold = cong1 thmT e_unfold

    -- (b) thmT (encDfo X) =Deriv= sbf sp (thmT (packAx 1 O)).
    e_at_sb :
      Deriv (eqF (ap1 thmT (encDfo X)) (ap2 sbf sp (ap1 thmT packAx1_O)))
    e_at_sb = thmT_at_sb sp packAx1_O

    -- (c) thmT (packAx 1 O) =Deriv= codeFormula axN1.
    e_axN1 :
      Deriv (eqF (ap1 thmT packAx1_O) axN1_form)
    e_axN1 = thmT_at_axN1 O

    e_lift_axN1 :
      Deriv (eqF (ap2 sbf sp (ap1 thmT packAx1_O)) (ap2 sbf sp axN1_form))
    e_lift_axN1 = congR sbf sp e_axN1

    -- (d) sbf sp axN1_form =Deriv= Pair tag_eq (Pair codeO(numX) O).
    e_sbf :
      Deriv (eqF (ap2 sbf sp axN1_form)
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair (codeO_numX X) O)))
    e_sbf = sbf_step X

    e_cascade :
      Deriv (eqF (ap1 thmT (ap1 Df_o X))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair (codeO_numX X) O)))
    e_cascade =
      ruleTrans e_thmT_unfold
        (ruleTrans e_at_sb
          (ruleTrans e_lift_axN1 e_sbf))

    -- (e) Bridge RHS slot : O =Deriv= num (o X).
    --   num (o X) =Deriv= num O      via cong1 num (ax_o X).
    --   num O     =Deriv= O           via num_at_O.
    rhs_bridge_inv :
      Deriv (eqF (ap1 num (ap1 o X)) O)
    rhs_bridge_inv = ruleTrans (cong1 num (ax_o X)) num_at_O

    rhs_bridge :
      Deriv (eqF O (ap1 num (ap1 o X)))
    rhs_bridge = ruleSym rhs_bridge_inv

    -- (f) Lift through outer Pair layers.
    e_inner_pair :
      Deriv (eqF
        (ap2 Pair (codeO_numX X) O)
        (ap2 Pair (codeO_numX X) (ap1 num (ap1 o X))))
    e_inner_pair = congR Pair (codeO_numX X) rhs_bridge

    e_outer_pair :
      Deriv (eqF
        (ap2 Pair (natCode tag_eq) (ap2 Pair (codeO_numX X) O))
        (ap2 Pair (natCode tag_eq) (ap2 Pair (codeO_numX X) (ap1 num (ap1 o X)))))
    e_outer_pair = congR Pair (natCode tag_eq) e_inner_pair

  in ruleTrans e_cascade e_outer_pair
