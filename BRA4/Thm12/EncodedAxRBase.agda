{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxRBase -- encoded  ax_R_base  instance via single sb-wrap
-- on axN9.
--
-- Goal (universal in g : Fun1, h1 h2 : Fun2, X : Term ; no Closed) :
--
--   Df_axRBase  : Fun1 -> Fun2 -> Fun2 -> Fun1
--   encodedAxRBase :
--     (g : Fun1) (h1 h2 : Fun2) (X : Term) ->
--     Deriv (eqF (ap1 thmT (ap1 (Df_axRBase g h1 h2) X))
--                 (encodedAxRBase_Term g h1 h2 X))
--
-- where  encodedAxRBase_Term g h1 h2 X  is the asymmetric encoding of the
-- formula  "R g h1 h2 (num X, O) = g (num X)"  :
--
--   Pair tag_eq (Pair encCodeLHS encCodeRHS)
--   where
--     encCodeLHS = Pair tag_ap2
--                    (Pair (codeFun2 (R g h1 h2)) (Pair (num X) O))
--     encCodeRHS = Pair tag_ap1
--                    (Pair (codeFun1 g) (num X))
--
-- Construction.  Df_axRBase g h1 h2 X = encode_sb 0 (num X)
--   (packAx 9 (codeFun2 (R g h1 h2))) :
--
--   Pair tag_sb
--     (Pair (Pair (natCode 0) (num X))
--           (Pair (natCode tag_ax)
--                 (Pair (natCode 9) (codeFun2 (R g h1 h2)))))
--
-- No Closed premise.  num X enters as a leaf via the sb-wrap ; sbt
-- walks the schema but never walks through (num X) itself.

module BRA4.Thm12.EncodedAxRBase where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.Num               using ( num )
open import BRA4.SbContract
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx9         using ( thmT_at_axN9 )
open import BRA4.Thm12.ConstTermFun1
  using ( constTermFun1 ; constTermFun1_eq
        ; NoVar ; NoVar_natCode ; NoVar_pair ; NoVar_pair_natCode )
open import BRA4.Thm12.EncodedAxC
  using ( NoVar_codeFun1 ; NoVar_codeFun2 )

open SbContract sbContract

------------------------------------------------------------------------
-- Constants and helpers.

private
  N9 : Nat
  N9 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  -- The inner constant Term  packAx 9 (codeFun2 (R g h1 h2)) .
  packAx9_codeR_Term : Fun1 -> Fun2 -> Fun2 -> Term
  packAx9_codeR_Term g h1 h2 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N9) (codeFun2 (R g h1 h2)))

  NoVar_packAx9_codeR :
    (g : Fun1) (h1 h2 : Fun2) -> NoVar (packAx9_codeR_Term g h1 h2)
  NoVar_packAx9_codeR g h1 h2 =
    NoVar_pair_natCode tag_ax
      (ap2 Pair (natCode N9) (codeFun2 (R g h1 h2)))
      (NoVar_pair_natCode N9 (codeFun2 (R g h1 h2))
         (NoVar_codeFun2 (R g h1 h2)))

  packAx9_codeR_Fun1 : Fun1 -> Fun2 -> Fun2 -> Fun1
  packAx9_codeR_Fun1 g h1 h2 =
    constTermFun1 (packAx9_codeR_Term g h1 h2)

  packAx9_codeR_eq :
    (g : Fun1) (h1 h2 : Fun2) (X : Term) ->
    Deriv (eqF (ap1 (packAx9_codeR_Fun1 g h1 h2) X)
                (packAx9_codeR_Term g h1 h2))
  packAx9_codeR_eq g h1 h2 X =
    constTermFun1_eq (packAx9_codeR_Term g h1 h2)
                     (NoVar_packAx9_codeR g h1 h2) X

------------------------------------------------------------------------
-- Df_axRBase : the Fun1 producing the sb-encoded ax_R_base instance.

Df_axRBase : Fun1 -> Fun2 -> Fun2 -> Fun1
Df_axRBase g h1 h2 =
  C Pair (constN tag_sb)
    (C Pair (C Pair (constN zero) num) (packAx9_codeR_Fun1 g h1 h2))

------------------------------------------------------------------------
-- The canonical unfold target  encDfAxRBase g h1 h2 X .

private
  encDfAxRBase : Fun1 -> Fun2 -> Fun2 -> Term -> Term
  encDfAxRBase g h1 h2 X =
    ap2 Pair (natCode tag_sb)
      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X))
                (packAx9_codeR_Term g h1 h2))

  Df_axRBase_unfold :
    (g : Fun1) (h1 h2 : Fun2) (X : Term) ->
    Deriv (eqF (ap1 (Df_axRBase g h1 h2) X) (encDfAxRBase g h1 h2 X))
  Df_axRBase_unfold g h1 h2 X =
    let pa_const : Fun1
        pa_const = packAx9_codeR_Fun1 g h1 h2

        pa_const_term : Term
        pa_const_term = packAx9_codeR_Term g h1 h2

        e1 :
          Deriv (eqF (ap1 (Df_axRBase g h1 h2) X)
                      (ap2 Pair (ap1 (constN tag_sb) X)
                                  (ap1 (C Pair (C Pair (constN zero) num) pa_const) X)))
        e1 = ax_C Pair (constN tag_sb)
                      (C Pair (C Pair (constN zero) num) pa_const) X

        e3 :
          Deriv (eqF (ap1 (C Pair (constN zero) num) X)
                      (ap2 Pair (natCode zero) (ap1 num X)))
        e3 = ruleTrans (ax_C Pair (constN zero) num X)
               (congL Pair (ap1 num X) (constN_eq zero X))

        e2' :
          Deriv (eqF (ap1 (C Pair (C Pair (constN zero) num) pa_const) X)
                      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X)) pa_const_term))
        e2' = ruleTrans (ax_C Pair (C Pair (constN zero) num) pa_const X)
                (ruleTrans (congL Pair (ap1 pa_const X) e3)
                           (congR Pair (ap2 Pair (natCode zero) (ap1 num X))
                                       (packAx9_codeR_eq g h1 h2 X)))

        cN_sb : Deriv (eqF (ap1 (constN tag_sb) X) (natCode tag_sb))
        cN_sb = constN_eq tag_sb X
    in ruleTrans e1
         (ruleTrans (congL Pair
                       (ap1 (C Pair (C Pair (constN zero) num) pa_const) X) cN_sb)
                    (congR Pair (natCode tag_sb) e2'))

------------------------------------------------------------------------
-- Bridge  outputRHS_at extra  to its concrete form with the Fst/Snd
-- projection in codeRHS evaluated.
--
--   axN9 outputRHS extra =
--     pi tag_eq (pi codeLHS codeRHS)
--   where
--     codeLHS = pi tag_ap2 (pi extra (pi cV0 O))
--     codeRHS = pi tag_ap1 (pi G cV0)  with  G = Fst (Snd extra) .
--
-- For  extra = codeFun2 (R g h1 h2) = pi tag_R (pi codeG (pi codeH1 codeH2)) ,
--   Snd extra = pi codeG (pi codeH1 codeH2)
--   Fst (Snd extra) = codeFun1 g .

private
  -- The "concrete" schema form ( = outputRHS extra with G replaced by codeFun1 g ).
  axN9_codeLHS : Fun1 -> Fun2 -> Fun2 -> Term
  axN9_codeLHS g h1 h2 =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair cV0 O))

  axN9_codeRHS : Fun1 -> Term
  axN9_codeRHS g = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 g) cV0)

  axN9_concrete : Fun1 -> Fun2 -> Fun2 -> Term
  axN9_concrete g h1 h2 =
    ap2 Pair (natCode tag_eq)
      (ap2 Pair (axN9_codeLHS g h1 h2) (axN9_codeRHS g))

  outputRHS_at : Term -> Term
  outputRHS_at extra =
    let G = ap1 Fst (ap1 Snd extra)
        codeLHS = ap2 Pair (natCode tag_ap2) (ap2 Pair extra (ap2 Pair cV0 O))
        codeRHS = ap2 Pair (natCode tag_ap1) (ap2 Pair G cV0)
    in ap2 Pair (natCode tag_eq) (ap2 Pair codeLHS codeRHS)

  -- When  extra = codeFun2 (R g h1 h2) ,  outputRHS_at extra  =Deriv=  axN9_concrete g h1 h2 .
  outputRHS_bridge :
    (g : Fun1) (h1 h2 : Fun2) ->
    Deriv (eqF (outputRHS_at (codeFun2 (R g h1 h2)))
                (axN9_concrete g h1 h2))
  outputRHS_bridge g h1 h2 =
    let extra : Term
        extra = codeFun2 (R g h1 h2)

        innerR : Term
        innerR = ap2 Pair (codeFun1 g)
                   (ap2 Pair (codeFun2 h1) (codeFun2 h2))

        innerHs : Term
        innerHs = ap2 Pair (codeFun2 h1) (codeFun2 h2)

        Snd_extra_eq : Deriv (eqF (ap1 Snd extra) innerR)
        Snd_extra_eq = axSnd (natCode tag_R) innerR

        Fst_Snd_extra_eq :
          Deriv (eqF (ap1 Fst (ap1 Snd extra)) (codeFun1 g))
        Fst_Snd_extra_eq =
          ruleTrans (cong1 Fst Snd_extra_eq)
                    (axFst (codeFun1 g) innerHs)

        G_old : Term
        G_old = ap1 Fst (ap1 Snd extra)

        -- codeLHS is unchanged (no projection bridges needed -- extra is in place).
        -- codeRHS = pi tag_ap1 (pi G_old cV0)  ->  axN9_codeRHS g  via Fst_Snd_extra_eq .

        pair_G_eq :
          Deriv (eqF (ap2 Pair G_old cV0) (ap2 Pair (codeFun1 g) cV0))
        pair_G_eq = congL Pair cV0 Fst_Snd_extra_eq

        codeRHS_eq :
          Deriv (eqF (ap2 Pair (natCode tag_ap1) (ap2 Pair G_old cV0))
                      (axN9_codeRHS g))
        codeRHS_eq = congR Pair (natCode tag_ap1) pair_G_eq

        outer_pair_eq :
          Deriv (eqF
            (ap2 Pair (axN9_codeLHS g h1 h2)
              (ap2 Pair (natCode tag_ap1) (ap2 Pair G_old cV0)))
            (ap2 Pair (axN9_codeLHS g h1 h2) (axN9_codeRHS g)))
        outer_pair_eq = congR Pair (axN9_codeLHS g h1 h2) codeRHS_eq
    in congR Pair (natCode tag_eq) outer_pair_eq

------------------------------------------------------------------------
-- Apply sbf spec to axN9_concrete.
--
-- spec = pi (natCode 0) (num X) ; substitutes v0 := num X .
--
-- sbt sp (axN9_codeLHS g h1 h2) :
--   axN9_codeLHS g h1 h2 = pi tag_ap2 (pi (codeFun2 (R g h1 h2)) (pi cV0 O))
--   sbt walks via sbt_at_ap2 with g_F2 = (R g h1 h2) , ca = cV0 , cb = O .
--   sbt sp cV0 = num X    (sbt_at_var_match)
--   sbt sp O   = O        (sbt_at_O)
--   result : pi tag_ap2 (pi (codeFun2 (R g h1 h2)) (pi (num X) O))  = encCodeLHS .
--
-- sbt sp (axN9_codeRHS g) :
--   axN9_codeRHS g = pi tag_ap1 (pi (codeFun1 g) cV0)
--   sbt walks via sbt_at_ap1 with f = g , ct = cV0 .
--   sbt sp cV0 = num X .
--   result : pi tag_ap1 (pi (codeFun1 g) (num X))  = encCodeRHS .

private
  encCodeLHS : Fun1 -> Fun2 -> Fun2 -> Term -> Term
  encCodeLHS g h1 h2 X =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) O))

  encCodeRHS : Fun1 -> Term -> Term
  encCodeRHS g X =
    ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 g) (ap1 num X))

encodedAxRBase_Term : Fun1 -> Fun2 -> Fun2 -> Term -> Term
encodedAxRBase_Term g h1 h2 X =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (encCodeLHS g h1 h2 X) (encCodeRHS g X))

------------------------------------------------------------------------
-- sbf-cascade lemma.

private
  spec_at : Term -> Term
  spec_at X = ap2 Pair (natCode zero) (ap1 num X)

  sbf_step :
    (g : Fun1) (h1 h2 : Fun2) (X : Term) ->
    Deriv (eqF (ap2 sbf (spec_at X) (axN9_concrete g h1 h2))
                (encodedAxRBase_Term g h1 h2 X))
  sbf_step g h1 h2 X =
    let sp : Term
        sp = spec_at X

        -- sbf_at_atomic at k=0, S=(num X), ca=axN9_codeLHS, cb=axN9_codeRHS.
        e_atomic :
          Deriv (eqF (ap2 sbf sp (axN9_concrete g h1 h2))
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt sp (axN9_codeLHS g h1 h2))
                          (ap2 sbt sp (axN9_codeRHS g)))))
        e_atomic =
          sbf_at_atomic zero (ap1 num X)
            (axN9_codeLHS g h1 h2) (axN9_codeRHS g)

        -- sbt sp cV0 = num X.
        e_cV0 : Deriv (eqF (ap2 sbt sp cV0) (ap1 num X))
        e_cV0 = sbt_at_var_match zero (ap1 num X)

        -- sbt sp O = O.
        e_O : Deriv (eqF (ap2 sbt sp O) O)
        e_O = sbt_at_O sp

        -- sbt sp axN9_codeLHS via sbt_at_ap2 with g_F2 = (R g h1 h2) .
        e_lhs_step :
          Deriv (eqF (ap2 sbt sp (axN9_codeLHS g h1 h2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 (R g h1 h2))
                          (ap2 Pair (ap2 sbt sp cV0) (ap2 sbt sp O)))))
        e_lhs_step = sbt_at_ap2 zero (ap1 num X) (R g h1 h2) cV0 O

        e_lhs_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt sp cV0) (ap2 sbt sp O))
                      (ap2 Pair (ap1 num X) O))
        e_lhs_inner =
          ruleTrans (congL Pair (ap2 sbt sp O) e_cV0)
                    (congR Pair (ap1 num X) e_O)

        e_lhs :
          Deriv (eqF (ap2 sbt sp (axN9_codeLHS g h1 h2)) (encCodeLHS g h1 h2 X))
        e_lhs = ruleTrans e_lhs_step
                  (congR Pair (natCode tag_ap2)
                    (congR Pair (codeFun2 (R g h1 h2)) e_lhs_inner))

        -- sbt sp axN9_codeRHS via sbt_at_ap1 with f = g .
        e_rhs_step :
          Deriv (eqF (ap2 sbt sp (axN9_codeRHS g))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 g) (ap2 sbt sp cV0))))
        e_rhs_step = sbt_at_ap1 zero (ap1 num X) g cV0

        e_rhs :
          Deriv (eqF (ap2 sbt sp (axN9_codeRHS g)) (encCodeRHS g X))
        e_rhs = ruleTrans e_rhs_step
                  (congR Pair (natCode tag_ap1)
                    (congR Pair (codeFun1 g) e_cV0))

        e_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt sp (axN9_codeLHS g h1 h2))
                      (ap2 sbt sp (axN9_codeRHS g)))
            (ap2 Pair (encCodeLHS g h1 h2 X) (encCodeRHS g X)))
        e_inner =
          ruleTrans (congL Pair (ap2 sbt sp (axN9_codeRHS g)) e_lhs)
                    (congR Pair (encCodeLHS g h1 h2 X) e_rhs)

        e_outer :
          Deriv (eqF
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt sp (axN9_codeLHS g h1 h2))
                        (ap2 sbt sp (axN9_codeRHS g))))
            (encodedAxRBase_Term g h1 h2 X))
        e_outer = congR Pair (natCode tag_eq) e_inner
    in ruleTrans e_atomic e_outer

------------------------------------------------------------------------
-- Main theorem.

encodedAxRBase :
  (g : Fun1) (h1 h2 : Fun2) (X : Term) ->
  Deriv (eqF (ap1 thmT (ap1 (Df_axRBase g h1 h2) X))
              (encodedAxRBase_Term g h1 h2 X))
encodedAxRBase g h1 h2 X =
  let
    sp : Term
    sp = spec_at X

    extra : Term
    extra = codeFun2 (R g h1 h2)

    pa_const_term : Term
    pa_const_term = packAx9_codeR_Term g h1 h2

    -- (a) Df_axRBase g h1 h2 X =Deriv= encDfAxRBase g h1 h2 X.
    e_unfold : Deriv (eqF (ap1 (Df_axRBase g h1 h2) X) (encDfAxRBase g h1 h2 X))
    e_unfold = Df_axRBase_unfold g h1 h2 X

    e_thmT_unfold :
      Deriv (eqF (ap1 thmT (ap1 (Df_axRBase g h1 h2) X))
                  (ap1 thmT (encDfAxRBase g h1 h2 X)))
    e_thmT_unfold = cong1 thmT e_unfold

    -- (b) thmT (encDfAxRBase g h1 h2 X) =Deriv= sbf sp (thmT pa_const_term).
    e_at_sb :
      Deriv (eqF (ap1 thmT (encDfAxRBase g h1 h2 X))
                  (ap2 sbf sp (ap1 thmT pa_const_term)))
    e_at_sb = thmT_at_sb sp pa_const_term

    -- (c) thmT pa_const_term =Deriv= outputRHS_at extra.
    e_axN9 :
      Deriv (eqF (ap1 thmT pa_const_term) (outputRHS_at extra))
    e_axN9 = thmT_at_axN9 extra

    e_lift_axN9 :
      Deriv (eqF (ap2 sbf sp (ap1 thmT pa_const_term))
                  (ap2 sbf sp (outputRHS_at extra)))
    e_lift_axN9 = congR sbf sp e_axN9

    -- (d) outputRHS_at extra =Deriv= axN9_concrete g h1 h2.
    e_bridge :
      Deriv (eqF (outputRHS_at extra) (axN9_concrete g h1 h2))
    e_bridge = outputRHS_bridge g h1 h2

    e_lift_bridge :
      Deriv (eqF (ap2 sbf sp (outputRHS_at extra))
                  (ap2 sbf sp (axN9_concrete g h1 h2)))
    e_lift_bridge = congR sbf sp e_bridge

    -- (e) sbf sp axN9_concrete =Deriv= encodedAxRBase_Term g h1 h2 X.
    e_sbf :
      Deriv (eqF (ap2 sbf sp (axN9_concrete g h1 h2))
                  (encodedAxRBase_Term g h1 h2 X))
    e_sbf = sbf_step g h1 h2 X

  in ruleTrans e_thmT_unfold
       (ruleTrans e_at_sb
         (ruleTrans e_lift_axN9
           (ruleTrans e_lift_bridge e_sbf)))
