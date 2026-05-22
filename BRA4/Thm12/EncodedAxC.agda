{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxC -- encoded  ax_C  instance via single sb-wrap
-- on axN8.
--
-- Goal (universal in g : Fun2, h1 h2 : Fun1, X : Term ; no Closed) :
--
--   Df_axC : Fun2 -> Fun1 -> Fun1 -> Fun1
--   encodedAxC :
--     (g : Fun2) (h1 h2 : Fun1) (X : Term) ->
--     Deriv (eqF (ap1 thmT (ap1 (Df_axC g h1 h2) X))
--                 (encodedAxC_Term g h1 h2 X))
--
-- where  encodedAxC_Term g h1 h2 X  is the asymmetric encoding of the
-- formula  "C g h1 h2 (num X) = g (h1 (num X)) (h2 (num X))"  :
--
--   Pair tag_eq
--     (Pair encCodeLHS encCodeRHS)
--   where
--     encCodeLHS = Pair tag_ap1 (Pair (codeFun1 (C g h1 h2)) (num X))
--     encCodeRHS = Pair tag_ap2 (Pair (codeFun2 g)
--                                  (Pair (Pair tag_ap1 (Pair (codeFun1 h1) (num X)))
--                                        (Pair tag_ap1 (Pair (codeFun1 h2) (num X)))))
--
-- Construction.  Df_axC g h1 h2 X = encode_sb 0 (num X) (packAx 8 (codeFun1 (C g h1 h2))) :
--   Pair tag_sb
--     (Pair (Pair (natCode 0) (num X))
--           (Pair (natCode tag_ax)
--                 (Pair (natCode 8) (codeFun1 (C g h1 h2)))))
--
-- thmT walks the wrap :
--   thmT (Df_axC g h1 h2 X)
--     = sbf spec (thmT (packAx 8 (codeFun1 (C g h1 h2))))           [thmT_at_sb]
--     = sbf spec (outputRHS (codeFun1 (C g h1 h2)))                  [thmT_at_axN8]
--     = sbf spec axN8_concrete                                       [bridge projections]
--     = encodedAxC_Term g h1 h2 X                                    [sbf cascade]
--
-- No Closed premise.  num X enters as a leaf via the single sb-wrap ;
-- sbt walks the schema (which has only var-positions and well-shaped
-- Pair structure) but never walks through (num X) itself.

module BRA4.Thm12.EncodedAxC where

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
open import BRA4.ThmTAtAx8         using ( thmT_at_axN8 )
open import BRA4.Thm12.ConstTermFun1
  using ( constTermFun1 ; constTermFun1_eq
        ; NoVar ; NoVar_natCode ; NoVar_pair ; NoVar_pair_natCode
        ; NoVarAnd ; mkAnd )

open SbContract sbContract

------------------------------------------------------------------------
-- NoVar for codeFun1 / codeFun2 by mutual structural induction.

NoVar_codeFun1 : (f : Fun1) -> NoVar (codeFun1 f)
NoVar_codeFun2 : (g : Fun2) -> NoVar (codeFun2 g)

NoVar_codeFun1 s             = NoVar_natCode tag_s
NoVar_codeFun1 o             = NoVar_natCode tag_o
NoVar_codeFun1 u             = NoVar_natCode tag_u
NoVar_codeFun1 (C g h1 h2)   =
  NoVar_pair_natCode tag_C
    (ap2 Pair (codeFun2 g) (ap2 Pair (codeFun1 h1) (codeFun1 h2)))
    (NoVar_pair (codeFun2 g)
                (ap2 Pair (codeFun1 h1) (codeFun1 h2))
                (NoVar_codeFun2 g)
                (NoVar_pair (codeFun1 h1) (codeFun1 h2)
                            (NoVar_codeFun1 h1) (NoVar_codeFun1 h2)))

NoVar_codeFun2 v             = NoVar_natCode tag_v
NoVar_codeFun2 (R g h1 h2)   =
  NoVar_pair_natCode tag_R
    (ap2 Pair (codeFun1 g) (ap2 Pair (codeFun2 h1) (codeFun2 h2)))
    (NoVar_pair (codeFun1 g)
                (ap2 Pair (codeFun2 h1) (codeFun2 h2))
                (NoVar_codeFun1 g)
                (NoVar_pair (codeFun2 h1) (codeFun2 h2)
                            (NoVar_codeFun2 h1) (NoVar_codeFun2 h2)))

------------------------------------------------------------------------
-- Constants and helpers.

private
  N8 : Nat
  N8 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  -- The inner constant Term  packAx 8 (codeFun1 (C g h1 h2)) .
  packAx8_codeC_Term : Fun2 -> Fun1 -> Fun1 -> Term
  packAx8_codeC_Term g h1 h2 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N8) (codeFun1 (C g h1 h2)))

  NoVar_packAx8_codeC :
    (g : Fun2) (h1 h2 : Fun1) -> NoVar (packAx8_codeC_Term g h1 h2)
  NoVar_packAx8_codeC g h1 h2 =
    NoVar_pair_natCode tag_ax
      (ap2 Pair (natCode N8) (codeFun1 (C g h1 h2)))
      (NoVar_pair_natCode N8 (codeFun1 (C g h1 h2))
         (NoVar_codeFun1 (C g h1 h2)))

  packAx8_codeC_Fun1 : Fun2 -> Fun1 -> Fun1 -> Fun1
  packAx8_codeC_Fun1 g h1 h2 =
    constTermFun1 (packAx8_codeC_Term g h1 h2)

  packAx8_codeC_eq :
    (g : Fun2) (h1 h2 : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (packAx8_codeC_Fun1 g h1 h2) X)
                (packAx8_codeC_Term g h1 h2))
  packAx8_codeC_eq g h1 h2 X =
    constTermFun1_eq (packAx8_codeC_Term g h1 h2)
                     (NoVar_packAx8_codeC g h1 h2) X

------------------------------------------------------------------------
-- Df_axC : the Fun1 producing the sb-encoded ax_C instance.

Df_axC : Fun2 -> Fun1 -> Fun1 -> Fun1
Df_axC g h1 h2 =
  C Pair (constN tag_sb)
    (C Pair (C Pair (constN zero) num) (packAx8_codeC_Fun1 g h1 h2))

------------------------------------------------------------------------
-- The canonical unfold target  encDfAxC g h1 h2 X .

private
  encDfAxC : Fun2 -> Fun1 -> Fun1 -> Term -> Term
  encDfAxC g h1 h2 X =
    ap2 Pair (natCode tag_sb)
      (ap2 Pair (ap2 Pair (natCode zero) (ap1 num X))
                (packAx8_codeC_Term g h1 h2))

  Df_axC_unfold :
    (g : Fun2) (h1 h2 : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (Df_axC g h1 h2) X) (encDfAxC g h1 h2 X))
  Df_axC_unfold g h1 h2 X =
    let pa_const : Fun1
        pa_const = packAx8_codeC_Fun1 g h1 h2

        pa_const_term : Term
        pa_const_term = packAx8_codeC_Term g h1 h2

        e1 :
          Deriv (eqF (ap1 (Df_axC g h1 h2) X)
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
                                       (packAx8_codeC_eq g h1 h2 X)))

        cN_sb : Deriv (eqF (ap1 (constN tag_sb) X) (natCode tag_sb))
        cN_sb = constN_eq tag_sb X
    in ruleTrans e1
         (ruleTrans (congL Pair
                       (ap1 (C Pair (C Pair (constN zero) num) pa_const) X) cN_sb)
                    (congR Pair (natCode tag_sb) e2'))

------------------------------------------------------------------------
-- Bridge  outputRHS (codeFun1 (C g h1 h2))  to its concrete form
-- with Fst/Snd projections evaluated.

private
  -- The "concrete" schema form ( = outputRHS extra with projections
  -- replaced by codeFun2 g / codeFun1 h1 / codeFun1 h2 ).
  axN8_codeLHS : Fun2 -> Fun1 -> Fun1 -> Term
  axN8_codeLHS g h1 h2 =
    ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 (C g h1 h2)) cV0)

  axN8_codeH1V0 : Fun1 -> Term
  axN8_codeH1V0 h1 = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 h1) cV0)

  axN8_codeH2V0 : Fun1 -> Term
  axN8_codeH2V0 h2 = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 h2) cV0)

  axN8_codeRHS : Fun2 -> Fun1 -> Fun1 -> Term
  axN8_codeRHS g h1 h2 =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 g)
        (ap2 Pair (axN8_codeH1V0 h1) (axN8_codeH2V0 h2)))

  axN8_concrete : Fun2 -> Fun1 -> Fun1 -> Term
  axN8_concrete g h1 h2 =
    ap2 Pair (natCode tag_eq)
      (ap2 Pair (axN8_codeLHS g h1 h2) (axN8_codeRHS g h1 h2))

  -- outputRHS extra (re-derived for clarity ; matches BRA4.ThmTAtAx8.outputRHS
  -- when extra is plugged in).
  outputRHS_at : Term -> Term
  outputRHS_at extra =
    let G = ap1 Fst (ap1 Snd extra)
        H1 = ap1 Fst (ap1 Snd (ap1 Snd extra))
        H2 = ap1 Snd (ap1 Snd (ap1 Snd extra))
        codeLHS = ap2 Pair (natCode tag_ap1) (ap2 Pair extra cV0)
        codeH1V0 = ap2 Pair (natCode tag_ap1) (ap2 Pair H1 cV0)
        codeH2V0 = ap2 Pair (natCode tag_ap1) (ap2 Pair H2 cV0)
        codeRHS = ap2 Pair (natCode tag_ap2) (ap2 Pair G (ap2 Pair codeH1V0 codeH2V0))
    in ap2 Pair (natCode tag_eq) (ap2 Pair codeLHS codeRHS)

  -- Bridge : when  extra = codeFun1 (C g h1 h2) ,  outputRHS_at extra
  -- equals  axN8_concrete g h1 h2 .
  outputRHS_bridge :
    (g : Fun2) (h1 h2 : Fun1) ->
    Deriv (eqF (outputRHS_at (codeFun1 (C g h1 h2)))
                (axN8_concrete g h1 h2))
  outputRHS_bridge g h1 h2 =
    let extra : Term
        extra = codeFun1 (C g h1 h2)

        -- codeFun1 (C g h1 h2)  =Deriv= Pair tag_C (Pair (codeFun2 g)
        --                                                  (Pair (codeFun1 h1) (codeFun1 h2))).
        -- (This is DEFINITIONAL in BRA4.Code.codeFun1 ;  no Deriv needed.)

        innerC : Term
        innerC = ap2 Pair (codeFun2 g)
                   (ap2 Pair (codeFun1 h1) (codeFun1 h2))

        innerHs : Term
        innerHs = ap2 Pair (codeFun1 h1) (codeFun1 h2)

        -- Snd extra  =Deriv= innerC .
        Snd_extra_eq : Deriv (eqF (ap1 Snd extra) innerC)
        Snd_extra_eq = axSnd (natCode tag_C) innerC

        -- Fst (Snd extra) =Deriv= codeFun2 g .
        Fst_Snd_extra_eq :
          Deriv (eqF (ap1 Fst (ap1 Snd extra)) (codeFun2 g))
        Fst_Snd_extra_eq =
          ruleTrans (cong1 Fst Snd_extra_eq)
                    (axFst (codeFun2 g) innerHs)

        -- Snd (Snd extra) =Deriv= innerHs .
        Snd_Snd_extra_eq :
          Deriv (eqF (ap1 Snd (ap1 Snd extra)) innerHs)
        Snd_Snd_extra_eq =
          ruleTrans (cong1 Snd Snd_extra_eq)
                    (axSnd (codeFun2 g) innerHs)

        -- Fst (Snd (Snd extra)) =Deriv= codeFun1 h1 .
        Fst_SS_eq :
          Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd extra))) (codeFun1 h1))
        Fst_SS_eq =
          ruleTrans (cong1 Fst Snd_Snd_extra_eq)
                    (axFst (codeFun1 h1) (codeFun1 h2))

        -- Snd (Snd (Snd extra)) =Deriv= codeFun1 h2 .
        Snd_SS_eq :
          Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd extra))) (codeFun1 h2))
        Snd_SS_eq =
          ruleTrans (cong1 Snd Snd_Snd_extra_eq)
                    (axSnd (codeFun1 h1) (codeFun1 h2))

        -- codeLHS already matches (extra = codeFun1 (C g h1 h2) directly).
        -- codeRHS needs the three projection bridges.

        G_old : Term
        G_old = ap1 Fst (ap1 Snd extra)
        H1_old : Term
        H1_old = ap1 Fst (ap1 Snd (ap1 Snd extra))
        H2_old : Term
        H2_old = ap1 Snd (ap1 Snd (ap1 Snd extra))

        codeH1V0_old : Term
        codeH1V0_old = ap2 Pair (natCode tag_ap1) (ap2 Pair H1_old cV0)
        codeH2V0_old : Term
        codeH2V0_old = ap2 Pair (natCode tag_ap1) (ap2 Pair H2_old cV0)

        -- Pair H1_old cV0  ->  Pair (codeFun1 h1) cV0 .
        pair_H1_eq :
          Deriv (eqF (ap2 Pair H1_old cV0) (ap2 Pair (codeFun1 h1) cV0))
        pair_H1_eq = congL Pair cV0 Fst_SS_eq

        codeH1V0_eq :
          Deriv (eqF codeH1V0_old (axN8_codeH1V0 h1))
        codeH1V0_eq = congR Pair (natCode tag_ap1) pair_H1_eq

        pair_H2_eq :
          Deriv (eqF (ap2 Pair H2_old cV0) (ap2 Pair (codeFun1 h2) cV0))
        pair_H2_eq = congL Pair cV0 Snd_SS_eq

        codeH2V0_eq :
          Deriv (eqF codeH2V0_old (axN8_codeH2V0 h2))
        codeH2V0_eq = congR Pair (natCode tag_ap1) pair_H2_eq

        pair_H_eq :
          Deriv (eqF (ap2 Pair codeH1V0_old codeH2V0_old)
                      (ap2 Pair (axN8_codeH1V0 h1) (axN8_codeH2V0 h2)))
        pair_H_eq =
          ruleTrans (congL Pair codeH2V0_old codeH1V0_eq)
                    (congR Pair (axN8_codeH1V0 h1) codeH2V0_eq)

        pair_G_pair_eq :
          Deriv (eqF (ap2 Pair G_old (ap2 Pair codeH1V0_old codeH2V0_old))
                      (ap2 Pair (codeFun2 g)
                        (ap2 Pair (axN8_codeH1V0 h1) (axN8_codeH2V0 h2))))
        pair_G_pair_eq =
          ruleTrans (congL Pair (ap2 Pair codeH1V0_old codeH2V0_old) Fst_Snd_extra_eq)
                    (congR Pair (codeFun2 g) pair_H_eq)

        codeRHS_eq :
          Deriv (eqF (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair G_old (ap2 Pair codeH1V0_old codeH2V0_old)))
                      (axN8_codeRHS g h1 h2))
        codeRHS_eq = congR Pair (natCode tag_ap2) pair_G_pair_eq

        outer_pair_eq :
          Deriv (eqF
            (ap2 Pair (axN8_codeLHS g h1 h2)
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair G_old (ap2 Pair codeH1V0_old codeH2V0_old))))
            (ap2 Pair (axN8_codeLHS g h1 h2) (axN8_codeRHS g h1 h2)))
        outer_pair_eq =
          congR Pair (axN8_codeLHS g h1 h2) codeRHS_eq
    in congR Pair (natCode tag_eq) outer_pair_eq

------------------------------------------------------------------------
-- Apply sbf spec to axN8_concrete.

private
  encCodeLHS : Fun2 -> Fun1 -> Fun1 -> Term -> Term
  encCodeLHS g h1 h2 X =
    ap2 Pair (natCode tag_ap1)
      (ap2 Pair (codeFun1 (C g h1 h2)) (ap1 num X))

  encH1X : Fun1 -> Term -> Term
  encH1X h1 X =
    ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 h1) (ap1 num X))

  encH2X : Fun1 -> Term -> Term
  encH2X h2 X =
    ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 h2) (ap1 num X))

  encCodeRHS : Fun2 -> Fun1 -> Fun1 -> Term -> Term
  encCodeRHS g h1 h2 X =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 g)
        (ap2 Pair (encH1X h1 X) (encH2X h2 X)))

encodedAxC_Term : Fun2 -> Fun1 -> Fun1 -> Term -> Term
encodedAxC_Term g h1 h2 X =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (encCodeLHS g h1 h2 X) (encCodeRHS g h1 h2 X))

------------------------------------------------------------------------
-- sbf-cascade lemma.

private
  spec_at : Term -> Term
  spec_at X = ap2 Pair (natCode zero) (ap1 num X)

  sbf_step :
    (g : Fun2) (h1 h2 : Fun1) (X : Term) ->
    Deriv (eqF (ap2 sbf (spec_at X) (axN8_concrete g h1 h2))
                (encodedAxC_Term g h1 h2 X))
  sbf_step g h1 h2 X =
    let sp : Term
        sp = spec_at X

        -- sbf_at_atomic at k=0, S=(num X), ca=codeLHS_schema, cb=codeRHS_schema.
        e_atomic :
          Deriv (eqF (ap2 sbf sp (axN8_concrete g h1 h2))
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt sp (axN8_codeLHS g h1 h2))
                          (ap2 sbt sp (axN8_codeRHS g h1 h2)))))
        e_atomic =
          sbf_at_atomic zero (ap1 num X)
            (axN8_codeLHS g h1 h2) (axN8_codeRHS g h1 h2)

        -- sbt sp cV0 = num X.
        e_cV0 : Deriv (eqF (ap2 sbt sp cV0) (ap1 num X))
        e_cV0 = sbt_at_var_match zero (ap1 num X)

        -- sbt sp codeLHS_schema = encCodeLHS.
        --   sbt_at_ap1  with k=0, S=(num X), f=(C g h1 h2), ct=cV0
        --   gives  Pair tag_ap1 (Pair (codeFun1 (C g h1 h2)) (sbt sp cV0)).
        e_lhs_step :
          Deriv (eqF (ap2 sbt sp (axN8_codeLHS g h1 h2))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 (C g h1 h2)) (ap2 sbt sp cV0))))
        e_lhs_step = sbt_at_ap1 zero (ap1 num X) (C g h1 h2) cV0

        e_lhs :
          Deriv (eqF (ap2 sbt sp (axN8_codeLHS g h1 h2))
                      (encCodeLHS g h1 h2 X))
        e_lhs = ruleTrans e_lhs_step
                  (congR Pair (natCode tag_ap1)
                    (congR Pair (codeFun1 (C g h1 h2)) e_cV0))

        -- sbt sp codeH1V0 = encH1X.
        e_h1_step :
          Deriv (eqF (ap2 sbt sp (axN8_codeH1V0 h1))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 h1) (ap2 sbt sp cV0))))
        e_h1_step = sbt_at_ap1 zero (ap1 num X) h1 cV0

        e_h1 :
          Deriv (eqF (ap2 sbt sp (axN8_codeH1V0 h1)) (encH1X h1 X))
        e_h1 = ruleTrans e_h1_step
                 (congR Pair (natCode tag_ap1)
                   (congR Pair (codeFun1 h1) e_cV0))

        -- sbt sp codeH2V0 = encH2X.
        e_h2_step :
          Deriv (eqF (ap2 sbt sp (axN8_codeH2V0 h2))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 h2) (ap2 sbt sp cV0))))
        e_h2_step = sbt_at_ap1 zero (ap1 num X) h2 cV0

        e_h2 :
          Deriv (eqF (ap2 sbt sp (axN8_codeH2V0 h2)) (encH2X h2 X))
        e_h2 = ruleTrans e_h2_step
                 (congR Pair (natCode tag_ap1)
                   (congR Pair (codeFun1 h2) e_cV0))

        -- sbt sp codeRHS_schema = encCodeRHS.
        --   sbt_at_ap2  with k=0, S=(num X), g=g, ca=codeH1V0, cb=codeH2V0.
        e_rhs_step :
          Deriv (eqF (ap2 sbt sp (axN8_codeRHS g h1 h2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt sp (axN8_codeH1V0 h1))
                            (ap2 sbt sp (axN8_codeH2V0 h2))))))
        e_rhs_step =
          sbt_at_ap2 zero (ap1 num X) g
            (axN8_codeH1V0 h1) (axN8_codeH2V0 h2)

        rhs_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt sp (axN8_codeH1V0 h1)) (ap2 sbt sp (axN8_codeH2V0 h2)))
            (ap2 Pair (encH1X h1 X) (encH2X h2 X)))
        rhs_inner =
          ruleTrans (congL Pair (ap2 sbt sp (axN8_codeH2V0 h2)) e_h1)
                    (congR Pair (encH1X h1 X) e_h2)

        e_rhs :
          Deriv (eqF (ap2 sbt sp (axN8_codeRHS g h1 h2)) (encCodeRHS g h1 h2 X))
        e_rhs = ruleTrans e_rhs_step
                  (congR Pair (natCode tag_ap2)
                    (congR Pair (codeFun2 g) rhs_inner))

        e_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt sp (axN8_codeLHS g h1 h2))
                      (ap2 sbt sp (axN8_codeRHS g h1 h2)))
            (ap2 Pair (encCodeLHS g h1 h2 X) (encCodeRHS g h1 h2 X)))
        e_inner =
          ruleTrans (congL Pair (ap2 sbt sp (axN8_codeRHS g h1 h2)) e_lhs)
                    (congR Pair (encCodeLHS g h1 h2 X) e_rhs)

        e_outer :
          Deriv (eqF
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt sp (axN8_codeLHS g h1 h2))
                        (ap2 sbt sp (axN8_codeRHS g h1 h2))))
            (encodedAxC_Term g h1 h2 X))
        e_outer = congR Pair (natCode tag_eq) e_inner
    in ruleTrans e_atomic e_outer

------------------------------------------------------------------------
-- Main theorem.

encodedAxC :
  (g : Fun2) (h1 h2 : Fun1) (X : Term) ->
  Deriv (eqF (ap1 thmT (ap1 (Df_axC g h1 h2) X))
              (encodedAxC_Term g h1 h2 X))
encodedAxC g h1 h2 X =
  let
    sp : Term
    sp = spec_at X

    extra : Term
    extra = codeFun1 (C g h1 h2)

    pa_const_term : Term
    pa_const_term = packAx8_codeC_Term g h1 h2

    -- (a) Df_axC g h1 h2 X =Deriv= encDfAxC g h1 h2 X.
    e_unfold : Deriv (eqF (ap1 (Df_axC g h1 h2) X) (encDfAxC g h1 h2 X))
    e_unfold = Df_axC_unfold g h1 h2 X

    e_thmT_unfold :
      Deriv (eqF (ap1 thmT (ap1 (Df_axC g h1 h2) X))
                  (ap1 thmT (encDfAxC g h1 h2 X)))
    e_thmT_unfold = cong1 thmT e_unfold

    -- (b) thmT (encDfAxC g h1 h2 X) =Deriv= sbf sp (thmT pa_const_term).
    e_at_sb :
      Deriv (eqF (ap1 thmT (encDfAxC g h1 h2 X))
                  (ap2 sbf sp (ap1 thmT pa_const_term)))
    e_at_sb = thmT_at_sb sp pa_const_term

    -- (c) thmT pa_const_term =Deriv= outputRHS_at extra.
    e_axN8 :
      Deriv (eqF (ap1 thmT pa_const_term) (outputRHS_at extra))
    e_axN8 = thmT_at_axN8 extra

    e_lift_axN8 :
      Deriv (eqF (ap2 sbf sp (ap1 thmT pa_const_term))
                  (ap2 sbf sp (outputRHS_at extra)))
    e_lift_axN8 = congR sbf sp e_axN8

    -- (d) outputRHS_at extra =Deriv= axN8_concrete g h1 h2.
    e_bridge :
      Deriv (eqF (outputRHS_at extra) (axN8_concrete g h1 h2))
    e_bridge = outputRHS_bridge g h1 h2

    e_lift_bridge :
      Deriv (eqF (ap2 sbf sp (outputRHS_at extra))
                  (ap2 sbf sp (axN8_concrete g h1 h2)))
    e_lift_bridge = congR sbf sp e_bridge

    -- (e) sbf sp axN8_concrete =Deriv= encodedAxC_Term g h1 h2 X.
    e_sbf :
      Deriv (eqF (ap2 sbf sp (axN8_concrete g h1 h2))
                  (encodedAxC_Term g h1 h2 X))
    e_sbf = sbf_step g h1 h2 X

  in ruleTrans e_thmT_unfold
       (ruleTrans e_at_sb
         (ruleTrans e_lift_axN8
           (ruleTrans e_lift_bridge e_sbf)))
