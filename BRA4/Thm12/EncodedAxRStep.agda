{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxRStep -- encoded  ax_R_step  instance via sb2-wrap on axN10.
--
-- Goal (universal in g : Fun1, h1 h2 : Fun2, X Y : Term ; no Closed) :
--
--   Df_axRStep : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
--   encodedAxRStep :
--     (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
--     Deriv (eqF (ap1 thmT (Df_axRStep g h1 h2 X Y))
--                 (encodedAxRStep_Term g h1 h2 X Y))
--
-- where  encodedAxRStep_Term g h1 h2 X Y  is the asymmetric encoding of
--
--   R g h1 h2 (num X, s_enc(num Y)) = h1 (h2 (num X, num Y)) (R g h1 h2 (num X, num Y))
--
-- with  s_enc(num Y)  =  Pair tag_ap1 (Pair (codeFun1 s) (num Y))   ( = "s applied to num Y" in code form ).
--
-- Concretely :
--   encCodeLHS = Pair tag_ap2 (Pair (codeFun2 (R g h1 h2)) (Pair (num X) s_enc(num Y)))
--   encH2_at   = Pair tag_ap2 (Pair (codeFun2 h2) (Pair (num X) (num Y)))
--   encR_at    = Pair tag_ap2 (Pair (codeFun2 (R g h1 h2)) (Pair (num X) (num Y)))
--   encCodeRHS = Pair tag_ap2 (Pair (codeFun2 h1) (Pair encH2_at encR_at))
--   encodedAxRStep_Term = Pair tag_eq (Pair encCodeLHS encCodeRHS)
--
-- Construction.  Df_axRStep g h1 h2 X Y is the sb2-wrap of  packAx 10 (codeFun2 (R g h1 h2))
-- with substituents  (k1 = 0 |-> num X , k2 = 1 |-> num Y) .

module BRA4.Thm12.EncodedAxRStep where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.Num               using ( num )
open import BRA4.SbContract2
open import BRA4.SbT2              using ( sbt2 )
open import BRA4.SbF2              using ( sbf2 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb2         using ( thmT_at_sb2 )
open import BRA4.ThmTAtAx10        using ( thmT_at_axN10 )
open import BRA4.Thm12.EncodedAxC  using ( NoVar_codeFun1 ; NoVar_codeFun2 )

open SbContract2 sbContract2

------------------------------------------------------------------------
-- Constants and helpers.

private
  N10 : Nat
  N10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  -- codeS_V1  =  codeTerm (ap1 s v1) = pi tag_ap1 (pi (natCode tag_s) cV1)
  --           =  pi tag_ap1 (pi (codeFun1 s) cV1) .
  codeS_V1 : Term
  codeS_V1 = ap2 Pair (natCode tag_ap1) (ap2 Pair (natCode tag_s) cV1)

  -- The inner constant Term  packAx 10 (codeFun2 (R g h1 h2)) .
  packAx10_codeR_Term : Fun1 -> Fun2 -> Fun2 -> Term
  packAx10_codeR_Term g h1 h2 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N10) (codeFun2 (R g h1 h2)))

------------------------------------------------------------------------
-- Df_axRStep : Term-level constructor (depends on raw X , Y) producing
-- the sb2-encoded ax_R_step instance.
--
--   Df_axRStep g h1 h2 X Y =
--     Pair tag_sb2
--       (Pair (Pair (Pair (natCode 0) (num X)) (Pair (natCode 1) (num Y)))
--             (Pair (natCode tag_ax) (Pair (natCode N10) (codeFun2 (R g h1 h2)))))

private
  spec2_at : Term -> Term -> Term
  spec2_at X Y =
    ap2 Pair (ap2 Pair (natCode zero) (ap1 num X))
             (ap2 Pair (natCode (suc zero)) (ap1 num Y))

Df_axRStep : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
Df_axRStep g h1 h2 X Y =
  ap2 Pair (natCode tag_sb2)
    (ap2 Pair (spec2_at X Y) (packAx10_codeR_Term g h1 h2))

------------------------------------------------------------------------
-- Bridge  outputRHS_at extra  (with H1 = Fst(Snd(Snd extra)) ,
-- H2 = Snd(Snd(Snd extra)) ) to a concrete form with the projections
-- evaluated for extra = codeFun2 (R g h1 h2) .
--
-- codeFun2 (R g h1 h2) = Pair tag_R (Pair (codeFun1 g)
--                                          (Pair (codeFun2 h1) (codeFun2 h2))) .
-- Snd extra                  = Pair (codeFun1 g) (Pair (codeFun2 h1) (codeFun2 h2))
-- Snd (Snd extra)            = Pair (codeFun2 h1) (codeFun2 h2)
-- Fst (Snd (Snd extra))      = codeFun2 h1
-- Snd (Snd (Snd extra))      = codeFun2 h2

private
  -- The "concrete" schema form (with H1 -> codeFun2 h1 , H2 -> codeFun2 h2).
  axN10_codeLHS : Fun1 -> Fun2 -> Fun2 -> Term
  axN10_codeLHS g h1 h2 =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair cV0 codeS_V1))

  axN10_codeH2_v0v1 : Fun2 -> Term
  axN10_codeH2_v0v1 h2 =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 h2) (ap2 Pair cV0 cV1))

  axN10_codeR_v0v1 : Fun1 -> Fun2 -> Fun2 -> Term
  axN10_codeR_v0v1 g h1 h2 =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair cV0 cV1))

  axN10_codeRHS : Fun1 -> Fun2 -> Fun2 -> Term
  axN10_codeRHS g h1 h2 =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 h1)
        (ap2 Pair (axN10_codeH2_v0v1 h2) (axN10_codeR_v0v1 g h1 h2)))

  axN10_concrete : Fun1 -> Fun2 -> Fun2 -> Term
  axN10_concrete g h1 h2 =
    ap2 Pair (natCode tag_eq)
      (ap2 Pair (axN10_codeLHS g h1 h2) (axN10_codeRHS g h1 h2))

  outputRHS_at : Term -> Term
  outputRHS_at extra =
    let H1 = ap1 Fst (ap1 Snd (ap1 Snd extra))
        H2 = ap1 Snd (ap1 Snd (ap1 Snd extra))
        codeLHS = ap2 Pair (natCode tag_ap2) (ap2 Pair extra (ap2 Pair cV0 codeS_V1))
        codeH2v0v1 = ap2 Pair (natCode tag_ap2) (ap2 Pair H2 (ap2 Pair cV0 cV1))
        codeR_v0v1 = ap2 Pair (natCode tag_ap2) (ap2 Pair extra (ap2 Pair cV0 cV1))
        codeRHS = ap2 Pair (natCode tag_ap2) (ap2 Pair H1 (ap2 Pair codeH2v0v1 codeR_v0v1))
    in ap2 Pair (natCode tag_eq) (ap2 Pair codeLHS codeRHS)

  outputRHS_bridge :
    (g : Fun1) (h1 h2 : Fun2) ->
    Deriv (eqF (outputRHS_at (codeFun2 (R g h1 h2)))
                (axN10_concrete g h1 h2))
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

        Snd_Snd_extra_eq :
          Deriv (eqF (ap1 Snd (ap1 Snd extra)) innerHs)
        Snd_Snd_extra_eq =
          ruleTrans (cong1 Snd Snd_extra_eq)
                    (axSnd (codeFun1 g) innerHs)

        Fst_SS_eq :
          Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd extra))) (codeFun2 h1))
        Fst_SS_eq =
          ruleTrans (cong1 Fst Snd_Snd_extra_eq)
                    (axFst (codeFun2 h1) (codeFun2 h2))

        Snd_SS_eq :
          Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd extra))) (codeFun2 h2))
        Snd_SS_eq =
          ruleTrans (cong1 Snd Snd_Snd_extra_eq)
                    (axSnd (codeFun2 h1) (codeFun2 h2))

        H1_old : Term
        H1_old = ap1 Fst (ap1 Snd (ap1 Snd extra))
        H2_old : Term
        H2_old = ap1 Snd (ap1 Snd (ap1 Snd extra))

        codeH2v0v1_old : Term
        codeH2v0v1_old = ap2 Pair (natCode tag_ap2) (ap2 Pair H2_old (ap2 Pair cV0 cV1))
        -- codeR_v0v1_old uses extra directly, no projection bridge needed.
        codeR_v0v1_old : Term
        codeR_v0v1_old = ap2 Pair (natCode tag_ap2) (ap2 Pair extra (ap2 Pair cV0 cV1))

        codeH2v0v1_eq :
          Deriv (eqF codeH2v0v1_old (axN10_codeH2_v0v1 h2))
        codeH2v0v1_eq =
          congR Pair (natCode tag_ap2)
            (congL Pair (ap2 Pair cV0 cV1) Snd_SS_eq)

        codeR_v0v1_eq :
          Deriv (eqF codeR_v0v1_old (axN10_codeR_v0v1 g h1 h2))
        codeR_v0v1_eq = axRefl codeR_v0v1_old

        pair_H2R_eq :
          Deriv (eqF (ap2 Pair codeH2v0v1_old codeR_v0v1_old)
                      (ap2 Pair (axN10_codeH2_v0v1 h2) (axN10_codeR_v0v1 g h1 h2)))
        pair_H2R_eq =
          ruleTrans (congL Pair codeR_v0v1_old codeH2v0v1_eq)
                    (congR Pair (axN10_codeH2_v0v1 h2) codeR_v0v1_eq)

        pair_H1_eq :
          Deriv (eqF (ap2 Pair H1_old (ap2 Pair codeH2v0v1_old codeR_v0v1_old))
                      (ap2 Pair (codeFun2 h1)
                        (ap2 Pair (axN10_codeH2_v0v1 h2) (axN10_codeR_v0v1 g h1 h2))))
        pair_H1_eq =
          ruleTrans (congL Pair (ap2 Pair codeH2v0v1_old codeR_v0v1_old) Fst_SS_eq)
                    (congR Pair (codeFun2 h1) pair_H2R_eq)

        codeRHS_eq :
          Deriv (eqF
            (ap2 Pair (natCode tag_ap2)
              (ap2 Pair H1_old (ap2 Pair codeH2v0v1_old codeR_v0v1_old)))
            (axN10_codeRHS g h1 h2))
        codeRHS_eq = congR Pair (natCode tag_ap2) pair_H1_eq

        outer_pair_eq :
          Deriv (eqF
            (ap2 Pair (axN10_codeLHS g h1 h2)
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair H1_old (ap2 Pair codeH2v0v1_old codeR_v0v1_old))))
            (ap2 Pair (axN10_codeLHS g h1 h2) (axN10_codeRHS g h1 h2)))
        outer_pair_eq = congR Pair (axN10_codeLHS g h1 h2) codeRHS_eq
    in congR Pair (natCode tag_eq) outer_pair_eq

------------------------------------------------------------------------
-- Apply sbf2 spec2 to axN10_concrete.
--
-- spec2 = pi (pi (natCode 0) (num X)) (pi (natCode 1) (num Y)) ;
-- substitutes v0 := num X , v1 := num Y .

private
  -- Target output sub-Terms.

  s_enc_num_Y : Term -> Term
  s_enc_num_Y Y =
    ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num Y))

  encCodeLHS : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
  encCodeLHS g h1 h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2))
        (ap2 Pair (ap1 num X) (s_enc_num_Y Y)))

  encH2_at : Fun2 -> Term -> Term -> Term
  encH2_at h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 h2) (ap2 Pair (ap1 num X) (ap1 num Y)))

  encR_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
  encR_at g h1 h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) (ap1 num Y)))

  encCodeRHS : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
  encCodeRHS g h1 h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 h1)
        (ap2 Pair (encH2_at h2 X Y) (encR_at g h1 h2 X Y)))

encodedAxRStep_Term : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
encodedAxRStep_Term g h1 h2 X Y =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (encCodeLHS g h1 h2 X Y) (encCodeRHS g h1 h2 X Y))

------------------------------------------------------------------------
-- sbf2-cascade lemma.
--
-- We compute sbt2 sp on each sub-Term of axN10_concrete piece by piece,
-- using sbContract2's closures.

private
  -- The shared sbt2-of-var-positions lemmas.
  zero_neq_one : Eq (natEq zero (suc zero)) false
  zero_neq_one = refl

  -- sbt2 sp cV0 = num X  (via sbt2_at_var_match_one with k1 = 0 , k2 = 1).
  e_cV0_at : (X Y : Term) ->
             Deriv (eqF (ap2 sbt2 (spec2_at X Y) cV0) (ap1 num X))
  e_cV0_at X Y = sbt2_at_var_match_one zero (suc zero) (ap1 num X) (ap1 num Y)

  -- sbt2 sp cV1 = num Y  (via sbt2_at_var_match_two with k1 = 0 , k2 = 1).
  e_cV1_at : (X Y : Term) ->
             Deriv (eqF (ap2 sbt2 (spec2_at X Y) cV1) (ap1 num Y))
  e_cV1_at X Y =
    sbt2_at_var_match_two zero (suc zero) (ap1 num X) (ap1 num Y) zero_neq_one

  -- sbt2 sp codeS_V1 :
  --   codeS_V1 = pi tag_ap1 (pi (codeFun1 s) cV1).
  --   sbt2_at_ap1 with k1=0, k2=1, S1=num X, S2=num Y, f=s, ct=cV1 gives
  --     pi tag_ap1 (pi (codeFun1 s) (sbt2 sp cV1))
  --   = pi tag_ap1 (pi (codeFun1 s) (num Y))
  --   = s_enc_num_Y Y .
  e_codeS_V1_at : (X Y : Term) ->
                  Deriv (eqF (ap2 sbt2 (spec2_at X Y) codeS_V1) (s_enc_num_Y Y))
  e_codeS_V1_at X Y =
    let sp = spec2_at X Y
        step1 : Deriv (eqF (ap2 sbt2 sp codeS_V1)
                            (ap2 Pair (natCode tag_ap1)
                              (ap2 Pair (codeFun1 s) (ap2 sbt2 sp cV1))))
        step1 = sbt2_at_ap1 zero (suc zero) (ap1 num X) (ap1 num Y) s cV1
        step2 : Deriv (eqF (ap2 Pair (codeFun1 s) (ap2 sbt2 sp cV1))
                            (ap2 Pair (codeFun1 s) (ap1 num Y)))
        step2 = congR Pair (codeFun1 s) (e_cV1_at X Y)
    in ruleTrans step1 (congR Pair (natCode tag_ap1) step2)

  -- sbt2 sp axN10_codeLHS :
  --   axN10_codeLHS = pi tag_ap2 (pi (codeFun2 (R g h1 h2)) (pi cV0 codeS_V1)).
  --   sbt2_at_ap2 with g_F2 = (R g h1 h2), ca = cV0, cb = codeS_V1.
  e_codeLHS_at :
    (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
    Deriv (eqF (ap2 sbt2 (spec2_at X Y) (axN10_codeLHS g h1 h2))
                (encCodeLHS g h1 h2 X Y))
  e_codeLHS_at g h1 h2 X Y =
    let sp = spec2_at X Y
        step1 :
          Deriv (eqF (ap2 sbt2 sp (axN10_codeLHS g h1 h2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 (R g h1 h2))
                          (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp codeS_V1)))))
        step1 = sbt2_at_ap2 zero (suc zero) (ap1 num X) (ap1 num Y)
                  (R g h1 h2) cV0 codeS_V1
        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp codeS_V1))
                      (ap2 Pair (ap1 num X) (s_enc_num_Y Y)))
        inner =
          ruleTrans (congL Pair (ap2 sbt2 sp codeS_V1) (e_cV0_at X Y))
                    (congR Pair (ap1 num X) (e_codeS_V1_at X Y))
    in ruleTrans step1
         (congR Pair (natCode tag_ap2)
           (congR Pair (codeFun2 (R g h1 h2)) inner))

  -- sbt2 sp axN10_codeH2_v0v1 :
  --   axN10_codeH2_v0v1 h2 = pi tag_ap2 (pi (codeFun2 h2) (pi cV0 cV1)).
  --   sbt2_at_ap2 with g_F2 = h2, ca = cV0, cb = cV1.
  e_codeH2_at :
    (h2 : Fun2) (X Y : Term) ->
    Deriv (eqF (ap2 sbt2 (spec2_at X Y) (axN10_codeH2_v0v1 h2))
                (encH2_at h2 X Y))
  e_codeH2_at h2 X Y =
    let sp = spec2_at X Y
        step1 :
          Deriv (eqF (ap2 sbt2 sp (axN10_codeH2_v0v1 h2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 h2)
                          (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1)))))
        step1 = sbt2_at_ap2 zero (suc zero) (ap1 num X) (ap1 num Y) h2 cV0 cV1
        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1))
                      (ap2 Pair (ap1 num X) (ap1 num Y)))
        inner =
          ruleTrans (congL Pair (ap2 sbt2 sp cV1) (e_cV0_at X Y))
                    (congR Pair (ap1 num X) (e_cV1_at X Y))
    in ruleTrans step1
         (congR Pair (natCode tag_ap2)
           (congR Pair (codeFun2 h2) inner))

  -- sbt2 sp axN10_codeR_v0v1 :
  --   sbt2_at_ap2 with g_F2 = (R g h1 h2), ca = cV0, cb = cV1.
  e_codeR_at :
    (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
    Deriv (eqF (ap2 sbt2 (spec2_at X Y) (axN10_codeR_v0v1 g h1 h2))
                (encR_at g h1 h2 X Y))
  e_codeR_at g h1 h2 X Y =
    let sp = spec2_at X Y
        step1 :
          Deriv (eqF (ap2 sbt2 sp (axN10_codeR_v0v1 g h1 h2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 (R g h1 h2))
                          (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1)))))
        step1 = sbt2_at_ap2 zero (suc zero) (ap1 num X) (ap1 num Y)
                  (R g h1 h2) cV0 cV1
        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1))
                      (ap2 Pair (ap1 num X) (ap1 num Y)))
        inner =
          ruleTrans (congL Pair (ap2 sbt2 sp cV1) (e_cV0_at X Y))
                    (congR Pair (ap1 num X) (e_cV1_at X Y))
    in ruleTrans step1
         (congR Pair (natCode tag_ap2)
           (congR Pair (codeFun2 (R g h1 h2)) inner))

  -- sbt2 sp axN10_codeRHS :
  --   axN10_codeRHS = pi tag_ap2 (pi (codeFun2 h1) (pi codeH2_v0v1 codeR_v0v1)).
  --   sbt2_at_ap2 with g_F2 = h1, ca = codeH2_v0v1, cb = codeR_v0v1.
  e_codeRHS_at :
    (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
    Deriv (eqF (ap2 sbt2 (spec2_at X Y) (axN10_codeRHS g h1 h2))
                (encCodeRHS g h1 h2 X Y))
  e_codeRHS_at g h1 h2 X Y =
    let sp = spec2_at X Y
        step1 :
          Deriv (eqF (ap2 sbt2 sp (axN10_codeRHS g h1 h2))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 h1)
                          (ap2 Pair
                            (ap2 sbt2 sp (axN10_codeH2_v0v1 h2))
                            (ap2 sbt2 sp (axN10_codeR_v0v1 g h1 h2))))))
        step1 = sbt2_at_ap2 zero (suc zero) (ap1 num X) (ap1 num Y) h1
                  (axN10_codeH2_v0v1 h2) (axN10_codeR_v0v1 g h1 h2)
        inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt2 sp (axN10_codeH2_v0v1 h2))
                      (ap2 sbt2 sp (axN10_codeR_v0v1 g h1 h2)))
            (ap2 Pair (encH2_at h2 X Y) (encR_at g h1 h2 X Y)))
        inner =
          ruleTrans (congL Pair (ap2 sbt2 sp (axN10_codeR_v0v1 g h1 h2))
                                (e_codeH2_at h2 X Y))
                    (congR Pair (encH2_at h2 X Y) (e_codeR_at g h1 h2 X Y))
    in ruleTrans step1
         (congR Pair (natCode tag_ap2)
           (congR Pair (codeFun2 h1) inner))

  sbf2_step :
    (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
    Deriv (eqF (ap2 sbf2 (spec2_at X Y) (axN10_concrete g h1 h2))
                (encodedAxRStep_Term g h1 h2 X Y))
  sbf2_step g h1 h2 X Y =
    let sp = spec2_at X Y
        e_atomic :
          Deriv (eqF (ap2 sbf2 sp (axN10_concrete g h1 h2))
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt2 sp (axN10_codeLHS g h1 h2))
                          (ap2 sbt2 sp (axN10_codeRHS g h1 h2)))))
        e_atomic =
          sbf2_at_atomic zero (suc zero) (ap1 num X) (ap1 num Y)
            (axN10_codeLHS g h1 h2) (axN10_codeRHS g h1 h2)

        e_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt2 sp (axN10_codeLHS g h1 h2))
                      (ap2 sbt2 sp (axN10_codeRHS g h1 h2)))
            (ap2 Pair (encCodeLHS g h1 h2 X Y) (encCodeRHS g h1 h2 X Y)))
        e_inner =
          ruleTrans (congL Pair (ap2 sbt2 sp (axN10_codeRHS g h1 h2))
                                (e_codeLHS_at g h1 h2 X Y))
                    (congR Pair (encCodeLHS g h1 h2 X Y) (e_codeRHS_at g h1 h2 X Y))

        e_outer :
          Deriv (eqF
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt2 sp (axN10_codeLHS g h1 h2))
                        (ap2 sbt2 sp (axN10_codeRHS g h1 h2))))
            (encodedAxRStep_Term g h1 h2 X Y))
        e_outer = congR Pair (natCode tag_eq) e_inner
    in ruleTrans e_atomic e_outer

------------------------------------------------------------------------
-- Main theorem.

encodedAxRStep :
  (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
  Deriv (eqF (ap1 thmT (Df_axRStep g h1 h2 X Y))
              (encodedAxRStep_Term g h1 h2 X Y))
encodedAxRStep g h1 h2 X Y =
  let
    sp : Term
    sp = spec2_at X Y

    extra : Term
    extra = codeFun2 (R g h1 h2)

    pa_const_term : Term
    pa_const_term = packAx10_codeR_Term g h1 h2

    -- (a) thmT (Df_axRStep g h1 h2 X Y) =Deriv= sbf2 sp (thmT pa_const_term).
    e_at_sb2 :
      Deriv (eqF (ap1 thmT (Df_axRStep g h1 h2 X Y))
                  (ap2 sbf2 sp (ap1 thmT pa_const_term)))
    e_at_sb2 = thmT_at_sb2 sp pa_const_term

    -- (b) thmT pa_const_term =Deriv= outputRHS_at extra.
    e_axN10 :
      Deriv (eqF (ap1 thmT pa_const_term) (outputRHS_at extra))
    e_axN10 = thmT_at_axN10 extra

    e_lift_axN10 :
      Deriv (eqF (ap2 sbf2 sp (ap1 thmT pa_const_term))
                  (ap2 sbf2 sp (outputRHS_at extra)))
    e_lift_axN10 = congR sbf2 sp e_axN10

    -- (c) outputRHS_at extra =Deriv= axN10_concrete g h1 h2.
    e_bridge :
      Deriv (eqF (outputRHS_at extra) (axN10_concrete g h1 h2))
    e_bridge = outputRHS_bridge g h1 h2

    e_lift_bridge :
      Deriv (eqF (ap2 sbf2 sp (outputRHS_at extra))
                  (ap2 sbf2 sp (axN10_concrete g h1 h2)))
    e_lift_bridge = congR sbf2 sp e_bridge

    -- (d) sbf2 sp axN10_concrete =Deriv= encodedAxRStep_Term g h1 h2 X Y.
    e_sbf2 :
      Deriv (eqF (ap2 sbf2 sp (axN10_concrete g h1 h2))
                  (encodedAxRStep_Term g h1 h2 X Y))
    e_sbf2 = sbf2_step g h1 h2 X Y

  in ruleTrans e_at_sb2
       (ruleTrans e_lift_axN10
         (ruleTrans e_lift_bridge e_sbf2))
