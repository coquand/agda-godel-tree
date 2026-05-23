{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxRStep -- encoded  ax_R_step  instance via a NESTED
-- single-variable sb-wrap on axN10  (no sbt2/sbf2).
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
-- Construction.  Df_axRStep g h1 h2 X Y is the NESTED sb-wrap of
--  packAx 10 (codeFun2 (R g h1 h2))  with substituents
--  (var 0 := num X outermost, var 1 := num Y innermost) :
--
--   Df_axRStep g h1 h2 X Y =
--     Pair tag_sb (Pair (Pair (natCode 0) (num X))
--       (Pair tag_sb (Pair (Pair (natCode 1) (num Y))
--         (packAx 10 (codeFun2 (R g h1 h2))))))
--
-- thmT walks the wrap with  thmT_at_sb  twice :
--   thmT (Df_axRStep ...)
--     = sbf spec0 (sbf spec1 (thmT (packAx 10 ...)))   [thmT_at_sb x2]
--     = sbf spec0 (sbf spec1 (outputRHS_at extra))     [thmT_at_axN10]
--     = sbf spec0 (sbf spec1 (axN10_concrete))         [outputRHS_bridge]
--     = sbf spec0 (FormRStep ... cV0 (num Y))          [inner pass, var 1 := num Y]
--     = FormRStep ... (num X) (num Y)                  [outer pass, var 0 := num X]
--     = encodedAxRStep_Term g h1 h2 X Y .
--
-- The inner pass plants  num Y ; the outer pass re-scans it, discharged
-- by  sbt_num_inert .

module BRA4.Thm12.EncodedAxRStep where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.Num               using ( num )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.NumInert          using ( sbt_num_inert )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx10        using ( thmT_at_axN10 )

------------------------------------------------------------------------
-- Constants and helpers.

private
  N10 : Nat
  N10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  -- code(ap1 f t) = Pair tag_ap1 (Pair (codeFun1 f) t).
  cAp1f : Fun1 -> Term -> Term
  cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

  -- code(ap2 g a b) = Pair tag_ap2 (Pair (codeFun2 g) (Pair a b)).
  cAp2g : Fun2 -> Term -> Term -> Term
  cAp2g g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

  -- codeS_V1  =  code(ap1 s v1) = Pair tag_ap1 (Pair (natCode tag_s) cV1)
  --           =  cAp1f s cV1   (definitionally, codeFun1 s = natCode tag_s).
  codeS_V1 : Term
  codeS_V1 = ap2 Pair (natCode tag_ap1) (ap2 Pair (natCode tag_s) cV1)

  -- The inner constant Term  packAx 10 (codeFun2 (R g h1 h2)) .
  packAx10_codeR_Term : Fun1 -> Fun2 -> Fun2 -> Term
  packAx10_codeR_Term g h1 h2 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N10) (codeFun2 (R g h1 h2)))

  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

------------------------------------------------------------------------
-- The "concrete" schema form (with H1 -> codeFun2 h1 , H2 -> codeFun2 h2).

private
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
-- Df_axRStep : the nested sb-wrap.

private
  spec0_X : Term -> Term
  spec0_X X = spec0_at (ap1 num X)

  spec1_Y : Term -> Term
  spec1_Y Y = spec1_at (ap1 num Y)

Df_axRStep : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
Df_axRStep g h1 h2 X Y =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_X X)
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_Y Y) (packAx10_codeR_Term g h1 h2))))

------------------------------------------------------------------------
-- Output sub-Terms.

private
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
-- The encoded skeleton  FormRStep g h1 h2 p0 p1  (p0 substitutes cV0,
-- p1 substitutes cV1).  FormRStep ... cV0 cV1     = axN10_concrete and
--                       FormRStep ... (num X)(num Y) = encodedAxRStep_Term .

private
  FormRStep : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
  FormRStep g h1 h2 p0 p1 =
    ap2 Pair (natCode tag_eq)
      (ap2 Pair
        (cAp2g (R g h1 h2) p0 (cAp1f s p1))
        (cAp2g h1 (cAp2g h2 p0 p1) (cAp2g (R g h1 h2) p0 p1)))

  -- One pass of  sbf  over the FormRStep skeleton.
  onePassRStep :
    (g : Fun1) (h1 h2 : Fun2) (k : Nat) (S : Term) (p0 p1 p0' p1' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) p0) p0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) p1) p1') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormRStep g h1 h2 p0 p1))
                (FormRStep g h1 h2 p0' p1'))
  onePassRStep g h1 h2 k S p0 p1 p0' p1' e0 e1 =
    sbf_step_atomic k S
      (cAp2g (R g h1 h2) p0 (cAp1f s p1))
      (cAp2g h1 (cAp2g h2 p0 p1) (cAp2g (R g h1 h2) p0 p1))
      (cAp2g (R g h1 h2) p0' (cAp1f s p1'))
      (cAp2g h1 (cAp2g h2 p0' p1') (cAp2g (R g h1 h2) p0' p1'))
      (sbt_step_ap2 k S (R g h1 h2) p0 (cAp1f s p1) p0' (cAp1f s p1')
        e0
        (sbt_step_ap1 k S s p1 p1' e1))
      (sbt_step_ap2 k S h1
        (cAp2g h2 p0 p1) (cAp2g (R g h1 h2) p0 p1)
        (cAp2g h2 p0' p1') (cAp2g (R g h1 h2) p0' p1')
        (sbt_step_ap2 k S h2 p0 p1 p0' p1' e0 e1)
        (sbt_step_ap2 k S (R g h1 h2) p0 p1 p0' p1' e0 e1))

------------------------------------------------------------------------
-- Main theorem.

encodedAxRStep :
  (g : Fun1) (h1 h2 : Fun2) (X Y : Term) ->
  Deriv (eqF (ap1 thmT (Df_axRStep g h1 h2 X Y))
              (encodedAxRStep_Term g h1 h2 X Y))
encodedAxRStep g h1 h2 X Y =
  let
    spec0 : Term
    spec0 = spec0_X X

    spec1 : Term
    spec1 = spec1_Y Y

    extra : Term
    extra = codeFun2 (R g h1 h2)

    pa : Term
    pa = packAx10_codeR_Term g h1 h2

    innerCode : Term
    innerCode = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 pa)

    -- (a) thmT (Df) = sbf spec0 (thmT innerCode)   [thmT_at_sb].
    e1 : Deriv (eqF (ap1 thmT (Df_axRStep g h1 h2 X Y))
                     (ap2 sbf spec0 (ap1 thmT innerCode)))
    e1 = thmT_at_sb spec0 innerCode

    -- (b) thmT innerCode = sbf spec1 (thmT pa)      [thmT_at_sb].
    e2 : Deriv (eqF (ap1 thmT innerCode) (ap2 sbf spec1 (ap1 thmT pa)))
    e2 = thmT_at_sb spec1 pa

    -- (c) thmT pa = outputRHS_at extra              [thmT_at_axN10].
    e3 : Deriv (eqF (ap1 thmT pa) (outputRHS_at extra))
    e3 = thmT_at_axN10 extra

    -- (d) outputRHS_at extra = axN10_concrete (= FormRStep ... cV0 cV1).
    e4 : Deriv (eqF (outputRHS_at extra) (FormRStep g h1 h2 cV0 cV1))
    e4 = outputRHS_bridge g h1 h2

    -- inner pass (var 1 := num Y).
    innerPass :
      Deriv (eqF (ap2 sbf spec1 (FormRStep g h1 h2 cV0 cV1))
                  (FormRStep g h1 h2 cV0 (ap1 num Y)))
    innerPass =
      onePassRStep g h1 h2 (suc zero) (ap1 num Y) cV0 cV1 cV0 (ap1 num Y)
        (sbt_at_var_nomatch (suc zero) zero (ap1 num Y) refl)
        (sbt_at_var_match (suc zero) (ap1 num Y))

    -- outer pass (var 0 := num X).
    outerPass :
      Deriv (eqF (ap2 sbf spec0 (FormRStep g h1 h2 cV0 (ap1 num Y)))
                  (FormRStep g h1 h2 (ap1 num X) (ap1 num Y)))
    outerPass =
      onePassRStep g h1 h2 zero (ap1 num X) cV0 (ap1 num Y) (ap1 num X) (ap1 num Y)
        (sbt_at_var_match zero (ap1 num X))
        (sbt_num_inert zero (ap1 num X) Y)

  in ruleTrans e1
       (ruleTrans (congR sbf spec0 e2)
         (ruleTrans (congR sbf spec0
                       (congR sbf spec1 (ruleTrans e3 e4)))
           (ruleTrans (congR sbf spec0 innerPass)
                      outerPass)))
