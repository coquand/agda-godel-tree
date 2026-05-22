{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqCong1 -- encoded  ax_eqCong1  instance via single
-- 2-variable simultaneous sb-wrap on axN5.
--
-- Goal (universal in f : Fun1, A B : Term ; no Closed) :
--
--   Df_axEqCong1 : Fun1 -> Term -> Term -> Term
--   encodedAxEqCong1 :
--     (f : Fun1) (A B : Term) ->
--     Deriv (eqF (ap1 thmT (Df_axEqCong1 f A B))
--                 (encodedAxEqCong1_Term f A B))
--
-- where  encodedAxEqCong1_Term f A B  is the encoded form of the formula
--   "(A = B) > (f A = f B)" :
--
--   Pair tag_imp
--     (Pair (Pair tag_eq (Pair A B))
--           (Pair tag_eq
--             (Pair (Pair tag_ap1 (Pair (codeFun1 f) A))
--                   (Pair tag_ap1 (Pair (codeFun1 f) B)))))
--
-- Construction.
--
--   Df_axEqCong1 f A B = encode_sb2 0 A 1 B (packAx 5 (codeFun1 f)) :
--     Pair tag_sb2
--       (Pair (Pair (Pair (natCode 0) A) (Pair (natCode 1) B))
--             (Pair (natCode tag_ax)
--                   (Pair (natCode 5) (codeFun1 f))))
--
-- thmT walks the wrap :
--   thmT (Df_axEqCong1 f A B)
--     = sbf2 spec2 (thmT (packAx 5 (codeFun1 f)))            [thmT_at_sb2]
--     = sbf2 spec2 (outputRHS5 (codeFun1 f))                 [thmT_at_axN5]
--     = encodedAxEqCong1_Term f A B                          [sbf2 cascade]
--
-- A and B enter as leaves via the 2-var sb-wrap ; sbt2 walks the schema
-- but treats  codeFun1 f  opaquely (via sbt2_at_ap1).

module BRA4.Thm12.EncodedAxEqCong1 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 )
open import BRA4.SbContract2
open import BRA4.SbT2              using ( sbt2 )
open import BRA4.SbF2              using ( sbf2 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb2         using ( thmT_at_sb2 )
open import BRA4.ThmTAtAx5         using ( thmT_at_axN5 )

open SbContract2 sbContract2

------------------------------------------------------------------------
-- Constants and helpers.

private
  N5 : Nat
  N5 = suc (suc (suc (suc (suc zero))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cEq01 : Term
  cEq01 = ap2 Pair (natCode tag_eq) (ap2 Pair cV0 cV1)

  cAp1_f_V_at : Term -> Term -> Term
  cAp1_f_V_at fT vT = ap2 Pair (natCode tag_ap1) (ap2 Pair fT vT)

  -- outputRHS5 fT : the asymmetric encoding of axN5's schema with
  -- functor-encoding fT plugged in (mirrors ThmTAtAx5.outputRHS).
  outputRHS5 : Term -> Term
  outputRHS5 fT =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair cEq01
        (ap2 Pair (natCode tag_eq)
          (ap2 Pair (cAp1_f_V_at fT cV0) (cAp1_f_V_at fT cV1))))

  -- The packed axiom Term  packAx 5 (codeFun1 f) .
  packAx5_codeF1 : Fun1 -> Term
  packAx5_codeF1 f =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N5) (codeFun1 f))

  -- 2-variable spec :  Pair (Pair (natCode 0) A) (Pair (natCode 1) B) .
  spec2_AB : Term -> Term -> Term
  spec2_AB A B =
    ap2 Pair (ap2 Pair (natCode zero) A) (ap2 Pair (natCode (suc zero)) B)

------------------------------------------------------------------------
-- Df_axEqCong1 : Fun1 -> Term -> Term -> Term.

Df_axEqCong1 : Fun1 -> Term -> Term -> Term
Df_axEqCong1 f A B =
  ap2 Pair (natCode tag_sb2)
    (ap2 Pair (spec2_AB A B) (packAx5_codeF1 f))

------------------------------------------------------------------------
-- The target encoded formula.

encodedAxEqCong1_Term : Fun1 -> Term -> Term -> Term
encodedAxEqCong1_Term f A B =
  ap2 Pair (natCode tag_imp)
    (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair A B))
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair
                  (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) A))
                  (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) B)))))

------------------------------------------------------------------------
-- sbf2-cascade lemma : sbf2 spec2_AB (outputRHS5 (codeFun1 f))
--                       = encodedAxEqCong1_Term f A B .

private
  sbf2_step :
    (f : Fun1) (A B : Term) ->
    Deriv (eqF (ap2 sbf2 (spec2_AB A B) (outputRHS5 (codeFun1 f)))
                (encodedAxEqCong1_Term f A B))
  sbf2_step f A B =
    let sp : Term
        sp = spec2_AB A B

        -- sbt2_at_var_match_one at k1=0, k2=1, S1=A, S2=B :
        --   sbt2 sp cV0 = A.
        e_cV0 : Deriv (eqF (ap2 sbt2 sp cV0) A)
        e_cV0 = sbt2_at_var_match_one zero (suc zero) A B

        -- sbt2_at_var_match_two at k1=0, k2=1 needs Eq (natEq 0 1) false = refl.
        e_cV1 : Deriv (eqF (ap2 sbt2 sp cV1) B)
        e_cV1 = sbt2_at_var_match_two zero (suc zero) A B refl

        -- (a) sbf2 sp cEq01 = Pair tag_eq (Pair A B).
        --     sbf2_at_atomic at k1=0, k2=1, S1=A, S2=B, ca=cV0, cb=cV1.
        e_eq01_atomic :
          Deriv (eqF (ap2 sbf2 sp cEq01)
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1))))
        e_eq01_atomic = sbf2_at_atomic zero (suc zero) A B cV0 cV1

        e_eq01_inner :
          Deriv (eqF (ap2 Pair (ap2 sbt2 sp cV0) (ap2 sbt2 sp cV1))
                      (ap2 Pair A B))
        e_eq01_inner =
          ruleTrans (congL Pair (ap2 sbt2 sp cV1) e_cV0)
                    (congR Pair A e_cV1)

        e_eq01 :
          Deriv (eqF (ap2 sbf2 sp cEq01)
                      (ap2 Pair (natCode tag_eq) (ap2 Pair A B)))
        e_eq01 = ruleTrans e_eq01_atomic
                   (congR Pair (natCode tag_eq) e_eq01_inner)

        -- (b) sbt2 sp (cAp1_f_V_at (codeFun1 f) cV0) =
        --       Pair tag_ap1 (Pair (codeFun1 f) A) .
        --     sbt2_at_ap1 at k1=0, k2=1, S1=A, S2=B, f=f, ct=cV0.
        e_lhs_step :
          Deriv (eqF (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV0))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (ap2 sbt2 sp cV0))))
        e_lhs_step = sbt2_at_ap1 zero (suc zero) A B f cV0

        e_lhs :
          Deriv (eqF (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV0))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) A)))
        e_lhs = ruleTrans e_lhs_step
                  (congR Pair (natCode tag_ap1)
                    (congR Pair (codeFun1 f) e_cV0))

        -- sbt2 sp (cAp1_f_V_at (codeFun1 f) cV1) =
        --       Pair tag_ap1 (Pair (codeFun1 f) B) .
        e_rhs_step :
          Deriv (eqF (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV1))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (ap2 sbt2 sp cV1))))
        e_rhs_step = sbt2_at_ap1 zero (suc zero) A B f cV1

        e_rhs :
          Deriv (eqF (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV1))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) B)))
        e_rhs = ruleTrans e_rhs_step
                  (congR Pair (natCode tag_ap1)
                    (congR Pair (codeFun1 f) e_cV1))

        -- (c) sbf2 sp (Pair tag_eq (Pair (cAp1_f_V_at (codeFun1 f) cV0)
        --                                (cAp1_f_V_at (codeFun1 f) cV1)))
        --     = Pair tag_eq (Pair (Pair tag_ap1 (Pair (codeFun1 f) A))
        --                          (Pair tag_ap1 (Pair (codeFun1 f) B))) .
        e_eq_consAtomic :
          Deriv (eqF
            (ap2 sbf2 sp
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair (cAp1_f_V_at (codeFun1 f) cV0)
                          (cAp1_f_V_at (codeFun1 f) cV1))))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV0))
                        (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV1)))))
        e_eq_consAtomic =
          sbf2_at_atomic zero (suc zero) A B
            (cAp1_f_V_at (codeFun1 f) cV0) (cAp1_f_V_at (codeFun1 f) cV1)

        e_eq_consInner :
          Deriv (eqF
            (ap2 Pair (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV0))
                      (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV1)))
            (ap2 Pair
              (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) A))
              (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) B))))
        e_eq_consInner =
          ruleTrans (congL Pair (ap2 sbt2 sp (cAp1_f_V_at (codeFun1 f) cV1)) e_lhs)
                    (congR Pair
                      (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) A))
                      e_rhs)

        e_eq_cons :
          Deriv (eqF
            (ap2 sbf2 sp
              (ap2 Pair (natCode tag_eq)
                (ap2 Pair (cAp1_f_V_at (codeFun1 f) cV0)
                          (cAp1_f_V_at (codeFun1 f) cV1))))
            (ap2 Pair (natCode tag_eq)
              (ap2 Pair
                (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) A))
                (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) B)))))
        e_eq_cons =
          ruleTrans e_eq_consAtomic
            (congR Pair (natCode tag_eq) e_eq_consInner)

        -- (d) The full outer  sbf2_at_imp : ant = cEq01 , cons = the
        -- pi tag_eq (...) term.
        ant : Term
        ant = cEq01

        cons : Term
        cons =
          ap2 Pair (natCode tag_eq)
            (ap2 Pair (cAp1_f_V_at (codeFun1 f) cV0)
                      (cAp1_f_V_at (codeFun1 f) cV1))

        e_imp :
          Deriv (eqF (ap2 sbf2 sp (outputRHS5 (codeFun1 f)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair (ap2 sbf2 sp ant) (ap2 sbf2 sp cons))))
        e_imp = sbf2_at_imp zero (suc zero) A B ant cons

        e_imp_inner :
          Deriv (eqF
            (ap2 Pair (ap2 sbf2 sp ant) (ap2 sbf2 sp cons))
            (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair A B))
                       (ap2 Pair (natCode tag_eq)
                         (ap2 Pair
                           (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) A))
                           (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) B))))))
        e_imp_inner =
          ruleTrans (congL Pair (ap2 sbf2 sp cons) e_eq01)
                    (congR Pair (ap2 Pair (natCode tag_eq) (ap2 Pair A B)) e_eq_cons)

    in ruleTrans e_imp (congR Pair (natCode tag_imp) e_imp_inner)

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqCong1 :
  (f : Fun1) (A B : Term) ->
  Deriv (eqF (ap1 thmT (Df_axEqCong1 f A B))
              (encodedAxEqCong1_Term f A B))
encodedAxEqCong1 f A B =
  let sp : Term
      sp = spec2_AB A B

      pa : Term
      pa = packAx5_codeF1 f

      -- (a) thmT (Df_axEqCong1 f A B) = sbf2 sp (thmT pa)  via thmT_at_sb2.
      e_at_sb2 :
        Deriv (eqF (ap1 thmT (Df_axEqCong1 f A B))
                    (ap2 sbf2 sp (ap1 thmT pa)))
      e_at_sb2 = thmT_at_sb2 sp pa

      -- (b) thmT pa = outputRHS5 (codeFun1 f)  via thmT_at_axN5.
      e_axN5 :
        Deriv (eqF (ap1 thmT pa) (outputRHS5 (codeFun1 f)))
      e_axN5 = thmT_at_axN5 (codeFun1 f)

      e_lift_axN5 :
        Deriv (eqF (ap2 sbf2 sp (ap1 thmT pa))
                    (ap2 sbf2 sp (outputRHS5 (codeFun1 f))))
      e_lift_axN5 = congR sbf2 sp e_axN5

      -- (c) sbf2 sp (outputRHS5 (codeFun1 f)) = encodedAxEqCong1_Term f A B.
      e_sbf2 :
        Deriv (eqF (ap2 sbf2 sp (outputRHS5 (codeFun1 f)))
                    (encodedAxEqCong1_Term f A B))
      e_sbf2 = sbf2_step f A B

  in ruleTrans e_at_sb2
       (ruleTrans e_lift_axN5 e_sbf2)
