{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTCompleteAxFunctor -- completeness for the functor-bearing
-- axioms ax_C , ax_R_base , ax_R_step .
--
-- These axioms package functor data in  extra  =  codeFun1/2 (...)  ;
-- the closure's outputRHS uses  Fst/Snd  projections of  extra  to
-- access the sub-functors (g , h1 , h2).  We discharge the projections
-- via axFst/axSnd to recover the SCHEMA codeFormula, then apply the
-- standard sb-wrap chain.
--
-- ax_C g h1 h2 t       : single Term arg t at var 0.  No Closed needed.
-- ax_R_base g h1 h2 x  : single Term arg x at var 0.  No Closed needed.
-- ax_R_step g h1 h2 x n: two Term args x@0, n@1.  Closed x needed.

module BRA4.ThmTCompleteAxFunctor where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Encode
open import BRA4.ThmT      using ( thmT )
open import BRA4.SbF       using ( sbf )
open import BRA4.SbT       using ( sbt )
open import BRA4.SbfAtClosures using ( sbContract )
open import BRA4.SbDerived using ( module Derive )

open import BRA4.ThmTAtSb  using ( thmT_at_sb )
open import BRA4.ThmTAtAx8 using ( thmT_at_axN8 )
open import BRA4.ThmTAtAx9 using ( thmT_at_axN9 )
open import BRA4.ThmTAtAx10 using ( thmT_at_axN10 )

open import BRA3.Church      using ( pi )
open import BRA3.PairAlgebra using ( axFst ; axSnd )
open import BRA3.Dispatch    using ( closedAt )
open import BRA3.RuleInst2   using
  ( NatLe ; le-zero ; le-suc ; le-trans
  ; maxN ; maxN-le-left ; maxN-le-right
  ; maxVarT ; maxVarF
  ; natEq-lt-false ; simSubstF ; three_step_F )

open Derive sbt sbf sbContract

------------------------------------------------------------------------
-- step_sb_wrap (same as in ThmTCompleteAxClosed but local to this file).

private
  step_sb_wrap :
    (k : Nat) (t : Term)
    (inputCode : Term) (schemaCarrier : Formula)
    (inner_eq : Deriv (eqF (ap1 thmT inputCode) (codeFormula schemaCarrier))) ->
    Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb)
                                  (ap2 pi (ap2 pi (natCode k) (codeTerm t)) inputCode)))
                (codeFormula (substF k t schemaCarrier)))
  step_sb_wrap k t inputCode schemaCarrier inner_eq =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)
        step_sb :
          Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb) (ap2 pi spec inputCode)))
                      (ap2 sbf spec (ap1 thmT inputCode)))
        step_sb = thmT_at_sb spec inputCode
        step_lift = congR sbf spec inner_eq
        step_codeF = sbfEq_codeFormula k t schemaCarrier
    in ruleTrans step_sb (ruleTrans step_lift step_codeF)

------------------------------------------------------------------------
-- ax_C g h1 h2 t  :  P = atomic (eqn (ap1 (C g h1 h2) t) (ap2 g (ap1 h1 t) (ap1 h2 t))) .
-- Schema  C g h1 h2 (var 0) = g (h1 (var 0)) (h2 (var 0)) .
-- Output of thmT_at_axN8 (codeFun1 (C g h1 h2)) has Fst/Snd projections on extra ;
-- bridge to codeFormula SCHEMA via axFst/axSnd , then sb-wrap with t at var 0.

thmT_complete_ax_C :
  (g : Fun2) (h1 h2 : Fun1) (t : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_C g h1 h2 t)))
              (codeFormula (atomic (eqn (ap1 (C g h1 h2) t)
                                        (ap2 g (ap1 h1 t) (ap1 h2 t))))))
thmT_complete_ax_C g h1 h2 t =
  let cG : Term
      cG = codeFun2 g
      cH1 : Term
      cH1 = codeFun1 h1
      cH2 : Term
      cH2 = codeFun1 h2
      extra : Term
      extra = codeFun1 (C g h1 h2)

      SCHEMA : Formula
      SCHEMA = atomic (eqn (ap1 (C g h1 h2) (var zero))
                            (ap2 g (ap1 h1 (var zero)) (ap1 h2 (var zero))))
      packBody : Term
      packBody = ap2 pi (natCode tag_ax)
                   (ap2 pi (natCode (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           extra)

      -- The thmT_at_axN8 output (parametric on Fst/Snd of extra).
      raw : Deriv (eqF (ap1 thmT packBody)
                        (ap2 pi (natCode tag_eq)
                          (ap2 pi
                            (ap2 pi (natCode tag_ap1)
                              (ap2 pi extra (ap2 pi (natCode tag_var) (natCode zero))))
                            (ap2 pi (natCode tag_ap2)
                              (ap2 pi (ap1 Fst (ap1 Snd extra))
                                (ap2 pi
                                  (ap2 pi (natCode tag_ap1)
                                    (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra)))
                                             (ap2 pi (natCode tag_var) (natCode zero))))
                                  (ap2 pi (natCode tag_ap1)
                                    (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                             (ap2 pi (natCode tag_var) (natCode zero))))))))))
      raw = thmT_at_axN8 extra

      -- Fst/Snd reductions on extra = pi tag_C (pi cG (pi cH1 cH2)).
      eq_snd : Deriv (eqF (ap1 Snd extra) (ap2 Pair cG (ap2 Pair cH1 cH2)))
      eq_snd = axSnd (natCode tag_C) (ap2 Pair cG (ap2 Pair cH1 cH2))

      eq_G : Deriv (eqF (ap1 Fst (ap1 Snd extra)) cG)
      eq_G = ruleTrans (cong1 Fst eq_snd) (axFst cG (ap2 Pair cH1 cH2))

      eq_snd_snd : Deriv (eqF (ap1 Snd (ap1 Snd extra)) (ap2 Pair cH1 cH2))
      eq_snd_snd = ruleTrans (cong1 Snd eq_snd) (axSnd cG (ap2 Pair cH1 cH2))

      eq_H1 : Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd extra))) cH1)
      eq_H1 = ruleTrans (cong1 Fst eq_snd_snd) (axFst cH1 cH2)

      eq_H2 : Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd extra))) cH2)
      eq_H2 = ruleTrans (cong1 Snd eq_snd_snd) (axSnd cH1 cH2)

      cV0 : Term
      cV0 = ap2 pi (natCode tag_var) (natCode zero)

      -- Replace H1 with cH1 in pi tag_ap1 (pi H1 cV0).
      eq_apH1 : Deriv (eqF (ap2 pi (natCode tag_ap1)
                              (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                            (ap2 pi (natCode tag_ap1) (ap2 pi cH1 cV0)))
      eq_apH1 = congR pi (natCode tag_ap1) (congL pi cV0 eq_H1)

      eq_apH2 : Deriv (eqF (ap2 pi (natCode tag_ap1)
                              (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0))
                            (ap2 pi (natCode tag_ap1) (ap2 pi cH2 cV0)))
      eq_apH2 = congR pi (natCode tag_ap1) (congL pi cV0 eq_H2)

      codeH1V0 : Term
      codeH1V0 = ap2 pi (natCode tag_ap1) (ap2 pi cH1 cV0)
      codeH2V0 : Term
      codeH2V0 = ap2 pi (natCode tag_ap1) (ap2 pi cH2 cV0)

      -- pi codeH1V0 codeH2V0 .
      eq_pairH :
        Deriv (eqF
          (ap2 pi (ap2 pi (natCode tag_ap1)
                          (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                  (ap2 pi (natCode tag_ap1)
                          (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)))
          (ap2 pi codeH1V0 codeH2V0))
      eq_pairH =
        ruleTrans (congL pi (ap2 pi (natCode tag_ap1)
                                    (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)) eq_apH1)
                   (congR pi codeH1V0 eq_apH2)

      -- pi cG (pi codeH1V0 codeH2V0) .
      eq_GPair :
        Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd extra))
                     (ap2 pi (ap2 pi (natCode tag_ap1)
                                      (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                              (ap2 pi (natCode tag_ap1)
                                      (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0))))
                    (ap2 pi cG (ap2 pi codeH1V0 codeH2V0)))
      eq_GPair =
        ruleTrans (congL pi (ap2 pi (ap2 pi (natCode tag_ap1)
                                            (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                                    (ap2 pi (natCode tag_ap1)
                                            (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)))
                            eq_G)
                   (congR pi cG eq_pairH)

      -- pi tag_ap2 ( ... )  =  codeTerm RHS.
      eq_rhs :
        Deriv (eqF (ap2 pi (natCode tag_ap2)
                     (ap2 pi (ap1 Fst (ap1 Snd extra))
                       (ap2 pi (ap2 pi (natCode tag_ap1)
                                       (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                               (ap2 pi (natCode tag_ap1)
                                       (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)))))
                    (ap2 pi (natCode tag_ap2) (ap2 pi cG (ap2 pi codeH1V0 codeH2V0))))
      eq_rhs = congR pi (natCode tag_ap2) eq_GPair

      -- pi LHS RHS .  LHS untouched.
      LHS : Term
      LHS = ap2 pi (natCode tag_ap1) (ap2 pi extra cV0)

      RHS_target : Term
      RHS_target = ap2 pi (natCode tag_ap2) (ap2 pi cG (ap2 pi codeH1V0 codeH2V0))

      eq_pair :
        Deriv (eqF (ap2 pi LHS
                     (ap2 pi (natCode tag_ap2)
                       (ap2 pi (ap1 Fst (ap1 Snd extra))
                         (ap2 pi (ap2 pi (natCode tag_ap1)
                                         (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                                 (ap2 pi (natCode tag_ap1)
                                         (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0))))))
                    (ap2 pi LHS RHS_target))
      eq_pair = congR pi LHS eq_rhs

      -- Wrap with pi tag_eq.
      schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
      schema_eq = ruleTrans raw (congR pi (natCode tag_eq) eq_pair)

      -- Apply step_sb_wrap at k=0, t.
      result : Deriv (eqF (ap1 thmT (encode (ax_C g h1 h2 t)))
                           (codeFormula (substF zero t SCHEMA)))
      result = step_sb_wrap zero t packBody SCHEMA schema_eq
  in result

------------------------------------------------------------------------
-- ax_R_base g h1 h2 x  :  P = atomic (eqn (ap2 (R g h1 h2) x O) (ap1 g x)) .
-- Schema  R g h1 h2 (var 0, O) = g(var 0) .

thmT_complete_ax_R_base :
  (g : Fun1) (h1 h2 : Fun2) (x : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_R_base g h1 h2 x)))
              (codeFormula (atomic (eqn (ap2 (R g h1 h2) x O) (ap1 g x)))))
thmT_complete_ax_R_base g h1 h2 x =
  let cG : Term
      cG = codeFun1 g
      cH1 : Term
      cH1 = codeFun2 h1
      cH2 : Term
      cH2 = codeFun2 h2
      extra : Term
      extra = codeFun2 (R g h1 h2)

      SCHEMA : Formula
      SCHEMA = atomic (eqn (ap2 (R g h1 h2) (var zero) O) (ap1 g (var zero)))
      packBody : Term
      packBody = ap2 pi (natCode tag_ax)
                   (ap2 pi (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
                           extra)

      cV0 : Term
      cV0 = ap2 pi (natCode tag_var) (natCode zero)

      raw : Deriv (eqF (ap1 thmT packBody)
                        (ap2 pi (natCode tag_eq)
                          (ap2 pi
                            (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 O)))
                            (ap2 pi (natCode tag_ap1)
                              (ap2 pi (ap1 Fst (ap1 Snd extra)) cV0)))))
      raw = thmT_at_axN9 extra

      eq_snd : Deriv (eqF (ap1 Snd extra) (ap2 Pair cG (ap2 Pair cH1 cH2)))
      eq_snd = axSnd (natCode tag_R) (ap2 Pair cG (ap2 Pair cH1 cH2))
      eq_G : Deriv (eqF (ap1 Fst (ap1 Snd extra)) cG)
      eq_G = ruleTrans (cong1 Fst eq_snd) (axFst cG (ap2 Pair cH1 cH2))

      eq_apG :
        Deriv (eqF (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd extra)) cV0))
                    (ap2 pi (natCode tag_ap1) (ap2 pi cG cV0)))
      eq_apG = congR pi (natCode tag_ap1) (congL pi cV0 eq_G)

      LHS : Term
      LHS = ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 O))

      eq_pair :
        Deriv (eqF (ap2 pi LHS
                     (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd extra)) cV0)))
                    (ap2 pi LHS (ap2 pi (natCode tag_ap1) (ap2 pi cG cV0))))
      eq_pair = congR pi LHS eq_apG

      schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
      schema_eq = ruleTrans raw (congR pi (natCode tag_eq) eq_pair)
  in step_sb_wrap zero x packBody SCHEMA schema_eq

------------------------------------------------------------------------
-- ax_R_step g h1 h2 x n  :
-- P = atomic (eqn (ap2 (R g h1 h2) x (ap1 s n)) (ap2 h1 (ap2 h2 x n) (ap2 (R g h1 h2) x n))) .
-- Schema with var 0 = x , var 1 = n.  Closed x needed.

thmT_complete_ax_R_step :
  (g : Fun1) (h1 h2 : Fun2) (x n : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_R_step g h1 h2 x n)))
              (codeFormula (atomic (eqn (ap2 (R g h1 h2) x (ap1 s n))
                                        (ap2 h1 (ap2 h2 x n) (ap2 (R g h1 h2) x n))))))
thmT_complete_ax_R_step g h1 h2 x n =
  let cG : Term
      cG = codeFun1 g
      cH1 : Term
      cH1 = codeFun2 h1
      cH2 : Term
      cH2 = codeFun2 h2
      extra : Term
      extra = codeFun2 (R g h1 h2)

      SCHEMA : Formula
      SCHEMA = atomic (eqn (ap2 (R g h1 h2) (var zero) (ap1 s (var (suc zero))))
                            (ap2 h1 (ap2 h2 (var zero) (var (suc zero)))
                                    (ap2 (R g h1 h2) (var zero) (var (suc zero)))))
      packBody : Term
      packBody = ap2 pi (natCode tag_ax)
                   (ap2 pi (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
                           extra)

      cV0 : Term
      cV0 = ap2 pi (natCode tag_var) (natCode zero)
      cV1 : Term
      cV1 = ap2 pi (natCode tag_var) (natCode (suc zero))
      codeS_V1 : Term
      codeS_V1 = ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) cV1)

      raw : Deriv (eqF (ap1 thmT packBody)
                        (ap2 pi (natCode tag_eq)
                          (ap2 pi
                            (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 codeS_V1)))
                            (ap2 pi (natCode tag_ap2)
                              (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra)))
                                (ap2 pi
                                  (ap2 pi (natCode tag_ap2)
                                    (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                             (ap2 pi cV0 cV1)))
                                  (ap2 pi (natCode tag_ap2)
                                    (ap2 pi extra (ap2 pi cV0 cV1)))))))))
      raw = thmT_at_axN10 extra

      eq_snd : Deriv (eqF (ap1 Snd extra) (ap2 Pair cG (ap2 Pair cH1 cH2)))
      eq_snd = axSnd (natCode tag_R) (ap2 Pair cG (ap2 Pair cH1 cH2))
      eq_snd_snd : Deriv (eqF (ap1 Snd (ap1 Snd extra)) (ap2 Pair cH1 cH2))
      eq_snd_snd = ruleTrans (cong1 Snd eq_snd) (axSnd cG (ap2 Pair cH1 cH2))
      eq_H1 : Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd extra))) cH1)
      eq_H1 = ruleTrans (cong1 Fst eq_snd_snd) (axFst cH1 cH2)
      eq_H2 : Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd extra))) cH2)
      eq_H2 = ruleTrans (cong1 Snd eq_snd_snd) (axSnd cH1 cH2)

      cH2V0V1 : Term
      cH2V0V1 = ap2 pi (natCode tag_ap2) (ap2 pi cH2 (ap2 pi cV0 cV1))
      cRV0V1 : Term
      cRV0V1 = ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1))

      eq_apH2 : Deriv (eqF (ap2 pi (natCode tag_ap2)
                              (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                       (ap2 pi cV0 cV1)))
                            cH2V0V1)
      eq_apH2 = congR pi (natCode tag_ap2) (congL pi (ap2 pi cV0 cV1) eq_H2)

      -- pi cH2V0V1 cRV0V1 .
      eq_pairInner :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_ap2)
                                    (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                             (ap2 pi cV0 cV1)))
                            cRV0V1)
                    (ap2 pi cH2V0V1 cRV0V1))
      eq_pairInner = congL pi cRV0V1 eq_apH2

      -- pi cH1 (pi cH2V0V1 cRV0V1) .
      eq_H1Pair :
        Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra)))
                     (ap2 pi (ap2 pi (natCode tag_ap2)
                                      (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                               (ap2 pi cV0 cV1)))
                              cRV0V1))
                    (ap2 pi cH1 (ap2 pi cH2V0V1 cRV0V1)))
      eq_H1Pair =
        ruleTrans (congL pi (ap2 pi (ap2 pi (natCode tag_ap2)
                                             (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                                      (ap2 pi cV0 cV1)))
                                     cRV0V1) eq_H1)
                   (congR pi cH1 eq_pairInner)

      eq_RHS :
        Deriv (eqF (ap2 pi (natCode tag_ap2)
                     (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra)))
                       (ap2 pi (ap2 pi (natCode tag_ap2)
                                        (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                                 (ap2 pi cV0 cV1)))
                                cRV0V1)))
                    (ap2 pi (natCode tag_ap2) (ap2 pi cH1 (ap2 pi cH2V0V1 cRV0V1))))
      eq_RHS = congR pi (natCode tag_ap2) eq_H1Pair

      LHS : Term
      LHS = ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 codeS_V1))

      RHS_target : Term
      RHS_target = ap2 pi (natCode tag_ap2) (ap2 pi cH1 (ap2 pi cH2V0V1 cRV0V1))

      eq_pair :
        Deriv (eqF (ap2 pi LHS
                     (ap2 pi (natCode tag_ap2)
                       (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra)))
                         (ap2 pi (ap2 pi (natCode tag_ap2)
                                          (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra)))
                                                   (ap2 pi cV0 cV1)))
                                  cRV0V1))))
                    (ap2 pi LHS RHS_target))
      eq_pair = congR pi LHS eq_RHS

      schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
      schema_eq = ruleTrans raw (congR pi (natCode tag_eq) eq_pair)

      c : Nat
      c = maxN (suc (suc zero)) (maxVarT x)

      le_two_c : NatLe (suc (suc zero)) c
      le_two_c = maxN-le-left (suc (suc zero)) (maxVarT x)

      le_one_c : NatLe (suc zero) c
      le_one_c = le-trans (le-suc (le-zero (suc zero))) le_two_c

      le_x_c : NatLe (maxVarT x) c
      le_x_c = maxN-le-right (suc (suc zero)) (maxVarT x)

      cNeZero : Eq (natEq c zero) false
      cNeZero = natEq-lt-false c zero le_one_c

      cNeOne : Eq (natEq c (suc zero)) false
      cNeOne = natEq-lt-false c (suc zero) le_two_c

      k1Nek2 : Eq (natEq zero (suc zero)) false
      k1Nek2 = refl

      le_schema_c : NatLe (maxVarF SCHEMA) c
      le_schema_c = le_two_c

      step1_code : Term
      step1_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c))) packBody)
      step1_eq : Deriv (eqF (ap1 thmT step1_code)
                              (codeFormula (substF (suc zero) (var c) SCHEMA)))
      step1_eq = step_sb_wrap (suc zero) (var c) packBody SCHEMA schema_eq

      step2_code : Term
      step2_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode zero) (codeTerm x)) step1_code)
      step2_eq : Deriv (eqF (ap1 thmT step2_code)
                              (codeFormula (substF zero x (substF (suc zero) (var c) SCHEMA))))
      step2_eq = step_sb_wrap zero x step1_code
                   (substF (suc zero) (var c) SCHEMA) step1_eq

      step3_code : Term
      step3_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode c) (codeTerm n)) step2_code)
      step3_eq : Deriv (eqF (ap1 thmT step3_code)
                              (codeFormula (substF c n
                                              (substF zero x (substF (suc zero) (var c) SCHEMA)))))
      step3_eq = step_sb_wrap c n step2_code
                   (substF zero x (substF (suc zero) (var c) SCHEMA)) step2_eq

      bridge_eq :
        Eq (substF c n (substF zero x (substF (suc zero) (var c) SCHEMA)))
           (simSubstF zero x (suc zero) n SCHEMA)
      bridge_eq = three_step_F zero x (suc zero) n c
                    k1Nek2 cNeZero cNeOne le_x_c SCHEMA le_schema_c
  in eqSubst (\ F -> Deriv (eqF (ap1 thmT step3_code) (codeFormula F)))
              bridge_eq step3_eq
