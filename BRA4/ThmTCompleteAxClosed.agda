{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTCompleteAxClosed -- per-axiom completeness lemmas for
-- the axiom cases that require  Closed  witnesses on Term arguments
-- to bridge  substT k b a = a  in the substituted schema codeFormula :
--
--   ax_v a b               : Closed a .
--   ax_eqTrans x y z       : Closed x , Closed y .
--   ax_eqCong1 f a b       : Closed a .
--   ax_eqCongL g a b c     : Closed a , Closed b .
--   ax_eqCongR g a b c     : Closed a , Closed b .
--
-- The Closed premises are discharged at the use site (typically via
--  closed_natCode  /  closed_O  /  closed_ap1  /  closed_ap2  from
--  BRA3.Dispatch ).
--
-- Functor-bearing axioms (ax_C / ax_R_base / ax_R_step) are in
--  BRA4.ThmTCompleteAxFunctor  : they need an additional axFst/axSnd
-- reduction chain on the outputRHS's projections of  extra .

module BRA4.ThmTCompleteAxClosed where

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
open import BRA4.ThmTAtAx3 using ( thmT_at_axN3 )
open import BRA4.ThmTAtAx4 using ( thmT_at_axN4 )
open import BRA4.ThmTAtAx5 using ( thmT_at_axN5 )
open import BRA4.ThmTAtAx6 using ( thmT_at_axN6 )
open import BRA4.ThmTAtAx7 using ( thmT_at_axN7 )

open import BRA3.Church          using ( pi )
open import BRA3.Dispatch        using ( closedAt )
open import BRA3.RuleInst2       using
  ( NatLe ; le-zero ; le-suc ; le-trans ; le-refl ; le-suc-right
  ; maxN ; maxN-le-left ; maxN-le-right
  ; maxVarT ; maxVarF
  ; natEq-lt-false ; simSubstF ; three_step_F )
open import BRA4.RuleInst3       using ( simSubst3F ; five_step_F )

open Derive sbt sbf sbContract

------------------------------------------------------------------------
-- Helpers for the 3-var Closed-free witnesses.

private
  -- natEq n (suc n) = false  (by induction).
  natEq_n_sucN_false : (n : Nat) -> Eq (natEq n (suc n)) false
  natEq_n_sucN_false zero     = refl
  natEq_n_sucN_false (suc n)  = natEq_n_sucN_false n

  -- NatLe 1 3 , NatLe 2 3 , NatLe 3 3 .
  le_one_three   : NatLe (suc zero) (suc (suc (suc zero)))
  le_one_three   = le-suc (le-zero (suc (suc zero)))
  le_two_three   : NatLe (suc (suc zero)) (suc (suc (suc zero)))
  le_two_three   = le-suc (le-suc (le-zero (suc zero)))
  le_three_three : NatLe (suc (suc (suc zero))) (suc (suc (suc zero)))
  le_three_three = le-refl (suc (suc (suc zero)))

------------------------------------------------------------------------
-- step_sb_wrap : add one  sb  wrap on top of an inner code that
-- already evaluates to a codeFormula.

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

        step_lift :
          Deriv (eqF (ap2 sbf spec (ap1 thmT inputCode))
                      (ap2 sbf spec (codeFormula schemaCarrier)))
        step_lift = congR sbf spec inner_eq

        step_codeF :
          Deriv (eqF (ap2 sbf spec (codeFormula schemaCarrier))
                      (codeFormula (substF k t schemaCarrier)))
        step_codeF = sbfEq_codeFormula k t schemaCarrier
    in ruleTrans step_sb (ruleTrans step_lift step_codeF)

------------------------------------------------------------------------
-- ax_v a b  :  P = atomic (eqn (ap2 v a b) b) .
--   Schema  v(var 0, var 1) = var 1 .
--   Closed-free via Church-VII 3-step substitution composition :
--     encode (ax_v a b) =
--       sb c (codeTerm b) (sb 0 (codeTerm a) (sb 1 (codeTerm (var c)) (packAx 3 O))) ,
--     with  c = maxN 2 (maxVarT a)  .
--   thmT-cascade produces
--     codeFormula (substF c b (substF 0 a (substF 1 (var c) SCHEMA))) ,
--   and  three_step_F  bridges this to  codeFormula (simSubstF 0 a 1 b SCHEMA)  ;
--   the latter reduces definitionally to  codeFormula (atomic (eqn (ap2 v a b) b)) .

thmT_complete_ax_v :
  (a b : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_v a b))) (codeFormula (atomic (eqn (ap2 v a b) b))))
thmT_complete_ax_v a b =
  let c : Nat
      c = maxN (suc (suc zero)) (maxVarT a)

      -- NatLe witnesses.
      le_two_c : NatLe (suc (suc zero)) c
      le_two_c = maxN-le-left (suc (suc zero)) (maxVarT a)

      le_one_two : NatLe (suc zero) (suc (suc zero))
      le_one_two = le-suc (le-zero (suc zero))

      le_one_c : NatLe (suc zero) c
      le_one_c = le-trans le_one_two le_two_c

      le_a_c : NatLe (maxVarT a) c
      le_a_c = maxN-le-right (suc (suc zero)) (maxVarT a)

      -- natEq facts:  c > 0  =>  c ≠ 0 ;  c > 1  =>  c ≠ 1 ;  natEq 0 1 = false (def).
      cNeZero : Eq (natEq c zero) false
      cNeZero = natEq-lt-false c zero le_one_c

      cNeOne : Eq (natEq c (suc zero)) false
      cNeOne = natEq-lt-false c (suc zero) le_two_c

      k1Nek2 : Eq (natEq zero (suc zero)) false
      k1Nek2 = refl

      SCHEMA : Formula
      SCHEMA = atomic (eqn (ap2 v (var zero) (var (suc zero))) (var (suc zero)))

      le_schema_c : NatLe (maxVarF SCHEMA) c
      le_schema_c = le_two_c   -- maxVarF SCHEMA = 2 definitionally.

      packBody : Term
      packBody = ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc (suc (suc zero)))) O)

      schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
      schema_eq = thmT_at_axN3 O

      -- Step 1 : sb 1 with codeTerm (var c).
      step1_code : Term
      step1_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c))) packBody)
      step1_schema : Formula
      step1_schema = substF (suc zero) (var c) SCHEMA
      step1_eq : Deriv (eqF (ap1 thmT step1_code) (codeFormula step1_schema))
      step1_eq = step_sb_wrap (suc zero) (var c) packBody SCHEMA schema_eq

      -- Step 2 : sb 0 with a.
      step2_code : Term
      step2_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode zero) (codeTerm a)) step1_code)
      step2_schema : Formula
      step2_schema = substF zero a step1_schema
      step2_eq : Deriv (eqF (ap1 thmT step2_code) (codeFormula step2_schema))
      step2_eq = step_sb_wrap zero a step1_code step1_schema step1_eq

      -- Step 3 : sb c with b.  step3_code = encode (ax_v a b)  (definitionally).
      step3_code : Term
      step3_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode c) (codeTerm b)) step2_code)
      step3_schema : Formula
      step3_schema = substF c b step2_schema
      step3_eq : Deriv (eqF (ap1 thmT step3_code) (codeFormula step3_schema))
      step3_eq = step_sb_wrap c b step2_code step2_schema step2_eq

      -- Bridge step3_schema -> simSubstF 0 a 1 b SCHEMA  via  three_step_F .
      bridge_eq :
        Eq (substF c b (substF zero a (substF (suc zero) (var c) SCHEMA)))
           (simSubstF zero a (suc zero) b SCHEMA)
      bridge_eq = three_step_F zero a (suc zero) b c
                    k1Nek2 cNeZero cNeOne le_a_c SCHEMA le_schema_c
  in eqSubst (\ F -> Deriv (eqF (ap1 thmT step3_code) (codeFormula F)))
              bridge_eq step3_eq

------------------------------------------------------------------------
-- ax_eqCong1 f a b  :  P = imp (eqF a b) (eqF (ap1 f a) (ap1 f b)) .

thmT_complete_ax_eqCong1 :
  (f : Fun1) (a b : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_eqCong1 f a b)))
              (codeFormula (imp (atomic (eqn a b)) (atomic (eqn (ap1 f a) (ap1 f b))))))
thmT_complete_ax_eqCong1 f a b =
  let c : Nat
      c = maxN (suc (suc zero)) (maxVarT a)

      le_two_c : NatLe (suc (suc zero)) c
      le_two_c = maxN-le-left (suc (suc zero)) (maxVarT a)

      le_one_c : NatLe (suc zero) c
      le_one_c = le-trans (le-suc (le-zero (suc zero))) le_two_c

      le_a_c : NatLe (maxVarT a) c
      le_a_c = maxN-le-right (suc (suc zero)) (maxVarT a)

      cNeZero : Eq (natEq c zero) false
      cNeZero = natEq-lt-false c zero le_one_c

      cNeOne : Eq (natEq c (suc zero)) false
      cNeOne = natEq-lt-false c (suc zero) le_two_c

      k1Nek2 : Eq (natEq zero (suc zero)) false
      k1Nek2 = refl

      SCHEMA : Formula
      SCHEMA = imp (atomic (eqn (var zero) (var (suc zero))))
                    (atomic (eqn (ap1 f (var zero)) (ap1 f (var (suc zero)))))

      le_schema_c : NatLe (maxVarF SCHEMA) c
      le_schema_c = le_two_c   -- maxVarF SCHEMA = 2 definitionally.

      packBody : Term
      packBody = ap2 pi (natCode tag_ax)
                   (ap2 pi (natCode (suc (suc (suc (suc (suc zero)))))) (codeFun1 f))

      schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
      schema_eq = thmT_at_axN5 (codeFun1 f)

      step1_code : Term
      step1_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c))) packBody)
      step1_eq : Deriv (eqF (ap1 thmT step1_code)
                              (codeFormula (substF (suc zero) (var c) SCHEMA)))
      step1_eq = step_sb_wrap (suc zero) (var c) packBody SCHEMA schema_eq

      step2_code : Term
      step2_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode zero) (codeTerm a)) step1_code)
      step2_eq : Deriv (eqF (ap1 thmT step2_code)
                              (codeFormula (substF zero a (substF (suc zero) (var c) SCHEMA))))
      step2_eq = step_sb_wrap zero a step1_code (substF (suc zero) (var c) SCHEMA) step1_eq

      step3_code : Term
      step3_code = ap2 pi (natCode tag_sb)
                     (ap2 pi (ap2 pi (natCode c) (codeTerm b)) step2_code)
      step3_eq : Deriv (eqF (ap1 thmT step3_code)
                              (codeFormula (substF c b
                                              (substF zero a (substF (suc zero) (var c) SCHEMA)))))
      step3_eq = step_sb_wrap c b step2_code
                   (substF zero a (substF (suc zero) (var c) SCHEMA)) step2_eq

      bridge_eq :
        Eq (substF c b (substF zero a (substF (suc zero) (var c) SCHEMA)))
           (simSubstF zero a (suc zero) b SCHEMA)
      bridge_eq = three_step_F zero a (suc zero) b c
                    k1Nek2 cNeZero cNeOne le_a_c SCHEMA le_schema_c
  in eqSubst (\ F -> Deriv (eqF (ap1 thmT step3_code) (codeFormula F)))
              bridge_eq step3_eq

------------------------------------------------------------------------
-- ax_eqTrans x y z  :  P = imp (eqF x y) (imp (eqF x z) (eqF y z)) .
--   Schema imp (eqF v0 v1) (imp (eqF v0 v2) (eqF v1 v2)) .
--   After substF 0 x : imp (eqF x v1) (imp (eqF x v2) (eqF v1 v2))
--   After substF 1 y : imp (eqF (substT 1 y x) y) (imp (eqF (substT 1 y x) v2) (eqF y v2))
--   After substF 2 z : imp (eqF (substT 2 z (substT 1 y x)) (substT 2 z y))
--                          (imp (eqF (substT 2 z (substT 1 y x)) z) (eqF (substT 2 z y) z))
-- Bridges :
--   Closed x => substT 1 y x = x  AND  substT 2 z x = x .
--   Closed y => substT 2 z y = y .

thmT_complete_ax_eqTrans :
  (x y z : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_eqTrans x y z)))
              (codeFormula (imp (atomic (eqn x y))
                                 (imp (atomic (eqn x z)) (atomic (eqn y z))))))
thmT_complete_ax_eqTrans x y z =
  let
    c1 : Nat
    c1 = maxN (suc (suc (suc zero))) (maxN (maxVarT x) (maxVarT y))
    c2 : Nat
    c2 = suc c1

    -- NatLe witnesses.
    le_three_c1 : NatLe (suc (suc (suc zero))) c1
    le_three_c1 = maxN-le-left (suc (suc (suc zero))) (maxN (maxVarT x) (maxVarT y))
    le_c1_c2 : NatLe c1 c2
    le_c1_c2 = le-suc-right (le-refl c1)
    le_three_c2 : NatLe (suc (suc (suc zero))) c2
    le_three_c2 = le-trans le_three_c1 le_c1_c2
    le_one_c1 : NatLe (suc zero) c1
    le_one_c1 = le-trans le_one_three le_three_c1
    le_one_c2 : NatLe (suc zero) c2
    le_one_c2 = le-trans le_one_three le_three_c2
    le_two_c1 : NatLe (suc (suc zero)) c1
    le_two_c1 = le-trans le_two_three le_three_c1
    le_two_c2 : NatLe (suc (suc zero)) c2
    le_two_c2 = le-trans le_two_three le_three_c2

    -- maxVarT bounds.
    le_xy : NatLe (maxN (maxVarT x) (maxVarT y)) c1
    le_xy = maxN-le-right (suc (suc (suc zero))) (maxN (maxVarT x) (maxVarT y))
    le_x_c1 : NatLe (maxVarT x) c1
    le_x_c1 = le-trans (maxN-le-left (maxVarT x) (maxVarT y)) le_xy
    le_x_c2 : NatLe (maxVarT x) c2
    le_x_c2 = le-trans le_x_c1 le_c1_c2
    le_y_c1 : NatLe (maxVarT y) c1
    le_y_c1 = le-trans (maxN-le-right (maxVarT x) (maxVarT y)) le_xy
    le_y_c2 : NatLe (maxVarT y) c2
    le_y_c2 = le-trans le_y_c1 le_c1_c2

    -- Eq (natEq _ _) false witnesses.
    k0Nek1 : Eq (natEq zero (suc zero)) false
    k0Nek1 = refl
    k0Nek2 : Eq (natEq zero (suc (suc zero))) false
    k0Nek2 = refl
    k1Nek2 : Eq (natEq (suc zero) (suc (suc zero))) false
    k1Nek2 = refl
    c1Nek0 : Eq (natEq c1 zero) false
    c1Nek0 = natEq-lt-false c1 zero le_one_c1
    c1Nek1 : Eq (natEq c1 (suc zero)) false
    c1Nek1 = natEq-lt-false c1 (suc zero) le_two_c1
    c1Nek2 : Eq (natEq c1 (suc (suc zero))) false
    c1Nek2 = natEq-lt-false c1 (suc (suc zero)) le_three_c1
    c2Nek0 : Eq (natEq c2 zero) false
    c2Nek0 = natEq-lt-false c2 zero le_one_c2
    c2Nek1 : Eq (natEq c2 (suc zero)) false
    c2Nek1 = natEq-lt-false c2 (suc zero) le_two_c2
    c2Nek2 : Eq (natEq c2 (suc (suc zero))) false
    c2Nek2 = natEq-lt-false c2 (suc (suc zero)) le_three_c2
    c1Nec2 : Eq (natEq c1 c2) false
    c1Nec2 = natEq_n_sucN_false c1

    SCHEMA : Formula
    SCHEMA = imp (atomic (eqn (var zero) (var (suc zero))))
                  (imp (atomic (eqn (var zero) (var (suc (suc zero)))))
                        (atomic (eqn (var (suc zero)) (var (suc (suc zero))))))

    le_schema_c1 : NatLe (maxVarF SCHEMA) c1
    le_schema_c1 = le_three_c1
    le_schema_c2 : NatLe (maxVarF SCHEMA) c2
    le_schema_c2 = le_three_c2

    packBody : Term
    packBody = ap2 pi (natCode tag_ax)
                 (ap2 pi (natCode (suc (suc (suc (suc zero))))) O)

    schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
    schema_eq = thmT_at_axN4 O

    -- 5 sb wraps, each via step_sb_wrap .

    step1_code : Term
    step1_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c1))) packBody)
    step1_sch : Formula
    step1_sch = substF (suc zero) (var c1) SCHEMA
    step1_eq : Deriv (eqF (ap1 thmT step1_code) (codeFormula step1_sch))
    step1_eq = step_sb_wrap (suc zero) (var c1) packBody SCHEMA schema_eq

    step2_code : Term
    step2_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode (suc (suc zero))) (codeTerm (var c2))) step1_code)
    step2_sch : Formula
    step2_sch = substF (suc (suc zero)) (var c2) step1_sch
    step2_eq : Deriv (eqF (ap1 thmT step2_code) (codeFormula step2_sch))
    step2_eq = step_sb_wrap (suc (suc zero)) (var c2) step1_code step1_sch step1_eq

    step3_code : Term
    step3_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode zero) (codeTerm x)) step2_code)
    step3_sch : Formula
    step3_sch = substF zero x step2_sch
    step3_eq : Deriv (eqF (ap1 thmT step3_code) (codeFormula step3_sch))
    step3_eq = step_sb_wrap zero x step2_code step2_sch step2_eq

    step4_code : Term
    step4_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode c1) (codeTerm y)) step3_code)
    step4_sch : Formula
    step4_sch = substF c1 y step3_sch
    step4_eq : Deriv (eqF (ap1 thmT step4_code) (codeFormula step4_sch))
    step4_eq = step_sb_wrap c1 y step3_code step3_sch step3_eq

    step5_code : Term
    step5_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode c2) (codeTerm z)) step4_code)
    step5_sch : Formula
    step5_sch = substF c2 z step4_sch
    step5_eq : Deriv (eqF (ap1 thmT step5_code) (codeFormula step5_sch))
    step5_eq = step_sb_wrap c2 z step4_code step4_sch step4_eq

    bridge_eq :
      Eq step5_sch (simSubst3F zero x (suc zero) y (suc (suc zero)) z SCHEMA)
    bridge_eq = five_step_F zero x (suc zero) y (suc (suc zero)) z c1 c2
                  k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
                  c2Nek0 c2Nek1 c2Nek2 c1Nec2
                  le_x_c1 le_x_c2 le_y_c2
                  SCHEMA le_schema_c1 le_schema_c2
  in eqSubst (\ F -> Deriv (eqF (ap1 thmT step5_code) (codeFormula F)))
              bridge_eq step5_eq

------------------------------------------------------------------------
-- ax_eqCongL g a b c  :  P = imp (eqF a b) (eqF (g a c) (g b c)) .
--   Schema  imp (eqF v0 v1) (eqF (g v0 v2) (g v1 v2)) .
-- After three substF : substT 2 c (substT 1 b a) -> a (need Closed a) ,
--                       substT 2 c (substT 1 b ???) -> b (need substT 2 c b = b , Closed b) ,
--                       substT 2 c c = c (no closure needed since c -> c is by definitional reduction).

thmT_complete_ax_eqCongL :
  (g : Fun2) (a b c : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_eqCongL g a b c)))
              (codeFormula (imp (atomic (eqn a b))
                                 (atomic (eqn (ap2 g a c) (ap2 g b c))))))
thmT_complete_ax_eqCongL g a b c =
  let
    c1 : Nat
    c1 = maxN (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
    c2 : Nat
    c2 = suc c1

    le_three_c1 : NatLe (suc (suc (suc zero))) c1
    le_three_c1 = maxN-le-left (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
    le_c1_c2 : NatLe c1 c2
    le_c1_c2 = le-suc-right (le-refl c1)
    le_three_c2 : NatLe (suc (suc (suc zero))) c2
    le_three_c2 = le-trans le_three_c1 le_c1_c2
    le_one_c1 : NatLe (suc zero) c1
    le_one_c1 = le-trans le_one_three le_three_c1
    le_one_c2 : NatLe (suc zero) c2
    le_one_c2 = le-trans le_one_three le_three_c2
    le_two_c1 : NatLe (suc (suc zero)) c1
    le_two_c1 = le-trans le_two_three le_three_c1
    le_two_c2 : NatLe (suc (suc zero)) c2
    le_two_c2 = le-trans le_two_three le_three_c2

    le_ab : NatLe (maxN (maxVarT a) (maxVarT b)) c1
    le_ab = maxN-le-right (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
    le_a_c1 : NatLe (maxVarT a) c1
    le_a_c1 = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) le_ab
    le_a_c2 : NatLe (maxVarT a) c2
    le_a_c2 = le-trans le_a_c1 le_c1_c2
    le_b_c1 : NatLe (maxVarT b) c1
    le_b_c1 = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) le_ab
    le_b_c2 : NatLe (maxVarT b) c2
    le_b_c2 = le-trans le_b_c1 le_c1_c2

    k0Nek1 : Eq (natEq zero (suc zero)) false
    k0Nek1 = refl
    k0Nek2 : Eq (natEq zero (suc (suc zero))) false
    k0Nek2 = refl
    k1Nek2 : Eq (natEq (suc zero) (suc (suc zero))) false
    k1Nek2 = refl
    c1Nek0 : Eq (natEq c1 zero) false
    c1Nek0 = natEq-lt-false c1 zero le_one_c1
    c1Nek1 : Eq (natEq c1 (suc zero)) false
    c1Nek1 = natEq-lt-false c1 (suc zero) le_two_c1
    c1Nek2 : Eq (natEq c1 (suc (suc zero))) false
    c1Nek2 = natEq-lt-false c1 (suc (suc zero)) le_three_c1
    c2Nek0 : Eq (natEq c2 zero) false
    c2Nek0 = natEq-lt-false c2 zero le_one_c2
    c2Nek1 : Eq (natEq c2 (suc zero)) false
    c2Nek1 = natEq-lt-false c2 (suc zero) le_two_c2
    c2Nek2 : Eq (natEq c2 (suc (suc zero))) false
    c2Nek2 = natEq-lt-false c2 (suc (suc zero)) le_three_c2
    c1Nec2 : Eq (natEq c1 c2) false
    c1Nec2 = natEq_n_sucN_false c1

    SCHEMA : Formula
    SCHEMA = imp (atomic (eqn (var zero) (var (suc zero))))
                  (atomic (eqn (ap2 g (var zero) (var (suc (suc zero))))
                                (ap2 g (var (suc zero)) (var (suc (suc zero))))))

    le_schema_c1 : NatLe (maxVarF SCHEMA) c1
    le_schema_c1 = le_three_c1
    le_schema_c2 : NatLe (maxVarF SCHEMA) c2
    le_schema_c2 = le_three_c2

    packBody : Term
    packBody = ap2 pi (natCode tag_ax)
                 (ap2 pi (natCode (suc (suc (suc (suc (suc (suc zero))))))) (codeFun2 g))

    schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
    schema_eq = thmT_at_axN6 (codeFun2 g)

    step1_code : Term
    step1_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c1))) packBody)
    step1_sch : Formula
    step1_sch = substF (suc zero) (var c1) SCHEMA
    step1_eq : Deriv (eqF (ap1 thmT step1_code) (codeFormula step1_sch))
    step1_eq = step_sb_wrap (suc zero) (var c1) packBody SCHEMA schema_eq

    step2_code : Term
    step2_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode (suc (suc zero))) (codeTerm (var c2))) step1_code)
    step2_sch : Formula
    step2_sch = substF (suc (suc zero)) (var c2) step1_sch
    step2_eq : Deriv (eqF (ap1 thmT step2_code) (codeFormula step2_sch))
    step2_eq = step_sb_wrap (suc (suc zero)) (var c2) step1_code step1_sch step1_eq

    step3_code : Term
    step3_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode zero) (codeTerm a)) step2_code)
    step3_sch : Formula
    step3_sch = substF zero a step2_sch
    step3_eq : Deriv (eqF (ap1 thmT step3_code) (codeFormula step3_sch))
    step3_eq = step_sb_wrap zero a step2_code step2_sch step2_eq

    step4_code : Term
    step4_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode c1) (codeTerm b)) step3_code)
    step4_sch : Formula
    step4_sch = substF c1 b step3_sch
    step4_eq : Deriv (eqF (ap1 thmT step4_code) (codeFormula step4_sch))
    step4_eq = step_sb_wrap c1 b step3_code step3_sch step3_eq

    step5_code : Term
    step5_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode c2) (codeTerm c)) step4_code)
    step5_sch : Formula
    step5_sch = substF c2 c step4_sch
    step5_eq : Deriv (eqF (ap1 thmT step5_code) (codeFormula step5_sch))
    step5_eq = step_sb_wrap c2 c step4_code step4_sch step4_eq

    bridge_eq :
      Eq step5_sch (simSubst3F zero a (suc zero) b (suc (suc zero)) c SCHEMA)
    bridge_eq = five_step_F zero a (suc zero) b (suc (suc zero)) c c1 c2
                  k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
                  c2Nek0 c2Nek1 c2Nek2 c1Nec2
                  le_a_c1 le_a_c2 le_b_c2
                  SCHEMA le_schema_c1 le_schema_c2
  in eqSubst (\ F -> Deriv (eqF (ap1 thmT step5_code) (codeFormula F)))
              bridge_eq step5_eq

------------------------------------------------------------------------
-- ax_eqCongR g a b c  :  P = imp (eqF a b) (eqF (g c a) (g c b)) .  Symmetric.

thmT_complete_ax_eqCongR :
  (g : Fun2) (a b c : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_eqCongR g a b c)))
              (codeFormula (imp (atomic (eqn a b))
                                 (atomic (eqn (ap2 g c a) (ap2 g c b))))))
thmT_complete_ax_eqCongR g a b c =
  let
    c1 : Nat
    c1 = maxN (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
    c2 : Nat
    c2 = suc c1

    le_three_c1 : NatLe (suc (suc (suc zero))) c1
    le_three_c1 = maxN-le-left (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
    le_c1_c2 : NatLe c1 c2
    le_c1_c2 = le-suc-right (le-refl c1)
    le_three_c2 : NatLe (suc (suc (suc zero))) c2
    le_three_c2 = le-trans le_three_c1 le_c1_c2
    le_one_c1 : NatLe (suc zero) c1
    le_one_c1 = le-trans le_one_three le_three_c1
    le_one_c2 : NatLe (suc zero) c2
    le_one_c2 = le-trans le_one_three le_three_c2
    le_two_c1 : NatLe (suc (suc zero)) c1
    le_two_c1 = le-trans le_two_three le_three_c1
    le_two_c2 : NatLe (suc (suc zero)) c2
    le_two_c2 = le-trans le_two_three le_three_c2

    le_ab : NatLe (maxN (maxVarT a) (maxVarT b)) c1
    le_ab = maxN-le-right (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
    le_a_c1 : NatLe (maxVarT a) c1
    le_a_c1 = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) le_ab
    le_a_c2 : NatLe (maxVarT a) c2
    le_a_c2 = le-trans le_a_c1 le_c1_c2
    le_b_c1 : NatLe (maxVarT b) c1
    le_b_c1 = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) le_ab
    le_b_c2 : NatLe (maxVarT b) c2
    le_b_c2 = le-trans le_b_c1 le_c1_c2

    k0Nek1 : Eq (natEq zero (suc zero)) false
    k0Nek1 = refl
    k0Nek2 : Eq (natEq zero (suc (suc zero))) false
    k0Nek2 = refl
    k1Nek2 : Eq (natEq (suc zero) (suc (suc zero))) false
    k1Nek2 = refl
    c1Nek0 : Eq (natEq c1 zero) false
    c1Nek0 = natEq-lt-false c1 zero le_one_c1
    c1Nek1 : Eq (natEq c1 (suc zero)) false
    c1Nek1 = natEq-lt-false c1 (suc zero) le_two_c1
    c1Nek2 : Eq (natEq c1 (suc (suc zero))) false
    c1Nek2 = natEq-lt-false c1 (suc (suc zero)) le_three_c1
    c2Nek0 : Eq (natEq c2 zero) false
    c2Nek0 = natEq-lt-false c2 zero le_one_c2
    c2Nek1 : Eq (natEq c2 (suc zero)) false
    c2Nek1 = natEq-lt-false c2 (suc zero) le_two_c2
    c2Nek2 : Eq (natEq c2 (suc (suc zero))) false
    c2Nek2 = natEq-lt-false c2 (suc (suc zero)) le_three_c2
    c1Nec2 : Eq (natEq c1 c2) false
    c1Nec2 = natEq_n_sucN_false c1

    SCHEMA : Formula
    SCHEMA = imp (atomic (eqn (var zero) (var (suc zero))))
                  (atomic (eqn (ap2 g (var (suc (suc zero))) (var zero))
                                (ap2 g (var (suc (suc zero))) (var (suc zero)))))

    le_schema_c1 : NatLe (maxVarF SCHEMA) c1
    le_schema_c1 = le_three_c1
    le_schema_c2 : NatLe (maxVarF SCHEMA) c2
    le_schema_c2 = le_three_c2

    packBody : Term
    packBody = ap2 pi (natCode tag_ax)
                 (ap2 pi (natCode (suc (suc (suc (suc (suc (suc (suc zero)))))))) (codeFun2 g))

    schema_eq : Deriv (eqF (ap1 thmT packBody) (codeFormula SCHEMA))
    schema_eq = thmT_at_axN7 (codeFun2 g)

    step1_code : Term
    step1_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c1))) packBody)
    step1_sch : Formula
    step1_sch = substF (suc zero) (var c1) SCHEMA
    step1_eq : Deriv (eqF (ap1 thmT step1_code) (codeFormula step1_sch))
    step1_eq = step_sb_wrap (suc zero) (var c1) packBody SCHEMA schema_eq

    step2_code : Term
    step2_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode (suc (suc zero))) (codeTerm (var c2))) step1_code)
    step2_sch : Formula
    step2_sch = substF (suc (suc zero)) (var c2) step1_sch
    step2_eq : Deriv (eqF (ap1 thmT step2_code) (codeFormula step2_sch))
    step2_eq = step_sb_wrap (suc (suc zero)) (var c2) step1_code step1_sch step1_eq

    step3_code : Term
    step3_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode zero) (codeTerm a)) step2_code)
    step3_sch : Formula
    step3_sch = substF zero a step2_sch
    step3_eq : Deriv (eqF (ap1 thmT step3_code) (codeFormula step3_sch))
    step3_eq = step_sb_wrap zero a step2_code step2_sch step2_eq

    step4_code : Term
    step4_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode c1) (codeTerm b)) step3_code)
    step4_sch : Formula
    step4_sch = substF c1 b step3_sch
    step4_eq : Deriv (eqF (ap1 thmT step4_code) (codeFormula step4_sch))
    step4_eq = step_sb_wrap c1 b step3_code step3_sch step3_eq

    step5_code : Term
    step5_code = ap2 pi (natCode tag_sb)
                   (ap2 pi (ap2 pi (natCode c2) (codeTerm c)) step4_code)
    step5_sch : Formula
    step5_sch = substF c2 c step4_sch
    step5_eq : Deriv (eqF (ap1 thmT step5_code) (codeFormula step5_sch))
    step5_eq = step_sb_wrap c2 c step4_code step4_sch step4_eq

    bridge_eq :
      Eq step5_sch (simSubst3F zero a (suc zero) b (suc (suc zero)) c SCHEMA)
    bridge_eq = five_step_F zero a (suc zero) b (suc (suc zero)) c c1 c2
                  k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
                  c2Nek0 c2Nek1 c2Nek2 c1Nec2
                  le_a_c1 le_a_c2 le_b_c2
                  SCHEMA le_schema_c1 le_schema_c2
  in eqSubst (\ F -> Deriv (eqF (ap1 thmT step5_code) (codeFormula F)))
              bridge_eq step5_eq
