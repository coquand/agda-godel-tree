{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.RuleInst3 -- 3-variable simultaneous substitution + 5-step
-- composition lemma.  The natural extension of BRA3.RuleInst2's
-- 2-variable  simSubstT / simSubstF + three_step_T / three_step_F .
--
-- Used by BRA4.ThmTCompleteAxClosed to discharge the  Closed -witness
-- premises of the 3-var axiom completeness lemmas (ax_eqTrans /
-- ax_eqCongL / ax_eqCongR).

module BRA4.RuleInst3 where

open import BRA4.Base
open import BRA3.RuleInst2 using
  ( NatLe ; le-zero ; le-suc ; le-trans
  ; maxN ; maxN-le-left ; maxN-le-right
  ; maxVarT ; maxVarF ; maxVarEq
  ; natEq-lt-false ; natEq-refl ; natEq_sym
  ; substT_above_max ; true_neq_false )

------------------------------------------------------------------------
-- simSubst3T / simSubst3Eq / simSubst3F : simultaneous 3-var substitution.

simSubst3T :
  Nat -> Term -> Nat -> Term -> Nat -> Term -> Term -> Term
simSubst3T k0 t0 k1 t1 k2 t2 O = O
simSubst3T k0 t0 k1 t1 k2 t2 (var m) =
  boolCase (natEq k0 m) t0
    (boolCase (natEq k1 m) t1
      (boolCase (natEq k2 m) t2 (var m)))
simSubst3T k0 t0 k1 t1 k2 t2 (ap1 f a) =
  ap1 f (simSubst3T k0 t0 k1 t1 k2 t2 a)
simSubst3T k0 t0 k1 t1 k2 t2 (ap2 g a b) =
  ap2 g (simSubst3T k0 t0 k1 t1 k2 t2 a)
         (simSubst3T k0 t0 k1 t1 k2 t2 b)

simSubst3Eq :
  Nat -> Term -> Nat -> Term -> Nat -> Term -> Equation -> Equation
simSubst3Eq k0 t0 k1 t1 k2 t2 (eqn a b) =
  eqn (simSubst3T k0 t0 k1 t1 k2 t2 a)
       (simSubst3T k0 t0 k1 t1 k2 t2 b)

simSubst3F :
  Nat -> Term -> Nat -> Term -> Nat -> Term -> Formula -> Formula
simSubst3F k0 t0 k1 t1 k2 t2 (atomic e) =
  atomic (simSubst3Eq k0 t0 k1 t1 k2 t2 e)
simSubst3F k0 t0 k1 t1 k2 t2 (neg p) =
  neg (simSubst3F k0 t0 k1 t1 k2 t2 p)
simSubst3F k0 t0 k1 t1 k2 t2 (imp p q) =
  imp (simSubst3F k0 t0 k1 t1 k2 t2 p) (simSubst3F k0 t0 k1 t1 k2 t2 q)

------------------------------------------------------------------------
-- Helpers.

private
  bc_false :
    {A : Set} {b : Bool} (X Y : A) -> Eq b false ->
    Eq (boolCase b X Y) Y
  bc_false {_} {b} X Y eq = eqCong (\ bb -> boolCase bb X Y) eq

  bc_true :
    {A : Set} {b : Bool} (X Y : A) -> Eq b true ->
    Eq (boolCase b X Y) X
  bc_true {_} {b} X Y eq = eqCong (\ bb -> boolCase bb X Y) eq

  natEq_flip_false :
    (a b : Nat) -> Eq (natEq a b) false -> Eq (natEq b a) false
  natEq_flip_false a b ab_false =
    eqTrans (natEq_sym b a) ab_false

  -- natEq a b = true  =>  a Eq b.
  natEqTrue_to_Eq :
    (a b : Nat) -> Eq (natEq a b) true -> Eq a b
  natEqTrue_to_Eq zero zero _ = refl
  natEqTrue_to_Eq zero (suc _) ()
  natEqTrue_to_Eq (suc _) zero ()
  natEqTrue_to_Eq (suc a) (suc b) eq =
    eqCong suc (natEqTrue_to_Eq a b eq)

  -- Derive contradiction from natEq a b = true and natEq a b = false.
  derive_contradiction :
    (a b : Nat) -> Eq (natEq a b) true -> Eq (natEq a b) false ->
    {X : Set} -> X
  derive_contradiction a b t f =
    emptyElim (true_neq_false (eqTrans (eqSym t) f))

------------------------------------------------------------------------
-- The var-case dispatch.

five_step_at_var :
  (k0 : Nat) (t0 : Term) (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term)
  (c1 c2 : Nat) (m : Nat) ->
  Eq (natEq k0 k1) false ->
  Eq (natEq k0 k2) false ->
  Eq (natEq k1 k2) false ->
  Eq (natEq c1 k0) false ->
  Eq (natEq c1 k1) false ->
  Eq (natEq c1 k2) false ->
  Eq (natEq c2 k0) false ->
  Eq (natEq c2 k1) false ->
  Eq (natEq c2 k2) false ->
  Eq (natEq c1 c2) false ->
  NatLe (maxVarT t0) c1 ->
  NatLe (maxVarT t0) c2 ->
  NatLe (maxVarT t1) c2 ->
  NatLe (suc m) c1 ->
  NatLe (suc m) c2 ->
  Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
        (substT k2 (var c2) (substT k1 (var c1) (var m))))))
     (simSubst3T k0 t0 k1 t1 k2 t2 (var m))
five_step_at_var k0 t0 k1 t1 k2 t2 c1 c2 m
                  k0Nek1 k0Nek2 k1Nek2
                  c1Nek0 c1Nek1 c1Nek2
                  c2Nek0 c2Nek1 c2Nek2
                  c1Nec2
                  t0FreshC1 t0FreshC2 t1FreshC2
                  mLtC1 mLtC2 =
  aux (natEq k0 m) (natEq k1 m) (natEq k2 m) refl refl refl
  where
    cNeMc1 : Eq (natEq c1 m) false
    cNeMc1 = natEq-lt-false c1 m mLtC1

    cNeMc2 : Eq (natEq c2 m) false
    cNeMc2 = natEq-lt-false c2 m mLtC2

    t0_fresh_at_c1 : (X : Term) -> Eq (substT c1 X t0) t0
    t0_fresh_at_c1 X = substT_above_max c1 t0 X t0FreshC1

    t0_fresh_at_c2 : (X : Term) -> Eq (substT c2 X t0) t0
    t0_fresh_at_c2 X = substT_above_max c2 t0 X t0FreshC2

    t1_fresh_at_c2 : (X : Term) -> Eq (substT c2 X t1) t1
    t1_fresh_at_c2 X = substT_above_max c2 t1 X t1FreshC2

    aux :
      (b0 b1 b2 : Bool) ->
      Eq (natEq k0 m) b0 ->
      Eq (natEq k1 m) b1 ->
      Eq (natEq k2 m) b2 ->
      Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
            (substT k2 (var c2) (substT k1 (var c1) (var m))))))
         (simSubst3T k0 t0 k1 t1 k2 t2 (var m))

    -- CASE A : m = k0.
    aux true _ _ k0eq _ _ =
      let
        k0_eq_m : Eq k0 m
        k0_eq_m = natEqTrue_to_Eq k0 m k0eq

        k1NeM : Eq (natEq k1 m) false
        k1NeM = eqSubst (\ z -> Eq (natEq k1 z) false) k0_eq_m
                  (natEq_flip_false k0 k1 k0Nek1)

        k2NeM : Eq (natEq k2 m) false
        k2NeM = eqSubst (\ z -> Eq (natEq k2 z) false) k0_eq_m
                  (natEq_flip_false k0 k2 k0Nek2)

        s1 : Eq (substT k1 (var c1) (var m)) (var m)
        s1 = bc_false (var c1) (var m) k1NeM

        s2 : Eq (substT k2 (var c2) (var m)) (var m)
        s2 = bc_false (var c2) (var m) k2NeM

        s12 : Eq (substT k2 (var c2) (substT k1 (var c1) (var m))) (var m)
        s12 = eqTrans (eqCong (substT k2 (var c2)) s1) s2

        s3 : Eq (substT k0 t0 (var m)) t0
        s3 = bc_true t0 (var m) k0eq

        s123 : Eq (substT k0 t0 (substT k2 (var c2) (substT k1 (var c1) (var m)))) t0
        s123 = eqTrans (eqCong (substT k0 t0) s12) s3

        s4 : Eq (substT c1 t1 t0) t0
        s4 = t0_fresh_at_c1 t1

        s1234 : Eq (substT c1 t1 (substT k0 t0
                    (substT k2 (var c2) (substT k1 (var c1) (var m))))) t0
        s1234 = eqTrans (eqCong (substT c1 t1) s123) s4

        s5 : Eq (substT c2 t2 t0) t0
        s5 = t0_fresh_at_c2 t2

        lhs : Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
                  (substT k2 (var c2) (substT k1 (var c1) (var m)))))) t0
        lhs = eqTrans (eqCong (substT c2 t2) s1234) s5

        rhs : Eq (simSubst3T k0 t0 k1 t1 k2 t2 (var m)) t0
        rhs = bc_true t0 _ k0eq
      in eqTrans lhs (eqSym rhs)

    -- CASE B : m = k1, m /= k0.
    aux false true _ k0neM k1eq _ =
      let
        s1 : Eq (substT k1 (var c1) (var m)) (var c1)
        s1 = bc_true (var c1) (var m) k1eq

        k2NeC1 : Eq (natEq k2 c1) false
        k2NeC1 = natEq_flip_false c1 k2 c1Nek2

        s2 : Eq (substT k2 (var c2) (var c1)) (var c1)
        s2 = bc_false (var c2) (var c1) k2NeC1

        s12 : Eq (substT k2 (var c2) (substT k1 (var c1) (var m))) (var c1)
        s12 = eqTrans (eqCong (substT k2 (var c2)) s1) s2

        k0NeC1 : Eq (natEq k0 c1) false
        k0NeC1 = natEq_flip_false c1 k0 c1Nek0

        s3 : Eq (substT k0 t0 (var c1)) (var c1)
        s3 = bc_false t0 (var c1) k0NeC1

        s123 : Eq (substT k0 t0 (substT k2 (var c2) (substT k1 (var c1) (var m)))) (var c1)
        s123 = eqTrans (eqCong (substT k0 t0) s12) s3

        s4 : Eq (substT c1 t1 (var c1)) t1
        s4 = bc_true t1 (var c1) (natEq-refl c1)

        s1234 : Eq (substT c1 t1 (substT k0 t0
                    (substT k2 (var c2) (substT k1 (var c1) (var m))))) t1
        s1234 = eqTrans (eqCong (substT c1 t1) s123) s4

        s5 : Eq (substT c2 t2 t1) t1
        s5 = t1_fresh_at_c2 t2

        lhs : Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
                  (substT k2 (var c2) (substT k1 (var c1) (var m)))))) t1
        lhs = eqTrans (eqCong (substT c2 t2) s1234) s5

        rhs_inner : Eq (boolCase (natEq k1 m) t1
                          (boolCase (natEq k2 m) t2 (var m))) t1
        rhs_inner = bc_true t1 _ k1eq

        rhs : Eq (simSubst3T k0 t0 k1 t1 k2 t2 (var m)) t1
        rhs = eqTrans (bc_false t0 _ k0neM) rhs_inner
      in eqTrans lhs (eqSym rhs)

    -- CASE C : m = k2, m /= k0, m /= k1.
    aux false false true k0neM k1neM k2eq =
      let
        s1 : Eq (substT k1 (var c1) (var m)) (var m)
        s1 = bc_false (var c1) (var m) k1neM

        s2 : Eq (substT k2 (var c2) (var m)) (var c2)
        s2 = bc_true (var c2) (var m) k2eq

        s12 : Eq (substT k2 (var c2) (substT k1 (var c1) (var m))) (var c2)
        s12 = eqTrans (eqCong (substT k2 (var c2)) s1) s2

        k0NeC2 : Eq (natEq k0 c2) false
        k0NeC2 = natEq_flip_false c2 k0 c2Nek0

        s3 : Eq (substT k0 t0 (var c2)) (var c2)
        s3 = bc_false t0 (var c2) k0NeC2

        s123 : Eq (substT k0 t0 (substT k2 (var c2) (substT k1 (var c1) (var m)))) (var c2)
        s123 = eqTrans (eqCong (substT k0 t0) s12) s3

        s4 : Eq (substT c1 t1 (var c2)) (var c2)
        s4 = bc_false t1 (var c2) c1Nec2

        s1234 : Eq (substT c1 t1 (substT k0 t0
                    (substT k2 (var c2) (substT k1 (var c1) (var m))))) (var c2)
        s1234 = eqTrans (eqCong (substT c1 t1) s123) s4

        s5 : Eq (substT c2 t2 (var c2)) t2
        s5 = bc_true t2 (var c2) (natEq-refl c2)

        lhs : Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
                  (substT k2 (var c2) (substT k1 (var c1) (var m)))))) t2
        lhs = eqTrans (eqCong (substT c2 t2) s1234) s5

        rhs_inner2 : Eq (boolCase (natEq k2 m) t2 (var m)) t2
        rhs_inner2 = bc_true t2 _ k2eq

        rhs_inner1 : Eq (boolCase (natEq k1 m) t1
                          (boolCase (natEq k2 m) t2 (var m))) t2
        rhs_inner1 = eqTrans (bc_false t1 _ k1neM) rhs_inner2

        rhs : Eq (simSubst3T k0 t0 k1 t1 k2 t2 (var m)) t2
        rhs = eqTrans (bc_false t0 _ k0neM) rhs_inner1
      in eqTrans lhs (eqSym rhs)

    -- CASE D : m /= k0, k1, k2.
    aux false false false k0neM k1neM k2neM =
      let
        s1 : Eq (substT k1 (var c1) (var m)) (var m)
        s1 = bc_false (var c1) (var m) k1neM

        s2 : Eq (substT k2 (var c2) (var m)) (var m)
        s2 = bc_false (var c2) (var m) k2neM

        s12 : Eq (substT k2 (var c2) (substT k1 (var c1) (var m))) (var m)
        s12 = eqTrans (eqCong (substT k2 (var c2)) s1) s2

        s3 : Eq (substT k0 t0 (var m)) (var m)
        s3 = bc_false t0 (var m) k0neM

        s123 : Eq (substT k0 t0 (substT k2 (var c2) (substT k1 (var c1) (var m)))) (var m)
        s123 = eqTrans (eqCong (substT k0 t0) s12) s3

        s4 : Eq (substT c1 t1 (var m)) (var m)
        s4 = bc_false t1 (var m) cNeMc1

        s1234 : Eq (substT c1 t1 (substT k0 t0
                    (substT k2 (var c2) (substT k1 (var c1) (var m))))) (var m)
        s1234 = eqTrans (eqCong (substT c1 t1) s123) s4

        s5 : Eq (substT c2 t2 (var m)) (var m)
        s5 = bc_false t2 (var m) cNeMc2

        lhs : Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
                  (substT k2 (var c2) (substT k1 (var c1) (var m)))))) (var m)
        lhs = eqTrans (eqCong (substT c2 t2) s1234) s5

        rhs_inner2 : Eq (boolCase (natEq k2 m) t2 (var m)) (var m)
        rhs_inner2 = bc_false t2 (var m) k2neM

        rhs_inner1 : Eq (boolCase (natEq k1 m) t1
                          (boolCase (natEq k2 m) t2 (var m))) (var m)
        rhs_inner1 = eqTrans (bc_false t1 _ k1neM) rhs_inner2

        rhs : Eq (simSubst3T k0 t0 k1 t1 k2 t2 (var m)) (var m)
        rhs = eqTrans (bc_false t0 _ k0neM) rhs_inner1
      in eqTrans lhs (eqSym rhs)

    -- IMPOSSIBLE CASES : two k_i true simultaneously => k_i Eq.
    aux true true _ k0eq k1eq _ =
      let
        k0_eq_m : Eq k0 m
        k0_eq_m = natEqTrue_to_Eq k0 m k0eq
        k1_eq_m : Eq k1 m
        k1_eq_m = natEqTrue_to_Eq k1 m k1eq
        k0_eq_k1 : Eq k0 k1
        k0_eq_k1 = eqTrans k0_eq_m (eqSym k1_eq_m)
        natEq_k0_k1_true : Eq (natEq k0 k1) true
        natEq_k0_k1_true = eqSubst (\ z -> Eq (natEq k0 z) true) k0_eq_k1 (natEq-refl k0)
      in derive_contradiction k0 k1 natEq_k0_k1_true k0Nek1

    aux true false true k0eq _ k2eq =
      let
        k0_eq_m : Eq k0 m
        k0_eq_m = natEqTrue_to_Eq k0 m k0eq
        k2_eq_m : Eq k2 m
        k2_eq_m = natEqTrue_to_Eq k2 m k2eq
        k0_eq_k2 : Eq k0 k2
        k0_eq_k2 = eqTrans k0_eq_m (eqSym k2_eq_m)
        natEq_k0_k2_true : Eq (natEq k0 k2) true
        natEq_k0_k2_true = eqSubst (\ z -> Eq (natEq k0 z) true) k0_eq_k2 (natEq-refl k0)
      in derive_contradiction k0 k2 natEq_k0_k2_true k0Nek2

    aux false true true _ k1eq k2eq =
      let
        k1_eq_m : Eq k1 m
        k1_eq_m = natEqTrue_to_Eq k1 m k1eq
        k2_eq_m : Eq k2 m
        k2_eq_m = natEqTrue_to_Eq k2 m k2eq
        k1_eq_k2 : Eq k1 k2
        k1_eq_k2 = eqTrans k1_eq_m (eqSym k2_eq_m)
        natEq_k1_k2_true : Eq (natEq k1 k2) true
        natEq_k1_k2_true = eqSubst (\ z -> Eq (natEq k1 z) true) k1_eq_k2 (natEq-refl k1)
      in derive_contradiction k1 k2 natEq_k1_k2_true k1Nek2

    aux true true true k0eq k1eq _ =
      let
        k0_eq_m : Eq k0 m
        k0_eq_m = natEqTrue_to_Eq k0 m k0eq
        k1_eq_m : Eq k1 m
        k1_eq_m = natEqTrue_to_Eq k1 m k1eq
        k0_eq_k1 : Eq k0 k1
        k0_eq_k1 = eqTrans k0_eq_m (eqSym k1_eq_m)
        natEq_k0_k1_true : Eq (natEq k0 k1) true
        natEq_k0_k1_true = eqSubst (\ z -> Eq (natEq k0 z) true) k0_eq_k1 (natEq-refl k0)
      in derive_contradiction k0 k1 natEq_k0_k1_true k0Nek1

------------------------------------------------------------------------
-- five_step_T : induction on T.

five_step_T :
  (k0 : Nat) (t0 : Term) (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term)
  (c1 c2 : Nat) ->
  Eq (natEq k0 k1) false ->
  Eq (natEq k0 k2) false ->
  Eq (natEq k1 k2) false ->
  Eq (natEq c1 k0) false ->
  Eq (natEq c1 k1) false ->
  Eq (natEq c1 k2) false ->
  Eq (natEq c2 k0) false ->
  Eq (natEq c2 k1) false ->
  Eq (natEq c2 k2) false ->
  Eq (natEq c1 c2) false ->
  NatLe (maxVarT t0) c1 ->
  NatLe (maxVarT t0) c2 ->
  NatLe (maxVarT t1) c2 ->
  (T : Term) ->
  NatLe (maxVarT T) c1 ->
  NatLe (maxVarT T) c2 ->
  Eq (substT c2 t2 (substT c1 t1 (substT k0 t0
        (substT k2 (var c2) (substT k1 (var c1) T)))))
     (simSubst3T k0 t0 k1 t1 k2 t2 T)

five_step_T k0 t0 k1 t1 k2 t2 c1 c2 _ _ _ _ _ _ _ _ _ _ _ _ _ O _ _ = refl

five_step_T k0 t0 k1 t1 k2 t2 c1 c2
            k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
            c2Nek0 c2Nek1 c2Nek2 c1Nec2
            t0FreshC1 t0FreshC2 t1FreshC2
            (var m) leC1 leC2 =
  five_step_at_var k0 t0 k1 t1 k2 t2 c1 c2 m
    k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
    c2Nek0 c2Nek1 c2Nek2 c1Nec2
    t0FreshC1 t0FreshC2 t1FreshC2 leC1 leC2

five_step_T k0 t0 k1 t1 k2 t2 c1 c2
            k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
            c2Nek0 c2Nek1 c2Nek2 c1Nec2
            t0FreshC1 t0FreshC2 t1FreshC2
            (ap1 f a) leC1 leC2 =
  eqCong (ap1 f)
    (five_step_T k0 t0 k1 t1 k2 t2 c1 c2
       k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
       c2Nek0 c2Nek1 c2Nek2 c1Nec2
       t0FreshC1 t0FreshC2 t1FreshC2 a leC1 leC2)

five_step_T k0 t0 k1 t1 k2 t2 c1 c2
            k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
            c2Nek0 c2Nek1 c2Nek2 c1Nec2
            t0FreshC1 t0FreshC2 t1FreshC2
            (ap2 g a b) leC1 leC2 =
  let
    le_a_c1 : NatLe (maxVarT a) c1
    le_a_c1 = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) leC1
    le_a_c2 : NatLe (maxVarT a) c2
    le_a_c2 = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) leC2
    le_b_c1 : NatLe (maxVarT b) c1
    le_b_c1 = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) leC1
    le_b_c2 : NatLe (maxVarT b) c2
    le_b_c2 = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) leC2

    eq_a = five_step_T k0 t0 k1 t1 k2 t2 c1 c2
             k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
             c2Nek0 c2Nek1 c2Nek2 c1Nec2
             t0FreshC1 t0FreshC2 t1FreshC2 a le_a_c1 le_a_c2
    eq_b = five_step_T k0 t0 k1 t1 k2 t2 c1 c2
             k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
             c2Nek0 c2Nek1 c2Nek2 c1Nec2
             t0FreshC1 t0FreshC2 t1FreshC2 b le_b_c1 le_b_c2
  in eqTrans
       (eqCong (\ a' -> ap2 g a' (substT c2 t2 (substT c1 t1 (substT k0 t0
                                   (substT k2 (var c2) (substT k1 (var c1) b)))))) eq_a)
       (eqCong (ap2 g (simSubst3T k0 t0 k1 t1 k2 t2 a)) eq_b)

------------------------------------------------------------------------
-- five_step_F : induction on F.

five_step_F :
  (k0 : Nat) (t0 : Term) (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term)
  (c1 c2 : Nat) ->
  Eq (natEq k0 k1) false ->
  Eq (natEq k0 k2) false ->
  Eq (natEq k1 k2) false ->
  Eq (natEq c1 k0) false ->
  Eq (natEq c1 k1) false ->
  Eq (natEq c1 k2) false ->
  Eq (natEq c2 k0) false ->
  Eq (natEq c2 k1) false ->
  Eq (natEq c2 k2) false ->
  Eq (natEq c1 c2) false ->
  NatLe (maxVarT t0) c1 ->
  NatLe (maxVarT t0) c2 ->
  NatLe (maxVarT t1) c2 ->
  (P : Formula) ->
  NatLe (maxVarF P) c1 ->
  NatLe (maxVarF P) c2 ->
  Eq (substF c2 t2 (substF c1 t1 (substF k0 t0
        (substF k2 (var c2) (substF k1 (var c1) P)))))
     (simSubst3F k0 t0 k1 t1 k2 t2 P)

five_step_F k0 t0 k1 t1 k2 t2 c1 c2
            k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
            c2Nek0 c2Nek1 c2Nek2 c1Nec2
            t0FreshC1 t0FreshC2 t1FreshC2
            (atomic (eqn a b)) leC1 leC2 =
  let
    le_a_c1 : NatLe (maxVarT a) c1
    le_a_c1 = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) leC1
    le_a_c2 : NatLe (maxVarT a) c2
    le_a_c2 = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) leC2
    le_b_c1 : NatLe (maxVarT b) c1
    le_b_c1 = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) leC1
    le_b_c2 : NatLe (maxVarT b) c2
    le_b_c2 = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) leC2

    eq_a = five_step_T k0 t0 k1 t1 k2 t2 c1 c2
             k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
             c2Nek0 c2Nek1 c2Nek2 c1Nec2
             t0FreshC1 t0FreshC2 t1FreshC2 a le_a_c1 le_a_c2
    eq_b = five_step_T k0 t0 k1 t1 k2 t2 c1 c2
             k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
             c2Nek0 c2Nek1 c2Nek2 c1Nec2
             t0FreshC1 t0FreshC2 t1FreshC2 b le_b_c1 le_b_c2

    mk : (a' b' : Term) -> Formula
    mk a' b' = atomic (eqn a' b')
  in eqTrans
       (eqCong (\ a' -> mk a' (substT c2 t2 (substT c1 t1 (substT k0 t0
                                  (substT k2 (var c2) (substT k1 (var c1) b)))))) eq_a)
       (eqCong (mk (simSubst3T k0 t0 k1 t1 k2 t2 a)) eq_b)

five_step_F k0 t0 k1 t1 k2 t2 c1 c2
            k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
            c2Nek0 c2Nek1 c2Nek2 c1Nec2
            t0FreshC1 t0FreshC2 t1FreshC2
            (neg P) leC1 leC2 =
  eqCong neg
    (five_step_F k0 t0 k1 t1 k2 t2 c1 c2
       k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
       c2Nek0 c2Nek1 c2Nek2 c1Nec2
       t0FreshC1 t0FreshC2 t1FreshC2 P leC1 leC2)

five_step_F k0 t0 k1 t1 k2 t2 c1 c2
            k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
            c2Nek0 c2Nek1 c2Nek2 c1Nec2
            t0FreshC1 t0FreshC2 t1FreshC2
            (imp P Q) leC1 leC2 =
  let
    le_P_c1 : NatLe (maxVarF P) c1
    le_P_c1 = le-trans (maxN-le-left (maxVarF P) (maxVarF Q)) leC1
    le_P_c2 : NatLe (maxVarF P) c2
    le_P_c2 = le-trans (maxN-le-left (maxVarF P) (maxVarF Q)) leC2
    le_Q_c1 : NatLe (maxVarF Q) c1
    le_Q_c1 = le-trans (maxN-le-right (maxVarF P) (maxVarF Q)) leC1
    le_Q_c2 : NatLe (maxVarF Q) c2
    le_Q_c2 = le-trans (maxN-le-right (maxVarF P) (maxVarF Q)) leC2

    eq_P = five_step_F k0 t0 k1 t1 k2 t2 c1 c2
             k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
             c2Nek0 c2Nek1 c2Nek2 c1Nec2
             t0FreshC1 t0FreshC2 t1FreshC2 P le_P_c1 le_P_c2
    eq_Q = five_step_F k0 t0 k1 t1 k2 t2 c1 c2
             k0Nek1 k0Nek2 k1Nek2 c1Nek0 c1Nek1 c1Nek2
             c2Nek0 c2Nek1 c2Nek2 c1Nec2
             t0FreshC1 t0FreshC2 t1FreshC2 Q le_Q_c1 le_Q_c2
  in eqTrans
       (eqCong (\ P' -> imp P' (substF c2 t2 (substF c1 t1 (substF k0 t0
                                    (substF k2 (var c2) (substF k1 (var c1) Q)))))) eq_P)
       (eqCong (imp (simSubst3F k0 t0 k1 t1 k2 t2 P)) eq_Q)
