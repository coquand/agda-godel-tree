{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbDerived -- derived sbEq lemmas from the per-shape SbContract.
--
-- Given an  SbContract sbt sbf , this module derives two key Deriv-level
-- lemmas that downstream code (BRA4/Diagonal, BRA4/Thm/Thm14) consumes:
--
--   sbtEq_codeTerm :
--     (k : Nat) (t r : Term) (F1Args : ...) ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) (codeTerm t)) (codeTerm r))
--                 (codeTerm (substT k t r)))
--
--   sbfEq_codeFormula :
--     (k : Nat) (t : Term) (F : Formula) ->
--     Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) (codeTerm t)) (codeFormula F))
--                 (codeFormula (substF k t F)))
--
-- Both proved by meta-induction (on  r , on  F ).  The contract's
-- per-shape closures fire at each level; sub-results carry over via the
-- inductive hypothesis.

module BRA4.SbDerived where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.SbContract

------------------------------------------------------------------------
-- Local helpers: Eq congruence over a 2-arg function.

private
  eqCong2 :
    {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B} ->
    Eq x x' -> Eq y y' -> Eq (f x y) (f x' y')
  eqCong2 f refl refl = refl

------------------------------------------------------------------------
-- Module fixed on (sbt, sbf, contract).

module Derive (sbt sbf : Fun2) (sbCon : SbContract sbt sbf) where
  open SbContract sbCon

  ----------------------------------------------------------------------
  -- sbt at codeTerm r , by induction on r.
  --
  -- Key recurrence:
  --   substT k t O           = O                                          (refl)
  --   substT k t (var m)     = boolCase (natEq k m) t (var m)
  --   substT k t (ap1 f r)   = ap1 f (substT k t r)
  --   substT k t (ap2 g a b) = ap2 g (substT k t a) (substT k t b)

  sbtEq_codeTerm :
    (k : Nat) (t r : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) (codeTerm t)) (codeTerm r))
                (codeTerm (substT k t r)))

  -- r = O case.  codeTerm O = O ; substT k t O = O.
  sbtEq_codeTerm k t O = sbt_at_O (ap2 Pair (natCode k) (codeTerm t))

  -- r = var m case.  codeTerm (var m) = Pair (natCode tag_var) (natCode m).
  -- Branch on natEq k m.
  sbtEq_codeTerm k t (var m) = aux (natEq k m) refl
    where
      spec : Term
      spec = ap2 Pair (natCode k) (codeTerm t)

      aux : (b : Bool) -> Eq (natEq k m) b ->
            Deriv (eqF (ap2 sbt spec (ap2 Pair (natCode tag_var) (natCode m)))
                        (codeTerm (substT k t (var m))))
      aux true eqb =
        -- substT k t (var m) = boolCase true t (var m) = t.  codeTerm t = ...
        -- Need: sbt spec (Pair tag_var (natCode m)) =Deriv= codeTerm t.
        -- From sbt_at_var_match : sbt spec (Pair tag_var (natCode k)) = codeTerm t.
        -- Bridge via natEq k m = true => Eq k m at the Nat level => Eq (natCode k) (natCode m) => transport.
        eqSubst (\ m' -> Deriv (eqF (ap2 sbt spec (ap2 Pair (natCode tag_var) (natCode m')))
                                    (codeTerm (boolCase (natEq k m') t (var m')))))
                (natEq_true_eq k m eqb)
                (sbt_at_var_match' k t)
        where
          natEq_true_eq : (a b : Nat) -> Eq (natEq a b) true -> Eq a b
          natEq_true_eq zero    zero    _ = refl
          natEq_true_eq zero    (suc _) ()
          natEq_true_eq (suc _) zero    ()
          natEq_true_eq (suc a) (suc b) p =
            eqCong suc (natEq_true_eq a b p)

          -- Specialise sbt_at_var_match at m = k:  the boolCase reduces to t,
          -- so codeTerm (boolCase ...) = codeTerm t.
          sbt_at_var_match' :
            (k' : Nat) (t' : Term) ->
            Deriv (eqF (ap2 sbt (ap2 Pair (natCode k') (codeTerm t'))
                         (ap2 Pair (natCode tag_var) (natCode k')))
                        (codeTerm (boolCase (natEq k' k') t' (var k'))))
          sbt_at_var_match' k' t' =
            eqSubst (\ b' -> Deriv (eqF (ap2 sbt (ap2 Pair (natCode k') (codeTerm t'))
                                          (ap2 Pair (natCode tag_var) (natCode k')))
                                         (codeTerm (boolCase b' t' (var k')))))
                    (eqSym (natEq_refl k'))
                    (sbt_at_var_match k' (codeTerm t'))
            where
              natEq_refl : (n : Nat) -> Eq (natEq n n) true
              natEq_refl zero    = refl
              natEq_refl (suc n) = natEq_refl n

      aux false eqb =
        -- substT k t (var m) = boolCase false t (var m) = var m  (definitionally).
        -- codeTerm (boolCase (natEq k m) t (var m)) reduces to Pair tag_var (natCode m)
        -- ONLY when (natEq k m) is concretely false.  We use eqSubst on eqb to
        -- rewrite (natEq k m) -> false in the type.
        eqSubst (\ b' -> Deriv (eqF (ap2 sbt spec (ap2 Pair (natCode tag_var) (natCode m)))
                                    (codeTerm (boolCase b' t (var m)))))
                (eqSym eqb)
                (sbt_at_var_nomatch k m (codeTerm t) eqb)

  -- r = ap1 f r' case.
  sbtEq_codeTerm k t (ap1 f r) =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)

        ih : Deriv (eqF (ap2 sbt spec (codeTerm r)) (codeTerm (substT k t r)))
        ih = sbtEq_codeTerm k t r

        step1 :
          Deriv (eqF (ap2 sbt spec (codeTerm (ap1 f r)))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f)
                          (ap2 sbt spec (codeTerm r)))))
        step1 = sbt_at_ap1 k (codeTerm t) f (codeTerm r)

        step2 :
          Deriv (eqF (ap2 Pair (codeFun1 f) (ap2 sbt spec (codeTerm r)))
                      (ap2 Pair (codeFun1 f) (codeTerm (substT k t r))))
        step2 = congR Pair (codeFun1 f) ih

        step3 :
          Deriv (eqF (ap2 Pair (natCode tag_ap1)
                       (ap2 Pair (codeFun1 f) (ap2 sbt spec (codeTerm r))))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (codeTerm (substT k t r)))))
        step3 = congR Pair (natCode tag_ap1) step2
    in ruleTrans step1 step3

  -- r = ap2 g a b case.
  sbtEq_codeTerm k t (ap2 g a b) =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)

        ih_a : Deriv (eqF (ap2 sbt spec (codeTerm a)) (codeTerm (substT k t a)))
        ih_a = sbtEq_codeTerm k t a

        ih_b : Deriv (eqF (ap2 sbt spec (codeTerm b)) (codeTerm (substT k t b)))
        ih_b = sbtEq_codeTerm k t b

        step1 :
          Deriv (eqF (ap2 sbt spec (codeTerm (ap2 g a b)))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt spec (codeTerm a))
                            (ap2 sbt spec (codeTerm b))))))
        step1 = sbt_at_ap2 k (codeTerm t) g (codeTerm a) (codeTerm b)

        inner1 :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm (substT k t a))
                                (ap2 sbt spec (codeTerm b))))
        inner1 = congL Pair (ap2 sbt spec (codeTerm b)) ih_a

        inner2 :
          Deriv (eqF (ap2 Pair (codeTerm (substT k t a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm (substT k t a))
                                (codeTerm (substT k t b))))
        inner2 = congR Pair (codeTerm (substT k t a)) ih_b

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm (substT k t a))
                                (codeTerm (substT k t b))))
        inner = ruleTrans inner1 inner2

        outer1 :
          Deriv (eqF (ap2 Pair (codeFun2 g)
                       (ap2 Pair (ap2 sbt spec (codeTerm a))
                                 (ap2 sbt spec (codeTerm b))))
                      (ap2 Pair (codeFun2 g)
                       (ap2 Pair (codeTerm (substT k t a))
                                 (codeTerm (substT k t b)))))
        outer1 = congR Pair (codeFun2 g) inner

        outer2 :
          Deriv (eqF (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 g)
                         (ap2 Pair (ap2 sbt spec (codeTerm a))
                                   (ap2 sbt spec (codeTerm b)))))
                      (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 g)
                         (ap2 Pair (codeTerm (substT k t a))
                                   (codeTerm (substT k t b))))))
        outer2 = congR Pair (natCode tag_ap2) outer1
    in ruleTrans step1 outer2

  ----------------------------------------------------------------------
  -- sbf at codeFormula F , by induction on F.

  sbfEq_codeFormula :
    (k : Nat) (t : Term) (F : Formula) ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) (codeTerm t)) (codeFormula F))
                (codeFormula (substF k t F)))

  sbfEq_codeFormula k t (atomic (eqn a b)) =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (atomic (eqn a b))))
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt spec (codeTerm a))
                          (ap2 sbt spec (codeTerm b)))))
        step1 = sbf_at_atomic k (codeTerm t) (codeTerm a) (codeTerm b)

        ih_a : Deriv (eqF (ap2 sbt spec (codeTerm a)) (codeTerm (substT k t a)))
        ih_a = sbtEq_codeTerm k t a

        ih_b : Deriv (eqF (ap2 sbt spec (codeTerm b)) (codeTerm (substT k t b)))
        ih_b = sbtEq_codeTerm k t b

        inner1 :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm (substT k t a))
                                (ap2 sbt spec (codeTerm b))))
        inner1 = congL Pair (ap2 sbt spec (codeTerm b)) ih_a

        inner2 :
          Deriv (eqF (ap2 Pair (codeTerm (substT k t a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm (substT k t a))
                                (codeTerm (substT k t b))))
        inner2 = congR Pair (codeTerm (substT k t a)) ih_b

        outer :
          Deriv (eqF (ap2 Pair (natCode tag_eq)
                       (ap2 Pair (ap2 sbt spec (codeTerm a))
                                 (ap2 sbt spec (codeTerm b))))
                      (ap2 Pair (natCode tag_eq)
                       (ap2 Pair (codeTerm (substT k t a))
                                 (codeTerm (substT k t b)))))
        outer = congR Pair (natCode tag_eq) (ruleTrans inner1 inner2)
    in ruleTrans step1 outer

  sbfEq_codeFormula k t (neg P) =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (neg P)))
                      (ap2 Pair (natCode tag_neg)
                        (ap2 sbf spec (codeFormula P))))
        step1 = sbf_at_neg k (codeTerm t) (codeFormula P)

        ih : Deriv (eqF (ap2 sbf spec (codeFormula P))
                         (codeFormula (substF k t P)))
        ih = sbfEq_codeFormula k t P

        step2 :
          Deriv (eqF (ap2 Pair (natCode tag_neg) (ap2 sbf spec (codeFormula P)))
                      (ap2 Pair (natCode tag_neg) (codeFormula (substF k t P))))
        step2 = congR Pair (natCode tag_neg) ih
    in ruleTrans step1 step2

  sbfEq_codeFormula k t (imp P Q) =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (imp P Q)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair
                          (ap2 sbf spec (codeFormula P))
                          (ap2 sbf spec (codeFormula Q)))))
        step1 = sbf_at_imp k (codeTerm t) (codeFormula P) (codeFormula Q)

        ih_P : Deriv (eqF (ap2 sbf spec (codeFormula P)) (codeFormula (substF k t P)))
        ih_P = sbfEq_codeFormula k t P

        ih_Q : Deriv (eqF (ap2 sbf spec (codeFormula Q)) (codeFormula (substF k t Q)))
        ih_Q = sbfEq_codeFormula k t Q

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbf spec (codeFormula P))
                                (ap2 sbf spec (codeFormula Q)))
                      (ap2 Pair (codeFormula (substF k t P))
                                (codeFormula (substF k t Q))))
        inner = ruleTrans (congL Pair (ap2 sbf spec (codeFormula Q)) ih_P)
                          (congR Pair (codeFormula (substF k t P)) ih_Q)

        outer :
          Deriv (eqF (ap2 Pair (natCode tag_imp)
                       (ap2 Pair (ap2 sbf spec (codeFormula P))
                                 (ap2 sbf spec (codeFormula Q))))
                      (ap2 Pair (natCode tag_imp)
                       (ap2 Pair (codeFormula (substF k t P))
                                 (codeFormula (substF k t Q)))))
        outer = congR Pair (natCode tag_imp) inner
    in ruleTrans step1 outer
