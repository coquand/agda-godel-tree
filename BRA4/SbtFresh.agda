{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbtFresh -- freshness-stability of  sbt / sbf  on codeTerm /
-- codeFormula.  When the substitution variable  c  is strictly above
-- every free variable in  t , the sub-on-codeTerms is a no-op :
--
--   c > maxVarT t  =>
--     Deriv (eqF (ap2 sbt (Pair (natCode c) S) (codeTerm t)) (codeTerm t))
--
--   c > maxVarF F  =>
--     Deriv (eqF (ap2 sbf (Pair (natCode c) S) (codeFormula F)) (codeFormula F))
--
-- Proved by meta-induction on  t  /  F .  The base case  var m  uses
-- sbt_at_var_nomatch  with  Eq (natEq c m) false  derived from
-- NatLe (suc m) c (= c > m) via natEq-lt-false (BRA4.RuleInst2).
--
-- This is the BRA4 thmT-level analog of BRA3 / RuleInst2's
-- substT_above_max .  Used by BRA4.ThmTCompleteAxEqTransUniv to
-- discharge the Closed-witness premises of  thmT_complete_ax_eqTrans .

module BRA4.SbtFresh where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.SbContract
open import BRA4.RuleInst2

------------------------------------------------------------------------
-- Module fixed on (sbt, sbf, contract).

module Fresh (sbt sbf : Fun2) (sbCon : SbContract sbt sbf) where
  open SbContract sbCon

  ----------------------------------------------------------------------
  -- sbt is a no-op on  codeTerm t  under freshness.

  sbtEq_codeTerm_fresh :
    (c : Nat) (S : Term) (t : Term) ->
    NatLe (maxVarT t) c ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode c) S) (codeTerm t)) (codeTerm t))

  sbtEq_codeTerm_fresh c S O le =
    sbt_at_O (ap2 Pair (natCode c) S)

  sbtEq_codeTerm_fresh c S (var m) le =
    let cNeM : Eq (natEq c m) false
        cNeM = natEq-lt-false c m le
    in sbt_at_var_nomatch c m S cNeM

  sbtEq_codeTerm_fresh c S (ap1 f r) le =
    let spec : Term
        spec = ap2 Pair (natCode c) S

        ih : Deriv (eqF (ap2 sbt spec (codeTerm r)) (codeTerm r))
        ih = sbtEq_codeTerm_fresh c S r le

        step1 :
          Deriv (eqF (ap2 sbt spec (codeTerm (ap1 f r)))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f)
                          (ap2 sbt spec (codeTerm r)))))
        step1 = sbt_at_ap1 c S f (codeTerm r)

        step2 :
          Deriv (eqF (ap2 Pair (codeFun1 f) (ap2 sbt spec (codeTerm r)))
                      (ap2 Pair (codeFun1 f) (codeTerm r)))
        step2 = congR Pair (codeFun1 f) ih

        step3 :
          Deriv (eqF (ap2 Pair (natCode tag_ap1)
                       (ap2 Pair (codeFun1 f) (ap2 sbt spec (codeTerm r))))
                      (ap2 Pair (natCode tag_ap1)
                       (ap2 Pair (codeFun1 f) (codeTerm r))))
        step3 = congR Pair (natCode tag_ap1) step2
    in ruleTrans step1 step3

  sbtEq_codeTerm_fresh c S (ap2 g a b) le =
    let spec : Term
        spec = ap2 Pair (natCode c) S

        le_a : NatLe (maxVarT a) c
        le_a = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) le

        le_b : NatLe (maxVarT b) c
        le_b = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) le

        ih_a : Deriv (eqF (ap2 sbt spec (codeTerm a)) (codeTerm a))
        ih_a = sbtEq_codeTerm_fresh c S a le_a

        ih_b : Deriv (eqF (ap2 sbt spec (codeTerm b)) (codeTerm b))
        ih_b = sbtEq_codeTerm_fresh c S b le_b

        step1 :
          Deriv (eqF (ap2 sbt spec (codeTerm (ap2 g a b)))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt spec (codeTerm a))
                            (ap2 sbt spec (codeTerm b))))))
        step1 = sbt_at_ap2 c S g (codeTerm a) (codeTerm b)

        inner1 :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a)
                                (ap2 sbt spec (codeTerm b))))
        inner1 = congL Pair (ap2 sbt spec (codeTerm b)) ih_a

        inner2 :
          Deriv (eqF (ap2 Pair (codeTerm a) (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a) (codeTerm b)))
        inner2 = congR Pair (codeTerm a) ih_b

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a) (codeTerm b)))
        inner = ruleTrans inner1 inner2

        outer1 :
          Deriv (eqF (ap2 Pair (codeFun2 g)
                       (ap2 Pair (ap2 sbt spec (codeTerm a))
                                 (ap2 sbt spec (codeTerm b))))
                      (ap2 Pair (codeFun2 g)
                       (ap2 Pair (codeTerm a) (codeTerm b))))
        outer1 = congR Pair (codeFun2 g) inner

        outer2 :
          Deriv (eqF (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 g)
                         (ap2 Pair (ap2 sbt spec (codeTerm a))
                                   (ap2 sbt spec (codeTerm b)))))
                      (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 g)
                         (ap2 Pair (codeTerm a) (codeTerm b)))))
        outer2 = congR Pair (natCode tag_ap2) outer1
    in ruleTrans step1 outer2

  ----------------------------------------------------------------------
  -- sbf is a no-op on  codeFormula F  under freshness.

  sbfEq_codeFormula_fresh :
    (c : Nat) (S : Term) (F : Formula) ->
    NatLe (maxVarF F) c ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode c) S) (codeFormula F)) (codeFormula F))

  sbfEq_codeFormula_fresh c S (atomic (eqn a b)) le =
    let spec : Term
        spec = ap2 Pair (natCode c) S

        le_a : NatLe (maxVarT a) c
        le_a = le-trans (maxN-le-left (maxVarT a) (maxVarT b)) le

        le_b : NatLe (maxVarT b) c
        le_b = le-trans (maxN-le-right (maxVarT a) (maxVarT b)) le

        ih_a : Deriv (eqF (ap2 sbt spec (codeTerm a)) (codeTerm a))
        ih_a = sbtEq_codeTerm_fresh c S a le_a

        ih_b : Deriv (eqF (ap2 sbt spec (codeTerm b)) (codeTerm b))
        ih_b = sbtEq_codeTerm_fresh c S b le_b

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (atomic (eqn a b))))
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt spec (codeTerm a))
                          (ap2 sbt spec (codeTerm b)))))
        step1 = sbf_at_atomic c S (codeTerm a) (codeTerm b)

        inner1 :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a)
                                (ap2 sbt spec (codeTerm b))))
        inner1 = congL Pair (ap2 sbt spec (codeTerm b)) ih_a

        inner2 :
          Deriv (eqF (ap2 Pair (codeTerm a) (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a) (codeTerm b)))
        inner2 = congR Pair (codeTerm a) ih_b

        outer :
          Deriv (eqF (ap2 Pair (natCode tag_eq)
                       (ap2 Pair (ap2 sbt spec (codeTerm a))
                                 (ap2 sbt spec (codeTerm b))))
                      (ap2 Pair (natCode tag_eq)
                       (ap2 Pair (codeTerm a) (codeTerm b))))
        outer = congR Pair (natCode tag_eq) (ruleTrans inner1 inner2)
    in ruleTrans step1 outer

  sbfEq_codeFormula_fresh c S (neg P) le =
    let spec : Term
        spec = ap2 Pair (natCode c) S

        ih : Deriv (eqF (ap2 sbf spec (codeFormula P)) (codeFormula P))
        ih = sbfEq_codeFormula_fresh c S P le

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (neg P)))
                      (ap2 Pair (natCode tag_neg)
                        (ap2 sbf spec (codeFormula P))))
        step1 = sbf_at_neg c S (codeFormula P)

        step2 :
          Deriv (eqF (ap2 Pair (natCode tag_neg) (ap2 sbf spec (codeFormula P)))
                      (ap2 Pair (natCode tag_neg) (codeFormula P)))
        step2 = congR Pair (natCode tag_neg) ih
    in ruleTrans step1 step2

  sbfEq_codeFormula_fresh c S (imp P Q) le =
    let spec : Term
        spec = ap2 Pair (natCode c) S

        le_P : NatLe (maxVarF P) c
        le_P = le-trans (maxN-le-left (maxVarF P) (maxVarF Q)) le

        le_Q : NatLe (maxVarF Q) c
        le_Q = le-trans (maxN-le-right (maxVarF P) (maxVarF Q)) le

        ih_P : Deriv (eqF (ap2 sbf spec (codeFormula P)) (codeFormula P))
        ih_P = sbfEq_codeFormula_fresh c S P le_P

        ih_Q : Deriv (eqF (ap2 sbf spec (codeFormula Q)) (codeFormula Q))
        ih_Q = sbfEq_codeFormula_fresh c S Q le_Q

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (imp P Q)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair
                          (ap2 sbf spec (codeFormula P))
                          (ap2 sbf spec (codeFormula Q)))))
        step1 = sbf_at_imp c S (codeFormula P) (codeFormula Q)

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbf spec (codeFormula P))
                                (ap2 sbf spec (codeFormula Q)))
                      (ap2 Pair (codeFormula P) (codeFormula Q)))
        inner = ruleTrans (congL Pair (ap2 sbf spec (codeFormula Q)) ih_P)
                          (congR Pair (codeFormula P) ih_Q)

        outer :
          Deriv (eqF (ap2 Pair (natCode tag_imp)
                       (ap2 Pair (ap2 sbf spec (codeFormula P))
                                 (ap2 sbf spec (codeFormula Q))))
                      (ap2 Pair (natCode tag_imp)
                       (ap2 Pair (codeFormula P) (codeFormula Q))))
        outer = congR Pair (natCode tag_imp) inner
    in ruleTrans step1 outer
