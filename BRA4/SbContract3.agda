{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbContract3 -- the Deriv-level contract realised by the 3-variable
-- simultaneous substitution functors  sbt3 , sbf3  -- both Fun2 .
--
-- spec3 = pi (pi (natCode k1) S1)
--            (pi (pi (natCode k2) S2) (pi (natCode k3) S3))
--
-- Contract has 10 closures: 6 for sbt3 (at_O, var_match_one/two/three,
-- var_nomatch, ap1, ap2) and 3 for sbf3 (atomic, neg, imp).
--
-- Justified at the Deriv level by BRA3.RuleInst3 (3-variable simultaneous
-- substitution metatheorem).

module BRA4.SbContract3 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

------------------------------------------------------------------------
-- Helper:  spec3T  -- the spec3 Term shape, repeatedly used.

spec3T : (k1 k2 k3 : Nat) (S1 S2 S3 : Term) -> Term
spec3T k1 k2 k3 S1 S2 S3 =
  ap2 Pair (ap2 Pair (natCode k1) S1)
           (ap2 Pair (ap2 Pair (natCode k2) S2) (ap2 Pair (natCode k3) S3))

------------------------------------------------------------------------
-- The 3-variable contract record.

record SbContract3 (sbt3 sbf3 : Fun2) : Set where
  field
    sbt3_at_O :
      (spec : Term) ->
      Deriv (eqF (ap2 sbt3 spec O) O)

    sbt3_at_var_match_one :
      (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
      Deriv (eqF (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_var) (natCode k1))) S1)

    sbt3_at_var_match_two :
      (k1 k2 k3 : Nat) (S1 S2 S3 : Term) -> Eq (natEq k1 k2) false ->
      Deriv (eqF (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_var) (natCode k2))) S2)

    sbt3_at_var_match_three :
      (k1 k2 k3 : Nat) (S1 S2 S3 : Term) ->
      Eq (natEq k1 k3) false -> Eq (natEq k2 k3) false ->
      Deriv (eqF (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_var) (natCode k3))) S3)

    sbt3_at_var_nomatch :
      (k1 k2 k3 m : Nat) (S1 S2 S3 : Term) ->
      Eq (natEq k1 m) false -> Eq (natEq k2 m) false -> Eq (natEq k3 m) false ->
      Deriv (eqF (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_var) (natCode m)))
                  (ap2 Pair (natCode tag_var) (natCode m)))

    sbt3_at_ap1 :
      (k1 k2 k3 : Nat) (S1 S2 S3 : Term) (f : Fun1) (ct : Term) ->
      Deriv (eqF (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 f)
                      (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3) ct))))

    sbt3_at_ap2 :
      (k1 k2 k3 : Nat) (S1 S2 S3 : Term) (g : Fun2) (ca cb : Term) ->
      Deriv (eqF (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_ap2)
                     (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g)
                      (ap2 Pair
                        (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3) ca)
                        (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3) cb)))))

    sbf3_at_atomic :
      (k1 k2 k3 : Nat) (S1 S2 S3 ca cb : Term) ->
      Deriv (eqF (ap2 sbf3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_eq) (ap2 Pair ca cb)))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair
                      (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3) ca)
                      (ap2 sbt3 (spec3T k1 k2 k3 S1 S2 S3) cb))))

    sbf3_at_neg :
      (k1 k2 k3 : Nat) (S1 S2 S3 cP : Term) ->
      Deriv (eqF (ap2 sbf3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_neg) cP))
                  (ap2 Pair (natCode tag_neg)
                    (ap2 sbf3 (spec3T k1 k2 k3 S1 S2 S3) cP)))

    sbf3_at_imp :
      (k1 k2 k3 : Nat) (S1 S2 S3 cP cQ : Term) ->
      Deriv (eqF (ap2 sbf3 (spec3T k1 k2 k3 S1 S2 S3)
                   (ap2 Pair (natCode tag_imp) (ap2 Pair cP cQ)))
                  (ap2 Pair (natCode tag_imp)
                    (ap2 Pair
                      (ap2 sbf3 (spec3T k1 k2 k3 S1 S2 S3) cP)
                      (ap2 sbf3 (spec3T k1 k2 k3 S1 S2 S3) cQ))))

------------------------------------------------------------------------
-- Concrete instance for our  sbt3 / sbf3 .

open import BRA4.SbT3            using ( sbt3 ; sbt3_at_O )
open import BRA4.SbT3AtVar       using ( sbt3_at_var_match_one
                                         ; sbt3_at_var_match_two
                                         ; sbt3_at_var_match_three
                                         ; sbt3_at_var_nomatch )
open import BRA4.SbT3AtAp        using ( sbt3_at_ap1 ; sbt3_at_ap2 )
open import BRA4.SbF3            using ( sbf3 )
open import BRA4.SbF3AtClosures  using ( sbf3_at_atomic ; sbf3_at_neg ; sbf3_at_imp )

sbContract3 : SbContract3 sbt3 sbf3
sbContract3 = record
  { sbt3_at_O               = sbt3_at_O
  ; sbt3_at_var_match_one   = sbt3_at_var_match_one
  ; sbt3_at_var_match_two   = sbt3_at_var_match_two
  ; sbt3_at_var_match_three = sbt3_at_var_match_three
  ; sbt3_at_var_nomatch     = sbt3_at_var_nomatch
  ; sbt3_at_ap1             = sbt3_at_ap1
  ; sbt3_at_ap2             = sbt3_at_ap2
  ; sbf3_at_atomic          = sbf3_at_atomic
  ; sbf3_at_neg             = sbf3_at_neg
  ; sbf3_at_imp             = sbf3_at_imp
  }
