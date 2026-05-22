{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbContract2 -- the Deriv-level contract realised by the 2-variable
-- simultaneous substitution functors  sbt2 , sbf2  -- both Fun2 .
--
-- Parallel to BRA4.SbContract (single-var sb).  The spec2 format is
--
--   spec2 = pi (pi (natCode k1) S1) (pi (natCode k2) S2)
--
-- with  k1 /= k2 .  The contract has 8 closure equations: 5 for sbt2
-- (at_O, var_match_one, var_match_two, var_nomatch, ap1, ap2) and 3 for
-- sbf2 (atomic, neg, imp).
--
-- Justification at the Deriv level: BRA3.RuleInst2 (ChurchT130, two-var
-- simultaneous substitution).  The contract is the encoded-level
-- counterpart.

module BRA4.SbContract2 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

------------------------------------------------------------------------
-- The 2-variable contract record.

record SbContract2 (sbt2 sbf2 : Fun2) : Set where
  field
    sbt2_at_O :
      (spec : Term) ->
      Deriv (eqF (ap2 sbt2 spec O) O)

    sbt2_at_var_match_one :
      (k1 k2 : Nat) (S1 S2 : Term) ->
      Deriv (eqF (ap2 sbt2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_var) (natCode k1))) S1)

    sbt2_at_var_match_two :
      (k1 k2 : Nat) (S1 S2 : Term) -> Eq (natEq k1 k2) false ->
      Deriv (eqF (ap2 sbt2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_var) (natCode k2))) S2)

    sbt2_at_var_nomatch :
      (k1 k2 m : Nat) (S1 S2 : Term) ->
      Eq (natEq k1 m) false -> Eq (natEq k2 m) false ->
      Deriv (eqF (ap2 sbt2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_var) (natCode m)))
                  (ap2 Pair (natCode tag_var) (natCode m)))

    sbt2_at_ap1 :
      (k1 k2 : Nat) (S1 S2 : Term) (f : Fun1) (ct : Term) ->
      Deriv (eqF (ap2 sbt2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 f)
                      (ap2 sbt2
                        (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                        ct))))

    sbt2_at_ap2 :
      (k1 k2 : Nat) (S1 S2 : Term) (g : Fun2) (ca cb : Term) ->
      Deriv (eqF (ap2 sbt2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_ap2)
                     (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g)
                      (ap2 Pair
                        (ap2 sbt2
                          (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                          ca)
                        (ap2 sbt2
                          (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                          cb)))))

    sbf2_at_atomic :
      (k1 k2 : Nat) (S1 S2 ca cb : Term) ->
      Deriv (eqF (ap2 sbf2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_eq) (ap2 Pair ca cb)))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair
                      (ap2 sbt2
                        (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                        ca)
                      (ap2 sbt2
                        (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                        cb))))

    sbf2_at_neg :
      (k1 k2 : Nat) (S1 S2 cP : Term) ->
      Deriv (eqF (ap2 sbf2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_neg) cP))
                  (ap2 Pair (natCode tag_neg)
                    (ap2 sbf2
                      (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                      cP)))

    sbf2_at_imp :
      (k1 k2 : Nat) (S1 S2 cP cQ : Term) ->
      Deriv (eqF (ap2 sbf2
                   (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                   (ap2 Pair (natCode tag_imp) (ap2 Pair cP cQ)))
                  (ap2 Pair (natCode tag_imp)
                    (ap2 Pair
                      (ap2 sbf2
                        (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                        cP)
                      (ap2 sbf2
                        (ap2 Pair (ap2 Pair (natCode k1) S1) (ap2 Pair (natCode k2) S2))
                        cQ))))

------------------------------------------------------------------------
-- Concrete instance for our  sbt2 / sbf2 .

open import BRA4.SbT2            using ( sbt2 ; sbt2_at_O )
open import BRA4.SbT2AtVar       using ( sbt2_at_var_match_one
                                         ; sbt2_at_var_match_two
                                         ; sbt2_at_var_nomatch )
open import BRA4.SbT2AtAp        using ( sbt2_at_ap1 ; sbt2_at_ap2 )
open import BRA4.SbF2            using ( sbf2 )
open import BRA4.SbF2AtClosures  using ( sbf2_at_atomic ; sbf2_at_neg ; sbf2_at_imp )

sbContract2 : SbContract2 sbt2 sbf2
sbContract2 = record
  { sbt2_at_O             = sbt2_at_O
  ; sbt2_at_var_match_one = sbt2_at_var_match_one
  ; sbt2_at_var_match_two = sbt2_at_var_match_two
  ; sbt2_at_var_nomatch   = sbt2_at_var_nomatch
  ; sbt2_at_ap1           = sbt2_at_ap1
  ; sbt2_at_ap2           = sbt2_at_ap2
  ; sbf2_at_atomic        = sbf2_at_atomic
  ; sbf2_at_neg           = sbf2_at_neg
  ; sbf2_at_imp           = sbf2_at_imp
  }
