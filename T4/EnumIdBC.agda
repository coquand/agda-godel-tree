{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EnumIdBC -- the ENUM-IDENTIFICATION ( clos Step 5's self-reference ),
-- reduced to the single Berry SIZE bound.
--
-- =====================================================================
-- THE POINT.
-- =====================================================================
--
-- The Chaitin/clos Step-5 closer needs : the diagonal program  gLcodeBC  IS one
-- of the enumerated short programs ( gLcodeBC = enum k_* ).   This is NOT an
-- unshipped "internal coverage" -- it is the SHIPPED META coverage
-- T4.EnumProg.enum_cover  applied to the CONCRETE diagonal term  gLcodeBC
-- ( whose  InAlph -validity is the shipped  T4.KdefDiagBC.inAlph_gLcodeBC ).
--
-- The ONLY genuine residual it is gated on is the BERRY SIZE BOUND
--
--   berry : NatLe (nodes (gLcodeBC enum fuel M)) Lstar_meta
--
-- i.e. "the diagonal program's description fits in the budget L*" -- the actual
-- mathematical heart of the surprise-exam / Chaitin argument ( the size-vs-budget
-- race ), NOT plumbing.   Given it, the enum-identification is immediate :

open import T4.Base

module T4.EnumIdBC (Lstar_meta : Nat) where

open import BRA3.RuleInst2 using ( NatLe )
open import T4.ProgEnc using ( nodes ; enc )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt )
open import T4.EnumProg Lstar_meta using ( enum ; enum_cover ; Bnat ; Sigma ; And )
open import T4.KdefDiagBC using ( gLcodeBC ; inAlph_gLcodeBC )

module _ (fuel : Term) (M : Nat)
  (berry : NatLe (nodes (gLcodeBC enum fuel M)) Lstar_meta)
  where

  -- The diagonal IS enumerated :  some slot  k_* < Bnat  with
  --   enum (natCode k_*) = enc (gLcodeBC enum fuel M) .
  enumId :
    Sigma Nat (\ k -> And (Lt k Bnat)
                          (Deriv (eqF (ap1 enum (natCode k))
                                      (enc (gLcodeBC enum fuel M)))))
  enumId = enum_cover (gLcodeBC enum fuel M) (inAlph_gLcodeBC enum fuel M) berry
