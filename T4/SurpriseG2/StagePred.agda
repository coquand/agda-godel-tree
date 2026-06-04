{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StagePred --
--
-- The per-stage hypothesis  S(r)  of the EXTERNAL induction in
-- T4/clos  ("surprise-G2 with ONLY ConOpenInt") .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * `ProgPack consts d`  :  one slot of the describing family at day  d ;
--   a record carrying the enum-index  k <= M  and a Deriv that
--   ap1 enum (natCode k)  describes day  d  ( OPEN-FUEL form ;  fuel
--   slot is  var 0 , consistent with T4.SurpriseG2.Describes ) .
--
-- * `DescribingFamily consts r`  :  the META data of a family
--   (ProgPack consts d)_{d in [r..N]} .
--
-- * `StagePred consts r`  :  the META function type  S(r) :=
--   "DescribingFamily consts r  ->  Deriv (0 = 1)" .
--
-- =====================================================================
-- LINK TO T4/clos .
-- =====================================================================
--
-- The clos sketch writes
--
--   neg (describe(p_r,l_r,r) /\ ... /\ describe(p_N,l_N,N))
--
-- as the S(r) statement .   The Agda formulation here uses
--
--   (family of describes for [r..N])  ->  Deriv (eqF O (ap1 s O))
--
-- which is the META-LEVEL equivalent  (a meta function instead of a
-- closed Deriv of the negated conjunction) .   The clos's specific  l_i
-- halt times are absorbed into the OPEN-FUEL  Describes  derivation
-- ( the same convention as the OLD  T4.SurpriseG2.StageZeroNegsConj
-- DescPackConj , see [[project_bra4_oldframework_retired_residualB_obstruction]] ) ;
-- downstream uses  ruleInst 0 t  to pin a specific fuel  t  as needed .

module T4.SurpriseG2.StagePred where

open import T4.Base
open import BRA3.RuleInst2                  using ( NatLe )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.Describes       using ( Describes )
open import T4.SurpriseG2.MetaPigeonhole  as MP using ( Lt )

------------------------------------------------------------------------
-- ProgPack consts d  -- one slot of the describing family at day  d .
--
-- progIx :  the enum-index  k  in  [0..M]  picking the program .
-- ixBd   :  bound  k <= M .
-- runs   :  Deriv  open over the fuel slot  var 0 , asserting that
--           ap1 enum (natCode k)  describes day  d  ( OPEN-FUEL form ) .

record ProgPack (consts : SurpriseConstsConj) (d : Nat) : Set where
  constructor mkProgPack
  field
    progIx : Nat
    ixBd   : NatLe progIx (SurpriseConstsConj.M consts)
    runs   : Deriv (Describes
                     (ap1 (SurpriseConstsConj.enum consts) (natCode progIx))
                     (natCode d))

open ProgPack public

------------------------------------------------------------------------
-- DescribingFamily consts r  -- the family at days  [r..N] .
--
-- For each day  d  with  Lt r (suc d)  (so  d >= r ) AND  NatLe d N
-- (so  d <= N ), a ProgPack consts d .

DescribingFamily : (consts : SurpriseConstsConj) -> Nat -> Set
DescribingFamily consts r =
  (d : Nat) ->
  Lt r (suc d) ->
  NatLe d (SurpriseConstsConj.N consts) ->
  ProgPack consts d

------------------------------------------------------------------------
-- StagePred consts r  -- the per-stage hypothesis S(r) .
--
-- Given a describing family for days [r..N] , derive  Deriv (0 = 1) .

StagePred : (consts : SurpriseConstsConj) -> Nat -> Set
StagePred consts r =
  DescribingFamily consts r -> Deriv (eqF O (ap1 s O))
