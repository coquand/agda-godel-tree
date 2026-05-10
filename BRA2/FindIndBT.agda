{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.FindIndBT -- partial first version of the find-and-extract
-- traversal locating a topmost indBTB in a  DerivTBounded 1 l bot
-- proof tree.
--
-- Strategy ((b) + leftmost): handle indBTB-at-root explicitly; defer
-- structural-rule-wrapped indBTBs to a later iteration.  At rank 1,
-- removing any indBTB suffices, so leftmost-by-traversal is fine.
--
-- Returns:
--   * nothing  -- shape this version cannot handle, OR encountered
--                 indBTB whose v1, v2, e fail the WellFormedIndBT
--                 dynamic check.
--   * just (inl d0)  -- (currently unreachable in this version)
--                       reserved for the case where the proof reduces
--                       to DerivT0 directly (no indBTB involved).
--   * just (inr pkg) -- found a topmost indBTB; pkg holds e/v1/v2,
--                       WellFormedIndBT witness, base/step lifted to
--                       DerivT0 via rankZero, and an IndBTContext0
--                       (atomic e) bot path (initially  hole bot ).
--
-- F is taken as a free index + Eq F bot witness so all 40 DerivTBounded
-- constructors are matchable (sidesteps the substF non-injectivity
-- of ruleInstB at output bot).
--
-- The rank index is taken via NatLE r 1 rather than fixed rank 1, so
-- the natMax-rank constructors (ruleTransB, mpB, indBTB) are also
-- matchable (Agda's unifier cannot invert  natMax r1 r2 = suc zero
-- directly; the LE bound provides the necessary refinement).

module BRA2.FindIndBT where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.MaxVar using (Geq ; geqZero ; geqSuc)
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded ; natMax)
open import BRA2.NatMaxLemmas
open import BRA2.WellFormedIndBT
open import BRA2.IndBTContext0
open import BRA2.SubstCompose using (maxVarEq)
open import BRA2.BoundedReductionRankZero using (rankZero)
open import BRA2.RankAtMost1Open using (natLE_zero_eq)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- Local Or.

data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

------------------------------------------------------------------------
-- IndBTPackage.

record IndBTPackage : Set where
  constructor mkPkg
  field
    pkgE     : Equation
    pkgV1    : Nat
    pkgV2    : Nat
    pkgWF    : WellFormedIndBT pkgE pkgV1 pkgV2
    pkgBase  : O.DerivT0 (atomic (substEq zero O pkgE))
    pkgStep  : O.DerivT0 ((atomic (substEq zero (var pkgV1) pkgE))
                          imp ((atomic (substEq zero (var pkgV2) pkgE))
                               imp (atomic (substEq zero (ap2 Pair (var pkgV1) (var pkgV2)) pkgE))))
    pkgCtx   : IndBTContext0 (atomic pkgE) bot
open IndBTPackage public

------------------------------------------------------------------------
-- Decision procedures for WellFormedIndBT components.

decideGeqSuc :
  (n m : Nat) -> Maybe (Geq n m) -> Maybe (Geq (suc n) (suc m))
decideGeqSuc _ _ (just ge) = just (geqSuc ge)
decideGeqSuc _ _ nothing   = nothing

decideGeq : (n m : Nat) -> Maybe (Geq n m)
decideGeq n       zero    = just (geqZero n)
decideGeq zero    (suc _) = nothing
decideGeq (suc n) (suc m) = decideGeqSuc n m (decideGeq n m)

decideNotEqNatHelper : (b : Bool) -> Maybe (Eq b false)
decideNotEqNatHelper false = just refl
decideNotEqNatHelper true  = nothing

decideNotEqNat : (v w : Nat) -> Maybe (Eq (natEq v w) false)
decideNotEqNat v w = decideNotEqNatHelper (natEq v w)

mkWellFormedFromDecisions :
  {e : Equation} {v1 v2 : Nat} ->
  Maybe (FreshEq v1 e) -> Maybe (FreshEq v2 e) -> Maybe (NotEqNat v2 v1) ->
  Maybe (WellFormedIndBT e v1 v2)
mkWellFormedFromDecisions (just f1) (just f2) (just nq) = just (mkWellFormed f1 f2 nq)
mkWellFormedFromDecisions nothing   _         _         = nothing
mkWellFormedFromDecisions (just _)  nothing   _         = nothing
mkWellFormedFromDecisions (just _)  (just _)  nothing   = nothing

decideWellFormed :
  (e : Equation) (v1 v2 : Nat) ->
  Maybe (WellFormedIndBT e v1 v2)
decideWellFormed e v1 v2 =
  mkWellFormedFromDecisions
    (decideGeq v1 (maxVarEq e))
    (decideGeq v2 (maxVarEq e))
    (decideNotEqNat v2 v1)

------------------------------------------------------------------------
-- buildPackageFromIndBT : build the IndBTPackage given:
--   * indBTB args (e, v1, v2),
--   * Eq (atomic e) bot witness for the path,
--   * WellFormedIndBT witness,
--   * inner premises base/step at rank 0.

buildPackageFromIndBT :
  (e : Equation) (v1 v2 : Nat) ->
  Eq (atomic e) bot ->
  WellFormedIndBT e v1 v2 ->
  {l1 l2 : Nat} ->
  DerivTBounded zero l1 (atomic (substEq zero O e)) ->
  DerivTBounded zero l2
    ((atomic (substEq zero (var v1) e))
     imp ((atomic (substEq zero (var v2) e))
          imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  IndBTPackage
buildPackageFromIndBT e v1 v2 eqOut wf base step =
  mkPkg e v1 v2 wf
    (rankZero base) (rankZero step)
    (eqSubst (\ F -> IndBTContext0 (atomic e) F) eqOut (hole (atomic e)))

packageOrFail :
  (e : Equation) (v1 v2 : Nat) ->
  Eq (atomic e) bot ->
  Maybe (WellFormedIndBT e v1 v2) ->
  {l1 l2 : Nat} ->
  DerivTBounded zero l1 (atomic (substEq zero O e)) ->
  DerivTBounded zero l2
    ((atomic (substEq zero (var v1) e))
     imp ((atomic (substEq zero (var v2) e))
          imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
packageOrFail e v1 v2 eqOut (just wf) base step =
  just (inr (buildPackageFromIndBT e v1 v2 eqOut wf base step))
packageOrFail _ _ _ _ nothing _ _ = nothing

------------------------------------------------------------------------
-- The main function.
--
-- Doubly-generic: F is a free index + Eq F bot witness; rank is a
-- free index + NatLE r 1 bound.  This makes all 40 DerivTBounded
-- constructors matchable.

findIndBTAux :
  (F : Formula) {l : Nat} {r : Nat} ->
  NatLE r (suc zero) ->
  DerivTBounded r l F ->
  Eq F bot ->
  Maybe (Or (O.DerivT0 F) IndBTPackage)

-- Atomic computation axioms.
findIndBTAux _ _ (B.axIB _ _ _)              _ = nothing
findIndBTAux _ _ (B.axFstB _ _ _ _)          _ = nothing
findIndBTAux _ _ (B.axSndB _ _ _ _)          _ = nothing
findIndBTAux _ _ (B.axFstLfB _ _)            _ = nothing
findIndBTAux _ _ (B.axSndLfB _ _)            _ = nothing
findIndBTAux _ _ (B.axConstB _ _ _ _)        _ = nothing
findIndBTAux _ _ (B.axCompB _ _ _ _ _)       _ = nothing
findIndBTAux _ _ (B.axComp2B _ _ _ _ _ _)    _ = nothing
findIndBTAux _ _ (B.axLiftB _ _ _ _ _)       _ = nothing
findIndBTAux _ _ (B.axPostB _ _ _ _ _ _)     _ = nothing
findIndBTAux _ _ (B.axFanB _ _ _ _ _ _ _)    _ = nothing
findIndBTAux _ _ (B.axZB _ _ _)              _ = nothing
findIndBTAux _ _ (B.axTreeRecLfB _ _ _ _ _)  _ = nothing
findIndBTAux _ _ (B.axTreeRecNdB _ _ _ _ _ _ _) _ = nothing
findIndBTAux _ _ (B.axIfLfLB _ _ _ _)        _ = nothing
findIndBTAux _ _ (B.axIfLfNB _ _ _ _ _ _)    _ = nothing
findIndBTAux _ _ (B.axIfLfLLB _ _)           _ = nothing
findIndBTAux _ _ (B.axIfLfNLB _ _ _ _)       _ = nothing
findIndBTAux _ _ (B.axTreeEqLLB _ _)         _ = nothing
findIndBTAux _ _ (B.axTreeEqLNB _ _ _ _)     _ = nothing
findIndBTAux _ _ (B.axTreeEqNLB _ _ _ _)     _ = nothing
findIndBTAux _ _ (B.axTreeEqNNB _ _ _ _ _ _) _ = nothing
findIndBTAux _ _ (B.axGoodsteinB _ _ _ _)    _ = nothing
findIndBTAux _ _ (B.axReflB _ _ _)           _ = nothing

-- Structural rules : pending the wrapped-traversal extension.
findIndBTAux _ _ (B.ruleSymB _)              _ = nothing
findIndBTAux _ _ (B.ruleTransB _ _)          _ = nothing
findIndBTAux _ _ (B.cong1B _ _)              _ = nothing
findIndBTAux _ _ (B.congLB _ _ _)            _ = nothing
findIndBTAux _ _ (B.congRB _ _ _)            _ = nothing

-- Equational implication / propositional axioms.
findIndBTAux _ _ (B.axEqTransB _ _ _ _ _)    _ = nothing
findIndBTAux _ _ (B.axEqCong1B _ _ _ _ _)    _ = nothing
findIndBTAux _ _ (B.axEqCongLB _ _ _ _ _ _)  _ = nothing
findIndBTAux _ _ (B.axEqCongRB _ _ _ _ _ _)  _ = nothing
findIndBTAux _ _ (B.axKB _ _ _ _)            _ = nothing
findIndBTAux _ _ (B.axSB _ _ _ _ _)          _ = nothing
findIndBTAux _ _ (B.axNegB _ _ _ _)          _ = nothing

-- Rules of inference : pending.
findIndBTAux _ _ (B.mpB _ _)                 _ = nothing
findIndBTAux _ _ (B.ruleInstB _ _ _)         _ = nothing

-- indBTB : the handled case.  NatLE bound (leSuc le') exposes
-- le' : NatLE (natMax r1 r2) 0, which natLE_zero_eq turns into
-- Eq (natMax r1 r2) 0; natMaxZero then gives (r1 = 0, r2 = 0).
-- Lift premises to rank 0 via eqSubst, then build the package.
findIndBTAux _ (leSuc le') (B.indBTB {r1} {l1} {r2} {l2} e v1 v2 base step) refl =
  let maxEqZ : Eq (natMax r1 r2) zero
      maxEqZ = natLE_zero_eq le'
      pair    = natMaxZero r1 r2 maxEqZ
      r1Eq0   = fst pair
      r2Eq0   = snd pair
      baseAt0 = eqSubst (\ rk -> DerivTBounded rk l1 (atomic (substEq zero O e))) r1Eq0 base
      stepAt0 = eqSubst (\ rk -> DerivTBounded rk l2 _) r2Eq0 step
  in packageOrFail e v1 v2 refl (decideWellFormed e v1 v2) baseAt0 stepAt0

-- indBT2B : pending.
findIndBTAux _ _ (B.indBT2B _ _ _ _ _ _ _ _ _) _ = nothing

------------------------------------------------------------------------
-- Public entry point.

findIndBT :
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
findIndBT d = findIndBTAux bot (natLERefl (suc zero)) d refl
