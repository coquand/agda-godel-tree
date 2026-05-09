{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.RankDecrementSymTrans
-- T2 of BRA2/NEXT-SESSION-RANKDECREMENT.md: case helpers for the
-- ruleSymB and ruleTransB cases of the eventual rank-decrement
-- function.
--
-- Two related deliveries:
--
--   (T2.A)  decrCaseRuleSym   -- ruleSymB case (trivial wrapper).
--   (T2.B)  decrCaseRuleTrans -- ruleTransB case using natMaxIdem to
--                                collapse  natMax rOut rOut = rOut .
--
-- Plus supporting infrastructure:
--
--   (S.1)   natMaxLE_split    -- NatLE distributes over natMax;
--                                derived from natMaxLE_L / natMaxLE_R
--                                in BRA2.NatMaxLemmas.
--   (S.2)   natMaxSucPred     -- demonstration that natMaxSucDecompose
--                                can be invoked and case-split on the
--                                MaxSucEvidence it returns.
--
-- Design choice.  Two equivalent rank-decrement signatures are
-- possible:
--
--   (i)  Exact-rank original (BoundedReduction.RankDecrement) :
--          (rOut : Nat) -> DerivTBounded (suc rOut) l bot ->
--          Sigma Nat (\ l' -> DerivTBounded rOut l' bot) .
--        Inner ruleTransB premises have ranks  r1, r2  with
--        natMax r1 r2 = suc rOut .  Per-side dispatch via
--        natMaxSucDecompose (Left/Right) identifies which side
--        carries the successor.  Recurse on that side; weaken the
--        other.  Requires a rank-weakening lemma.
--
--   (ii) Generalised  (rOut : Nat) (rIn : Nat) {F : Formula} ->
--          NatLE rIn (suc rOut) ->
--          DerivTBounded rIn l F ->
--          Sigma Nat (\ l' -> DerivTBounded rOut l' F) .
--        Inner ruleTransB premises  r1 r2  satisfy
--        natMax r1 r2 ≤ suc rOut .  Split via natMaxLE_split and
--        recurse on both sides; combine via natMaxIdem.  No
--        weakening lemma needed.  Generalised  F  also sidesteps
--        Agda's substF inversion issue with ruleInstB.
--
-- T2 delivers the generalised-signature case helpers as the actual
-- proof obligation; the natMaxSucDecompose plumbing for (i) is
-- exposed via natMaxSucPred (S.2) for future reference if (i) is
-- preferred later.

module BRA2.RankDecrementSymTrans where

open import BRA2.Base
open import BRA2.Term using (Term ; Equation ; eqn)
open import BRA2.Formula using (Formula ; atomic)
import BRA2.DerivTBounded as B
open import BRA2.DerivTBounded using (DerivTBounded ; natMax)
open import BRA2.NatMaxLemmas

------------------------------------------------------------------------
-- The generalised rank-decrement spec.
--
-- The eventual main function will have this signature (option (ii)
-- in the comment above).  Specialising  rIn := suc rOut  with
-- bound  natLERefl (suc rOut)  and  F := bot  recovers the original
-- BoundedReduction.RankDecrement.

RankDecGen : Set
RankDecGen =
  {l : Nat} {F : Formula} (rOut : Nat) (rIn : Nat) ->
  NatLE rIn (suc rOut) ->
  DerivTBounded rIn l F ->
  Sigma Nat (\ l' -> DerivTBounded rOut l' F)

------------------------------------------------------------------------
-- (S.1) NatLE distributes through natMax.
--
-- If  natMax a b ≤ c , then  a ≤ c  and  b ≤ c .  This is the
-- bound-splitting lemma that the generalised ruleTransB case needs:
-- the input bound  natMax r1 r2 ≤ suc rOut  becomes
-- ( r1 ≤ suc rOut , r2 ≤ suc rOut ), so each premise can be recursed
-- on with the same bound.

natMaxLE_split :
  {a b c : Nat} ->
  NatLE (natMax a b) c ->
  Sigma (NatLE a c) (\ _ -> NatLE b c)
natMaxLE_split {a} {b} le =
  mkSigma (natLETrans (natMaxLE_L a b) le)
          (natLETrans (natMaxLE_R a b) le)

------------------------------------------------------------------------
-- (T2.A) ruleSymB case.
--
-- Given the rank-decremented inner derivation d', wrap with
-- ruleSymB.  Rank is preserved by ruleSymB, so no rank bookkeeping.

decrCaseRuleSym :
  {l' : Nat} (rOut : Nat) {t u : Term} ->
  DerivTBounded rOut l' (atomic (eqn t u)) ->
  DerivTBounded rOut l' (atomic (eqn u t))
decrCaseRuleSym _ d' = B.ruleSymB d'

------------------------------------------------------------------------
-- (T2.B) ruleTransB case.
--
-- Given rank-decremented inner derivations  d1' (rank rOut) and  d2'
-- (rank rOut), produce the trans at rank rOut.  ruleTransB combines
-- ranks via natMax, so the output has rank  natMax rOut rOut , which
-- equals  rOut  by natMaxIdem.  Transport via eqSubst.

decrCaseRuleTrans :
  (rOut : Nat) {l1' l2' : Nat} {t u v : Term} ->
  DerivTBounded rOut l1' (atomic (eqn t u)) ->
  DerivTBounded rOut l2' (atomic (eqn u v)) ->
  DerivTBounded rOut (natMax l1' l2') (atomic (eqn t v))
decrCaseRuleTrans rOut {l1'} {l2'} {t} {_} {v} d1' d2' =
  let combined : DerivTBounded (natMax rOut rOut)
                                (natMax l1' l2')
                                (atomic (eqn t v))
      combined = B.ruleTransB d1' d2'
      eqRR : Eq (natMax rOut rOut) rOut
      eqRR = natMaxIdem rOut
  in eqSubst (\ rr -> DerivTBounded rr (natMax l1' l2') (atomic (eqn t v)))
              eqRR combined

------------------------------------------------------------------------
-- (S.2) natMaxSucDecompose plumbing demonstration.
--
-- For the EXACT-rank original spec (alternative formulation), the
-- ruleTransB case requires identifying which premise carries the
-- successor: given  natMax r1 r2 = suc rOut , at least one of  r1,
-- r2  is a successor.  natMaxSucDecompose returns a MaxSucEvidence
-- witness; this function demonstrates pattern-matching on it.
--
-- natMaxSucPred returns the predecessor of whichever side
-- contributes the successor.  This is the rank to recurse on in the
-- exact-rank ruleTransB case.

pickPred : {r1 r2 rOut : Nat} -> MaxSucEvidence r1 r2 rOut -> Nat
pickPred (maxFromLeft  r1' _ _ _) = r1'
pickPred (maxFromRight r2' _ _ _) = r2'

natMaxSucPred :
  (r1 r2 rOut : Nat) ->
  Eq (natMax r1 r2) (suc rOut) ->
  Nat
natMaxSucPred r1 r2 rOut eq = pickPred (natMaxSucDecompose r1 r2 rOut eq)

-- Companion: the predecessor satisfies  NatLE pred rOut .

pickLE :
  {r1 r2 rOut : Nat} (ev : MaxSucEvidence r1 r2 rOut) ->
  NatLE (pickPred ev) rOut
pickLE (maxFromLeft  _ _ le_r1' _) = le_r1'
pickLE (maxFromRight _ _ le_r2' _) = le_r2'

natMaxSucPred_LE :
  (r1 r2 rOut : Nat) (eq : Eq (natMax r1 r2) (suc rOut)) ->
  NatLE (natMaxSucPred r1 r2 rOut eq) rOut
natMaxSucPred_LE r1 r2 rOut eq = pickLE (natMaxSucDecompose r1 r2 rOut eq)
