{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.LeqMono -- Cantor monotonicity lemmas for the BRA4 sbt at
-- ap1 / ap2 closures.
--
-- We prove:
--   leq_sigma_right : leq B (sigma A B)
--   leq_pi_right    : leq B (pi A B)         (via T114 + leq_sigma_right)
--   leq_trans       : leq a b -> leq b c -> leq a c
--
-- These are the BRA-Deriv-level facts that "sub-positions of a Cantor pair
-- are bounded by the predecessor of the pair".  Used in S4 to discharge
-- the `leq ct K` hypothesis of stabilityP_sbt_at.

module BRA4.LeqMono where

open import BRA4.Base

open import BRA3.Church       using ( pi ; sigma ; tau ; sub ; T36 ; T114 )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.ChurchT84    using ( T84 )
open import BRA3.ChurchT85    using ( T85 )
open import BRA3.RuleInst2    using ( ruleInst2 )

import BRA3.RuleInst2
open BRA3.RuleInst2 using
  ( NatLe ; le-suc-right ; le-trans ; maxN ; maxN-le-left ; maxN-le-right
  ; maxVarT ; substT_above_max ; natEq-refl )

------------------------------------------------------------------------
-- T85 specialized:  leq A (sigma A B)  (universal in A, B : Term).

leq_sigma_left : (A B : Term) -> Deriv (leq A (ap2 sigma A B))
leq_sigma_left A B = ruleInst2 0 A 1 B refl T85

------------------------------------------------------------------------
-- T36 specialized:  sigma A B = sigma B A.

T36_at : (A B : Term) -> Deriv (eqF (ap2 sigma A B) (ap2 sigma B A))
T36_at A B = ruleInst2 0 A 1 B refl T36

------------------------------------------------------------------------
-- leq_sigma_right :  leq B (sigma A B).

leq_sigma_right : (A B : Term) -> Deriv (leq B (ap2 sigma A B))
leq_sigma_right A B =
  let l1 : Deriv (eqF (ap2 sub B (ap2 sigma B A)) O)
      l1 = leq_sigma_left B A

      eqBA : Deriv (eqF (ap2 sigma B A) (ap2 sigma A B))
      eqBA = T36_at B A

      cong_sub :
        Deriv (eqF (ap2 sub B (ap2 sigma B A)) (ap2 sub B (ap2 sigma A B)))
      cong_sub = congR sub B eqBA

      cong_sub_sym :
        Deriv (eqF (ap2 sub B (ap2 sigma A B)) (ap2 sub B (ap2 sigma B A)))
      cong_sub_sym = ruleSym cong_sub
  in ruleTrans cong_sub_sym l1

------------------------------------------------------------------------
-- leq_pi_right :  leq B (pi A B).

T114_at : (A B : Term) -> Deriv (eqF (ap2 pi A B) (ap2 sigma (ap1 tau (ap2 sigma A B)) B))
T114_at A B = ruleInst2 0 A 1 B refl T114

leq_pi_right : (A B : Term) -> Deriv (leq B (ap2 pi A B))
leq_pi_right A B =
  let X : Term
      X = ap1 tau (ap2 sigma A B)

      lemSig : Deriv (eqF (ap2 sub B (ap2 sigma X B)) O)
      lemSig = leq_sigma_right X B

      eqPi : Deriv (eqF (ap2 pi A B) (ap2 sigma X B))
      eqPi = T114_at A B

      cong_sub :
        Deriv (eqF (ap2 sub B (ap2 pi A B)) (ap2 sub B (ap2 sigma X B)))
      cong_sub = congR sub B eqPi
  in ruleTrans cong_sub lemSig

------------------------------------------------------------------------
-- Freshness helper for leq_trans.

private
  -- A fresh variable index above maxVarT of three Terms.  We add TWO
  -- leading sucs so that  natEq 0 f  and  natEq 1 f  both reduce to false
  -- definitionally (Agda needs the structure suc (suc _) to fire the
  -- false branches of natEq).
  freshABC : Term -> Term -> Term -> Nat
  freshABC a b c = suc (suc (maxN (maxVarT a) (maxN (maxVarT b) (maxVarT c))))

  freshABC_above_a : (a b c : Term) -> NatLe (maxVarT a) (freshABC a b c)
  freshABC_above_a a b c =
    le-suc-right
      (le-suc-right
        (maxN-le-left (maxVarT a) (maxN (maxVarT b) (maxVarT c))))

  freshABC_above_b : (a b c : Term) -> NatLe (maxVarT b) (freshABC a b c)
  freshABC_above_b a b c =
    let leA : NatLe (maxVarT b) (maxN (maxVarT b) (maxVarT c))
        leA = maxN-le-left (maxVarT b) (maxVarT c)
        leB : NatLe (maxN (maxVarT b) (maxVarT c))
                     (maxN (maxVarT a) (maxN (maxVarT b) (maxVarT c)))
        leB = maxN-le-right (maxVarT a) (maxN (maxVarT b) (maxVarT c))
    in le-suc-right (le-suc-right (le-trans leA leB))

------------------------------------------------------------------------
-- leq_trans :  leq a b -> leq b c -> leq a c.
--
-- Proof technique: c-renaming exactly as in stabilityP_subT_at.
--   1. Rename T84's var 2 -> var f for f fresh in a, b, c.
--   2. ruleInst2 var 0 := a, var 1 := b simultaneously.
--   3. ruleInst f := c, bridging substT f c a = a and substT f c b = b
--      via substT_above_max.
--
-- Note: ruleInst2 0 a 1 b is OK even if a, b contain var 0 or 1, because
-- simSubst keeps the substituents verbatim.  After this, only var f
-- remains in the formula, and (var f) substitutes cleanly.

leq_trans :
  (a b c : Term) ->
  Deriv (leq a b) ->
  Deriv (leq b c) ->
  Deriv (leq a c)
leq_trans a b c lab lbc =
  let f : Nat
      f = freshABC a b c

      -- Step 1: rename T84's var 2 to var f.  T84 has form
      --   imp (leq v0 v1) (imp (leq v1 v2) (leq v0 v2))
      -- After ruleInst 2 (var f), formula has v0, v1, vf.
      r2 : Deriv (imp (leq (var 0) (var 1)) (imp (leq (var 1) (var f)) (leq (var 0) (var f))))
      r2 = ruleInst 2 (var f) T84

      -- Step 2: ruleInst2 0 a 1 b refl r2.  Simultaneous substitution of
      -- var 0 := a, var 1 := b.  Substituents stay verbatim.
      r01 : Deriv (imp (leq a b) (imp (leq b (var f)) (leq a (var f))))
      r01 = ruleInst2 0 a 1 b refl r2

      -- Step 3: ruleInst f c r01.  Substitutes var f := c.
      -- This also applies substT f c to a and b in the formula, and to
      -- (var f) which should reduce to c via natEq f f = true.

      -- Pre-form using substT to match Agda's normalized form.
      r_pre : Deriv (imp (leq (substT f c a) (substT f c b)) (imp (leq (substT f c b) (substT f c (var f))) (leq (substT f c a) (substT f c (var f)))))
      r_pre = ruleInst f c r01

      bridge_vf : Eq (substT f c (var f)) c
      bridge_vf = eqCong (\ b' -> boolCase b' c (var f)) (natEq-refl f)

      r_raw : Deriv (imp (leq (substT f c a) (substT f c b)) (imp (leq (substT f c b) c) (leq (substT f c a) c)))
      r_raw = eqSubst (\ x -> Deriv (imp (leq (substT f c a) (substT f c b)) (imp (leq (substT f c b) x) (leq (substT f c a) x))))
                       bridge_vf r_pre

      -- Bridges: substT f c a = a, substT f c b = b by freshness.
      bridge_a : Eq (substT f c a) a
      bridge_a = substT_above_max f a c (freshABC_above_a a b c)

      bridge_b : Eq (substT f c b) b
      bridge_b = substT_above_max f b c (freshABC_above_b a b c)

      -- Clean up first arg of a-occurrences.
      r_a : Deriv (imp (leq a (substT f c b)) (imp (leq (substT f c b) c) (leq a c)))
      r_a = eqSubst (\ x -> Deriv (imp (leq x (substT f c b)) (imp (leq (substT f c b) c) (leq x c))))
                     bridge_a r_raw

      r : Deriv (imp (leq a b) (imp (leq b c) (leq a c)))
      r = eqSubst (\ x -> Deriv (imp (leq a x) (imp (leq x c) (leq a c))))
                   bridge_b r_a
  in mp (mp r lab) lbc
