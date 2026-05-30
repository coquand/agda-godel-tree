{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SubstCongInternal -- the "under-hypothesis" variants of
-- BRA3.Substitutivity.substT_cong / substF_cong .
--
-- Given a Deriv-of-imp  Deriv (imp Hyp (eqF a b))  rather than a
-- naked  Deriv (eqF a b) , produce a Deriv-of-imp form of the
-- substitutivity result:
--
--   substT_cong_imp :  Deriv (imp Hyp (eqF a b))  -> (t : Term) ->
--                       Deriv (imp Hyp (eqF (substT k a t) (substT k b t)))
--
--   substF_cong_imp :  Deriv (imp Hyp (eqF a b))  -> (F : Formula) ->
--                       Deriv (imp Hyp (imp (substF k a F) (substF k b F)))
--
-- The proofs mirror substT_cong / substF_cong but with every
-- Deriv wrapped in  imp Hyp .  Standard Hilbert combinators
-- (axK, axS, mp, liftP, bComb, bCombTwo, compI) suffice; no new
-- axioms.

module BRA4.SubstCongInternal where

open import BRA4.Base
open import BRA4.SubLeqIdentities using ( transUnderOne )

open import BRA3.Logic        using ( impTrans ; eqSymImp )
open import BRA3.Equational   using ( axRefl ; ruleSym ; ruleTrans ; cong1 ; congL ; congR )
open import BRA3.Contrapositive
  using ( identP ; liftP ; bComb ; bCombTwo ; compI
        ; axContrapos )

------------------------------------------------------------------------
-- Hilbert composition helpers (under-hypothesis form).

-- composeUnder : from  imp Hyp (imp A B)  and  imp Hyp (imp B C) ,
--   derive  imp Hyp (imp A C) .

composeUnder :
  (Hyp A B Cf : Formula) ->
  Deriv (imp Hyp (imp A B)) ->
  Deriv (imp Hyp (imp B Cf)) ->
  Deriv (imp Hyp (imp A Cf))
composeUnder Hyp A B Cf h1 h2 =
  let h2_lifted : Deriv (imp Hyp (imp A (imp B Cf)))
      h2_lifted = bComb (liftP Hyp (axK (imp B Cf) A)) h2
  in bCombTwo h2_lifted h1

------------------------------------------------------------------------
-- The "swap" Hilbert combinator:
--    imp (imp X (imp Y Z)) (imp Y (imp X Z))
--
-- Derived from axK + axS via the standard SKI construction.

swap-imp :
  (X Y Z : Formula) ->
  Deriv (imp (imp X (imp Y Z)) (imp Y (imp X Z)))
swap-imp X Y Z =
  let A : Formula
      A = imp X (imp Y Z)

      P : Formula
      P = imp X Y

      Q : Formula
      Q = imp X Z

      stepA : Deriv (imp A (imp P Q))
      stepA = axS X Y Z

      stepB : Deriv (imp Y P)
      stepB = axK Y X

      -- step_inner : imp A (imp (imp P Q) (imp Y (imp P Q)))
      step_inner : Deriv (imp A (imp (imp P Q) (imp Y (imp P Q))))
      step_inner = liftP A (axK (imp P Q) Y)

      step_AYpq : Deriv (imp A (imp Y (imp P Q)))
      step_AYpq = bComb step_inner stepA

      stepB_under_A : Deriv (imp A (imp Y P))
      stepB_under_A = liftP A stepB
  in bCombTwo step_AYpq stepB_under_A

------------------------------------------------------------------------
-- Internalised implication-composition combinators.
--
-- composeImpR_axiom :  imp (imp Y Z) (imp (imp X Y) (imp X Z)) .
--   ("reverse" composition: takes (Y -> Z) first, then (X -> Y))
--
-- composeImpL_axiom :  imp (imp X Y) (imp (imp Y Z) (imp X Z)) .
--   ("forward" composition: takes (X -> Y) first, then (Y -> Z))

composeImpR_axiom :
  (X Y Z : Formula) ->
  Deriv (imp (imp Y Z) (imp (imp X Y) (imp X Z)))
composeImpR_axiom X Y Z =
  compI (axK (imp Y Z) X) (axS X Y Z)

composeImpL_axiom :
  (X Y Z : Formula) ->
  Deriv (imp (imp X Y) (imp (imp Y Z) (imp X Z)))
composeImpL_axiom X Y Z =
  mp (swap-imp (imp Y Z) (imp X Y) (imp X Z))
     (composeImpR_axiom X Y Z)

------------------------------------------------------------------------
-- Under-hypothesis versions of composeImpL / composeImpR.

composeImpL_under :
  (Hyp Hf Hf' Qf : Formula) ->
  Deriv (imp Hyp (imp Hf Hf')) ->
  Deriv (imp Hyp (imp (imp Hf' Qf) (imp Hf Qf)))
composeImpL_under Hyp Hf Hf' Qf h =
  bComb (liftP Hyp (composeImpL_axiom Hf Hf' Qf)) h

composeImpR_under :
  (Hyp Pf Qf Qf' : Formula) ->
  Deriv (imp Hyp (imp Qf Qf')) ->
  Deriv (imp Hyp (imp (imp Pf Qf) (imp Pf Qf')))
composeImpR_under Hyp Pf Qf Qf' h =
  bComb (liftP Hyp (composeImpR_axiom Pf Qf Qf')) h

------------------------------------------------------------------------
-- The internalised  appendEqRight :
--    imp (eqF b c) (imp (eqF a b) (eqF a c)) .
--
-- Carneiro-style: derive the imp form from  ax_eqTrans + eqSymImp .

appendEqRight_internal :
  (a b c : Term) ->
  Deriv (imp (eqF b c) (imp (eqF a b) (eqF a c)))
appendEqRight_internal a b c =
  let Hyp : Formula
      Hyp = eqF b c

      ax_inner : Deriv (imp Hyp (imp (eqF b a) (eqF c a)))
      ax_inner = ax_eqTrans b c a

      sym_ab : Deriv (imp Hyp (imp (eqF a b) (eqF b a)))
      sym_ab = liftP Hyp (eqSymImp a b)

      sym_ca : Deriv (imp Hyp (imp (eqF c a) (eqF a c)))
      sym_ca = liftP Hyp (eqSymImp c a)

      step1 : Deriv (imp Hyp (imp (eqF a b) (eqF c a)))
      step1 = composeUnder Hyp (eqF a b) (eqF b a) (eqF c a) sym_ab ax_inner

  in composeUnder Hyp (eqF a b) (eqF c a) (eqF a c) step1 sym_ca

------------------------------------------------------------------------
-- substT_cong_imp : structural induction on the term.

substT_cong_imp :
  (Hyp : Formula) (k : Nat) (a b : Term) ->
  Deriv (imp Hyp (eqF a b)) ->
  (t : Term) ->
  Deriv (imp Hyp (eqF (substT k a t) (substT k b t)))
substT_cong_imp Hyp k a b h O = liftP Hyp (axRefl O)
substT_cong_imp Hyp k a b h (var m) = aux (natEq k m) refl
  where
    aux : (bb : Bool) -> Eq (natEq k m) bb ->
          Deriv (imp Hyp (eqF (boolCase bb a (var m))
                               (boolCase bb b (var m))))
    aux true  _ = h
    aux false _ = liftP Hyp (axRefl (var m))
substT_cong_imp Hyp k a b h (ap1 f t) =
  let ih = substT_cong_imp Hyp k a b h t
      cng = ax_eqCong1 f (substT k a t) (substT k b t)
  in compI ih cng
substT_cong_imp Hyp k a b h (ap2 g t1 t2) =
  let ih1 = substT_cong_imp Hyp k a b h t1
      ih2 = substT_cong_imp Hyp k a b h t2

      L1 : Term
      L1 = substT k a t1
      L2 : Term
      L2 = substT k b t1
      R1 : Term
      R1 = substT k a t2
      R2 : Term
      R2 = substT k b t2

      step1 : Deriv (imp Hyp (eqF (ap2 g L1 R1) (ap2 g L2 R1)))
      step1 = compI ih1 (ax_eqCongL g L1 L2 R1)

      step2 : Deriv (imp Hyp (eqF (ap2 g L2 R1) (ap2 g L2 R2)))
      step2 = compI ih2 (ax_eqCongR g R1 R2 L2)
  in transUnderOne step1 step2

------------------------------------------------------------------------
-- substF_cong_imp : structural induction on the formula.

substF_cong_imp :
  (Hyp : Formula) (k : Nat) (a b : Term) ->
  Deriv (imp Hyp (eqF a b)) ->
  (F : Formula) ->
  Deriv (imp Hyp (imp (substF k a F) (substF k b F)))
substF_cong_imp Hyp k a b h (atomic (eqn l r)) =
  let L1 : Term
      L1 = substT k a l
      L2 : Term
      L2 = substT k b l
      R1 : Term
      R1 = substT k a r
      R2 : Term
      R2 = substT k b r

      eL : Deriv (imp Hyp (eqF L1 L2))
      eL = substT_cong_imp Hyp k a b h l

      eR : Deriv (imp Hyp (eqF R1 R2))
      eR = substT_cong_imp Hyp k a b h r

      -- step1 : imp Hyp (imp (eqF L1 R1) (eqF L2 R1)) .
      step1 : Deriv (imp Hyp (imp (eqF L1 R1) (eqF L2 R1)))
      step1 = compI eL (ax_eqTrans L1 L2 R1)

      -- step2 : imp Hyp (imp (eqF L2 R1) (eqF L2 R2)) .
      step2 : Deriv (imp Hyp (imp (eqF L2 R1) (eqF L2 R2)))
      step2 = compI eR (appendEqRight_internal L2 R1 R2)

  in composeUnder Hyp (eqF L1 R1) (eqF L2 R1) (eqF L2 R2) step1 step2
substF_cong_imp Hyp k a b h (neg p) =
  let h_rev : Deriv (imp Hyp (eqF b a))
      h_rev = compI h (eqSymImp a b)

      ih_p_rev : Deriv (imp Hyp (imp (substF k b p) (substF k a p)))
      ih_p_rev = substF_cong_imp Hyp k b a h_rev p

      contra : Deriv (imp (imp (substF k b p) (substF k a p))
                           (imp (neg (substF k a p)) (neg (substF k b p))))
      contra = axContrapos (substF k b p) (substF k a p)

      contra_lifted : Deriv (imp Hyp (imp (imp (substF k b p) (substF k a p))
                                            (imp (neg (substF k a p))
                                                  (neg (substF k b p)))))
      contra_lifted = liftP Hyp contra
  in bComb contra_lifted ih_p_rev
substF_cong_imp Hyp k a b h (imp p q) =
  let pA : Formula
      pA = substF k a p
      pB : Formula
      pB = substF k b p
      qA : Formula
      qA = substF k a q
      qB : Formula
      qB = substF k b q

      h_rev : Deriv (imp Hyp (eqF b a))
      h_rev = compI h (eqSymImp a b)

      E_p : Deriv (imp Hyp (imp pB pA))
      E_p = substF_cong_imp Hyp k b a h_rev p

      E_q : Deriv (imp Hyp (imp qA qB))
      E_q = substF_cong_imp Hyp k a b h q

      step1 : Deriv (imp Hyp (imp (imp pA qA) (imp pB qA)))
      step1 = composeImpL_under Hyp pB pA qA E_p

      step2 : Deriv (imp Hyp (imp (imp pB qA) (imp pB qB)))
      step2 = composeImpR_under Hyp pB qA qB E_q

  in composeUnder Hyp (imp pA qA) (imp pB qA) (imp pB qB) step1 step2
