{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTCompleteRec -- the unified, structurally-recursive
-- completeness theorem.  Composes the 17 per-constructor lemmas
-- of BRA4.ThmTCompleteAll .  No  Closed -witness premise :  every
-- per-axiom lemma is now Closed-free  (the multi-var axiom cases
-- use BRA3.RuleInst2.three_step_F  /  BRA4.RuleInst3.five_step_F
-- internally to bridge the sb-wrap cascade ; see
--  BRA4.ThmTCompleteAxClosed  and  BRA4.ThmTCompleteAxFunctor ).
--
--   thmT_complete_rec :
--     {P : Formula} (d : Deriv P) ->
--     Deriv (eqF (ap1 thmT (encode d)) (codeFormula P))

module BRA4.ThmTCompleteRec where

open import BRA4.Base
open import BRA4.Encode using ( encode )
open import BRA4.ThmT   using ( thmT )
open import BRA4.Code   using ( codeFormula )

open import BRA4.ThmTCompleteAll

------------------------------------------------------------------------
-- Recursive thmT_complete .

thmT_complete_rec :
  {P : Formula} (d : Deriv P) ->
  Deriv (eqF (ap1 thmT (encode d)) (codeFormula P))

thmT_complete_rec ax_succ_nonzero =
  thmT_complete_ax_succ_nonzero

thmT_complete_rec (ax_o t) =
  thmT_complete_ax_o t

thmT_complete_rec (ax_u t) =
  thmT_complete_ax_u t

thmT_complete_rec (ax_v a b) =
  thmT_complete_ax_v a b

thmT_complete_rec (ax_eqTrans x y z) =
  thmT_complete_ax_eqTrans x y z

thmT_complete_rec (ax_eqCong1 f a b) =
  thmT_complete_ax_eqCong1 f a b

thmT_complete_rec (ax_eqCongL g a b c) =
  thmT_complete_ax_eqCongL g a b c

thmT_complete_rec (ax_eqCongR g a b c) =
  thmT_complete_ax_eqCongR g a b c

thmT_complete_rec (ax_C g h1 h2 t) =
  thmT_complete_ax_C g h1 h2 t

thmT_complete_rec (ax_R_base g h1 h2 x) =
  thmT_complete_ax_R_base g h1 h2 x

thmT_complete_rec (ax_R_step g h1 h2 x n) =
  thmT_complete_ax_R_step g h1 h2 x n

thmT_complete_rec (axK A B) =
  thmT_complete_axK A B

thmT_complete_rec (axS A B Cf) =
  thmT_complete_axS A B Cf

thmT_complete_rec (axNeg A B) =
  thmT_complete_axNeg A B

thmT_complete_rec (mp {P} {Q} dPQ dP) =
  thmT_complete_mp P Q dPQ dP
    (thmT_complete_rec dPQ)
    (thmT_complete_rec dP)

thmT_complete_rec (ruleInst k t {P} dP) =
  thmT_complete_ruleInst k t P dP (thmT_complete_rec dP)

thmT_complete_rec (ruleIndNat k {P} dB dS) =
  thmT_complete_ruleIndNat k P dB dS
    (thmT_complete_rec dB)
    (thmT_complete_rec dS)
