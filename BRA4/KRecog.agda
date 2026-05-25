{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KRecog -- Phase E2 (CHAITIN-G1-STANDARD-DIRECTION.md SS5): the search
-- RECOGNISER  hitK  (= hit_L) for the standard-route Kolmogorov formula, and
-- its bridge to  dNeg .  The standard-route analog of BRA4.ChaitinG1Neg's
-- hitNeg / dNeg_from_hitNeg, re-pointed from the provability atom to the
-- evalU K-formula  Kgt L x  (BRA4.KFormula).
--
--   hitK L out w  =  eqInd (thmT w) (negKgtCodeOf L (out w))            -- 0/1
--     -- "is thmT(w) the code of  Kgt L (out w) ?"  (codes are Nats; numeric eq)
--   dNeg_from_hitK : a firing  hitK L out w0 = 1  yields
--     thmT w0 = negKgtCodeOf L (out w0)    -- = codeFormula (Kgt L z0) once
--                                          --   z0 := out w0 is pinned numeral
--                                          --   (negKgtCodeOf_correct, E3/E4).
-- The bridge is the shipped numeric reflection  eqInd_sound  -- no thmT_at_sb,
-- no open->closed step (the codes are closed Nats).  hitK is parametric in the
-- hole projector  out : Fun1  (built concretely in E2.4 / BRA4.KOut).

module BRA4.KRecog where

open import BRA4.Base
open import BRA4.ThmT       using ( thmT )
open import BRA4.KFormula   using ( negKgtCodeOf )
open import BRA4.CountingObj using ( eqIndF ; eqIndF_eq )
open import BRA4.Counting    using ( eqInd ; eqInd_le_one )
open import BRA4.Bridge      using ( eqInd_sound )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; axComp )

------------------------------------------------------------------------
-- The recogniser indicator, parametric in the hole projector  out : Fun1 .

hitK : Term -> Fun1 -> Fun1
hitK L out = C eqIndF thmT (compose1U (negKgtCodeOf L) out)

hitK_eval :
  (L : Term) (out : Fun1) (w : Term) ->
  Deriv (eqF (ap1 (hitK L out) w)
             (eqInd (ap1 thmT w) (ap1 (negKgtCodeOf L) (ap1 out w))))
hitK_eval L out w =
  ruleTrans (ax_C eqIndF thmT (compose1U (negKgtCodeOf L) out) w)
    (ruleTrans (congR eqIndF (ap1 thmT w) (axComp (negKgtCodeOf L) out w))
               (eqIndF_eq (ap1 thmT w) (ap1 (negKgtCodeOf L) (ap1 out w))))

-- 0/1-valued (shipped eqInd_le_one, re-keyed via hitK_eval).
hitK_le_one :
  (L : Term) (out : Fun1) (w : Term) ->
  Deriv (leq (ap1 (hitK L out) w) (ap1 s O))
hitK_le_one L out w =
  let c0 : Term
      c0 = ap1 (hitK L out) w
      c1 : Term
      c1 = eqInd (ap1 thmT w) (ap1 (negKgtCodeOf L) (ap1 out w))
      rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
      rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
             (congL sub (ap1 s O) (hitK_eval L out w))
  in mp rw (eqInd_le_one (ap1 thmT w) (ap1 (negKgtCodeOf L) (ap1 out w)))

------------------------------------------------------------------------
-- The bridge: a firing match  ==>  dNeg .  z0 := ap1 out w0 .

dNeg_from_hitK :
  (L : Term) (out : Fun1) (w0 : Term) ->
  Deriv (eqF (ap1 (hitK L out) w0) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT w0) (ap1 (negKgtCodeOf L) (ap1 out w0)))
dNeg_from_hitK L out w0 h =
  let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 (negKgtCodeOf L) (ap1 out w0)))
                         (ap1 s O))
      match = ruleTrans (ruleSym (hitK_eval L out w0)) h
  in eqInd_sound (ap1 thmT w0) (ap1 (negKgtCodeOf L) (ap1 out w0)) match
