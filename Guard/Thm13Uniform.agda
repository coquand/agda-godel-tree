{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm13Uniform -- Guard's Theorem 13 (conditional corollary).
--
-- guard15 p.16 Thm 13:
--     For each singulary  f  we can prove
--         f(x) = y  ⊃  th(Df(x)) = "fx_ = y" .
--     An analogous result holds for binary functors.
--
-- Guard's proof transports Thm 12's output  "fx_ = fx" = 3J(num(fx),
-- num(fx))  through the hypothesis  f(x) = y  to obtain the RHS
--  "fx_ = y" = 3J(num(fx), num y) .  The transport step is
-- num-congruence: from  f(x) = y  derive  num(f x) = num y  by
-- axEqCong1 applied to  num  as a BRA functor.  This is a BRA
-- theorem, not a meta-theorem.
--
-- In our system, we have:
--  *  cor : Fun1        as the  num  analog;
--  * `cong1 cor` and `axEqCong1 cor`  providing num-congruence at
--    the Deriv level.
-- Thm 13 becomes a two-step Deriv transport built on Thm 12:
--
--     thm13Fun1Imp f x y H =
--         ruleTrans
--           (encAxReflCorr (ap1 cor (ap1 f x)))         -- Thm 12
--           (congR Pair (ap1 cor (ap1 f x))             -- lift cong1
--              (cong1 cor H))                            -- num-cong
--
-- We formulate as a META-function (Agda-level) returning a Deriv
-- conditional on the hypothesis Deriv, following the plan agreed in
-- session G STEP 4 (Option F).  The chain consumers call this with
-- the specific hypothesis Deriv they have at each step of Thm 14.

module Guard.Thm13Uniform where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForHF using (thmT)
open import Guard.CodeOfReifyUnify using (cor)
open import Guard.Thm12Uniform using (D1 ; D2)

------------------------------------------------------------------------
-- Singulary Thm 13 (conditional form).

thm13Fun1Imp : (f : Fun1) (x y : Term) ->
  Deriv (atomic (eqn (ap1 f x) y)) ->
  Deriv (atomic (eqn (ap1 thmT (D1 f x))
                     (ap2 Pair (ap1 cor (ap1 f x))
                               (ap1 cor y))))
thm13Fun1Imp f x y H =
  let corFx : Term ; corFx = ap1 cor (ap1 f x)
      corY  : Term ; corY  = ap1 cor y
      -- Thm 12: thmT(D1 f x) = Pair corFx corFx.
      base  : Deriv (atomic (eqn (ap1 thmT (D1 f x))
                                 (ap2 Pair corFx corFx)))
      base  = encAxReflCorrD1 f x
      -- cong1 cor on hypothesis: corFx = corY.
      corH  : Deriv (atomic (eqn corFx corY))
      corH  = cong1 cor H
      -- congR Pair on the Pair's RHS slot: Pair corFx corFx = Pair corFx corY.
      step  : Deriv (atomic (eqn (ap2 Pair corFx corFx)
                                 (ap2 Pair corFx corY)))
      step  = congR Pair corFx corH
  in ruleTrans base step
  where
  open import Guard.ProofEncUnify using (encAxReflCorr)
  encAxReflCorrD1 : (f : Fun1) (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (D1 f x))
                       (ap2 Pair (ap1 cor (ap1 f x))
                                 (ap1 cor (ap1 f x)))))
  encAxReflCorrD1 f x = encAxReflCorr (ap1 cor (ap1 f x))

------------------------------------------------------------------------
-- Binary Thm 13.

thm13Fun2Imp : (g : Fun2) (x y yRHS : Term) ->
  Deriv (atomic (eqn (ap2 g x y) yRHS)) ->
  Deriv (atomic (eqn (ap1 thmT (D2 g x y))
                     (ap2 Pair (ap1 cor (ap2 g x y))
                               (ap1 cor yRHS))))
thm13Fun2Imp g x y yRHS H =
  let corGxy : Term ; corGxy = ap1 cor (ap2 g x y)
      corY   : Term ; corY   = ap1 cor yRHS
      base   : Deriv (atomic (eqn (ap1 thmT (D2 g x y))
                                  (ap2 Pair corGxy corGxy)))
      base   = encAxReflCorrD2 g x y
      corH   : Deriv (atomic (eqn corGxy corY))
      corH   = cong1 cor H
      step   : Deriv (atomic (eqn (ap2 Pair corGxy corGxy)
                                  (ap2 Pair corGxy corY)))
      step   = congR Pair corGxy corH
  in ruleTrans base step
  where
  open import Guard.ProofEncUnify using (encAxReflCorr)
  encAxReflCorrD2 : (g : Fun2) (x y : Term) ->
    Deriv (atomic (eqn (ap1 thmT (D2 g x y))
                       (ap2 Pair (ap1 cor (ap2 g x y))
                                 (ap1 cor (ap2 g x y)))))
  encAxReflCorrD2 g x y = encAxReflCorr (ap1 cor (ap2 g x y))
