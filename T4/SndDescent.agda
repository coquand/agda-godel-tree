{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SndDescent -- Cantor-projection descent bounds for course-of-values
-- induction over opaque codes.  NO surjective pairing.
--
-- DELIVERED GREEN:
--   sndLe  : Snd x <= x                         (non-strict; free, via sub_le_arg1)
--   muStep : mu x n <= mu x (s n)               (single-step mu-monotonicity;
--                                                base ingredient for nu x >= 2)
--
-- RESIDUAL (the STRICT descent, the piece that actually unblocks the
-- induction).  descSnd : Snd x < x for x >= 1 is NOT "modest": Snd is
-- nu-defined, so the strictness genuinely engages the triangular-root
-- arithmetic.  Precise remaining chain (see report):
--   (R1) muMono : leq n m -> leq (mu x n) (mu x m)      [ruleIndNat on m,
--        using muStep + leq_trans + a T82-style case split; ~80-120 lines]
--   (R2) mu(x, 3) = sigma(alpha x, s O), via T99 + T100 + T97 +
--        ssub(x, s O) = x + (alpha (s x') = s O, T30); so mu(x,3) >= 2 for x>=1
--   (R3) nuGe2 : x>=1 -> nu x >= 2, from T107 (nu x = mu(x, s(s x))) +
--        muMono(3 <= s(s x)) + (R2)
--   (R4) subStrict : a>=1 -> c>=1 -> s(sub a c) <= a   [sub antitone in 2nd
--        arg + s(pred a) = a; possibly another induction]
--   (R5) tauPredNuGe1 : x>=1 -> tau(pred(nu x)) >= 1  [pred-mono + tau>=1]
--   descSnd := subStrict x (tau(pred(nu x))) (x>=1) (R5) , rewritten by
--   Snd_closed.   fstLe additionally needs pred(nu x) <= x (another nu bound).
-- Total estimate ~250-350 lines, 2-3 inductions.  So the strict descent is a
-- real (finite, no-eta) arithmetic sub-project, not a one-liner.

module T4.SndDescent where

open import T4.Base

open import BRA3.Church   using ( sub ; tau ; predecessor ; sigma )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT116 using ( Snd ; Snd_closed )
open import BRA3.ChurchNu  using ( nuFn )
open import BRA3.ChurchMu  using ( mu ; T99 )
open import BRA3.ChurchEta1 using ( eta1 )
open import BRA3.RuleInst2  using ( ruleInst2 )
open import T4.LeqMono     using ( leq_sigma_right )
open import T4.ChaitinG1Arith using ( sub_le_arg1 )

------------------------------------------------------------------------
-- sndLe :  Snd x <= x .   Snd x = sub x c (Snd_closed), and sub a b <= a.

sndLe : (x : Term) -> Deriv (leq (ap1 Snd x) x)
sndLe x =
  let c : Term
      c = ap1 tau (ap1 predecessor (ap1 nuFn x))
      cong : Deriv (eqF (ap2 sub (ap1 Snd x) x) (ap2 sub (ap2 sub x c) x))
      cong = congL sub x (Snd_closed x)
  in ruleTrans cong (sub_le_arg1 x c)

------------------------------------------------------------------------
-- muStep :  mu x n <= mu x (s n) .   (single-step monotonicity in 2nd arg;
-- base ingredient of the mu-monotonicity induction needed for nu x >= 2.)

muStep : (x n : Term) -> Deriv (leq (ap2 mu x n) (ap2 mu x (ap1 s n)))
muStep x n =
  let t99 : Deriv (eqF (ap2 mu x (ap1 s n))
                       (ap2 sigma (ap2 eta1 x n) (ap2 mu x n)))
      t99 = ruleInst2 0 x 1 n refl T99
      lsr : Deriv (leq (ap2 mu x n) (ap2 sigma (ap2 eta1 x n) (ap2 mu x n)))
      lsr = leq_sigma_right (ap2 eta1 x n) (ap2 mu x n)
      cong : Deriv (eqF (ap2 sub (ap2 mu x n) (ap2 mu x (ap1 s n)))
                        (ap2 sub (ap2 mu x n) (ap2 sigma (ap2 eta1 x n) (ap2 mu x n))))
      cong = congR sub (ap2 mu x n) t99
  in ruleTrans cong lsr
