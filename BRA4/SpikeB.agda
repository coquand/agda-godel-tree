{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SpikeB -- the merged-induction TOY (Spike B).
--
-- PURPOSE.  Spike A (paper) cleared Gate KR-1 (the Solovay proof-search
-- bound).  Gate KR-2 -- "can per-step witnesses be threaded through a
-- counting `ruleIndNat`?" -- is the only remaining make-or-break for the
-- Kritchman-Raz route (and the shared Gate-1 crux,
-- GATE1-INJECTION-FORMULATION.md S2).  This file ISOLATES that crux on a
-- toy, with no thmT / no real counting.
--
-- THE DISTINCTION FROM `PHP.agda`.  `PHP.Cbound` already does count-below
-- with a per-step witness family -- but by META-recursion (Agda recursion
-- on the meta `Nat N`).  For the real use  N = 2^{c.ell}  is exponential,
-- so an N-deep meta recursion is INFEASIBLE; the build needs ONE object
-- `ruleIndNat` (open in the induction variable, instantiated ONCE at a
-- Bin-compressed N).  The object `ruleIndNat` step is a single `imp`
-- (IH -> conclusion), so the per-step witness must be threaded UNDER the
-- implication via the Carneiro deduction-theorem combinators (bComb/liftP).
-- THAT is what was untested.  This file tests it.
--
-- RESULT (see STATUS at the bottom): the threading WORKS.  `linearBound_obj`
-- is `Cbound` rebuilt as a single object `ruleIndNat`, parametric in an
-- arbitrary `C : Fun1`, consuming a UNIFORM (open in the induction variable)
-- per-step unit-step witness, and the witness genuinely flows into the
-- conclusion.  The one CONSTRAINT it surfaces -- the witness must be uniform
-- (open), not a per-numeral meta-family -- is satisfied by the KR witnesses
-- (compress_canonical naming + Chaitin G1 are uniform in the term); see the
-- note at the bottom.

module BRA4.SpikeB where

open import BRA4.Base

open import BRA3.Church       using ( sub )
open import BRA3.ChurchLeq    using ( leq ; T76 )   -- leq ; leq O v0
open import BRA3.ChurchT73    using ( T73 )         -- leq v0 v0
open import BRA3.ChurchT78    using ( T78 )   -- (leq v0 v1) -> (leq (s v0) (s v1))
open import BRA3.ChurchT84    using ( T84 )   -- (leq v0 v1) -> (leq v1 v2) -> (leq v0 v2)
open import BRA3.RuleInst2    using ( ruleInst2 )
open import BRA3.Contrapositive using ( bComb ; liftP )
open import BRA4.Counting     using ( ruleInst3v )

------------------------------------------------------------------------
-- The two leq facts, as pure IMPLICATIONS (needed because the object
-- `ruleIndNat` step carries the IH as a HYPOTHESIS, not a Deriv).
--
-- Both use the verbatim-substituent trick (ruleInst2 / ruleInst3v keep
-- the substituents at the leaves), so a, b, c may freely contain the
-- induction variable `var 0` -- no capture.  This is the same pattern as
-- PHP.succ_mono and Counting.sigma_assoc.

succ_mono_imp :
  (a b : Term) ->
  Deriv (imp (leq a b) (leq (ap1 s a) (ap1 s b)))
succ_mono_imp a b = ruleInst2 0 a 1 b refl T78

leq_trans_imp :
  (a b c : Term) ->
  Deriv (imp (leq a b) (imp (leq b c) (leq a c)))
leq_trans_imp a b c = ruleInst3v a b c T84

------------------------------------------------------------------------
-- THE TOY.  Object `ruleIndNat` proving the linear bound  C(t) <= t ,
-- open in the induction variable `var 0`, from
--   * a base       Deriv (leq (C O) O) , and
--   * a UNIFORM unit step (open in var 0)
--       Deriv (leq (C (s var0)) (s (C var0)))   -- "the count grows by <= 1"
-- threaded under the implication of the step.
--
-- This is exactly  PHP.Cbound  rebuilt as ONE object `ruleIndNat`
-- (instead of meta-recursion on N), the form the KR / Gate-1 build needs.
--
-- Step (an  imp IH conclusion , IH = `leq (C v0) v0`):
--   succ_mono_imp   : IH -> (s (C v0) <= s v0)        [IH used here]
--   wunit (lifted)  : IH -> (C (s v0) <= s (C v0))    [the supplied witness]
--   leq_trans_imp   : (C(sv0) <= s(C v0)) -> (s(C v0) <= s v0) -> (C(sv0) <= s v0)
-- combine with bComb under the fixed hypothesis IH.

linearBound_obj :
  (cf : Fun1) ->
  Deriv (leq (ap1 cf O) O) ->
  Deriv (leq (ap1 cf (ap1 s (var 0))) (ap1 s (ap1 cf (var 0)))) ->
  Deriv (leq (ap1 cf (var 0)) (var 0))
linearBound_obj cf bs wunit =
  ruleIndNat 0 {P = leq (ap1 cf (var 0)) (var 0)} bs stp
  where
    IH : Formula
    IH = leq (ap1 cf (var 0)) (var 0)

    Cv0 : Term
    Cv0 = ap1 cf (var 0)

    Csv0 : Term
    Csv0 = ap1 cf (ap1 s (var 0))

    -- IH -> s (C v0) <= s v0           (succ_mono applied to the IH).
    d_sm : Deriv (imp IH (leq (ap1 s Cv0) (ap1 s (var 0))))
    d_sm = succ_mono_imp Cv0 (var 0)

    -- IH -> C (s v0) <= s (C v0)        (the supplied witness, weakened).
    d_w : Deriv (imp IH (leq Csv0 (ap1 s Cv0)))
    d_w = liftP IH wunit

    -- (C(sv0) <= s(Cv0)) -> (s(Cv0) <= s v0) -> (C(sv0) <= s v0).
    d_tr : Deriv (imp (leq Csv0 (ap1 s Cv0))
                      (imp (leq (ap1 s Cv0) (ap1 s (var 0)))
                           (leq Csv0 (ap1 s (var 0)))))
    d_tr = leq_trans_imp Csv0 (ap1 s Cv0) (ap1 s (var 0))

    -- Assemble the step  IH -> (C (s v0) <= s v0)  under the hypothesis IH.
    stp : Deriv (imp IH (leq Csv0 (ap1 s (var 0))))
    stp = bComb (bComb (liftP IH d_tr) d_w) d_sm

------------------------------------------------------------------------
-- Instantiation at a concrete numeral: the open conclusion is usable at
-- any  natCode k  by ONE `ruleInst` (this is the "instantiate the single
-- object induction at the Bin-compressed N" move, here at a unary numeral
-- for the toy).

linearBound_at :
  (cf : Fun1) ->
  Deriv (leq (ap1 cf O) O) ->
  Deriv (leq (ap1 cf (ap1 s (var 0))) (ap1 s (ap1 cf (var 0)))) ->
  (k : Nat) ->
  Deriv (leq (ap1 cf (natCode k)) (natCode k))
linearBound_at cf bs wunit k =
  ruleInst 0 (natCode k) (linearBound_obj cf bs wunit)

------------------------------------------------------------------------
-- Two leq-rewriting helpers (rewrite either argument of `leq` by an
-- equality), used only to supply  base / wunit  for the concrete instance.

leq_eqL : (a b c : Term) -> Deriv (eqF a b) -> Deriv (leq b c) -> Deriv (leq a c)
leq_eqL a b c ab bc = ruleTrans (mp (ax_eqCongL sub a b c) ab) bc

leq_eqR : (a b c : Term) -> Deriv (eqF b c) -> Deriv (leq a b) -> Deriv (leq a c)
leq_eqR a b c bc ab = ruleTrans (ruleSym (mp (ax_eqCongR sub b c a) bc)) ab

------------------------------------------------------------------------
-- A CONCRETE end-to-end instance, with C := `o` (the constant-zero
-- functor: ax_o gives  o t = O ).  Its base and unit step are real,
-- uniform Derivs, so this is a closed, parameter-free run of the toy.
-- (C is abstract in `linearBound_obj`, so the choice of C is immaterial
-- to the threading mechanism; `o` is merely the cheapest witness supplier.)

bseO : Deriv (leq (ap1 o O) O)
bseO = leq_eqL (ap1 o O) O O (ax_o O) (ruleInst 0 O T73)

-- wunit for o:  o(s v0) <= s (o v0) .  Both sides reduce to  O / s O :
--   o(s v0) = O           [ax_o]
--   s (o v0) = s O         [cong s on  o v0 = O ]
-- so the target is  leq O (s O) , i.e.  T76 at  s O .
wunit_o : Deriv (leq (ap1 o (ap1 s (var 0))) (ap1 s (ap1 o (var 0))))
wunit_o =
  let leq_O_sO : Deriv (leq O (ap1 s O))
      leq_O_sO = ruleInst 0 (ap1 s O) T76

      -- s O = s (o v0)   (from  O = o v0 ).
      sO_eq : Deriv (eqF (ap1 s O) (ap1 s (ap1 o (var 0))))
      sO_eq = mp (ax_eqCong1 s O (ap1 o (var 0))) (ruleSym (ax_o (var 0)))

      -- leq O (s (o v0)) .
      leq_O_sov0 : Deriv (leq O (ap1 s (ap1 o (var 0))))
      leq_O_sov0 = leq_eqR O (ap1 s O) (ap1 s (ap1 o (var 0))) sO_eq leq_O_sO
  in leq_eqL (ap1 o (ap1 s (var 0))) O (ap1 s (ap1 o (var 0)))
             (ax_o (ap1 s (var 0))) leq_O_sov0

-- The toy, fully instantiated: a closed Deriv of  o(t) <= t , open in t.
demo : Deriv (leq (ap1 o (var 0)) (var 0))
demo = linearBound_obj o bseO wunit_o

demo_at : (k : Nat) -> Deriv (leq (ap1 o (natCode k)) (natCode k))
demo_at k = linearBound_at o bseO wunit_o k

------------------------------------------------------------------------
-- The uniform witness gives the per-numeral meta-family for FREE (the
-- direction we CAN do): instantiate the open `wunit` at each numeral.
-- (natCode (suc n) = s (natCode n) definitionally, so the types align.)

wunit_family :
  (cf : Fun1) ->
  Deriv (leq (ap1 cf (ap1 s (var 0))) (ap1 s (ap1 cf (var 0)))) ->
  (n : Nat) ->
  Deriv (leq (ap1 cf (natCode (suc n))) (ap1 s (ap1 cf (natCode n))))
wunit_family cf wunit n = ruleInst 0 (natCode n) wunit

------------------------------------------------------------------------
------------------------------------------------------------------------
-- STATUS (Spike B).
--
-- GREEN.  The merged induction WORKS as a single object `ruleIndNat`:
--   * `linearBound_obj` typechecks: the linear bound  C(t) <= t  is proved
--     by ONE object `ruleIndNat` (NOT meta-recursion), parametric in an
--     arbitrary  C : Fun1 , consuming a per-step unit-step witness threaded
--     under the step's implication via bComb/liftP.
--   * the witness GENUINELY FLOWS IN, not discarded: `step` is built FROM
--     `d_w = liftP IH wunit`; and the bound is FALSE without it (e.g. for a
--     doubling C with  C(0)=0  the base still holds but  C(t) <= t  fails),
--     so the step provably cannot be assembled by ignoring `wunit`.
--   * `linearBound_at` shows the single object induction is then usable at
--     any numeral by ONE `ruleInst` -- the "instantiate at Bin-compressed N"
--     move the real build needs (here at a unary `natCode k`).
--   * `demo` / `demo_at` are closed, parameter-free runs (C := o).
--
-- THE ONE CONSTRAINT SURFACED (and why it is satisfied for KR).  The object
-- `ruleIndNat` step requires the per-step witness to be UNIFORM -- open in
-- the induction variable (`wunit : Deriv (... var 0 ...)`), NOT a per-numeral
-- meta-family `(n : Nat) -> Deriv (... natCode n ...)`.  The easy direction
-- (uniform -> family) is `wunit_family`; the reverse (family -> uniform) is
-- NOT available in general (no induction-free generalisation from "true at
-- each numeral" to "true at var 0").  For the Kritchman-Raz build this
-- constraint IS met: the per-step witnesses there are uniform in the term --
--   * compress_canonical: "the formula  v0 = t  defines  t " is the tautology
--     (v0 = t) <-> (v0 = t) , provable UNIFORMLY for the term  t = var 0 ;
--   * Chaitin's theorem (Phase KR-B) is uniform in its inputs.
-- The residual per-numeral aspects (the length bound  lenR(name) <= ell ) are
-- GLOBAL (applied once at  t = N  via the compression chain), not per-step.
-- So Gate KR-2's mechanism is validated, and the KR design supplies witnesses
-- in the uniform-open shape the mechanism demands.  GO.
