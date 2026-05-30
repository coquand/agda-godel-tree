{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SubLeq -- Phase R5, steps (1)+(2) (CHAITIN-G1-FAITHFUL-BLUEPRINT.md
-- S5bis R5d): the  leq -> sub = O  bridge over NUMERALS, symbolic in the
-- abstract sizes.
--
--   sub_le_zero  : NatLe a b -> Deriv (sub (natCode a) (natCode b) = O)
--   sub_exp2_le  : NatLe n (powN k)
--                  -> Deriv (sub (natCode n) (ap1 exp2 (natCode k)) = O)
--
-- Nothing is computed.  sub_le_zero is the meta fact "a <= b  =>  a - b = 0"
-- transcribed onto the two shipped closed-form subtraction lemmas
-- (sub_natCode for the  a = b  case,  sub_of_smaller_eq_O  for  a < b ),
-- selected by the meta witness  b = d + a  (le_to_addN).  sub_exp2_le keeps
-- the threshold's value symbolic by rewriting  ap1 exp2 (natCode k) =
-- natCode (powN k)  via the shipped  Exp.exp2_natCode  INSIDE -- so
-- natCode (powN k) is never formed as a literal, the equation stays general.

module BRA4.SubLeq where

open import BRA4.Base
open import BRA4.Exp using ( powN ; exp2 ; exp2_natCode )

open import BRA3.Church        using ( sub )
open import BRA3.Code.Tag      using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right ; addN_suc_right )
open import BRA3.RuleInst2     using ( NatLe ; le-zero ; le-suc )
open import BRA3.Dispatch      using ( sub_natCode )
open import BRA3.SubT.V2NatEqLt using ( sub_of_smaller_eq_O )

------------------------------------------------------------------------
-- A local dependent pair (no Sigma in BRA3.Base).

record Sg (A : Set) (B : A -> Set) : Set where
  constructor mkSg
  field
    fst : A
    snd : B fst
open Sg public

------------------------------------------------------------------------
-- NatLe a b  =>  b = d + a  (d = b - a), the witness that selects the case.

le_to_addN : {a b : Nat} -> NatLe a b -> Sg Nat (\ d -> Eq b (addN d a))
le_to_addN (le-zero n)        = mkSg n (eqSym (addN_zero_right n))
le_to_addN (le-suc {m} {n} le) =
  let r = le_to_addN le
  in mkSg (fst r)
          (eqTrans (eqCong suc (snd r)) (eqSym (addN_suc_right (fst r) m)))

------------------------------------------------------------------------
-- The  a + (d, a)  closed form:  sub (natCode a) (natCode (d + a)) = O .
-- d = 0  : the  a = b  case (sub_natCode 0, since addN 0 a = a, natCode 0 = O).
-- d = s _: the  a < b  case (sub_of_smaller_eq_O, since addN (s d') a =
--          s (addN d' a)).

sub_le_addN_zero :
  (d a : Nat) ->
  Deriv (eqF (ap2 sub (natCode a) (natCode (addN d a))) O)
sub_le_addN_zero zero     a = sub_natCode zero a
sub_le_addN_zero (suc d') a = sub_of_smaller_eq_O d' a

------------------------------------------------------------------------
-- (1)  sub_le_zero .

sub_le_zero :
  {a b : Nat} -> NatLe a b ->
  Deriv (eqF (ap2 sub (natCode a) (natCode b)) O)
sub_le_zero {a} {b} le =
  let r = le_to_addN le
  in eqSubst (\ B' -> Deriv (eqF (ap2 sub (natCode a) (natCode B')) O))
             (eqSym (snd r))
             (sub_le_addN_zero (fst r) a)

------------------------------------------------------------------------
-- (2)  sub_exp2_le :  bound a NUMERAL against the (unformed) threshold
-- value  2^k = ap1 exp2 (natCode k) .  Rewrites the threshold to
-- natCode (powN k) via exp2_natCode, then sub_le_zero.

sub_exp2_le :
  (n k : Nat) -> NatLe n (powN k) ->
  Deriv (eqF (ap2 sub (natCode n) (ap1 exp2 (natCode k))) O)
sub_exp2_le n k le =
  ruleTrans (congR sub (natCode n) (exp2_natCode k))
            (sub_le_zero le)
