{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.GoedelI -- Goedel's Incompleteness Theorem for BRA, Guard 1963
-- Theorem 11 (p. 15).
--
-- Statement :  Deriv G -> Deriv (eqF O (ap1 s O))   (= "0 = 1") .
--
-- Construction (follows guard15.pdf p. 14-15 + learnt.md) :
--
--   sub : Fun2  (Exercise 24 [8]) ; built from BRA4.sbf + BRA4.num as
--                 sub z P =  sbf (Pair (natCode 0) (num z)) P .
--   F_seed   : single-var-x_0 (and aux x_1) seed formula
--              =  neg (eqF (ap1 thmT (var 1)) (var 0)) .
--   H        : Formula with TWO free vars x_0, x_1, =  F_seed[x_0 := sub(x_0, x_0)] ,
--              i.e.  H(x_0, x_1) = "th(x_1) /= sub(x_0, x_0)" .
--   iH : Nat = codeFormulaNat H  ("the numeral i" of guard15 Th 11).
--   G        : single-var-x_1 sentence, = H[x_0 := natCode iH]
--              i.e.  G(x_1) = "th(x_1) /= sub(i_, i_)" .
--   iG : Nat = codeFormulaNat G  ("the numeral j" of guard15 Th 11).
--
-- The proof.  Suppose  d : Deriv G .
--   1. y := encode d : Term .
--   2. eq1 := thmT_complete_rec d dc : thmT y = codeFormula G .
--   3. ky := codeTermNat y : Nat ; eq2 := codeTerm_eq y : y = natCode ky .
--   4. From eq1, eq2 :  thmT(natCode ky) = codeFormula G .
--   5. codeFormula_eq G :  codeFormula G = natCode iG .
--   6. Chain (4) , (5) :  thmT(natCode ky) = natCode iG .
--   7. diag_term_eq : diag_inst = codeFormula G ; chain (5) :
--      diag_inst = natCode iG .
--   8. Combine (6) , (7) :  thmT(natCode ky) = diag_inst .
--   9. d_subst1 := ruleInst 1 (natCode ky) d :
--      Deriv (substF 1 (natCode ky) G)  ; substT-bridge via Closed diag_inst :
--      d_inst_neg : Deriv (neg (atomic (eqn (ap1 thmT (natCode ky)) diag_inst))) .
--  10. axExFalso (atomic ...) falseF  + mp (8) + mp (9)  ->  Deriv falseF .
--
-- This is the "consistency-relative" form (Guard does the contrapositive
-- + meta-validity argument to conclude G is valid but unprovable ; we
-- give the BRA-internal contradiction-derivation form, which is its
-- key technical content).

module BRA4.GoedelI where

open import BRA4.Base
open import BRA4.Code
open import BRA4.Tags
open import BRA4.SbF       using ( sbf )
open import BRA4.SbT       using ( sbt )
open import BRA4.Num       using ( num )
open import BRA4.SbfAtClosures using ( sbContract )
open import BRA4.NumContract  using ( numContract )
open import BRA4.ThmT      using ( thmT )
open import BRA4.NatBridge using ( codeTermNat ; codeFormulaNat
                                  ; codeTerm_eq ; codeFormula_eq )
open import BRA4.Encode    using ( encode )
open import BRA4.Diagonal  using ( module Diagonal )
open import BRA4.ThmTCompleteRec using ( thmT_complete_rec )

open import BRA3.Church       using ( pi )
open import BRA3.Contrapositive using ( axExFalso )
open import BRA3.Dispatch     using ( closed_ap1 ; closed_ap2 ; closedAt )

------------------------------------------------------------------------
-- The seed formula F_seed with TWO free variables :
--   x_0 -- the "diagonal" slot (Gödel handle substituent).
--   x_1 -- the auxiliary slot, ranges over (numerals of) verifier inputs.
--
-- After diagonal substitution + sentence instantiation,  G(x_1) =
-- "th(x_1) /= sub(i_, i_)" .

F_seed : Formula
F_seed = neg (atomic (eqn (ap1 thmT (var (suc zero))) (var zero)))

------------------------------------------------------------------------
-- Instantiate the Diagonal module at the concrete pair  (sbt, sbf,
-- sbContract)  +  (num, numContract)  +  F_seed .

module D = Diagonal sbt sbf sbContract num numContract F_seed
open D using ( H ; j ; G ; diag_inst ; diag_term_eq )

------------------------------------------------------------------------
-- Gödel handles iH , iG.  Aliases for Diagonal's  j  +  codeFormulaNat G .

iH : Nat
iH = j

iG : Nat
iG = codeFormulaNat G

------------------------------------------------------------------------
-- diag_inst is closed -- it's built from natCode-leaves and num applied
-- to natCode-leaves under Pair / sbf / ap1.

closed_diag_inst : Closed diag_inst
closed_diag_inst =
  closed_ap2 sbf
    (ap2 Pair (natCode zero) (ap1 num (natCode iH)))
    (natCode iH)
    (closed_ap2 Pair (natCode zero) (ap1 num (natCode iH))
       (closed_natCode zero)
       (closed_ap1 num (natCode iH) (closed_natCode iH)))
    (closed_natCode iH)

------------------------------------------------------------------------
-- The target "false" formula  P_false = (O = s O)  ( = "0 = 1" ).

P_false : Formula
P_false = atomic (eqn O (ap1 s O))

------------------------------------------------------------------------
-- GOEDEL I.

godelI : (d : Deriv G) -> Deriv P_false
godelI d =
  let y : Term
      y = encode d

      -- (1) thmT(y) = codeFormula G   (verifier completeness on d).
      eq1 : Deriv (eqF (ap1 thmT y) (codeFormula G))
      eq1 = thmT_complete_rec d

      -- (2) thmT(y) = diag_inst   (chain (1) with the diagonal equation).
      -- diag_term_eq : Deriv (eqF diag_inst (codeFormula G)) .
      eq2 : Deriv (eqF (ap1 thmT y) diag_inst)
      eq2 = ruleTrans eq1 (ruleSym diag_term_eq)

      -- (3) ruleInst 1 y d : Deriv (substF 1 y G) .
      -- substF 1 y G  reduces Agda-definitionally to
      --   neg (atomic (eqn (ap1 thmT (substT 1 y (var 1)))
      --                     (substT 1 y diag_inst)))
      --   = neg (atomic (eqn (ap1 thmT y) (substT 1 y diag_inst))) .
      d_subst1 : Deriv (substF (suc zero) y G)
      d_subst1 = ruleInst (suc zero) y d

      -- (4) substT 1 y diag_inst = diag_inst  via  Closed diag_inst .
      subst_diag_eq : Eq (substT (suc zero) y diag_inst) diag_inst
      subst_diag_eq = closedAt closed_diag_inst (suc zero) y

      -- (5) Rewrite d_subst1's type to use bare  diag_inst .
      d_inst_neg :
        Deriv (neg (atomic (eqn (ap1 thmT y) diag_inst)))
      d_inst_neg =
        eqSubst (\ z -> Deriv (neg (atomic (eqn (ap1 thmT y) z))))
                 subst_diag_eq
                 d_subst1

      -- (6) Combine (2) + (5) via  axExFalso + double-mp .
      eq_form : Formula
      eq_form = atomic (eqn (ap1 thmT y) diag_inst)

      exFalso_imp : Deriv (imp eq_form (imp (neg eq_form) P_false))
      exFalso_imp = axExFalso eq_form P_false

      step_after_eq : Deriv (imp (neg eq_form) P_false)
      step_after_eq = mp exFalso_imp eq2

      result : Deriv P_false
      result = mp step_after_eq d_inst_neg
  in result
