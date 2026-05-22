{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14F -- the concrete formula  F  driving the diagonal
-- lemma for Guard's Theorem 14 (Goedel II for BRA) , and the resulting
-- numerals  i ,  j  (matching guard15.pdf p.16 notation exactly).
--
-- DESIGN.  Per Guard's paper, only the function  sub : Fun2  appears at
-- the Term level -- NOT  sbf .  Hence we do the diagonalisation here
-- with  diag_sub  =  ap2 sub (var 0) (var 0)  (not BRA4.Diagonal's
-- sbf-form ; BRA4.Diagonal is kept untouched and serves BRA4.GoedelI ) .
--
-- Diagonalisation chain :
--
--     F = neg ( eqF (ap1 thmT (var 1)) (var 0) )         -- the seed formula
--     diag_sub = ap2 sub (var 0) (var 0)                  -- the diagonal Term
--     H = substF 0 diag_sub F                              -- the open formula
--     iNat = codeFormulaNat H                              -- Guard 's "i" handle (Nat)
--     i = natCode iNat                                     -- Guard 's "i" (Term)
--     G = substF 0 i H                                     -- the closed Goedel sentence
--     jNat = codeFormulaNat G                              -- Guard 's "j" handle
--     j = natCode jNat                                     -- Guard 's "j" (Term)
--     diag_inst = substT 0 i diag_sub = ap2 sub i i        -- = Guard 's "sub(i, i)"
--
-- diag_inst reduces definitionally to  ap2 sub i i  via natEq 0 0 = true
--  applied twice at the two var-0 slots .
--
-- diag_term_eq :  ap2 sub i i  =Deriv=  codeFormula G .  Proof chains
--  sub_eq + numEq + congs + sbfEq_codeFormula  ( sbf appears INSIDE the
-- proof but NOT in the conclusion's Term structure -- the Term-level
-- statement is in sub form ) .

module BRA4.Thm.Thm14F where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 ; codeFormula ; codeTerm )
open import BRA4.Num               using ( num )
open import BRA4.NumContract       using ( numContract ; NumContract ; module NumContract )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.SbDerived         using ( module Derive )
open import BRA4.ThmT              using ( thmT )
open import BRA4.NatBridge         using ( codeFormulaNat ; codeFormula_eq )
open import BRA4.Sub               using ( sub ; sub_eq )

------------------------------------------------------------------------
-- The seed formula  F .

F : Formula
F = neg (atomic (eqn (ap1 thmT (var (suc zero))) (var zero)))

------------------------------------------------------------------------
-- The diagonal Term  ( sub  form , NOT sbf ) .

diag_sub : Term
diag_sub = ap2 sub (var zero) (var zero)

------------------------------------------------------------------------
-- The diagonalised open formula  H .

H : Formula
H = substF zero diag_sub F

------------------------------------------------------------------------
-- Guard's  i  (handle of  H ) .

iNat : Nat
iNat = codeFormulaNat H

i : Term
i = natCode iNat

------------------------------------------------------------------------
-- The closed Goedel sentence  G .

G : Formula
G = substF zero i H

------------------------------------------------------------------------
-- Guard's  j  (handle of  G ) .

jNat : Nat
jNat = codeFormulaNat G

j : Term
j = natCode jNat

------------------------------------------------------------------------
-- The diagonal Term -instance  ( substT 0 i diag_sub ) .  Reduces
-- definitionally to  ap2 sub i i  via  natEq 0 0 = true .

diag_inst : Term
diag_inst = ap2 sub i i

------------------------------------------------------------------------
-- Guard 's diagonal identity   sub(i, i)  =Deriv=  codeFormula G .
--
-- Proof chain (sbf appears only INSIDE the proof , not in the final
-- Term form) :
--   (1)  ap2 sub i i  =Deriv=  ap2 sbf (Pair 0 (ap1 num i)) i      [sub_eq]
--   (2)  ap1 num i  =Deriv=  codeTerm i                              [numEq iNat]
--   (3)  Pair 0 (ap1 num i)  =Deriv=  Pair 0 (codeTerm i)             [congR Pair]
--   (4)  ap2 sbf (Pair 0 (ap1 num i)) i  =Deriv=
--          ap2 sbf (Pair 0 (codeTerm i)) i                            [congL sbf]
--   (5)  i  =Deriv=  codeFormula H                                    [ruleSym codeFormula_eq H]
--   (6)  ap2 sbf (Pair 0 (codeTerm i)) i  =Deriv=
--          ap2 sbf (Pair 0 (codeTerm i)) (codeFormula H)              [congR sbf]
--   (7)  ap2 sbf (Pair 0 (codeTerm i)) (codeFormula H)  =Deriv=
--          codeFormula (substF 0 i H)  = codeFormula G                [sbfEq_codeFormula]

open Derive sbt sbf sbContract using ( sbfEq_codeFormula )
open NumContract numContract using ( numEq )

diag_term_eq : Deriv (eqF diag_inst (codeFormula G))
diag_term_eq =
  let
    step1 :
      Deriv (eqF (ap2 sub i i)
                  (ap2 sbf (ap2 Pair (natCode zero) (ap1 num i)) i))
    step1 = sub_eq i i

    step2 :
      Deriv (eqF (ap1 num i) (codeTerm i))
    step2 = numEq iNat

    step3 :
      Deriv (eqF (ap2 Pair (natCode zero) (ap1 num i))
                  (ap2 Pair (natCode zero) (codeTerm i)))
    step3 = congR Pair (natCode zero) step2

    step4 :
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (ap1 num i)) i)
                  (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) i))
    step4 = congL sbf i step3

    step5 :
      Deriv (eqF i (codeFormula H))
    step5 = ruleSym (codeFormula_eq H)

    step6 :
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) i)
                  (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) (codeFormula H)))
    step6 = congR sbf (ap2 Pair (natCode zero) (codeTerm i)) step5

    step7 :
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) (codeFormula H))
                  (codeFormula G))
    step7 = sbfEq_codeFormula zero i H

  in ruleTrans step1 (ruleTrans step4 (ruleTrans step6 step7))

------------------------------------------------------------------------
-- Guard's diagonal identity at the j -form :  sub(i, i)  =Deriv=  j .
--
-- Chain :  diag_term_eq + codeFormula_eq G .

sub_ii_eq_j : Deriv (eqF (ap2 sub i i) j)
sub_ii_eq_j = ruleTrans diag_term_eq (codeFormula_eq G)

------------------------------------------------------------------------
-- The Deriv-level identity  codeFormula G  =Deriv=  j  (bridge between
--  codeFormula G  and  j  forms ).

codeFormulaG_eq_j : Deriv (eqF (codeFormula G) j)
codeFormulaG_eq_j = codeFormula_eq G

------------------------------------------------------------------------
-- Guard-style Term-level abbreviations .
--
--   code t       =  ap1 num t                              -- Guard 's "t" (= code of t)
--   encEqF a b   =  Pair tag_eq (Pair a b)                 -- Guard 's "a = b"
--   encThm t     =  Pair tag_ap1 (Pair (codeFun1 thmT) t)   -- Guard 's "th(t)"
--   encSub a b   =  Pair tag_ap2 (Pair (codeFun2 sub) (Pair a b))  -- Guard 's "sub(a, b)"
--   encNeg t     =  Pair tag_neg t                          -- Guard 's "¬ t"

code : Term -> Term
code t = ap1 num t

encEqF : Term -> Term -> Term
encEqF a b = ap2 Pair (natCode tag_eq) (ap2 Pair a b)

encThm : Term -> Term
encThm t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 thmT) t)

encSub : Term -> Term -> Term
encSub a b =
  ap2 Pair (natCode tag_ap2)
    (ap2 Pair (codeFun2 sub) (ap2 Pair a b))

encNeg : Term -> Term
encNeg t = ap2 Pair (natCode tag_neg) t
