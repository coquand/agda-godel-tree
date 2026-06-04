{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.KcodeConj -- Piece 2b of the KdefConj reformulation
-- ( per  T4/NEXT-SESSION-KDEFCONJ.md ).
--
-- The BRA-internal code-builder for the conjunction-shape K-formula
-- at index  r , parallel to  Kcode L  in  T4.Kdef .   This is the
-- "negKgtCodeOf  analog" for the new shape :  a  Fun1  `KcodeConj M enum`
-- such that  ap1 (KcodeConj M enum) (natCode r) = codeFormula (KdefConj
-- M enum (natCode r)) .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   KcodeConj : Nat -> Fun1 -> Fun1
--   KcodeConj_eval :
--     (M : Nat) (enum : Fun1) (x : Term) ->
--     Deriv (eqF (ap1 (KcodeConj M enum) x)
--                 (kdefConjSkel M enum (ap1 num x)))
--   KcodeConj_correct :
--     (M : Nat) (enum : Fun1) (n : Nat) ->
--     Deriv (eqF (ap1 (KcodeConj M enum) (natCode n))
--                 (codeFormula (KdefConj M enum (natCode n))))
--   KcodeConj_correct_T :
--     (M : Nat) (enum : Fun1) (x : Term) -> isNat x ->
--     Deriv (eqF (ap1 (KcodeConj M enum) x)
--                 (codeFormula (KdefConj M enum x)))
--
-- Structure :  define a 7-element  NVList  ( kdefConjConsts )  matching
-- the codeFormula skeleton of  KdefConj M enum x  with one hole at
-- codeTerm x ; wrap with  num  via  wrapAll  to get  KcodeConj ; the
-- correctness proof is  ruleTrans  of  wrapAll_eq  +  skelOf_cong  on
-- num_eq_code  ( = the exact pattern of  Kcode_correct  in  T4.Kdef ).
--
-- =====================================================================
-- CONSTANTS  (7).
-- =====================================================================
--
-- KdefConj M enum x  unfolds to
--   imp (eqF (ap2 sub v0 (natCode M)) O)
--       (neg (eqF (ap2 (enumRunProgOf enum) v0 v1) (ap1 s x)))
--
-- whose codeFormula tree-walk gives the 7 constants ( root -> hole ) :
--
--   1.  natCode tag_imp
--   2.  codeFormula (eqF (ap2 sub v0 (natCode M)) O)     -- closed
--   3.  natCode tag_neg
--   4.  natCode tag_eq
--   5.  codeTerm (ap2 (enumRunProgOf enum) v0 v1)        -- closed (NEW shape)
--   6.  natCode tag_ap1
--   7.  codeFun1 s
--   HOLE :  codeTerm x .
--
-- The hole is the same as in  Kdef.kdefConsts ; constants 1, 3, 4, 6, 7
-- are identical ; constant 2 differs (size atom -> leq-atom) and
-- constant 5 now uses the  enumRunProgOf enum  combinator ( instead of
-- ap2 runProg (ap1 enum v0) v1 ) ; see  T4.SurpriseG2.EnumRunProg
-- for the equational equivalence  enumRunProgOf_eq  .

module T4.SurpriseG2.KcodeConj where

open import T4.Base
open import T4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_s )
open import T4.Code using ( codeTerm ; codeFormula ; codeFun1 )
open import T4.Num using ( num )
open import T4.IsNat using ( num_eq_code ; isNat )
open import T4.NumContract using ( isNat_natCode )
open import T4.Kdef using ( runProg )
open import T4.SurpriseG2.EnumRunProg using ( enumRunProgOf )
open import T4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import T4.DoubleCodeNum using ( NoVar_codeFun1L )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import BRA3.Church using ( sub )

open import T4.SurpriseG2.KdefConj using ( KdefConj )

------------------------------------------------------------------------
-- The 7 constants of  codeFormula (KdefConj M enum x)  (left children,
-- root -> hole).

kdefConjConsts : Nat -> Fun1 -> NVList
kdefConjConsts M enum =
  nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula (eqF (ap2 sub (var zero) (natCode M)) O))
          (NoVar_codeFormula (eqF (ap2 sub (var zero) (natCode M)) O))
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap2 (enumRunProgOf enum) (var zero) (var (suc zero))))
          (NoVar_codeTerm (ap2 (enumRunProgOf enum) (var zero) (var (suc zero))))
  (nvcons (natCode tag_ap1) (NoVar_natCode tag_ap1)
  (nvcons (codeFun1 s) (NoVar_codeFun1L s)
  nvnil))))))

kdefConjSkel : Nat -> Fun1 -> Term -> Term
kdefConjSkel M enum h = skelOf (kdefConjConsts M enum) h

------------------------------------------------------------------------
-- PIN (encoding bookkeeping, machine-checked): the 7 constants ARE the
-- codeFormula skeleton, hole = codeTerm subject (single coding).

skel_pins_conj :
  (M : Nat) (enum : Fun1) (x : Term) ->
  Eq (codeFormula (KdefConj M enum x))
     (kdefConjSkel M enum (codeTerm x))
skel_pins_conj M enum x = refl

------------------------------------------------------------------------
-- KcodeConj + its proved correctness.

KcodeConj : Nat -> Fun1 -> Fun1
KcodeConj M enum = wrapAll (kdefConjConsts M enum) num

KcodeConj_eval :
  (M : Nat) (enum : Fun1) (x : Term) ->
  Deriv (eqF (ap1 (KcodeConj M enum) x)
              (kdefConjSkel M enum (ap1 num x)))
KcodeConj_eval M enum x = wrapAll_eq (kdefConjConsts M enum) num x

KcodeConj_correct :
  (M : Nat) (enum : Fun1) (n : Nat) ->
  Deriv (eqF (ap1 (KcodeConj M enum) (natCode n))
              (codeFormula (KdefConj M enum (natCode n))))
KcodeConj_correct M enum n =
  ruleTrans (KcodeConj_eval M enum (natCode n))
            (skelOf_cong (kdefConjConsts M enum)
                          (num_eq_code (natCode n) (isNat_natCode n)))

KcodeConj_correct_T :
  (M : Nat) (enum : Fun1) (x : Term) -> isNat x ->
  Deriv (eqF (ap1 (KcodeConj M enum) x)
              (codeFormula (KdefConj M enum x)))
KcodeConj_correct_T M enum x nx =
  ruleTrans (KcodeConj_eval M enum x)
            (skelOf_cong (kdefConjConsts M enum) (num_eq_code x nx))
