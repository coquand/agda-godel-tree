{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefAlph -- the  checkAlphN -guarded analog of  T4.Kdef .
--
-- Identical to  T4.Kdef  EXCEPT the guard atom of the open K-formula is the
-- VALIDITY test  checkAlphN Lstar_meta (var 0) = sO  ( "p = var 0 is a valid
-- program code of depth <= Lstar_meta" ) instead of the SIZE test
-- szLeqApp L (var 0) = sO .   This is the K-formula  T4.CoverBridge.coverBridge
-- produces ( its formula code embeds NO enumeration -- the program is  var 0 --
-- so the SMALL Chaitin diagonal applies ), and  T4.InternalCover  needs
-- VALIDITY, not just size.
--
-- The guard is a CLOSED atom ( checkAlphN Lstar_meta  is a closed Fun1 ), so
-- KdefAlph  needs no Term threshold  L : the whole family is indexed only by
-- the meta depth  Lstar_meta  ( a module parameter ).

open import T4.Base

module T4.KdefAlph (Lstar_meta : Nat) where

open import T4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import T4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 )
open import T4.Num using ( num )
open import T4.IsNat using ( num_eq_code ; isNat )
open import T4.NumContract using ( isNat_natCode )
open import T4.CheckAlphN using ( checkAlphN )
open import T4.Kdef using ( runProg ; definable )
open import T4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import T4.DoubleCodeNum using ( NoVar_codeFun1L )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )

------------------------------------------------------------------------
-- SECTION 1.  The guard atom and the open K-formula.

guardAlph : Formula
guardAlph = eqF (ap1 (checkAlphN Lstar_meta) (var zero)) (ap1 s O)

KdefAlph : Term -> Formula
KdefAlph x =
  imp guardAlph
      (neg (definable (var zero) x (var (suc zero))))

------------------------------------------------------------------------
-- SECTION 2.  The 7 constants of  codeFormula (KdefAlph x)  (left children,
-- root -> hole), hole = codeTerm x .  Each carries its NoVar proof.

kdefAlphConsts : NVList
kdefAlphConsts =
  nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula guardAlph) (NoVar_codeFormula guardAlph)
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap2 runProg (var zero) (var (suc zero))))
          (NoVar_codeTerm (ap2 runProg (var zero) (var (suc zero))))
  (nvcons (natCode tag_ap1) (NoVar_natCode tag_ap1)
  (nvcons (codeFun1 s) (NoVar_codeFun1L s)
  nvnil))))))

kdefAlphSkel : Term -> Term
kdefAlphSkel h = skelOf kdefAlphConsts h

-- PIN (encoding bookkeeping, machine-checked): the 7 constants ARE the
-- codeFormula skeleton, hole = codeTerm subject (single coding).
skel_pins :
  (x : Term) ->
  Eq (codeFormula (KdefAlph x)) (kdefAlphSkel (codeTerm x))
skel_pins x = refl

------------------------------------------------------------------------
-- SECTION 3.  KcodeAlph + its PROVED correctness.

KcodeAlph : Fun1
KcodeAlph = wrapAll kdefAlphConsts num

KcodeAlph_eval :
  (x : Term) ->
  Deriv (eqF (ap1 KcodeAlph x) (kdefAlphSkel (ap1 num x)))
KcodeAlph_eval x = wrapAll_eq kdefAlphConsts num x

KcodeAlph_correct :
  (n : Nat) ->
  Deriv (eqF (ap1 KcodeAlph (natCode n))
              (codeFormula (KdefAlph (natCode n))))
KcodeAlph_correct n =
  ruleTrans (KcodeAlph_eval (natCode n))
            (skelOf_cong kdefAlphConsts (num_eq_code (natCode n) (isNat_natCode n)))

KcodeAlph_correct_T :
  (x : Term) -> isNat x ->
  Deriv (eqF (ap1 KcodeAlph x) (codeFormula (KdefAlph x)))
KcodeAlph_correct_T x nx =
  ruleTrans (KcodeAlph_eval x)
            (skelOf_cong kdefAlphConsts (num_eq_code x nx))
