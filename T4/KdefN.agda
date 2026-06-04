{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefN -- the number-code re-pointing of T4.Kdef : the OPEN K-formula and
-- its num-raw code-builder, at the HONEST guard and decoder
-- (CHAITIN-NUMBER-CODE-HANDOFF.md S5.0, brick towards the encoded GI goal
--   Deriv (imp (thmT w = code (K(_)>L*)) (thmT (G w) = codeFalse)) ).
--
-- Programs ARE numbers; "p describes x" is decoded by  runProgN  ( = the
-- universal machine on the base-3 digit-string  candidate p , T4.ParseN ), and
-- the finite candidate set  { |p| <= n }  is the initial segment  { p < N } ,
-- so the guard is the clean O(1)  p <= predN  ( predN := N-1 , symbolic ) :
--
--   definableN p x n = eqF (ap2 runProgN p n) (ap1 s x)              ( "p, run n, outputs x" )
--   KdefN x = imp (leq (var 0) predN) (neg (definableN (var 0) x (var 1)))
--           = ( p <= predN )  ->  ~ ( runProgN p n = s x )           ( p=var0, n=var1 )
--
-- This is the honest replacement for  T4.Kdef.Kdef  ( szLeqApp size-guard +
-- runProg ): leq a b = ( sub a b = O ).  Everything else ( the 7-constant
-- skeleton, Kcode = wrapAll, the num/codeTerm bridge ) mirrors  T4.Kdef
-- verbatim -- the re-pointing is mechanical, exactly two slots change.

open import T4.Base

module T4.KdefN (predN : Term) where

open import T4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import T4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 )
open import T4.Num using ( num )
open import T4.IsNat using ( num_eq_code ; isNat )
open import T4.NumContract using ( isNat_natCode )
open import T4.ParseN using ( runProgN )
open import T4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import T4.DoubleCodeNum using ( NoVar_codeFun1L )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )

open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- SECTION 1.  The open K-formula.  Free  var 0 = p ( program NUMBER ),
-- var 1 = n ( fuel ) ; subject  x .   Guard the clean  p < N .

definableN : Term -> Term -> Term -> Formula
definableN p x n = eqF (ap2 runProgN p n) (ap1 s x)

KdefN : Term -> Formula
KdefN x =
  imp (leq (var zero) predN)
      (neg (definableN (var zero) x (var (suc zero))))

------------------------------------------------------------------------
-- SECTION 2.  The 7 constants of  codeFormula (KdefN x)  ( left children,
-- root -> hole ), hole = codeTerm x .   Each carries its NoVar proof.
-- ( The guard constant's NoVar is the stuck-but-typed  NoVar_codeFormula  on
--   the abstract  predN  -- a valid neutral term, no reduction needed. )

kdefConstsN : NVList
kdefConstsN =
  nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula (leq (var zero) predN))
          (NoVar_codeFormula (leq (var zero) predN))
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap2 runProgN (var zero) (var (suc zero))))
          (NoVar_codeTerm (ap2 runProgN (var zero) (var (suc zero))))
  (nvcons (natCode tag_ap1) (NoVar_natCode tag_ap1)
  (nvcons (codeFun1 s) (NoVar_codeFun1L s)
  nvnil))))))

kdefSkelN : Term -> Term
kdefSkelN h = skelOf kdefConstsN h

-- PIN ( encoding bookkeeping, machine-checked ): the 7 constants ARE the
-- codeFormula skeleton, hole = codeTerm subject ( single coding ).
skel_pinsN :
  (x : Term) ->
  Eq (codeFormula (KdefN x)) (kdefSkelN (codeTerm x))
skel_pinsN x = refl

------------------------------------------------------------------------
-- SECTION 3.  KcodeN + its PROVED correctness ( hole filled  ap1 num subject ,
-- bridged to  codeTerm subject  by  num_eq_code  on the numeral ).

KcodeN : Fun1
KcodeN = wrapAll kdefConstsN num

KcodeN_eval :
  (x : Term) ->
  Deriv (eqF (ap1 KcodeN x) (kdefSkelN (ap1 num x)))
KcodeN_eval x = wrapAll_eq kdefConstsN num x

KcodeN_correct :
  (n : Nat) ->
  Deriv (eqF (ap1 KcodeN (natCode n))
              (codeFormula (KdefN (natCode n))))
KcodeN_correct n =
  ruleTrans (KcodeN_eval (natCode n))
            (skelOf_cong kdefConstsN (num_eq_code (natCode n) (isNat_natCode n)))

KcodeN_correct_T :
  (x : Term) -> isNat x ->
  Deriv (eqF (ap1 KcodeN x) (codeFormula (KdefN x)))
KcodeN_correct_T x nx =
  ruleTrans (KcodeN_eval x)
            (skelOf_cong kdefConstsN (num_eq_code x nx))
