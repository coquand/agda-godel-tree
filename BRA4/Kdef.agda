{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Kdef -- CGI num-raw step (a): the OPEN K-formula  Kdef L x  and its
-- num-raw code-builder  Kcode L : Fun1  (the negKgtCodeOf analog).
--
-- Per surprise.pdf, K(x) is the length of the shortest program that OUTPUTS x
-- AND STOPS (via a universal machine).  So definability is a SINGLE equation:
--
--   definable p x n  :=  evalU(parse p, n) = s x         ("p, run n steps, halted with output x")
--   "p outputs x"     :=  exists n. definable p x n
--
-- and it is MONOTONE (definable p x n -> definable p x m for n <= m), since the
-- halt configuration is a stepU-fixpoint (BRA4.EvalUStep.stepU_at_halt) -- so the
-- EXACT first halt time is irrelevant and no second "still running" conjunct is
-- needed.  The K-formula is the open Pi_1 negation (plain implication, spec SS2):
--
--   Kdef L x = imp (szLeq(p) = 1) (neg (definable p x n))        (p = var 0, n = var 1)
--
-- with the subject x kept as the TERM the program outputs, coded num-raw (the
-- single wrapAll hole  num x ), the recogniser delivering it, decode inverting num.
-- runProg packages  evalU . parse  as one Fun2 so its argument  p  is direct
-- (a clean num-leaf after instantiation -- the codeFXeqY2 shape dPos produces).

module BRA4.Kdef where

open import BRA4.Base
open import BRA4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import BRA4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 )
open import BRA4.Num using ( num )
open import BRA4.IsNat using ( num_eq_code ; isNat )
open import BRA4.NumContract using ( isNat_natCode )
open import BRA4.KFormula using ( szLeqFun ; szLeqApp )
open import BRA4.EvalUEval using ( evalU )
open import BRA4.ProgParse using ( parse )
open import BRA4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import BRA4.DoubleCodeNum using ( NoVar_codeFun1L )
open import BRA4.Thm12.ConstTermFun1 using ( NoVar_natCode )

------------------------------------------------------------------------
-- SECTION 1.  runProg : Fun2 -- the universal machine on a program NAME.
--   ap2 runProg p n = evalU (parse p) n   (parse decodes the name, faithful K).

runProg : Fun2
runProg = Fan (Lift1 parse) v evalU

runProg_eq :
  (p n : Term) ->
  Deriv (eqF (ap2 runProg p n) (ap2 evalU (ap1 parse p) n))
runProg_eq p n =
  ruleTrans (axFan (Lift1 parse) v evalU p n)
    (ruleTrans (congL evalU (ap2 v p n) (axLift parse p n))
               (congR evalU (ap1 parse p) (ax_v p n)))

------------------------------------------------------------------------
-- SECTION 2.  The open K-formula.  Free  var 0 = p (program name),
-- var 1 = n (fuel); subject  x .

-- definable p x n : the SINGLE-equation definability matrix ("p outputs x at n").
definable : Term -> Term -> Term -> Formula
definable p x n = eqF (ap2 runProg p n) (ap1 s x)

Kdef : Term -> Term -> Formula
Kdef L x =
  imp (eqF (szLeqApp L (var zero)) (ap1 s O))
      (neg (definable (var zero) x (var (suc zero))))

------------------------------------------------------------------------
-- SECTION 3.  The 7 constants of  codeFormula (Kdef L x)  (left children,
-- root -> hole), hole = codeTerm x .  Each carries its NoVar proof.

kdefConsts : Term -> NVList
kdefConsts L =
  nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula (eqF (szLeqApp L (var zero)) (ap1 s O)))
          (NoVar_codeFormula (eqF (szLeqApp L (var zero)) (ap1 s O)))
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap2 runProg (var zero) (var (suc zero))))
          (NoVar_codeTerm (ap2 runProg (var zero) (var (suc zero))))
  (nvcons (natCode tag_ap1) (NoVar_natCode tag_ap1)
  (nvcons (codeFun1 s) (NoVar_codeFun1L s)
  nvnil))))))

kdefSkel : Term -> Term -> Term
kdefSkel L h = skelOf (kdefConsts L) h

-- PIN (encoding bookkeeping, machine-checked): the 7 constants ARE the
-- codeFormula skeleton, hole = codeTerm subject (single coding).
skel_pins :
  (L x : Term) ->
  Eq (codeFormula (Kdef L x)) (kdefSkel L (codeTerm x))
skel_pins L x = refl

------------------------------------------------------------------------
-- SECTION 4.  Kcode + its PROVED correctness (hole filled  ap1 num subject ,
-- bridged to  codeTerm subject  by  num_eq_code  on the numeral).

Kcode : Term -> Fun1
Kcode L = wrapAll (kdefConsts L) num

Kcode_eval :
  (L x : Term) ->
  Deriv (eqF (ap1 (Kcode L) x) (kdefSkel L (ap1 num x)))
Kcode_eval L x = wrapAll_eq (kdefConsts L) num x

Kcode_correct :
  (L : Term) (n : Nat) ->
  Deriv (eqF (ap1 (Kcode L) (natCode n))
              (codeFormula (Kdef L (natCode n))))
Kcode_correct L n =
  ruleTrans (Kcode_eval L (natCode n))
            (skelOf_cong (kdefConsts L) (num_eq_code (natCode n) (isNat_natCode n)))

Kcode_correct_T :
  (L x : Term) -> isNat x ->
  Deriv (eqF (ap1 (Kcode L) x) (codeFormula (Kdef L x)))
Kcode_correct_T L x nx =
  ruleTrans (Kcode_eval L x)
            (skelOf_cong (kdefConsts L) (num_eq_code x nx))
