{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KFormula -- Phase E2 (CHAITIN-G1-STANDARD-DIRECTION.md SS3/SS5):
-- the code-size indicator  szLeq , the open Pi_1 Kolmogorov formula
--   Kgt L x  :=  ~( szLeq(e,L)=1  /\  evalU(e,n)=s x )    (free e,n)
-- and the search-side object code-builder  negKgtCodeOf : the Fun1 that,
-- from a NUMERAL subject, rebuilds  codeFormula (Kgt L subject) .
--
-- This is the standard-route analog of BRA4.NegAtomComp (the discarded
-- provability atom's code-builder): the SAME wrapAll / skelOf / num-headed
-- machinery (reused verbatim from BRA4.NegAtomCode), only the skeleton
-- changes -- 9 constants down the right spine of  codeFormula (Kgt L x) ,
-- hole = codeTerm subject (single), bridged by  num_eq_code .

module BRA4.KFormula where

open import BRA4.Base
open import BRA4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_s )
open import BRA4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 )
open import BRA4.LenR using ( lenR )
open import BRA4.Num using ( num )
open import BRA4.IsNat using ( num_eq_code )
open import BRA4.NumContract using ( isNat_natCode )
open import BRA4.EvalUEval using ( evalU )
open import BRA4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import BRA4.DoubleCodeNum using ( NoVar_codeFun1L )
open import BRA4.Thm12.ConstTermFun1 using ( NoVar_natCode ; constTermFun1 )

open import BRA3.Church using ( isZero ; sub )

------------------------------------------------------------------------
-- SECTION 1.  The code-size indicator  szLeqFun L : Fun1 .
--   ap1 (szLeqFun L) e  =  isZero (sub (lenR e) L)  ( = s O iff |e| <= L ).
--
-- For E2 only the CODE codeFun1 (szLeqFun L) is used (an opaque closed
-- constant inside Kgt); its reduction / dLen is Phase E3 (when L is pinned).

szLeqFun : Term -> Fun1
szLeqFun L = compose1U isZero (C sub lenR (constTermFun1 L))

szLeqApp : Term -> Term -> Term
szLeqApp L e = ap1 (szLeqFun L) e

------------------------------------------------------------------------
-- SECTION 2.  The K-formula.  Free object variables  var 0 = e (program),
-- var 1 = n (runtime).  x = the subject (the value asserted incompressible).
--
--   pKgt L     :=  szLeq(e,L) = 1            (the size budget)
--   qKgt L x   :=  evalU(e,n) = s x          (the machine halts with output x)
--   Kgt L x    :=  ~( pKgt /\ qKgt )  =  ~ ~( pKgt  ->  ~ qKgt )

pKgt : Term -> Formula
pKgt L = eqF (szLeqApp L (var 0)) (ap1 s O)

qKgt : Term -> Term -> Formula
qKgt L x = eqF (ap2 evalU (var 0) (var 1)) (ap1 s x)

Kgt : Term -> Term -> Formula
Kgt L x = neg (neg (imp (pKgt L) (neg (qKgt L x))))

------------------------------------------------------------------------
-- SECTION 3.  The 9 constants of  codeFormula (Kgt L x)  (left children,
-- root -> hole).  Hole = codeTerm x .  Each carries its NoVar proof
-- (codes never contain  var ).

kgtConsts : Term -> NVList
kgtConsts L =
  nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula (pKgt L)) (NoVar_codeFormula (pKgt L))
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap2 evalU (var 0) (var 1)))
          (NoVar_codeTerm (ap2 evalU (var 0) (var 1)))
  (nvcons (natCode tag_ap1) (NoVar_natCode tag_ap1)
  (nvcons (codeFun1 s) (NoVar_codeFun1L s)
  nvnil))))))))

kgtSkel : Term -> Term -> Term
kgtSkel L h = skelOf (kgtConsts L) h

-- PIN (encoding bookkeeping, machine-checked): the 9 constants ARE the
-- codeFormula skeleton, hole = codeTerm subject (single coding).
skel_pins :
  (L x : Term) ->
  Eq (codeFormula (Kgt L x)) (kgtSkel L (codeTerm x))
skel_pins L x = refl

------------------------------------------------------------------------
-- SECTION 4.  negKgtCodeOf + its PROVED correctness (the num-headed
-- code-builder: hole filled by  ap1 num subject , bridged to  codeTerm
-- subject by  num_eq_code  on the numeral).

negKgtCodeOf : Term -> Fun1
negKgtCodeOf L = wrapAll (kgtConsts L) num

negKgtCodeOf_eval :
  (L subject : Term) ->
  Deriv (eqF (ap1 (negKgtCodeOf L) subject) (kgtSkel L (ap1 num subject)))
negKgtCodeOf_eval L subject = wrapAll_eq (kgtConsts L) num subject

negKgtCodeOf_correct :
  (L : Term) (n : Nat) ->
  Deriv (eqF (ap1 (negKgtCodeOf L) (natCode n))
              (codeFormula (Kgt L (natCode n))))
negKgtCodeOf_correct L n =
  ruleTrans (negKgtCodeOf_eval L (natCode n))
            (skelOf_cong (kgtConsts L) (num_eq_code (natCode n) (isNat_natCode n)))
