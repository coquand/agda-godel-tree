{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.NegAtomCode -- the object functor  negAtomCodeOf : Term -> Fun1  that
-- builds, from a NUMERAL subject, the code  codeFormula (neg (atomForm ell x))
-- that the Chaitin search's  hit / bridge  compares against (CHAITIN-G1-SEARCH-
-- DESIGN.md, interface (B), step 1).
--
-- METHODOLOGY (the user's point): the correctness equality is a PROVED  Deriv ,
-- NOT a definitional reduction.  codeFormula (neg (atomForm ell x))  is a pure
-- right-spine of  ap2 Pair  nodes with CONSTANT left children and the single
-- hole  codeTerm (codeTerm x)  at the bottom (term-equality atom: subject
-- occurs once).  So:
--   negAtomCodeOf ell = wrapAll (negConsts ell) doubleCodeNum
-- where  wrapAll  nests  wrapL c inner = C Pair (constTermFun1 c) inner , and the
-- correctness  ap1 (negAtomCodeOf ell) (natCode n) = codeFormula (neg (atomForm
-- ell (natCode n)))  is proved as a  Deriv  by:
--   (i)  wrapAll_eq  -- the object evaluation of the nested  wrapL  (combinator
--        axioms  ax_C  +  constTermFun1_eq , one induction over the spine), and
--   (ii) doubleCodeNum_correct  (a Deriv) at the hole, lifted by  skelOf_cong .
-- Only the pinning  skel_pins  (that the 13 constants ARE the codeFormula
-- skeleton) is definitional -- pure encoding bookkeeping, machine-checked, NOT
-- the mathematical content (which is (i)+(ii), genuine object Derivs).

module BRA4.NegAtomCode where

open import BRA4.Base
open import BRA4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2
                            ; tag_var ; tag_s ; tag_o ; tag_u ; tag_C
                            ; tag_v ; tag_R )
open import BRA4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 )
open import BRA4.LenR using ( lenR )
open import BRA4.ThmT using ( thmT )
open import BRA4.Parse using ( parse )
open import BRA4.DefWit using ( atomForm ; vFlin ; vPi )
open import BRA4.DoubleCodeNum
  using ( doubleCodeNum ; doubleCodeNum_correct
        ; NoVar_codeFun1L ; NoVar_codeFun2L )
open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; NoVarAnd ; mkAnd ; NoVar_natCode
        ; constTermFun1 ; constTermFun1_eq )

open import BRA3.ChurchLeq using ( leq )
open import BRA3.Equational using ( axRefl )

------------------------------------------------------------------------
-- SECTION 1.  NoVar for arbitrary codes (codes never contain  var ).

NoVar_codeTerm : (t : Term) -> NoVar (codeTerm t)
NoVar_codeTerm O          = tt
NoVar_codeTerm (var k)    = mkAnd (NoVar_natCode tag_var) (NoVar_natCode k)
NoVar_codeTerm (ap1 f t)  =
  mkAnd (NoVar_natCode tag_ap1)
    (mkAnd (NoVar_codeFun1L f) (NoVar_codeTerm t))
NoVar_codeTerm (ap2 g a b) =
  mkAnd (NoVar_natCode tag_ap2)
    (mkAnd (NoVar_codeFun2L g)
      (mkAnd (NoVar_codeTerm a) (NoVar_codeTerm b)))

NoVar_codeFormula : (P : Formula) -> NoVar (codeFormula P)
NoVar_codeFormula (atomic (eqn a b)) =
  mkAnd (NoVar_natCode tag_eq)
    (mkAnd (NoVar_codeTerm a) (NoVar_codeTerm b))
NoVar_codeFormula (neg p)   =
  mkAnd (NoVar_natCode tag_neg) (NoVar_codeFormula p)
NoVar_codeFormula (imp p q) =
  mkAnd (NoVar_natCode tag_imp)
    (mkAnd (NoVar_codeFormula p) (NoVar_codeFormula q))

------------------------------------------------------------------------
-- SECTION 2.  A NoVar-carrying list of constants + the spine builders.

data NVList : Set where
  nvnil  : NVList
  nvcons : (c : Term) -> NoVar c -> NVList -> NVList

-- wrapL c inner = C Pair (constTermFun1 c) inner :  ap1 _ x = ap2 Pair c (ap1 inner x).
wrapL : Term -> Fun1 -> Fun1
wrapL c inner = C Pair (constTermFun1 c) inner

wrapL_eq :
  (c : Term) -> NoVar c -> (inner : Fun1) (x : Term) ->
  Deriv (eqF (ap1 (wrapL c inner) x) (ap2 Pair c (ap1 inner x)))
wrapL_eq c nv inner x =
  ruleTrans (ax_C Pair (constTermFun1 c) inner x)
            (congL Pair (ap1 inner x) (constTermFun1_eq c nv x))

wrapAll : NVList -> Fun1 -> Fun1
wrapAll nvnil           baseF = baseF
wrapAll (nvcons c _ cs) baseF = wrapL c (wrapAll cs baseF)

skelOf : NVList -> Term -> Term
skelOf nvnil           h = h
skelOf (nvcons c _ cs) h = ap2 Pair c (skelOf cs h)

skelOf_cong :
  (cs : NVList) {h h' : Term} -> Deriv (eqF h h') ->
  Deriv (eqF (skelOf cs h) (skelOf cs h'))
skelOf_cong nvnil           e = e
skelOf_cong (nvcons c _ cs) e = congR Pair c (skelOf_cong cs e)

-- the object evaluation:  ap1 (wrapAll cs baseF) x = skelOf cs (ap1 baseF x) .
wrapAll_eq :
  (cs : NVList) (baseF : Fun1) (x : Term) ->
  Deriv (eqF (ap1 (wrapAll cs baseF) x) (skelOf cs (ap1 baseF x)))
wrapAll_eq nvnil           baseF x = axRefl (ap1 baseF x)
wrapAll_eq (nvcons c nv cs) baseF x =
  ruleTrans (wrapL_eq c nv (wrapAll cs baseF) x)
            (congR Pair c (wrapAll_eq cs baseF x))

------------------------------------------------------------------------
-- SECTION 3.  The 13 constants of the  codeFormula (neg (atomForm ell x))
-- right-spine (left children, root to hole), each with its NoVar proof.

negConsts : Term -> NVList
negConsts ell =
  nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula (leq (ap1 lenR vFlin) ell))
          (NoVar_codeFormula (leq (ap1 lenR vFlin) ell))
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap1 thmT vPi)) (NoVar_codeTerm (ap1 thmT vPi))
  (nvcons (natCode tag_ap2) (NoVar_natCode tag_ap2)
  (nvcons (codeFun2 Pair) (NoVar_codeFun2L Pair)
  (nvcons (codeTerm (natCode tag_eq)) (NoVar_codeTerm (natCode tag_eq))
  (nvcons (natCode tag_ap2) (NoVar_natCode tag_ap2)
  (nvcons (codeFun2 Pair) (NoVar_codeFun2L Pair)
  (nvcons (codeTerm (ap1 parse vFlin)) (NoVar_codeTerm (ap1 parse vFlin))
  nvnil))))))))))))

negAtomSkel : Term -> Term -> Term
negAtomSkel ell h = skelOf (negConsts ell) h

-- PIN (encoding bookkeeping, machine-checked):  the constants ARE the skeleton.
skel_pins :
  (ell x : Term) ->
  Eq (codeFormula (neg (atomForm ell x)))
     (negAtomSkel ell (codeTerm (codeTerm x)))
skel_pins ell x = refl

------------------------------------------------------------------------
-- SECTION 4.  negAtomCodeOf + its PROVED correctness.

negAtomCodeOf : Term -> Fun1
negAtomCodeOf ell = wrapAll (negConsts ell) doubleCodeNum

-- the object evaluation:  ap1 (negAtomCodeOf ell) x = skeleton with the hole
-- filled by  ap1 doubleCodeNum x  (a Deriv, via combinator axioms).
negAtomCodeOf_eval :
  (ell x : Term) ->
  Deriv (eqF (ap1 (negAtomCodeOf ell) x)
             (negAtomSkel ell (ap1 doubleCodeNum x)))
negAtomCodeOf_eval ell x = wrapAll_eq (negConsts ell) doubleCodeNum x

-- correctness for a NUMERAL subject:  PROVED Deriv (eval + doubleCodeNum_correct
-- at the hole via skelOf_cong; the final skeleton = codeFormula (...) by skel_pins).
negAtomCodeOf_correct :
  (ell : Term) (n : Nat) ->
  Deriv (eqF (ap1 (negAtomCodeOf ell) (natCode n))
             (codeFormula (neg (atomForm ell (natCode n)))))
negAtomCodeOf_correct ell n =
  ruleTrans (negAtomCodeOf_eval ell (natCode n))
            (skelOf_cong (negConsts ell) (doubleCodeNum_correct n))
