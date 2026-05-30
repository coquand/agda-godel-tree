{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.AtomComp -- the POSITIVE companion of BRA4.NegAtomComp: the search-side
-- code-builder  atomCompOf ell srch : Fun1  for the (un-negated) computation
-- atom  atomFormCompAt ell (canonName srch ell) (canonPrf srch ell) subject
-- (= Comp_L(subject)).  This is the num-headed positive code  P  the G1
-- assembly (BRA4.ChaitinG1) feeds as  dPos / dExF 's antecedent.
--
-- atomFormCompAt = fAnd C1 C2 = neg (imp C1 (neg C2)) , so
--   codeFormula (atomFormCompAt ...)
--     = codeFormula (neg (imp C1 (neg C2)))
-- which is EXACTLY  negConstsComp  MINUS its outer  tag_neg  (the negative atom
-- adds one further  neg  on top).  Hence  atomConstsComp = the tail of
-- negConstsComp : the SAME 14 lower constants, no leading neg.  All machinery
-- (NegAtomCode.wrapAll / skelOf / skelOf_cong / wrapAll_eq) and slots
-- (canonName / canonPrf) are REUSED; the hole is  codeTerm subject  (single),
-- bridged by  num_eq_code  on the numeral.  No double-coding, no codeTermF.

module BRA4.AtomComp where

open import BRA4.Base
open import BRA4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 )
open import BRA4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 )
open import BRA4.LenR using ( lenR )
open import BRA4.ThmT using ( thmT )
open import BRA4.Parse using ( parse )
open import BRA4.Num using ( num )
open import BRA4.IsNat using ( num_eq_code )
open import BRA4.NumContract using ( isNat_natCode )
open import BRA4.ParseRoundtrip using ( linTop )
open import BRA4.DefWitComp using ( atomFormCompAt )
open import BRA4.DefWit using ( cNeg )
open import BRA4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import BRA4.DoubleCodeNum using ( NoVar_codeFun1L ; NoVar_codeFun2L )
open import BRA4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import BRA4.NegAtomComp using ( canonName ; canonPrf ; negAtomCompOf ; negAtomCompOf_eval )

open import BRA3.ChurchLeq using ( leq )
open import BRA3.Equational using ( congR )

------------------------------------------------------------------------
-- SECTION 1.  The 14 constants of  codeFormula (atomFormCompAt ell
-- (canonName srch ell) (canonPrf srch ell) subject)  -- i.e. negConstsComp
-- with the OUTER  tag_neg  removed (the fAnd's own neg is the leading node).

atomConstsComp : Term -> Fun1 -> NVList
atomConstsComp ell srch =
  nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_imp) (NoVar_natCode tag_imp)
  (nvcons (codeFormula (leq (ap1 lenR (canonName srch ell)) ell))
          (NoVar_codeFormula (leq (ap1 lenR (canonName srch ell)) ell))
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_eq) (NoVar_natCode tag_eq)
  (nvcons (codeTerm (ap1 thmT (canonPrf srch ell)))
          (NoVar_codeTerm (ap1 thmT (canonPrf srch ell)))
  (nvcons (natCode tag_ap2) (NoVar_natCode tag_ap2)
  (nvcons (codeFun2 Pair) (NoVar_codeFun2L Pair)
  (nvcons (codeTerm (natCode tag_eq)) (NoVar_codeTerm (natCode tag_eq))
  (nvcons (natCode tag_ap2) (NoVar_natCode tag_ap2)
  (nvcons (codeFun2 Pair) (NoVar_codeFun2L Pair)
  (nvcons (codeTerm (ap1 parse (canonName srch ell)))
          (NoVar_codeTerm (ap1 parse (canonName srch ell)))
  (nvcons (natCode tag_ap1) (NoVar_natCode tag_ap1)
  (nvcons (codeFun1 num) (NoVar_codeFun1L num)
  nvnil)))))))))))))

-- the skeleton with the hole open.
atomCompSkel : Term -> Fun1 -> Term -> Term
atomCompSkel ell srch h = skelOf (atomConstsComp ell srch) h

-- PIN (encoding bookkeeping, machine-checked): the 14 constants ARE the
-- skeleton of the POSITIVE atom, hole = codeTerm subject (single).
skel_pins_pos :
  (ell : Term) (srch : Fun1) (subject : Term) ->
  Eq (codeFormula (atomFormCompAt ell (canonName srch ell)
                                  (canonPrf srch ell) subject))
     (atomCompSkel ell srch (codeTerm subject))
skel_pins_pos ell srch subject = refl

------------------------------------------------------------------------
-- SECTION 2.  atomCompOf + its PROVED correctness (mirrors NegAtomComp).

atomCompOf : Term -> Fun1 -> Fun1
atomCompOf ell srch = wrapAll (atomConstsComp ell srch) num

-- object evaluation:  ap1 (atomCompOf ell srch) subject = skeleton with the
-- hole filled by  ap1 num subject  (a Deriv, via the combinator axioms).
atomCompOf_eval :
  (ell : Term) (srch : Fun1) (subject : Term) ->
  Deriv (eqF (ap1 (atomCompOf ell srch) subject)
             (atomCompSkel ell srch (ap1 num subject)))
atomCompOf_eval ell srch subject =
  wrapAll_eq (atomConstsComp ell srch) num subject

-- correctness for a NUMERAL subject:  PROVED Deriv (eval + num_eq_code at the
-- hole via skelOf_cong; the final skeleton = codeFormula (...) by skel_pins_pos).
atomCompOf_correct :
  (ell : Term) (srch : Fun1) (n : Nat) ->
  Deriv (eqF (ap1 (atomCompOf ell srch) (natCode n))
             (codeFormula (atomFormCompAt ell (canonName srch ell)
                                          (canonPrf srch ell) (natCode n))))
atomCompOf_correct ell srch n =
  ruleTrans (atomCompOf_eval ell srch (natCode n))
            (skelOf_cong (atomConstsComp ell srch)
                         (num_eq_code (natCode n) (isNat_natCode n)))

------------------------------------------------------------------------
-- SECTION 3.  COMPLEMENTARITY  N = cNeg P  (the ex-falso soundness check).
--
-- The G1 assembly (BRA4.ChaitinG1) feeds  dExF : thmT cExF = cImp P (cImp N
-- codeFalse)  with  P = atomCompOf z0 ,  N = negAtomCompOf z0 .  That is the
-- genuine ex-falso  "P -> (not P -> 0=1)"  -- hence the spine is non-vacuous,
-- and  dExF  is buildable (Phase 2 = encoded_exfalso at cA = P) -- ONLY IF
--   N  =  cNeg P  =  the code of the NEGATION of  P .
-- Type-checking the assembly does NOT verify this (its codes are abstract
-- hypotheses).  Here it is PROVED:  negConstsComp = (tag_neg) :: atomConstsComp
-- and  cNeg c = ap2 Pair (natCode tag_neg) c , so  negAtomCompSkel = cNeg o
-- atomCompSkel  DEFINITIONALLY; lifting through the two  wrapAll  evals gives
-- the equation at the  ap1  level.

negAtomCompOf_eq_cNeg_atomCompOf :
  (ell : Term) (srch : Fun1) (subj : Term) ->
  Deriv (eqF (ap1 (negAtomCompOf ell srch) subj)
             (cNeg (ap1 (atomCompOf ell srch) subj)))
negAtomCompOf_eq_cNeg_atomCompOf ell srch subj =
  ruleTrans (negAtomCompOf_eval ell srch subj)               -- = negAtomCompSkel(num subj) ≡ cNeg(atomCompSkel(num subj))
            (congR Pair (natCode tag_neg)
                   (ruleSym (atomCompOf_eval ell srch subj))) -- cNeg(atomCompSkel(num subj)) = cNeg(ap1 atomCompOf subj)
