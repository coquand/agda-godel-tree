{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.NegAtomComp -- the search-side code-builder for the CORRECTED
-- (computation-naming) atom: the object functor  negAtomCompOf ell srch : Fun1
-- that, from a NUMERAL subject, builds the code  codeFormula (neg
-- (atomFormCompAt ell (linTop (ap1 srch ell)) (Df ell) subject))  the Chaitin
-- search's  hit / bridge  compares against (NEXT-SESSION-CHAITIN-G1.md Step 2b).
--
-- This is the  num -single companion of  BRA4.NegAtomCode  (which built the
-- OLD self-naming atom's code via  doubleCodeNum ).  The ONLY changes:
--
--   * the negated computation atom is a pure right-spine of  ap2 Pair  nodes
--     with CONSTANT left children, the same machinery (NegAtomCode.wrapAll /
--     skelOf / wrapAll_eq) reused VERBATIM, but the spine has 15 constants
--     (the OLD 13, with the name/proof slots pinned to the canonical  linTop
--     (ap1 srch ell) / Df ell , PLUS two new const nodes  tag_ap1 / codeFun1
--     num  introduced by the  num  wrapper in the 2nd conjunct);
--   * the hole is  codeTerm subject  (SINGLE), filled by the inner functor
--     num  (the search-side numeral coder), so the correctness bridge at the
--     hole is  num_eq_code  (num (natCode n) = codeTerm (natCode n)), NOT
--     doubleCodeNum_correct .  No double-coding, no  codeTermF .
--
-- The correctness  ap1 (negAtomCompOf ell srch) (natCode n) = codeFormula (neg
-- (atomFormCompAt ... (natCode n)))  is a PROVED  Deriv :
--   (i)  wrapAll_eq  -- the object evaluation of the nested  wrapL  spine, and
--   (ii) num_eq_code  at the hole, lifted by  skelOf_cong .
-- Only the pinning  skel_pins_comp  (that the 15 constants ARE the codeFormula
-- skeleton) is definitional -- pure encoding bookkeeping, machine-checked.

module BRA4.NegAtomComp where

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
open import BRA4.NegAtomCode
  using ( NVList ; nvnil ; nvcons ; wrapAll ; skelOf ; skelOf_cong ; wrapAll_eq
        ; NoVar_codeTerm ; NoVar_codeFormula )
open import BRA4.DoubleCodeNum using ( NoVar_codeFun1L ; NoVar_codeFun2L )
open import BRA4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import BRA4.Thm12.All using ( thm12 ; fst )

open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- SECTION 1.  The canonical name / proof slots (pinned, as in CompressComp).

-- the canonical description term-name  linTop (ap1 srch ell) .
canonName : Fun1 -> Term -> Term
canonName srch ell = linTop (ap1 srch ell)

-- the canonical proof code  Df ell = (fst (thm12 srch)) ell .
canonPrf : Fun1 -> Term -> Term
canonPrf srch ell = ap1 (fst (thm12 srch)) ell

------------------------------------------------------------------------
-- SECTION 2.  The 15 constants of the  codeFormula (neg (atomFormCompAt ell
-- (canonName srch ell) (canonPrf srch ell) subject))  right-spine (left
-- children, root to hole), each with its NoVar proof.
--
-- Spine (root -> hole):  tag_neg . tag_neg . tag_imp . codeFormula (leq ...)
-- . tag_neg . tag_eq . codeTerm (ap1 thmT prf) . tag_ap2 . codeFun2 Pair .
-- codeTerm (natCode tag_eq) . tag_ap2 . codeFun2 Pair . codeTerm (ap1 parse
-- flin) . tag_ap1 . codeFun1 num . [hole: codeTerm subject] .  The last two
-- (tag_ap1, codeFun1 num) are the  codeTerm (ap1 num subject)  wrapper -- the
-- NEW nodes vs NegAtomCode's 13-spine, from naming the VALUE via  num .

negConstsComp : Term -> Fun1 -> NVList
negConstsComp ell srch =
  nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
  (nvcons (natCode tag_neg) (NoVar_natCode tag_neg)
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
  nvnil))))))))))))))

-- the skeleton with the hole open.
negAtomCompSkel : Term -> Fun1 -> Term -> Term
negAtomCompSkel ell srch h = skelOf (negConstsComp ell srch) h

-- PIN (encoding bookkeeping, machine-checked): the 15 constants ARE the
-- skeleton, with the hole = codeTerm subject (single).
skel_pins_comp :
  (ell : Term) (srch : Fun1) (subject : Term) ->
  Eq (codeFormula (neg (atomFormCompAt ell (canonName srch ell)
                                       (canonPrf srch ell) subject)))
     (negAtomCompSkel ell srch (codeTerm subject))
skel_pins_comp ell srch subject = refl

------------------------------------------------------------------------
-- SECTION 3.  negAtomCompOf + its PROVED correctness.
--
-- Inner functor  num  : the hole is filled by  ap1 num subject , bridged to
-- the codeFormula hole  codeTerm subject  by  num_eq_code  on the numeral.

negAtomCompOf : Term -> Fun1 -> Fun1
negAtomCompOf ell srch = wrapAll (negConstsComp ell srch) num

-- the object evaluation:  ap1 (negAtomCompOf ell srch) subject = skeleton with
-- the hole filled by  ap1 num subject  (a Deriv, via the combinator axioms).
negAtomCompOf_eval :
  (ell : Term) (srch : Fun1) (subject : Term) ->
  Deriv (eqF (ap1 (negAtomCompOf ell srch) subject)
             (negAtomCompSkel ell srch (ap1 num subject)))
negAtomCompOf_eval ell srch subject =
  wrapAll_eq (negConstsComp ell srch) num subject

-- correctness for a NUMERAL subject:  PROVED Deriv (eval + num_eq_code at the
-- hole via skelOf_cong; the final skeleton = codeFormula (...) by skel_pins_comp).
negAtomCompOf_correct :
  (ell : Term) (srch : Fun1) (n : Nat) ->
  Deriv (eqF (ap1 (negAtomCompOf ell srch) (natCode n))
             (codeFormula (neg (atomFormCompAt ell (canonName srch ell)
                                               (canonPrf srch ell) (natCode n)))))
negAtomCompOf_correct ell srch n =
  ruleTrans (negAtomCompOf_eval ell srch (natCode n))
            (skelOf_cong (negConstsComp ell srch)
                         (num_eq_code (natCode n) (isNat_natCode n)))
