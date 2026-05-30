{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.DefWitComp -- the COMPUTATION-naming atom (the CORRECTED Chaitin
-- definability layer), the search-side / DefWit-compatible companion of the
-- kernel BRA4.CompressComp.  See BRA4/CHAITIN-KERNEL-THM13.md and
-- BRA4/NEXT-SESSION-CHAITIN-G1.md (Step 2a).
--
-- The decisive one-line fix vs the old self-naming  DefWit.nameEqCode :
--
--   nameEqCode     flin x = cEqTm (ap1 parse flin) (codeTerm x)   -- RHS codeTerm x => DOUBLE-coded
--   nameEqCodeComp flin y = cEqTm (ap1 parse flin) (ap1 num   y)  -- RHS num y    => SINGLE-coded
--
-- The subject is the VALUE  y  (the search output, a numeral), named by its
-- numeral code  num y  (one application of the shipped coder  BRA4.Num.num ).
-- No  codeTerm -of-a-code, no  codeTermF .
--
-- The atom is the search side's open Pi_1 form  atomFormComp ell y  (free
-- name  var1 , proof  var2 ); its negation is the "no short program computes
-- y" predicate the bounded search refutes.  The single coherence point is
--
--   nameEqComp_roundtrip srch ell y (eN : isNat ell) :
--     Deriv (eqF (nameEqCodeComp (linTop (ap1 srch ell)) y)
--                (codeFXeqY1 srch ell y))
--
-- the COMPUTATION analogue of the shipped  DefWit.nameEq_roundtrip  (now with
-- the  num y  RHS): at the canonical name  linTop (ap1 srch ell)  the parsed
-- description equals  codeFXeqY1 srch ell y  -- the formula  thm13_singulary
-- produces and  CompressComp.dPosComp  targets.  Proved by  parse_roundtrip_term
-- plus the numeral identity  codeTerm ell = num ell  (num_eq_code, ell a
-- numeral) -- a Deriv chain, NOT a reduction.

module BRA4.DefWitComp where

open import BRA4.Base
open import BRA4.Tags using ( tag_eq ; tag_ap1 )
open import BRA4.Code using ( codeTerm ; codeFun1 )
open import BRA4.ThmT using ( thmT )
open import BRA4.LenR using ( lenR )
open import BRA4.Parse using ( parse )
open import BRA4.ParseRoundtrip using ( linTop ; parse_roundtrip_term )
open import BRA4.Num using ( num )
open import BRA4.IsNat using ( isNat ; num_eq_code )
open import BRA4.DefWit using ( cEqTm ; fAnd ; vFlin ; vPi )
open import BRA4.Thm12.Thm13 using ( codeFXeqY1 )

open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- SECTION 1.  The computation-naming code and atom.
--
-- nameEqCodeComp flin y : code of the TERM-EQUALITY naming formula  "g = y" ,
-- where  g  is the description term named by  flin  (parse flin = codeTerm g)
-- and the subject is the VALUE  y , coded by its numeral code  num y .  The
-- single-num RHS is the entire double-coding fix.

nameEqCodeComp : Term -> Term -> Term
nameEqCodeComp flin y = cEqTm (ap1 parse flin) (ap1 num y)

-- atomFormCompAt ell flin prf y : the computation-naming atom with name /
-- proof slots FILLED by  flin / prf .
--   (lenR flin <= ell)  AND  (thmT prf = code of  (g = y))  [g named by flin] .
atomFormCompAt : Term -> Term -> Term -> Term -> Formula
atomFormCompAt ell flin prf y =
  fAnd (leq (ap1 lenR flin) ell)
       (eqF (ap1 thmT prf) (nameEqCodeComp flin y))

-- atomFormComp ell y : the open computation-naming atom for value  y  at
-- budget  ell  (name = vFlin = var 1 , proof = vPi = var 2 , both free).
atomFormComp : Term -> Term -> Formula
atomFormComp ell y = atomFormCompAt ell vFlin vPi y

-- IncompressibleComp ell y : "no short program computes  y "  -- the open
-- Pi_1 negation the bounded search refutes (parallels  DefWit.Incompressible ).
IncompressibleComp : Term -> Term -> Formula
IncompressibleComp ell y = neg (atomFormComp ell y)

------------------------------------------------------------------------
-- SECTION 2.  The coherence (the NEXT-SESSION-CHAITIN-G1 sec.2/sec.7
-- alignment, in Agda).
--
-- nameEqComp_roundtrip : at the canonical name  linTop (ap1 srch ell) , the
-- computation-naming code equals  codeFXeqY1 srch ell y  -- the formula
-- thm13_singulary  produces and  CompressComp.dPosComp  targets.  So the open
-- atom (search side, canonically instantiated) and the kernel's closed atom
-- are the SAME formula.  Proof (no reduction-justified equalities):
--   * parse_roundtrip_term (ap1 srch ell) :
--       parse (linTop (ap1 srch ell)) = codeTerm (ap1 srch ell)
--                                      = Pair tag_ap1 (Pair (codeFun1 srch) (codeTerm ell))
--     (the last equality DEFINITIONAL, BRA4.Code.codeTerm on ap1);
--   * bridge the numeral slot  codeTerm ell = num ell  (num_eq_code, ell a
--     numeral) => parse (...) = Pair tag_ap1 (Pair (codeFun1 srch) (num ell))
--                             = codeFXeqY1's ap-slot ;
--   * wrap by the  tag_eq  head and the  num y  RHS slot (congR / congL).
-- This is the computation analogue of  DefWit.nameEq_roundtrip  (num y RHS).

nameEqComp_roundtrip :
  (srch : Fun1) (ell y : Term) -> isNat ell ->
  Deriv (eqF (nameEqCodeComp (linTop (ap1 srch ell)) y)
             (codeFXeqY1 srch ell y))
nameEqComp_roundtrip srch ell y eN =
  let
    -- the numeral identity, reversed:  codeTerm ell -> num ell .
    ellBridge : Deriv (eqF (codeTerm ell) (ap1 num ell))
    ellBridge = ruleSym (num_eq_code ell eN)

    -- lift it into the ap-slot of  codeTerm (ap1 srch ell) .
    apSlotBridge :
      Deriv (eqF (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 srch) (codeTerm ell)))
                 (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 srch) (ap1 num ell))))
    apSlotBridge =
      congR Pair (natCode tag_ap1) (congR Pair (codeFun1 srch) ellBridge)

    -- parse the canonical name and land in  codeFXeqY1 's ap-slot.
    parseEqApSlot :
      Deriv (eqF (ap1 parse (linTop (ap1 srch ell)))
                 (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 srch) (ap1 num ell))))
    parseEqApSlot =
      ruleTrans (parse_roundtrip_term (ap1 srch ell)) apSlotBridge
  in
    congR Pair (natCode tag_eq) (congL Pair (ap1 num y) parseEqApSlot)
