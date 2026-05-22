{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Code -- the Guard-style pair-based coding scheme.
--
-- codeTerm / codeFun1 / codeFun2 / codeFormula are meta-level Agda
-- functions producing Term-level (Pair-encoded) outputs suitable
-- for inspection by thmT via the Fst / Snd projections of
-- BRA3.PairAlgebra.
--
-- Tag layout (BRA4/Tags.agda):
--
--   codeTerm O           = O                                            -- bare leaf
--   codeTerm (var k)     = Pair (natCode tag_var) (natCode k)
--   codeTerm (ap1 f t)   = Pair (natCode tag_ap1)
--                                (Pair (codeFun1 f) (codeTerm t))
--   codeTerm (ap2 g a b) = Pair (natCode tag_ap2)
--                                (Pair (codeFun2 g)
--                                  (Pair (codeTerm a) (codeTerm b)))
--
--   codeFun1 s           = natCode tag_s                                 -- leaf
--   codeFun1 o           = natCode tag_o
--   codeFun1 u           = natCode tag_u
--   codeFun1 (C g h1 h2) = Pair (natCode tag_C) (Pair (codeFun2 g)
--                                (Pair (codeFun1 h1) (codeFun1 h2)))
--
--   codeFun2 v           = natCode tag_v                                 -- leaf
--   codeFun2 (R g h1 h2) = Pair (natCode tag_R) (Pair (codeFun1 g)
--                                (Pair (codeFun2 h1) (codeFun2 h2)))
--
--   codeFormula (atomic (eqn a b)) = Pair (natCode tag_eq)
--                                          (Pair (codeTerm a) (codeTerm b))
--   codeFormula (neg p)            = Pair (natCode tag_neg) (codeFormula p)
--   codeFormula (imp p q)          = Pair (natCode tag_imp)
--                                          (Pair (codeFormula p) (codeFormula q))
--
-- NUM COLLAPSE.  Per BRA4/PLAN.md the design ideal is that
--   codeTerm (ap1 num t) = codeTerm t
-- holds syntactically.  In Agda one cannot pattern-match on the
-- *defined* Fun1  num  because  Fun1  is the BRA3 grammar
-- (s / o / u / C) with no num constructor.  Two consequences:
--
--   * codeTerm here is purely structural -- no num-special-case.
--   * The "num and code agree on numerals" property is provided as a
--     Deriv-level lemma in BRA4.IsNat:
--          num_eq_code : (t : Term) -> isNat t ->
--                         Deriv (eqF (ap1 num t) (codeTerm t))
--     for numerals  t .  For NON-numeral encoded subterms inside a
--     Pair tree, the bridge between  ap1 num (...)  and  codeTerm (...)
--     is handled where it arises (typically at Thm 14's Step 3 / 4
--     boundary; see PLAN.md "Step 3 <-> Step 4 alignment" section).

module BRA4.Code where

open import BRA4.Base
open import BRA4.Tags

------------------------------------------------------------------------
-- Fun1 / Fun2 mutually recursive coding.

codeFun1 : Fun1 -> Term
codeFun2 : Fun2 -> Term

codeFun1 s             = natCode tag_s
codeFun1 o             = natCode tag_o
codeFun1 u             = natCode tag_u
codeFun1 (C g h1 h2)   = ap2 Pair (natCode tag_C)
                          (ap2 Pair (codeFun2 g)
                            (ap2 Pair (codeFun1 h1) (codeFun1 h2)))

codeFun2 v             = natCode tag_v
codeFun2 (R g h1 h2)   = ap2 Pair (natCode tag_R)
                          (ap2 Pair (codeFun1 g)
                            (ap2 Pair (codeFun2 h1) (codeFun2 h2)))

------------------------------------------------------------------------
-- Term coding.

codeTerm : Term -> Term
codeTerm O           = O
codeTerm (var k)     = ap2 Pair (natCode tag_var) (natCode k)
codeTerm (ap1 f t)   = ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (codeTerm t))
codeTerm (ap2 g a b) = ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair (codeTerm a) (codeTerm b)))

------------------------------------------------------------------------
-- Formula coding.

codeFormula : Formula -> Term
codeFormula (atomic (eqn a b)) = ap2 Pair (natCode tag_eq)
                                   (ap2 Pair (codeTerm a) (codeTerm b))
codeFormula (neg p)            = ap2 Pair (natCode tag_neg) (codeFormula p)
codeFormula (imp p q)          = ap2 Pair (natCode tag_imp)
                                   (ap2 Pair (codeFormula p) (codeFormula q))

------------------------------------------------------------------------
-- Canonical "trivial truth"  0 = 0  used as the fallback output of
-- thmT and the handler dispatchers when shape-checking fails.
-- (Per validating-decoder invariant: bad inputs decode to a
-- derivable formula.)

codeTriv : Term
codeTriv = codeFormula (atomic (eqn O O))

------------------------------------------------------------------------
-- Canonical contradiction  0 = 1  (= the conclusion of Thm 11 / Thm 14).
-- Goedel I says  Deriv G -> Deriv (0 = 1) ; Goedel II says
--   Deriv (th(x0) != code(0=1)) -> Deriv (0 = 1) .

codeFalse : Term
codeFalse = codeFormula (atomic (eqn O (ap1 s O)))

falseF : Formula
falseF = atomic (eqn O (ap1 s O))
