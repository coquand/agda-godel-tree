{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Formula -- propositional formulas above the equational layer.
--
-- Following Guard 1963 (BRA, lecture notes p.10), formulas are
-- atomic equations or propositional combinations using ~ and ⊃.
-- We use ASCII names matching our project conventions:
--   atomic eq    -- A = B  (an Equation)
--   not_ P       -- ~ P
--   _imp_ P Q    -- P ⊃ Q

module BRA2.Formula where

open import BRA2.Base
open import BRA2.Term using
  ( Equation ; eqn ; Term ; substEq ; code ; reify
  ; Tree ; lf ; nd
  ; IsValue ; valO ; valNd
  ; tagAp1 ; tagAp2 ; tagVar
  ; tagAp1_isValue ; tagAp2_isValue ; tagVar_isValue
  ; codeF1 ; codeF2 ; codeF1_isValue ; codeF2_isValue
  ; natCode ; natCode_isValue
  ; code_isValue
  )

------------------------------------------------------------------------
-- Gödel-encoding of an equation (Guard 1963 Def 11, rule 1, tree form):
--   "A = B" = 3 J("A", "B")    -- with J replaced by binary pairing.
-- A two-child  nd  carrying the codes of LHS and RHS.

codeEqn : Equation -> Tree
codeEqn (eqn l r) = nd (code l) (code r)

------------------------------------------------------------------------
-- Formula: propositional combination of atomic equations.
--
-- Following Guard's BRA (axioms 11, 12, 13 use only ~ and ⊃ as
-- propositional connectives; other connectives could be defined as
-- abbreviations later if needed).

data Formula : Set where
  atomic : Equation -> Formula
  not_   : Formula -> Formula
  _imp_  : Formula -> Formula -> Formula

infixr 5 not_
infixr 4 _imp_

------------------------------------------------------------------------
-- Substitution at the Formula level: replace variable x with term t.
--
-- Atomic equations use the existing substEq (BRA2.Term).
-- Compound formulas recurse structurally.

substF : Nat -> Term -> Formula -> Formula
substF x t (atomic eq) = atomic (substEq x t eq)
substF x t (not P)     = not (substF x t P)
substF x t (P imp Q)   = (substF x t P) imp (substF x t Q)

------------------------------------------------------------------------
-- Gödel-encoding of formulas (Guard 1963 Def 11, tree form).
--
-- Guard 1963 numbering:
--   "A = B"   = 3J("A", "B")       -- atomic equation
--   "P ⊃ Q"   = 3J("P", "Q") + 1   -- implication
--   "~P"      = 3("P") + 2          -- negation
--
-- Tree form: atomic reuses  codeEqn  (two-child  nd ).  Implication
-- and negation use new distinguishing tags  tagImp  and  tagNeg ,
-- both chosen to be structurally disjoint from the term-encoding
-- tags  tagO / tagVar / tagAp1 / tagAp2  of  BRA2.Term .
--
-- Shape inspection at the outermost  nd :
--   atomic  ->  first-child = code of LHS (starts with tagO/Var/Ap1/Ap2)
--   impF    ->  first-child = tagImp  (nd (nd lf lf) (nd lf lf))
--   negF    ->  first-child = tagNeg  (nd (nd lf lf) lf)
-- These three are pairwise disjoint as tree shapes.

tagImp : Tree
tagImp = nd (nd lf lf) (nd lf lf)

tagNeg : Tree
tagNeg = nd (nd lf lf) lf

codeFormula : Formula -> Tree
codeFormula (atomic eq) = codeEqn eq
codeFormula (not P)     = nd tagNeg (codeFormula P)
codeFormula (P imp Q)   = nd tagImp (nd (codeFormula P) (codeFormula Q))

------------------------------------------------------------------------
-- IsValue helpers for the formula-level tags and codes.

tagNeg_isValue : IsValue tagNeg
tagNeg_isValue =
  valNd (nd lf lf) lf (valNd lf lf valO valO) valO

tagImp_isValue : IsValue tagImp
tagImp_isValue =
  valNd (nd lf lf) (nd lf lf)
        (valNd lf lf valO valO) (valNd lf lf valO valO)

codeEqn_isValue : (eq : Equation) -> IsValue (codeEqn eq)
codeEqn_isValue (eqn l r) =
  valNd (code l) (code r) (code_isValue l) (code_isValue r)

codeFormula_isValue : (P : Formula) -> IsValue (codeFormula P)
codeFormula_isValue (atomic eq) = codeEqn_isValue eq
codeFormula_isValue (not P)     =
  valNd tagNeg (codeFormula P) tagNeg_isValue (codeFormula_isValue P)
codeFormula_isValue (P imp Q)   =
  valNd tagImp (nd (codeFormula P) (codeFormula Q)) tagImp_isValue
        (valNd (codeFormula P) (codeFormula Q)
               (codeFormula_isValue P) (codeFormula_isValue Q))
