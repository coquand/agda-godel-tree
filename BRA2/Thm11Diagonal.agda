{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm11Diagonal
--
-- Gödel's diagonal lemma for Thm 11 (see BRA/THM11-GAP.md).
--
-- Spec (the content of "th is a BRA provability functor"):
--
--   th              : Fun1
--   thClosed        : substF1 x r th  =  th
--   codeF1Th_noVar  : codedSubst repl (code (var x)) (codeF1 th) = codeF1 th
--
-- Output (of the nested  Diagonal  module):
--
--   F_pre : Formula  = not (ap1 th (var 1) = ap2 sub (var 0) (var 0))
--   j     : Tree     = codeFormula F_pre
--   G     : Formula  = substF 0 (reify j) F_pre              -- Gödel sentence
--   diagonal : (y : Tree) -> Deriv G ->
--              Deriv (not (atomic (eqn (ap1 th (reify y))
--                                      (reify (codeFormula G)))))
--
-- Framing principle (per THM11-GAP.md):  correctness does not rely on
-- heavy computation.  Elements that would otherwise force Agda to
-- unfold through closed combinator trees (sub's Fan/Lift/KT/.. tree,
-- reify-of-code, etc.) are encapsulated inside an  abstract  block,
-- and their characteristic properties (G_unfold, step_A, cc) are
-- exposed as named propositional equations.  The top-level
--  diagonal  composes those equations without ever re-unfolding the
-- concrete shapes.

module BRA2.Thm11Diagonal where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.ReifyClosed
open import BRA2.CodeCommutes
open import BRA2.Sub using (sub ; subDef)

module Diagonal
  (th : Fun1)
  (thClosed :
     (x : Nat) (r : Term) -> Eq (substF1 x r th) th)
  (codeF1Th_noVar :
     (x : Nat) (repl : Tree) ->
     Eq (codedSubst repl (code (var x)) (codeF1 th)) (codeF1 th))
  where

  ------------------------------------------------------------------------
  -- The Gödel formula.

  F_pre : Formula
  F_pre = not (atomic (eqn (ap1 th (var (suc zero)))
                           (ap2 sub (var zero) (var zero))))

  ------------------------------------------------------------------------
  -- Heavy section: j, G, subClosed, cc, G_norm, G_unfold, step_A all
  -- depend on Agda normalising through sub's combinator tree (and
  -- codeCommutesFormula's traversal of F_pre).  We localise that work
  -- inside a single  abstract  block so the downstream  diagonal
  -- below re-uses the results opaquely (Agda does not re-unfold).

  abstract
    j : Tree
    j = codeFormula F_pre

    j_isValue : IsValue j
    j_isValue = codeFormula_isValue F_pre

    G : Formula
    G = substF zero (reify j) F_pre

    -- sub is closed under substitution.  Proof reduces through sub's
    -- Fan/Lift/KT/Post/.. combinator tree and the  reify (code ...)
    -- closed Terms inside the KT nodes; once localised here, consumer
    -- sites never see this reduction.
    subClosed : (x : Nat) (r : Term) -> Eq (substF2 x r sub) sub
    subClosed x r = refl

    -- Coding commutes with substitution, at F_pre.  Delegates to the
    -- generic  codeCommutesFormula  from BRA2.CodeCommutes.
    cc : Eq (codedSubst (code (reify j)) (code (var zero)) j) (codeFormula G)
    cc = eqSym (codeCommutesFormula zero (reify j) F_pre)

  -- Propositional normal form of G.  Eliminates substF1/substF2 on
  --  th  and  sub  using thClosed and subClosed.
  --
  -- KEPT OUTSIDE the  abstract  block above so downstream consumers
  -- (Thm14Abstract.closureToG) can construct  Deriv G_norm  via
  -- notEqTransport and then transport to  Deriv G  via  G_unfold .
  -- Inside-abstract would make the literal  Deriv (not ... )  produced
  -- by notEqTransport not unify with  Deriv G_norm .  j stays abstract.

  G_norm : Formula
  G_norm = not (atomic (eqn (ap1 th (var (suc zero)))
                            (ap2 sub (reify j) (reify j))))

  abstract
    G_unfold : Eq G G_norm
    G_unfold =
      let th_eq    = thClosed   zero (reify j)
          sub_eq   = subClosed  zero (reify j)

          inner_ap1 :
            Eq (ap1 (substF1 zero (reify j) th) (var (suc zero)))
               (ap1 th (var (suc zero)))
          inner_ap1 = eqCong (\ f -> ap1 f (var (suc zero))) th_eq

          inner_ap2 :
            Eq (ap2 (substF2 zero (reify j) sub) (reify j) (reify j))
               (ap2 sub (reify j) (reify j))
          inner_ap2 = eqCong (\ g -> ap2 g (reify j) (reify j)) sub_eq
      in eqCong (\ P -> not P)
           (eqCong atomic
             (eqCong2 eqn inner_ap1 inner_ap2))

    -- step_A:  substF 1 (reify y) G  =  F_G(y) , via G_unfold then
    -- thClosed + subClosed + reifyClosed on the concrete G_norm.
    step_A : (y : Tree) ->
             Eq (substF (suc zero) (reify y) G)
                (not (atomic (eqn (ap1 th (reify y))
                                  (ap2 sub (reify j) (reify j)))))
    step_A y =
      let via_unfold :
            Eq (substF (suc zero) (reify y) G)
               (substF (suc zero) (reify y) G_norm)
          via_unfold = eqCong (substF (suc zero) (reify y)) G_unfold

          th_eq      = thClosed  (suc zero) (reify y)
          sub_eq     = subClosed (suc zero) (reify y)
          reify_j_eq = reifyClosed j j_isValue (suc zero) (reify y)

          ap1_eq :
            Eq (ap1 (substF1 (suc zero) (reify y) th) (reify y))
               (ap1 th (reify y))
          ap1_eq = eqCong (\ f -> ap1 f (reify y)) th_eq

          ap2_eq :
            Eq (ap2 (substF2 (suc zero) (reify y) sub)
                    (subst (suc zero) (reify y) (reify j))
                    (subst (suc zero) (reify y) (reify j)))
               (ap2 sub (reify j) (reify j))
          ap2_eq = eqCong3 ap2 sub_eq reify_j_eq reify_j_eq

          fwd :
            Eq (substF (suc zero) (reify y) G_norm)
               (not (atomic (eqn (ap1 th (reify y))
                                 (ap2 sub (reify j) (reify j)))))
          fwd =
            eqCong (\ P -> not P)
              (eqCong atomic
                (eqCong2 eqn ap1_eq ap2_eq))
      in eqTrans via_unfold fwd

  ------------------------------------------------------------------------
  -- Propositional plumbing (generic, no reference to sub/th/j/G).

  imp_trans : (A B C : Formula) ->
              Deriv (A imp B) -> Deriv (B imp C) -> Deriv (A imp C)
  imp_trans A B C AB BC =
    mp (mp (axS A B C) (mp (axK (B imp C) A) BC)) AB

  eqSymImp : (a b : Term) ->
             Deriv (atomic (eqn a b) imp atomic (eqn b a))
  eqSymImp a b =
    let A : Formula
        A = atomic (eqn a b)
        B : Formula
        B = atomic (eqn a a)
        C : Formula
        C = atomic (eqn b a)
        AimpB : Deriv (A imp B)
        AimpB = mp (axK B A) (axRefl a)
        axT : Deriv (A imp (B imp C))
        axT = axEqTrans a b a
    in mp (mp (axS A B C) axT) AimpB

  -- From Deriv (T1 = T2) and Deriv (not (X = T1)), derive Deriv (not (X = T2)).
  notEqTransport :
    (X T1 T2 : Term) ->
    Deriv (atomic (eqn T1 T2)) ->
    Deriv (not (atomic (eqn X T1))) ->
    Deriv (not (atomic (eqn X T2)))
  notEqTransport X T1 T2 eT1T2 neg =
    let E : Formula
        E = atomic (eqn X T2)
        F : Formula
        F = atomic (eqn X T1)

        step1 : Deriv (atomic (eqn T2 X) imp atomic (eqn T1 X))
        step1 = mp (axEqTrans T2 T1 X) (ruleSym eT1T2)

        symE : Deriv (E imp atomic (eqn T2 X))
        symE = eqSymImp X T2

        symF : Deriv (atomic (eqn T1 X) imp F)
        symF = eqSymImp T1 X

        EimpF : Deriv (E imp F)
        EimpF =
          imp_trans E (atomic (eqn T1 X)) F
            (imp_trans E (atomic (eqn T2 X)) (atomic (eqn T1 X)) symE step1)
            symF

        negFimpnegE : Deriv (not F imp not E)
        negFimpnegE = mp (axContrapos E F) EimpF
    in mp negFimpnegE neg

  ------------------------------------------------------------------------
  -- Diagonal theorem.  Outside the  abstract  block: composes the
  -- opaque specs (j, G, step_A, cc) with subDef and notEqTransport.

  diagonal :
    (y : Tree) (pf : Deriv G) ->
    Deriv (not (atomic (eqn (ap1 th (reify y))
                            (reify (codeFormula G)))))
  diagonal y pf =
    let NEG_raw : Deriv (substF (suc zero) (reify y) G)
        NEG_raw = ruleInst (suc zero) (reify y) pf

        F_G : Formula
        F_G = not (atomic (eqn (ap1 th (reify y))
                               (ap2 sub (reify j) (reify j))))

        NEG_sub : Deriv F_G
        NEG_sub = eqSubst Deriv (step_A y) NEG_raw

        sub_red :
          Deriv (atomic (eqn (ap2 sub (reify j) (reify j))
                             (reify (codedSubst (code (reify j))
                                                (code (var zero))
                                                j))))
        sub_red = subDef j j_isValue j j_isValue

        sub_to_G :
          Deriv (atomic (eqn (ap2 sub (reify j) (reify j))
                             (reify (codeFormula G))))
        sub_to_G =
          eqSubst
            (\ T -> Deriv (atomic (eqn (ap2 sub (reify j) (reify j)) (reify T))))
            cc
            sub_red
    in notEqTransport (ap1 th (reify y))
                      (ap2 sub (reify j) (reify j))
                      (reify (codeFormula G))
                      sub_to_G
                      NEG_sub
