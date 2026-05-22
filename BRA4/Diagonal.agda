{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Diagonal -- Goedel's diagonal lemma in the BRA4 Pair-encoding,
-- parametric on the substitution functor  sb : Fun2  (via
-- BRA4.SbContract) and our concrete  num : Fun1  (BRA4.Num,
-- contract from BRA4.NumContract).
--
-- Given any single-variable Formula F (with var 0 free), produces:
--
--   H        : Formula  = F[ diag_sub / 0 ]
--   j        : Nat      = codeFormulaNat H
--   G        : Formula  = H[ natCode j / 0 ]              -- fixed-point
--   G_norm   : Formula  = F[ diag_inst / 0 ]
--   G_eq_norm : Eq G G_norm                                -- meta-Eq
--   diag_term_eq : Deriv (eqF diag_inst (codeFormula G))
--   bicond_fwd / bicond_bwd : G iff F[ codeFormula G / 0 ]
--
-- ARCHITECTURE.  Mirrors BRA3.Thm.Thm11.Diagonal but uses BRA4.Code
-- (Pair-encoded codeFormula / codeTerm returning Term, not Nat) and
-- BRA4.NatBridge.codeFormula_eq to bridge between the Pair-tree
-- codeFormula H and its flattened natCode (codeFormulaNat H).

module BRA4.Diagonal where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.NatBridge
open import BRA4.NumContract
open import BRA4.SbContract
open import BRA4.SbDerived

open import BRA3.Substitutivity using ( substF_cong )

------------------------------------------------------------------------
-- Local helpers: Eq congruence over a 2-arg function.

private
  eqCong2 :
    {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B} ->
    Eq x x' -> Eq y y' -> Eq (f x y) (f x' y')
  eqCong2 f refl refl = refl

------------------------------------------------------------------------
-- substT composition (Term).

private
  substT_compose_var :
    (k : Nat) (t1 r : Term) (m : Nat) ->
    Eq (substT k t1 (substT k r (var m)))
       (substT k (substT k t1 r) (var m))
  substT_compose_var k t1 r m = aux (natEq k m) refl
    where
      aux : (b : Bool) -> Eq (natEq k m) b ->
            Eq (substT k t1 (boolCase b r (var m)))
               (boolCase b (substT k t1 r) (var m))
      aux true  eqb = refl
      aux false eqb =
        eqSubst (\ b' -> Eq (boolCase b' t1 (var m)) (var m))
                (eqSym eqb)
                refl

  substT_compose :
    (k : Nat) (t1 r a : Term) ->
    Eq (substT k t1 (substT k r a))
       (substT k (substT k t1 r) a)
  substT_compose k t1 r O           = refl
  substT_compose k t1 r (var m)     = substT_compose_var k t1 r m
  substT_compose k t1 r (ap1 f a)   = eqCong (ap1 f) (substT_compose k t1 r a)
  substT_compose k t1 r (ap2 g a b) =
    eqCong2 (ap2 g) (substT_compose k t1 r a) (substT_compose k t1 r b)

  substE_compose :
    (k : Nat) (t1 r : Term) (e : Equation) ->
    Eq (substEq k t1 (substEq k r e))
       (substEq k (substT k t1 r) e)
  substE_compose k t1 r (eqn a b) =
    eqCong2 eqn (substT_compose k t1 r a) (substT_compose k t1 r b)

  substF_compose :
    (k : Nat) (t1 r : Term) (F : Formula) ->
    Eq (substF k t1 (substF k r F))
       (substF k (substT k t1 r) F)
  substF_compose k t1 r (atomic e) = eqCong atomic (substE_compose k t1 r e)
  substF_compose k t1 r (neg p)    = eqCong neg (substF_compose k t1 r p)
  substF_compose k t1 r (imp p q)  =
    eqCong2 imp (substF_compose k t1 r p) (substF_compose k t1 r q)

------------------------------------------------------------------------
-- The diagonal module.

module Diagonal
  (sbt sbf : Fun2) (sbC : SbContract sbt sbf)
  (num1 : Fun1) (numC : NumContract num1)
  (F   : Formula)
  where

  open NumContract numC

  -- Derived  sbfEq_codeFormula  via meta-induction on Formula.
  open Derive sbt sbf sbC

  ----------------------------------------------------------------------
  -- The diagonal substitution term.  Option B's sb takes
  --   ap2 sb (Pair (natCode k) substituent) (formula-code)
  -- so for var 0 in F we package  (k=0, substituent = num(var 0))  in
  -- the first arg and pass  var 0  (the formula-code slot, later
  -- substituted with  natCode j ) as the second arg.

  diag_sub : Term
  diag_sub = ap2 sbf (ap2 Pair (natCode zero) (ap1 num1 (var zero))) (var zero)

  ----------------------------------------------------------------------
  -- The diagonalised formula.

  H : Formula
  H = substF zero diag_sub F

  ----------------------------------------------------------------------
  -- Its Goedel handle, as a Nat (flattened codeFormula).

  j : Nat
  j = codeFormulaNat H

  ----------------------------------------------------------------------
  -- The fixed-point sentence.

  G : Formula
  G = substF zero (natCode j) H

  ----------------------------------------------------------------------
  -- Closed-form for G via substF composition.
  --
  -- substT 0 (natCode j) diag_sub
  --   = substT 0 (natCode j)
  --       (ap2 sb (ap2 Pair (natCode 0) (ap1 num1 (var 0))) (var 0))
  --   = ap2 sb (ap2 Pair (natCode 0) (ap1 num1 (natCode j))) (natCode j)
  -- by definitional reduction of substT on  var 0  (var 0 -> natCode j ;
  -- natCode 0  is closed under substT so unchanged).

  diag_inst : Term
  diag_inst = ap2 sbf (ap2 Pair (natCode zero) (ap1 num1 (natCode j))) (natCode j)

  G_norm : Formula
  G_norm = substF zero diag_inst F

  G_eq_norm : Eq G G_norm
  G_eq_norm = substF_compose zero (natCode j) diag_sub F

  ----------------------------------------------------------------------
  -- The diagonal equation.
  --
  -- Chain (Option B, in BRA4 Pair-encoding):
  --   (1)  ap1 num1 (natCode j) =Deriv= codeTerm (natCode j)            [numEq j]
  --   (2)  on (1), congR Pair under congL sb :
  --        diag_inst
  --        =Deriv= ap2 sb (ap2 Pair (natCode 0) (codeTerm (natCode j)))
  --                        (natCode j)
  --   (3)  natCode j =Deriv= codeFormula H                              [ruleSym codeFormula_eq H]
  --   (4)  congR sb on (3):
  --        =Deriv= ap2 sb (ap2 Pair (natCode 0) (codeTerm (natCode j)))
  --                        (codeFormula H)
  --   (5)  sbEq 0 H (natCode j):
  --        =Deriv= codeFormula (substF 0 (natCode j) H)
  --                 = codeFormula G  by definition.

  diag_term_eq : Deriv (eqF diag_inst (codeFormula G))
  diag_term_eq =
    let
      step1 :
        Deriv (eqF (ap1 num1 (natCode j)) (codeTerm (natCode j)))
      step1 = numEq j

      -- Lift step1 inside  Pair (natCode 0) (_) .
      step1_pair :
        Deriv (eqF (ap2 Pair (natCode zero) (ap1 num1 (natCode j)))
                    (ap2 Pair (natCode zero) (codeTerm (natCode j))))
      step1_pair = congR Pair (natCode zero) step1

      -- Lift inside  ap2 sbf (_) (natCode j) :  congL sbf (natCode j) on step1_pair.
      step2 :
        Deriv (eqF diag_inst
                    (ap2 sbf (ap2 Pair (natCode zero) (codeTerm (natCode j)))
                              (natCode j)))
      step2 = congL sbf (natCode j) step1_pair

      step3 :
        Deriv (eqF (natCode j) (codeFormula H))
      step3 = ruleSym (codeFormula_eq H)

      step4 :
        Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (codeTerm (natCode j)))
                              (natCode j))
                    (ap2 sbf (ap2 Pair (natCode zero) (codeTerm (natCode j)))
                              (codeFormula H)))
      step4 = congR sbf (ap2 Pair (natCode zero) (codeTerm (natCode j))) step3

      -- sbfEq_codeFormula gives:
      --   sbf (Pair (natCode 0) (codeTerm (natCode j))) (codeFormula H)
      --     =Deriv= codeFormula (substF 0 (natCode j) H)
      --           = codeFormula G  by definition of G.
      step5 :
        Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (codeTerm (natCode j)))
                              (codeFormula H))
                    (codeFormula G))
      step5 = sbfEq_codeFormula zero (natCode j) H
    in ruleTrans step2 (ruleTrans step4 step5)

  ----------------------------------------------------------------------
  -- The biconditional:  G iff F[ codeFormula G / 0 ] .

  F_at_codeG : Formula
  F_at_codeG = substF zero (codeFormula G) F

  -- G  -->  F[codeFormula G / 0] .
  bicond_fwd : Deriv (imp G F_at_codeG)
  bicond_fwd =
    let imp_norm : Deriv (imp G_norm F_at_codeG)
        imp_norm = substF_cong zero diag_inst (codeFormula G) diag_term_eq F
    in eqSubst (\ Gx -> Deriv (imp Gx F_at_codeG))
                (eqSym G_eq_norm)
                imp_norm

  -- F[codeFormula G / 0]  -->  G .
  bicond_bwd : Deriv (imp F_at_codeG G)
  bicond_bwd =
    let imp_norm : Deriv (imp F_at_codeG G_norm)
        imp_norm = substF_cong zero (codeFormula G) diag_inst
                                (ruleSym diag_term_eq) F
    in eqSubst (\ Gx -> Deriv (imp F_at_codeG Gx))
                (eqSym G_eq_norm)
                imp_norm
