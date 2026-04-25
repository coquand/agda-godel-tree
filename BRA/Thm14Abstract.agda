{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14Abstract
--
-- Goedel II in BRA, factored to mirror Guard 1963 Thm 14 (p.16-17)
-- HONESTLY w.r.t. universal-closure semantics:
--
--   * Every Thm 14 step is a  Deriv  of an INTERNAL IMPLICATION
--     between two encoded equations (Guard's "th(x) = j ⊃ th(...) = '...'").
--   * No  Deriv (not P)  for open P as an intermediate (would be
--     unsound; see BRA/THM14-OBSTRUCTIONS.md "PINNED" section).
--   * No Sigma / meta-arrow contract shapes (cannot compose with
--     axContrapos in the closure).
--   * Con is PARAMETRIC in y (universally closed: "for all y,
--     th(y) != codeBot"), not a closed instance.
--
-- Architectural correction history: an earlier surface had 5
-- contracts (3 Sigma-form steps + internalStep5 + internalDiag).
-- Pre-flight verification of guard15.pdf revealed all 5 were
-- malformed at the type level: internalDiag asks for
-- closed-implies-universal (no Hilbert-style ruleInst), the Sigma
-- step shapes don't compose with axContrapos, and closed Con can't
-- be ruleInst-ed at the closure witness.  See
-- BRA/THM14-OBSTRUCTIONS.md.
--
-- The corrected single contract:
--
--   constr5 : Fun1                                 -- Guard's "h" / "g"
--             construction such that th(constr5(x)) computes "0=1"'s
--             code under the hypothesis th(x) = j .
--   step5   : (x : Term) ->                         -- meta-Pi over x
--             Deriv ((th(x) = cG) imp (th(constr5(x)) = "0=1"))
--             -- Guard p.17 line 5, internal-implication form.
--             -- Built (in a future session) from Guard's steps 1-4
--             -- + Definition 12 mp/sb clauses.
--
-- The closure  Deriv Con -> Deriv G  is then mechanical:
-- ruleInst step5 + axContrapos + ruleInst Con + mp + transport via
-- subIIeqcG and G_unfold.
--
-- Output:  godelII : Deriv Con -> Deriv bot

module BRA.Thm14Abstract where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.ReifyClosed
open import BRA.Sub using (sub ; subDef)
open import BRA.Thm14CodeFTeq using (codeFTeq)

import BRA.Thm11Abstract
import BRA.Thm11Diagonal

module Thm14
  (th : Fun1)
  (thClosed :
     (x : Nat) (r : Term) -> Eq (substF1 x r th) th)
  (codeF1Th_noVar :
     (x : Nat) (repl : Tree) ->
     Eq (codedSubst repl (code (var x)) (codeF1 th)) (codeF1 th))
  (encode :
     (P : Formula) -> Deriv P ->
     Sigma Tree (\ y ->
       Deriv (atomic (eqn (ap1 th (reify y))
                          (reify (codeFormula P))))))
  where

  open BRA.Thm11Diagonal.Diagonal th thClosed codeF1Th_noVar
    using (j ; G ; G_norm ; cc ; G_unfold ; diagonal ; notEqTransport) public

  open BRA.Thm11Abstract.Godel th G encode diagonal
    using (bot ; thm11) public

  ----------------------------------------------------------------------
  -- Convenience definitions (i, cG, PrAtX, Con).

  i : Term
  i = reify j

  cG : Term
  cG = reify (codeFormula G)

  -- Hypothesis predicate (parametric in x).  Guard's "th(x) = j" .
  PrAtX : Term -> Formula
  PrAtX x = atomic (eqn (ap1 th x) cG)

  -- Universally-closed consistency.  Guard's "th(y) != '0=1'" .
  -- Free variable is var zero; the closure ruleInst-s at constr5(var 1).
  Con : Formula
  Con = not (atomic (eqn (ap1 th (var zero))
                          (reify (codeFormula bot))))

  ----------------------------------------------------------------------
  -- Reusable lemma: ap2 sub i i = cG  (BRA-derivable via subDef + cc).
  --
  -- Used in the closure transport (cG <-> sub i i  step before G_unfold).

  subIIeqcG : Deriv (atomic (eqn (ap2 sub i i) cG))
  subIIeqcG =
    let sub_red :
          Deriv (atomic (eqn (ap2 sub i i)
                             (reify (codedSubst (code i)
                                                (code (var zero))
                                                j))))
        sub_red = subDef j j

    in eqSubst
         (\ T -> Deriv (atomic (eqn (ap2 sub i i) (reify T))))
         cc
         sub_red

  ----------------------------------------------------------------------
  -- The Goedel II module.

  module GodelII

    -- The single Thm 14 contract: a construction  constr5 : Fun1
    -- and an internal-implication parametric in  x , asserting
    -- Guard's step 5 (p.17 line 5):
    --   th(x) = j  ⊃  th(constr5(x)) = "0 = 1" .
    --
    -- Why meta-Pi (x : Term) ... : direct instantiation at any Term,
    -- with Agda computing substitution at typecheck time -- avoids
    -- substF / thClosed gymnastics in the closure body.

    (constr5 : Fun1)
    (step5 :
       (x : Term) ->
       Deriv ((atomic (eqn (ap1 th x) cG))
               imp (atomic (eqn (ap1 th (ap1 constr5 x))
                                (reify (codeFormula bot))))))

    where

    --------------------------------------------------------------------
    -- closureToG : from  Deriv Con  derive  Deriv G .
    --
    -- Mirrors Guard p.17 last paragraph:
    --   1. step5 at x := var 1   (meta).
    --   2. axContrapos                         (~codeBot ⊃ ~PrAtX(var 1)).
    --   3. ruleInst Con at constr5(var 1)      (~(th(constr5(var 1)) = codeBot)).
    --   4. mp                                   (~PrAtX(var 1)).
    --   5. notEqTransport via subIIeqcG        (G_norm).
    --   6. eqSubst via G_unfold                (G).

    closureToG : Deriv Con -> Deriv G
    closureToG conPf =
      let
          -- Step 1: instantiate step5 at x := var 1 (meta-Pi).
          A : Formula
          A = atomic (eqn (ap1 th (var (suc zero))) cG)

          B : Formula
          B = atomic (eqn (ap1 th (ap1 constr5 (var (suc zero))))
                          (reify (codeFormula bot)))

          step5_at1 : Deriv (A imp B)
          step5_at1 = step5 (var (suc zero))

          -- Step 2: axContrapos.
          contra5 : Deriv ((not B) imp (not A))
          contra5 = mp (axContrapos A B) step5_at1

          -- Step 3: ruleInst Con at constr5(var 1).
          --
          -- substF zero (ap1 constr5 (var 1)) Con  reduces to
          --   not (atomic (eqn (ap1 (substF1 0 (...) th)
          --                          (ap1 constr5 (var 1)))
          --                    (reify (codeFormula bot))))
          -- (the reify (codeFormula bot) RHS reduces by  reifyClosed ).
          -- thClosed converts substF1 0 (...) th  to  th .  Bridge via
          -- eqSubst.

          conRaw :
            Deriv (substF zero (ap1 constr5 (var (suc zero))) Con)
          conRaw = ruleInst zero (ap1 constr5 (var (suc zero))) conPf

          -- The thClosed-bridged target.
          conNorm : Deriv (not B)
          conNorm =
            eqSubst
              (\ T ->
                 Deriv (not (atomic
                              (eqn (ap1 T (ap1 constr5 (var (suc zero))))
                                   (subst zero (ap1 constr5 (var (suc zero)))
                                          (reify (codeFormula bot)))))))
              (thClosed zero (ap1 constr5 (var (suc zero))))
              conRaw

          -- The reifyClosed-bridged target ( subst on closed reify ).
          conFinal : Deriv (not B)
          conFinal =
            eqSubst
              (\ T ->
                 Deriv (not (atomic
                              (eqn (ap1 th (ap1 constr5 (var (suc zero))))
                                   T))))
              (reifyClosed (codeFormula bot)
                           zero
                           (ap1 constr5 (var (suc zero))))
              conNorm

          -- Step 4: mp gives  Deriv (not A) , i.e.  not PrAtX(var 1) .
          notPrAtX1 : Deriv (not A)
          notPrAtX1 = mp contra5 conFinal

          -- Step 5: transport cG -> sub i i  via  notEqTransport
          --         (using ruleSym subIIeqcG).
          --
          -- Result type uses  G_norm  (now exported transparent from
          -- Thm11Diagonal -- see that file for why).  Since
          --   G_norm = not (atomic (eqn (ap1 th (var 1)) (ap2 sub i i)))
          -- definitionally, notEqTransport's literal output unifies.

          gNormDeriv : Deriv G_norm
          gNormDeriv =
            notEqTransport (ap1 th (var (suc zero))) cG (ap2 sub i i)
              (ruleSym subIIeqcG)
              notPrAtX1

          -- Step 6: G_norm = G  via eqSym G_unfold + eqSubst.
          gDeriv : Deriv G
          gDeriv =
            eqSubst Deriv
              (eqSym G_unfold)
              gNormDeriv

      in gDeriv

    --------------------------------------------------------------------
    -- Goedel II.  thm11 collapses Deriv G -> Deriv bot.

    godelII : Deriv Con -> Deriv bot
    godelII conPf = thm11 (closureToG conPf)
