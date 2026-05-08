{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.GoedelII
--
-- Full chain composition: concrete Thm 11 (from BRA2.Thm.ThmT) plugged
-- into the abstract Goedel II tower (BRA2.Thm14Abstract).
--
-- After the universal-closure architectural correction
-- (see BRA/THM14-OBSTRUCTIONS.md "PINNED" section), the surface is
-- a SINGLE contract:
--
--   constr5 : Fun1                                 -- the construction
--   step5   : (x : Term) ->                         -- meta-Pi over x
--             Deriv ((th(x) = cG) imp (th(constr5(x)) = "0=1"))
--
-- This is Guard's step 5 (p.17 line 5) in honest internal-implication
-- form (no Sigma, no meta-arrow, no  Deriv (not P)  for open P).
--
-- Output:  godelII : Deriv Con -> Deriv bot
-- where  Con = not (atomic (eqn (ap1 thmT (var 0)) (reify codeBot))) ,
-- universally closed in y .

module BRA2.GoedelII where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv

import BRA2.Thm.ThmT
import BRA2.Thm14Abstract

----------------------------------------------------------------------
-- Pull concrete Thm 11 components from BRA2.Thm.ThmT.

open BRA2.Thm.ThmT
  using (thmT ; thClosed ; codeF1Th_noVar)

open BRA2.Thm.ThmT.WithDispatch
  using (encode)

----------------------------------------------------------------------
-- Instantiate Thm14Abstract.Thm14 with concrete Thm 11 components.

module Outer = BRA2.Thm14Abstract.Thm14 thmT thClosed codeF1Th_noVar encode

open Outer
  using (j ; j_isValue ; G ; G_norm ; G_unfold ; diagonal ; bot ; thm11
       ; i ; cG ; PrAtX ; Con ; subIIeqcG) public

----------------------------------------------------------------------
-- The composition module.  Takes the SINGLE Thm 14 contract
-- (constr5 + step5 in internal-implication / meta-Pi form) and
-- produces  godelII .

module Compose

  -- Guard's step 5 (p.17 line 5) for the BRA Goedel II chain.
  --
  -- constr5 : the singular functor such that  thmT(constr5(x))
  --           computes the code of  bot  under hypothesis
  --           thmT(x) = j .  Built (in a future session) from
  --           Guard's steps 1-4 + Definition 12 mp/sb clauses.
  --
  -- step5   : the parametric internal implication.  meta-Pi over x
  --           lets the closure instantiate at any Term without
  --           ruleInst gymnastics.

  (constr5 : Fun1)
  (step5 :
     (x : Term) ->
     Deriv ((atomic (eqn (ap1 thmT x) cG))
             imp (atomic (eqn (ap1 thmT (ap1 constr5 x))
                              (reify (codeFormula bot))))))

  where

  ----------------------------------------------------------------------
  -- Apply the abstract GodelII module with the contract.

  module Final = Outer.GodelII constr5 step5

  ----------------------------------------------------------------------
  -- Headline export: Goedel II.

  godelII : Deriv Con -> Deriv bot
  godelII = Final.godelII
