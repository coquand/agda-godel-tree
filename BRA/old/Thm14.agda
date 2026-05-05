{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14
--
-- Goedel's Second Theorem for BRA, faithful to Guard 1963 pp.16-17
-- (guard15.pdf, Theorem 14).
--
-- This file is the orchestrating layer that sits ABOVE
-- BRA.Thm14Abstract (which carries the closure  Deriv Con -> Deriv G
-- and  godelII = thm11 . closureToG ).
--
-- ARCHITECTURE
-- ============
--
-- The complete Goedel II argument (Guard p.16-17) is a 5-step internal
-- derivation under the hypothesis  th(x) = j , culminating in
-- "th(constr5(x)) = '0=1'".  In our setting the steps are:
--
--   1. Thm 13 on  thmT  + the hypothesis  th(x) = j  yields
--          th(D_thmT(x)) = "th(cor x) = j" .                     (Th 13 on thmT)
--   2. Thm 13 on  sub  + the closed fact  sub(i,i) = j  yields
--          th(D_sub(i,i)) = "sub(i,i) = j" .                     (Th 13 on sub)
--   3. axEqTrans  internalised + (1) + (2) yields
--          th(g(x)) = "th(cor x) = sub(i,i)" .                   (Step 3)
--   4. Definition 12 line 2 (the substitution clause of  th )
--      together with the diagonal lemma yields
--          th(...) = "neg(th(cor x) = sub(i,i))" .                (Step 4)
--   5. axNeg  + (3) + (4) yields
--          th(constr5(x)) = "0 = 1" .                             (Step 5)
--
-- Steps 1 + 2 are mechanical applications of  thm13_F1 / thm13_F2  (this
-- module exposes them inline as  step1_meta_at /  step2_meta ).
-- Step 3 is a meta-level  ruleTrans  on the combined equations.
-- Steps 4 and 5 require:
--
--   * the BRA-internalisation of Definition 12 line 2 ("sb"
--     primitive-recursive substitution on coded formulas) -- a
--     multi-file subproject not yet built;
--   * a Hilbert-style deduction-theorem-equivalent that lifts the
--     meta-arrow steps 1-3 into an INTERNAL implication of the shape
--     Thm14Abstract.GodelII.step5 demands.
--
-- Both of those gaps are documented in  BRA/THM14-OBSTRUCTIONS.md .
--
-- This module therefore takes the two outputs of those gaps -- the
-- Fun1 construction  constr5  and the proven internal implication
-- step5  -- as PARAMETERS, and discharges everything else from the
-- Theorem 12 / Theorem 13 specifications.  The headline
--
--   godelII : Deriv Con -> Deriv bot
--
-- is delivered by composing those parameters with the closure already
-- in  BRA.Thm14Abstract.GodelII  via  BRA.GoedelII.Compose .
--
-- IMPORT STRUCTURE
-- ================
--
-- This file imports  BRA.Thm13  for  thm13_F1 / thm13_F2  -- and
-- thereby Theorem 12's specification (via  Thm12_F1_Result  /
-- Thm12_F2_Result , which  BRA.Thm13  re-exports publicly).  It does
-- NOT import  BRA.Thm12  directly; the recursive  thm12_F1 / thm12_F2
-- machinery in  BRA.Thm12.FromBridges  is unnecessary here.
--
-- The Thm 12 results themselves are taken as parameters
-- ( r12_th , r12_sub ); a producer of those results lives in
-- BRA.Thm12 .

module BRA.Thm14 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Sub      using (sub ; subDef)

-- BRA.Thm13 re-exports  Thm12_F1_Result / Thm12_F2_Result  publicly
-- (these are the only Thm 12 names this file needs).
open import BRA.Thm13
  using (Thm12_F1_Result ; Thm12_F2_Result
       ; codeFTeq1 ; codeFTeq2
       ; codeFTeq1Hyp ; codeFTeq2Hyp
       ; thm13_F1 ; thm13_F2)

-- Concrete  thmT  and the closure infrastructure live in BRA.GoedelII
-- (which instantiates BRA.Thm14Abstract).  Re-using GoedelII.Compose
-- as the headline closure keeps the chain consistent with the
-- existing  BRA/GoedelII.agda  output.
open import BRA.GoedelII
  using (i ; cG ; PrAtX ; Con ; bot ; subIIeqcG)

import BRA.GoedelII

-- We need  thmT  by name in the parameter types below; pull it from
-- BRA.Thm.ThmT  (the canonical concrete  thmT ).
open import BRA.Thm.ThmT using (thmT)

------------------------------------------------------------------------
-- The Thm14 module proper.
--
--   r12_th  : Thm12_F1_Result thmT
--   r12_sub : Thm12_F2_Result sub
--   constr5 : Fun1
--   step5   : ...
--
-- The closure is delivered by  BRA.GoedelII.Compose  (which itself
-- composes  BRA.Thm14Abstract.GodelII  with the concrete  thmT ).

module Thm14
  -- Theorem 12 specifications -- consumed via Theorem 13.
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  -- The Thm 14 contract that  Thm14Abstract.GodelII  takes.
  --
  -- constr5 : Fun1
  --   Guard's "h" / "g"  construction (a Fun1 such that
  --   thmT(constr5(x))  evaluates to the code of  bot  under
  --   hypothesis  th(x) = cG ).  In the next session this would be
  --   built explicitly as   encMp (encMp h(x) g(x)) (step4_witness x)
  --   wrapped into a Fun1 via  Lift / KT / Comp / cor  arithmetic.
  --
  -- step5 : (x : Term) ->
  --         Deriv (PrAtX x  imp  th(constr5(x)) = code bot)
  --   Guard p.17 line 5 in internal-implication, meta-Pi form.  In a
  --   future session this would be discharged from steps 1-4 +
  --   axEqTrans / axNeg / axExFalso .
  (constr5 : Fun1)
  (step5 :
     (x : Term) ->
     Deriv ((atomic (eqn (ap1 thmT x) cG))
             imp (atomic (eqn (ap1 thmT (ap1 constr5 x))
                              (reify (codeFormula bot))))))
  where

  ----------------------------------------------------------------------
  -- Convenience names for the Thm 12 outputs that drive Steps 1 and 2.

  D_thmT : Fun1
  D_thmT = Thm12_F1_Result.Df r12_th

  thm12_thmT_proof :
    (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_thmT x)) (codeFTeq1 thmT x)))
  thm12_thmT_proof = Thm12_F1_Result.proof r12_th

  D_sub : Fun2
  D_sub = Thm12_F2_Result.Dg r12_sub

  thm12_sub_proof :
    (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_sub x v)) (codeFTeq2 sub x v)))
  thm12_sub_proof = Thm12_F2_Result.proof r12_sub

  ----------------------------------------------------------------------
  -- Step 1 (meta-arrow form).
  --
  -- Guard p.17 line 1.  Given  H : th(x) = cG , Theorem 13 instantiated
  -- on  thmT  (with  hyp = H , so the right-hand slot is rewritten from
  --  cor (th x)  to  cor cG ) yields:
  --
  --     th(D_thmT(x)) = codeFTeq1Hyp thmT x cG
  --
  -- where  codeFTeq1Hyp thmT x cG  is the encoded equation
  --     "th(cor x) = cor cG"  .
  --
  -- (Guard's "th(cor x) = j" .  In our system  cor cG  plays the role
  -- of Guard's  j  -- they coincide on the relevant numeral inputs.)

  step1_meta_at :
    (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT x) cG)) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_thmT x))
                       (codeFTeq1Hyp thmT x cG)))
  step1_meta_at x H = thm13_F1 thmT r12_th x cG H

  ----------------------------------------------------------------------
  -- Step 2 (closed).
  --
  -- Guard p.17 line 2.  Theorem 13 instantiated on  sub  with the
  -- closed hypothesis  subIIeqcG : sub(i,i) = cG  yields:
  --
  --     th(D_sub(i,i)) = codeFTeq2Hyp sub i i cG
  --
  -- where  codeFTeq2Hyp sub i i cG  is the encoded equation
  --     "sub(cor i, cor i) = cor cG"  .
  --
  -- This is closed in  x  -- it is a single derivation, not
  -- parameterised in any free variable.

  step2_meta :
    Deriv (atomic (eqn (ap1 thmT (ap2 D_sub i i))
                       (codeFTeq2Hyp sub i i cG)))
  step2_meta = thm13_F2 sub r12_sub i i cG subIIeqcG

  ----------------------------------------------------------------------
  -- Step 3 (meta-arrow form, optional).
  --
  -- Guard p.17 line 3 chains step 1 and step 2 via internalised
  -- equality transitivity.  At the meta level we have the two
  -- equations
  --
  --     E1 :  ap1 thmT (ap1 D_thmT x)   = codeFTeq1Hyp thmT x cG
  --     E2 :  ap1 thmT (ap2 D_sub i i)  = codeFTeq2Hyp sub i i cG
  --
  -- internalising the conjunction is exactly the missing  axEqTrans /
  -- mp  splicing that  step5  must perform.  We do not produce that
  -- splicing here; instead we expose  step1_meta_at  and  step2_meta
  -- as building blocks for downstream  step5  development.

  ----------------------------------------------------------------------
  -- Closure.  Delegate to  BRA.GoedelII.Compose constr5 step5 .
  --
  -- BRA.GoedelII.Compose  itself instantiates
  -- BRA.Thm14Abstract.Thm14.GodelII  on the concrete  thmT , giving
  --
  --     closureToG : Deriv Con -> Deriv G
  --     godelII    : Deriv Con -> Deriv bot
  --
  -- constructed from  step5  +  axContrapos  +  ruleInst  on  Con  +
  --  notEqTransport  +  G_unfold  +  thm11 .

  module Closure = BRA.GoedelII.Compose constr5 step5

  ----------------------------------------------------------------------
  -- Headline export: Goedel II.

  godelII : Deriv Con -> Deriv bot
  godelII = Closure.godelII
