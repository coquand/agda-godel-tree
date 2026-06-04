{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1Core -- a Sigma-shape (Con-FREE) Chaitin-Goedel I variant
-- AT THE Kgt / Deriv-LEVEL HYPOTHESIS  (NOT the documented  CGI_core ).
--
-- ***  THIS IS NOT THE  CGI_core  OF T4/CGI-NUMRAW-DESIGN.md.  ***
-- The documented  CGI_core  takes a PROVABILITY-LEVEL hypothesis with no
-- isNat:
--   CGI_core : (w x : Term) ->
--              Deriv (eqF (ap1 thmT w) (codeFormula (Kdef Lstar x))) ->
--              Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
-- See  T4/CGI-CORE-HANDOFF.md  for the design (and the standing
-- obstruction to discharging it directly).
--
-- What THIS module proves is the strictly STRONGER and more constrained
-- shape  CGI_core_Kgt_Deriv :  a  Deriv-level  proof  d : Deriv (Kgt
-- Lstar x)  plus  isNat  on the subject.  The hypothesis is convertible
-- to the documented  CGI_core 's  thmT -shape only via  thmT_complete_rec
-- (a Sigma_1-completeness reflection that itself injects an  isNat ),
-- so this module is the engineering-conditional warm-up, not the
-- target.
--
-- Assembled from:
--   T4.ChaitinG1FinalSigma.Assemble.chaitin_G1_Sigma  (Con-free spine
--     at the Kgt-codeFormula form)
--   +  T4.ChaitinG1Chain.Chain  (the gLcode-based dEval discharge).
--
-- Standing assumptions (surprise.pdf-granted; same as the consistency-
-- conditional barrier, MINUS the  con  hypothesis):
--   * nx, nOut, clOut -- the assumed subject  x  and the read-off
--                       subject are integers; the latter is closed.
--   * cl_encD, sim_encD -- the encoded proof is substT-/simSubstT-closed
--                         (the standard "no free term variables in the
--                         meta-encoding" assumption).
--
-- NO  con  PARAMETER:  the conclusion is the constructed proof code  z
-- of  0=1 , not  falseF .   Adding  con  externally and applying  it
-- to  z  refutes  z  to give  falseF  (the first-incompleteness
-- corollary), but the Con-free CORE statement is this  Sigma .

module T4.ChaitinG1Core where

open import T4.Base
open import T4.Code        using ( codeFalse )
open import T4.IsNat       using ( isNat )
open import T4.ThmT        using ( thmT )
open import T4.KFormula    using ( Kgt )
open import T4.KOut        using ( out_L )
open import T4.KGodel1Bridge using ( Lstar )
open import T4.Encode      using ( encode )

open import BRA3.Dispatch    using ( Closed )
open import BRA3.RuleInst2   using ( simSubstT )

import T4.ChaitinG1FinalSigma
import T4.ChaitinG1Chain

------------------------------------------------------------------------
-- CGI_core, the Σ-shape Chaitin-Gödel I.   Con-FREE.

open import T4.KClashSigma using ( Sigma ; mkSigma )
open T4.ChaitinG1FinalSigma.Assemble using ( chaitin_G1_Sigma ; firstProof )

-- THIS IS NOT CGI_core.   See header.
CGI_core_Kgt_Deriv :
  (x : Term) (nx : isNat x) (d : Deriv (Kgt Lstar x)) ->
  isNat   (ap1 (out_L Lstar) (firstProof x nx d)) ->
  Closed  (ap1 (out_L Lstar) (firstProof x nx d)) ->
  Closed  (encode d) ->
  ((a b : Term) ->
     Eq (simSubstT zero a (suc zero) b (encode d)) (encode d)) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
CGI_core_Kgt_Deriv x nx d nOut clOut cl_encD sim_encD =
  let open T4.ChaitinG1Chain.Chain
            x nx d cl_encD sim_encD
        using ( nTerm ; clN ; dEval_witness )
  in chaitin_G1_Sigma x nx d nOut clOut nTerm clN dEval_witness
