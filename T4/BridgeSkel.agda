{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BridgeSkel -- the Chaitin search recogniser's SOUNDNESS, in
-- skeleton-plugged (num-headed) form, UNIVERSAL in the subject.
--
-- The recogniser  hit z = eqInd (thmT z) (negAtomCompOf ell srch subj)  is the
-- decidable test "thmT z matches the fixed incompressibility template
-- code(neg Comp_L(.)), whose single hole is the Num-headed subject slot"
-- (chaitin-G1-statement.tex rem:subjcode; the subject is value-coded by
-- Num = Nelson's Name, elements.pdf SS19 #4).  Its SOUNDNESS is the shipped
-- numeric reflection  eqInd_sound  composed with the universal object
-- evaluation  negAtomCompOf_eval  (NegAtomComp):
--
--   bridgeSkel : a firing numeric match  hmatch  at  proofCode  means
--     thmT proofCode  =  negAtomCompSkel ell srch (num subj)
--   i.e. thmT proofCode is the fixed 15-constant skeleton with the Num-headed
--   subject  num subj  plugged into the hole.
--
-- This is the  num -single (Name) companion of  Bridge.bridge_subject_as_code
-- (which did the OLD self-naming skeleton).  It is SYMBOLIC in  subj  (no
-- numeral premise, no codeTermF) -- the soundness never touches the
-- codeTerm-vs-num question; that enters only when aligning  negAtomCompSkel
-- (num subj)  to  codeFormula (neg (atomComp ... subj))  (= num subj = codeTerm
-- subj, the numeral step  negAtomCompOf_correct  /  num_eq_code ), which the
-- subject being a numeral discharges.

module T4.BridgeSkel where

open import T4.Base
open import T4.ThmT using ( thmT )
open import T4.Num using ( num )
open import T4.Code using ( codeFormula ; codeTerm )
open import T4.NegAtomComp
  using ( negAtomCompOf ; negAtomCompOf_eval ; negAtomCompSkel
        ; negConstsComp ; canonName ; canonPrf )
open import T4.NegAtomCode using ( skelOf_cong )
open import T4.DefWitComp using ( atomFormCompAt )
open import T4.Bridge using ( eqInd_sound )
open import T4.Counting using ( eqInd ; eqInd_le_one )

open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- SECTION 1.  bridgeSkel -- recogniser soundness, num-headed, universal in subj.

bridgeSkel :
  (ell : Term) (srch : Fun1) (subj proofCode : Term) ->
  Deriv (eqF (eqInd (ap1 thmT proofCode) (ap1 (negAtomCompOf ell srch) subj))
             (ap1 s O)) ->
  Deriv (eqF (ap1 thmT proofCode) (negAtomCompSkel ell srch (ap1 num subj)))
bridgeSkel ell srch subj proofCode hmatch =
  ruleTrans (eqInd_sound (ap1 thmT proofCode)
                         (ap1 (negAtomCompOf ell srch) subj) hmatch)
            (negAtomCompOf_eval ell srch subj)

------------------------------------------------------------------------
-- SECTION 2.  The 0/1 bound for the recogniser indicator (= hit_le_one once
-- hit is wired through enum):  the shipped  eqInd_le_one .

hitBoundSkel :
  (a b : Term) -> Deriv (leq (eqInd a b) (ap1 s O))
hitBoundSkel = eqInd_le_one

------------------------------------------------------------------------
-- SECTION 3.  bridgeToCodeFormula -- bridgeSkel (num-headed) ==> the
-- codeFormula form the shipped ex-falso (CompressComp/ChaitinComp) consumes,
-- ISOLATING the whole residual to the SINGLE Deriv  num subj = codeTerm subj .
--
-- This is  BridgeComp.bridgeCompCore  GENERALISED from a meta-numeral  natCode n
-- to a SYMBOLIC subject  subj , with the numeral side-condition made EXPLICIT as
-- the hypothesis  numEqCode : num subj = codeTerm subj .  The num/code ~
-- numeral/term correspondence (the value-coder  num  vs the syntax-coder
-- codeTerm , Nelson's  Name  vs  ulcorner . urcorner ) is now LITERAL: the
-- recogniser's  num -headed match (bridgeSkel) lands on the verifier's
-- codeFormula  ( codeTerm -headed) form EXACTLY when  num subj = codeTerm subj ,
-- i.e. exactly when  subj  is a numeral (num_eq_code) -- the term-vs-numeral
-- boundary.  Everything else (eqInd_sound, negAtomCompOf_eval, skelOf_cong,
-- skel_pins_comp) is universal/symbolic.  So the entire Chaitin-G1 construction
-- reduces to this one fact about the search-output subject.

bridgeToCodeFormula :
  (ell : Term) (srch : Fun1) (subj proofCode : Term) ->
  Deriv (eqF (ap1 num subj) (codeTerm subj)) ->                 -- THE residual (= num_eq_code on a numeral)
  Deriv (eqF (eqInd (ap1 thmT proofCode) (ap1 (negAtomCompOf ell srch) subj))
             (ap1 s O)) ->                                      -- the numeric match  hmatch
  Deriv (eqF (ap1 thmT proofCode)
             (codeFormula (neg (atomFormCompAt ell (canonName srch ell)
                                               (canonPrf srch ell) subj))))
bridgeToCodeFormula ell srch subj proofCode numEqCode hmatch =
  ruleTrans (bridgeSkel ell srch subj proofCode hmatch)        -- thmT = negAtomCompSkel (num subj)
            (skelOf_cong (negConstsComp ell srch) numEqCode)   -- = negAtomCompSkel (codeTerm subj)
                                                               --   ( ==def==  codeFormula (neg (...)), skel_pins_comp )
