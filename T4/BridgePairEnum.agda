{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BridgePairEnum -- the user's pair-enumeration bridge, validated, and the
-- reduction of the WHOLE subject-coding question to the single fixed-skeleton
-- equation (A1).
--
-- SETTLED SEMANTICS (this conversation):  the search carries the subject as its
-- DOUBLE-QUOTATION  sc = codeTerm (codeTerm x)  of the short description term  x
-- (= chaitinSearch ell);  sc  is a SYNTACTIC payload, NOT the subject.  The
-- incompressibility code is the fixed skeleton with  sc  plugged:  negAtomSkel
-- ell sc  (NegAtomCode).
--
-- SECTION 1 (bridge_subject_as_code):  the bridge's soundness for an ARBITRARY
-- (symbolic) subject code  sc  is the SHIPPED numeric reflection  eqInd_sound
-- alone -- no  doubleCodeNum , no numeral premise.  (Confirms: the codeTerm-
-- coherence I called a wall is never invoked here.)
--
-- SECTION 2 (align):  GIVEN  (A1)  sc = codeTerm (codeTerm x) , the bridge's
-- dNeg  (= negAtomSkel ell sc)  IS the open-atom incompressibility code
-- codeFormula (neg (atomForm ell x)) .  So the entire subject-coding obligation
-- collapses to  (A1)  -- a single equation about ONE term  x , discharged (when
-- x = chaitinSearch ell  is the fixed description) by codeTermF-correctness on
-- that FIXED FoldRec skeleton (numeral leaves only).  This is the modest
-- representability fact, NOT a uniform symbolic-term theorem.
--
-- (Remaining, separately:  the open->closed  thmT_at_sb  thread substituting the
-- name/proof slots  var 1 := linTop x , var 2 := piStar x  to reach the CLOSED
-- atom  chaitinBarrierFinish  consumes;  and discharging  (A1)  at the fixed  g .)

module T4.BridgePairEnum where

open import T4.Base
open import T4.Code using ( codeTerm ; codeFormula )
open import T4.ThmT using ( thmT )
open import T4.DefWit using ( atomForm )
open import T4.NegAtomCode
  using ( negAtomSkel ; negConsts ; skelOf_cong ; skel_pins )
open import T4.Counting using ( eqInd )
open import T4.Bridge using ( eqInd_sound )

------------------------------------------------------------------------
-- SECTION 1.  The bridge for a SUBJECT-AS-CODE  sc  (arbitrary Term, symbolic-OK):
-- a firing numeric match means  thmT proofCode  reads as the incompressibility
-- code with the subject hole  =  sc .  PROVED by eqInd_sound alone.

bridge_subject_as_code :
  (ell sc proofCode : Term) ->
  Deriv (eqF (eqInd (ap1 thmT proofCode) (negAtomSkel ell sc)) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT proofCode) (negAtomSkel ell sc))
bridge_subject_as_code ell sc proofCode hmatch =
  eqInd_sound (ap1 thmT proofCode) (negAtomSkel ell sc) hmatch

------------------------------------------------------------------------
-- SECTION 2.  GIVEN (A1), the bridge's dNeg is the open-atom incompressibility
-- code.  The subject-coding question collapses to (A1) alone.
--
--   align :  (A1)  sc = codeTerm (codeTerm x)
--         -> dNeg  thmT proofCode = negAtomSkel ell sc
--         -> thmT proofCode = codeFormula (neg (atomForm ell x)) .
--
-- PROVED: rewrite the hole of the bridge's dNeg from  sc  to  codeTerm (codeTerm
-- x)  by (A1) under the fixed skeleton (skelOf_cong), then pin the skeleton to
-- codeFormula via skel_pins (the encoding-bookkeeping refl).

align :
  (ell x sc proofCode : Term) ->
  Deriv (eqF sc (codeTerm (codeTerm x))) ->                       -- (A1)
  Deriv (eqF (ap1 thmT proofCode) (negAtomSkel ell sc)) ->        -- bridge dNeg
  Deriv (eqF (ap1 thmT proofCode) (codeFormula (neg (atomForm ell x))))
align ell x sc proofCode a1 dneg =
  let s1 : Deriv (eqF (negAtomSkel ell sc)
                      (negAtomSkel ell (codeTerm (codeTerm x))))
      s1 = skelOf_cong (negConsts ell) a1
      d2 : Deriv (eqF (ap1 thmT proofCode)
                      (negAtomSkel ell (codeTerm (codeTerm x))))
      d2 = ruleTrans dneg s1
  in eqSubst (\ z -> Deriv (eqF (ap1 thmT proofCode) z))
             (eqSym (skel_pins ell x))
             d2
