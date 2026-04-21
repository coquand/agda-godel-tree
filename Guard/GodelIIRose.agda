{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIRose -- classical Gödel II via Rose's / Ryan's
-- object-level-implication approach.
--
-- Layer 5 of the Rose/Ryan Goedel II plan (see NEXT-SESSION-IMPT-GODELII.md).
--
-- The V3 Gödel II in  Guard/GodelIIV3.agda  states internal
-- consistency as a TreeEq-form equation:
--
--   conSentenceV3 = eqn (TreeEq (thmT (reify cGSV3) (var 0)) codeBotT)
--                        falseT .
--
-- Rose's (1967) / Ryan's (1978) formulation uses object-level
-- implication at the top level instead of an "= falseT":
--
--   conSentenceRose = eqn (impT (TreeEq (thmT (reify cGSV3) (var 0))
--                                        codeBotT)
--                                falseT)
--                         trueT
--
-- semantically "for every proof-encoding x,  impT (TreeEq .. codeBotT)
-- falseT  evaluates to trueT" -- i.e. "no x satisfies  TreeEq .. =
-- trueT", which is classical consistency.  The impT formulation has
-- the advantage that it composes cleanly with Rose's chained-MP proof
-- of Theorem 4.
--
-- Here we prove the analogue of V3's  godelIIV3 , now with  impT -form
-- consistency, by the Rose-style contradiction closure provided in
-- Layer 4 (Guard.RoseDC2).

module Guard.GodelIIRose where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompV3
open import Guard.Thm14EV3 using (thm14EV3)
open import Guard.GodelIV3 using (godelIDerivV3)
open import Guard.Nelson.SubstReify using (substReify)
open import Guard.ProvV3 hiding (trueT ; falseT)
open import Guard.ImpT
open import Guard.ImpTProp
open import Guard.RoseDC2

------------------------------------------------------------------------
-- Rose-style internal consistency sentence.
--
-- "For every proof-encoding x, it is NOT the case that  thmT(reify
-- cGSV3)(x) = codeBotT" -- with the "NOT" expressed via object-level
-- implication.

conSentenceRose : Equation
conSentenceRose =
  eqn (impT (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (var zero))
                         codeBotT)
             falseT)
      trueT

------------------------------------------------------------------------
-- Shared: the Gödel-I-via-thm14EV3 encoding of  trueT = falseT .

provBot : Prov3 godelSentenceV3 (eqn trueT falseT)
provBot = necessitation (thm14EV3 godelIDerivV3)

------------------------------------------------------------------------
-- Main theorem: from  conSentenceRose  as a Deriv-hypothesis, derive
-- trueT = falseT .

conToBotRose : {hyp : Equation} ->
  Deriv hyp conSentenceRose ->
  Deriv hyp (eqn trueT falseT)
conToBotRose {hyp} dCon = ruleSym falseIsTrue
  where
  ------------------------------------------------------------------
  -- Step 1: instantiate var 0 with enc provBot.
  -- The substitution is identity on the closed reified trees  reify
  -- cGSV3 , codeBotT , and on the closed  falseT = Pair O O ,  O .

  instD0 : Deriv hyp (substEq zero (enc provBot) conSentenceRose)
  instD0 = ruleInst zero (enc provBot) dCon

  -- The substituted form:  impT (TreeEq (thmT cGSV3-reified (enc
  -- provBot)) codeBotT) falseT = trueT .

  instForm : Eq (substEq zero (enc provBot) conSentenceRose)
    (eqn (impT (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (enc provBot))
                            codeBotT)
                falseT)
         trueT)
  instForm =
    eqCong2 eqn
      (eqCong2 (ap2 IfLf)
        (eqCong2 (ap2 TreeEq)
          (eqCong2 ap1
            (eqCong thmT (substReify zero (enc provBot) cGSV3))
            refl)
          (substReify zero (enc provBot) codeBot))
        refl)
      refl

  instD : Deriv hyp
    (eqn (impT (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (enc provBot))
                            codeBotT)
                falseT)
         trueT)
  instD = eqSubst (\eq -> Deriv hyp eq) instForm instD0

  ------------------------------------------------------------------
  -- Step 2: use  corr provBot  to show  thmT cGSV3 (enc provBot) =
  -- codeBotT .  Bridge  codeEqn godelSentenceV3  with  cGSV3  via
  -- cGSdefV3 (propositional equality of codes).

  corrBot : Deriv hyp (eqn (ap1 (thmT (reify cGSV3)) (enc provBot))
                           codeBotT)
  corrBot = eqSubst
    (\c -> Deriv hyp (eqn (ap1 (thmT (reify c)) (enc provBot)) codeBotT))
    (eqSym cGSdefV3)
    (corr provBot)

  ------------------------------------------------------------------
  -- Step 3: apply Rose's contradiction closure (from RoseDC2).
  --
  -- With  X := ap1 (thmT (reify cGSV3)) (enc provBot)  and the impT-
  -- form consistency  instD , roseContradict gives  falseT = trueT .

  falseIsTrue : Deriv hyp (eqn falseT trueT)
  falseIsTrue =
    roseContradict (ap1 (thmT (reify cGSV3)) (enc provBot))
      corrBot
      instD

------------------------------------------------------------------------
-- Gödel II (positive form) for the Rose encoding of consistency.

godelIIRosePositive :
  Deriv godelSentenceV3 conSentenceRose ->
  Deriv godelSentenceV3 (eqn trueT falseT)
godelIIRosePositive dCon = conToBotRose dCon

------------------------------------------------------------------------
-- Gödel II (negative / contrapositive form).
--
-- No consistent hypothesis proves its own  conSentenceRose .

godelIIRose :
  Consistent godelSentenceV3 ->
  Deriv godelSentenceV3 conSentenceRose ->
  Empty
godelIIRose con dCon = con (godelIIRosePositive dCon)

------------------------------------------------------------------------
-- Sharpest form: conSentenceRose alone is inconsistent.

godelIIRoseConAlone : Deriv conSentenceRose (eqn trueT falseT)
godelIIRoseConAlone = conToBotRose (ruleHyp {conSentenceRose})

------------------------------------------------------------------------
-- Summary
--
-- The Rose-style Gödel II mirrors  Guard.GodelIIV3 's godelIIV3 with
-- an impT-based internal consistency statement:
--
--   * conSentenceRose       : impT-form of "no x encodes a bot-proof"
--   * provBot               : Prov3 of godelSentenceV3 |- (trueT = falseT)
--   * conToBotRose          : dCon(Rose-form)  |-  trueT = falseT
--   * godelIIRosePositive   : positive Gödel II
--   * godelIIRose           : classical contrapositive
--   * godelIIRoseConAlone   : consistency alone is inconsistent
--
-- Machinery used (Rose-approach):
--   * impT / impTIntroByAntPair / impTOfTreeEqMP   (Guard.ImpT, ImpTProp)
--   * roseContradict                                (Guard.RoseDC2)
--
-- Machinery reused from V3 pipeline:
--   * thm14EV3 godelIDerivV3                        (Gödel I encoding)
--   * necessitation                                  (DC1)
--   * cGSdefV3                                       (cGSV3 = codeEqn gsV3)
--   * substReify                                     (subst-is-identity)
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.
