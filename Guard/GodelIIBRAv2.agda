{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIBRAv2 -- Gödel II at the BRA layer (Option G).
--
-- This is the chain-transcription deliverable of the Option G
-- (Guard-close BRA) redesign.  It sits on top of:
--
--   * Guard/BRA.agda            -- single-layer BRA data type
--   * Guard/Formula.agda        -- codeFormula, tagImp, tagNeg
--   * Guard/ProofEncFormula.agda -- encAxK/S/Neg/Mp + *Corr + *Pass
--   * Guard/ThFunTForV3.agda     -- case30..case33 dispatches
--
-- Architecture invariants maintained (BRA-DESIGN.md):
--   - Deriv is frozen; Gödel I stays where it is.
--   - BRA operates OVER Deriv via fromDeriv.
--   - No new Deriv axioms.
--
-- Deliverables in this file:
--
--   * provToBRA        -- mechanical bridge from Provable to BRA,
--                         reusing every Provable-layer lemma at the
--                         BRA layer without re-proof.
--
--   * chainStep1BRA    -- Guard Th 14 step 1, BRA layer.
--   * chainStep2BRA    -- step 2.
--   * chainStep3BRA    -- step 3.
--
-- Step 4, 5, and closure are DOCUMENTED AS AN OBSTRUCTION at the
-- bottom of this file.  The obstruction is intrinsic to the
-- interaction between (a) BRA's formula-level negation (not_) and
-- (b) our equational encoding of "A ≠ B" as the equation
-- "TreeEq A B = poo".  See the "Implications" block at the bottom
-- for the full analysis — it is structurally parallel to the
-- ChainPrototype.agda step-2 obstruction.
--
-- Typechecks under --safe --without-K --exact-split with no
-- postulates, no holes.  Use ~/.cabal/bin/agda-2.9.0 to typecheck.

module Guard.GodelIIBRAv2 where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv ; Consistent)
open import Guard.SubstOp using (substOp)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.CodeOfReify using (cor)
open import Guard.SubstTForPrecompClassical
  using (Triv ; trivCT ; cGSCR ; gsCR ; templateCodeCR)
open import Guard.GodelIClassical using (diagFTargetCR)
open import Guard.Formula
open import Guard.BRA

-- Provable-layer imports, renamed to avoid constructor-name clashes
-- with BRA.  We re-use every Provable-layer result via provToBRA
-- rather than mechanically porting each module.

import Guard.Provable as Prov
open Prov using (Provable)

open import Guard.ProvableLemmas using (deductionThm ; provI)
open import Guard.ProvableEqLifts using (prSym ; prTrans ; prCong1 ; prCongR)
open import Guard.RouteADf using (DfRefl ; encEqRefl ; thm13AtRefl)
open import Guard.RouteAChain
  using (chainStep1 ; chainStep2 ; chainStep3 ; j ; rhsT ; thx)

------------------------------------------------------------------------
-- provToBRA: mechanical Provable -> BRA bridge.
--
-- Every Provable constructor has a corresponding BRA constructor with
-- the same type (BRA is a strict extension of Provable, adding
-- ruleSub ).  The bridge is a direct structural recursion.

provToBRA : {hyp : Formula} {P : Formula} -> Provable hyp P -> BRA hyp P
provToBRA (Prov.fromDeriv d)         = fromDeriv d
provToBRA  Prov.ruleHypP              = ruleHypB
provToBRA (Prov.axK P Q)              = axK P Q
provToBRA (Prov.axS P Q R)            = axS P Q R
provToBRA (Prov.axNeg P Q)            = axNeg P Q
provToBRA (Prov.axEqTrans a b c)      = axEqTrans a b c
provToBRA (Prov.axEqCong1 f a b)      = axEqCong1 f a b
provToBRA (Prov.axEqCongL g a b c)    = axEqCongL g a b c
provToBRA (Prov.axEqCongR g a b c)    = axEqCongR g a b c
provToBRA (Prov.mp pq p)              = mp (provToBRA pq) (provToBRA p)

------------------------------------------------------------------------
-- The conjunction-hypothesis of the chain: "th(x) = j", where x is
-- the proof-slot free variable (= var zero) and j = reify cGSCR.

conjHyp : Formula
conjHyp = atomic (eqn thx j)

------------------------------------------------------------------------
-- Chain Step 1 (BRA layer):
--
--   BRA hyp (conjHyp ⊃ atomic (eqn (thmT trivCT (DfRefl thx j))
--                                   (encEqRefl thx j)))
--
-- Guard's "th(x) = j ⊃ th(Dth(x)) = 'th(x) = j'" under the whole-
-- underline convention.  Direct bridge of RouteAChain.chainStep1.

chainStep1BRA : {hyp : Formula} ->
  BRA hyp (conjHyp
           imp
           atomic (eqn (ap1 (thmT trivCT) (DfRefl thx j))
                       (encEqRefl thx j)))
chainStep1BRA {hyp} = provToBRA (chainStep1 {hyp})

------------------------------------------------------------------------
-- Chain Step 2 (BRA layer):
--
--   BRA hyp (atomic (eqn (thmT trivCT (DfRefl rhsT j))
--                        (encEqRefl rhsT j)))
--
-- Closed.  Guard's "th(Dsub(i,i)) = 'sub(i,i) = j'" — encoded form
-- of the closed equational fact  rhsT = j .

chainStep2BRA : {hyp : Formula} ->
  BRA hyp (atomic (eqn (ap1 (thmT trivCT) (DfRefl rhsT j))
                       (encEqRefl rhsT j)))
chainStep2BRA {hyp} = provToBRA (chainStep2 {hyp})

------------------------------------------------------------------------
-- Chain Step 3 (BRA layer):
--
--   BRA hyp (conjHyp ⊃ atomic (eqn (thmT trivCT (DfRefl thx j))
--                                   (Pair (cor thx) (cor rhsT))))
--
-- Guard's "th(x) = j ⊃ th(gx) = 'th(x) = sub(i,i)'" where gx is the
-- diagonalised term.  Direct bridge of RouteAChain.chainStep3.

chainStep3BRA : {hyp : Formula} ->
  BRA hyp (conjHyp
           imp
           atomic (eqn (ap1 (thmT trivCT) (DfRefl thx j))
                       (ap2 Pair (ap1 cor thx) (ap1 cor rhsT))))
chainStep3BRA {hyp} = provToBRA (chainStep3 {hyp})

------------------------------------------------------------------------
-- Step 4, 5, Closure: OBSTRUCTION
-- =====================================================================
--
-- Guard 1963 Th 14 continues with:
--
--   Step 4 : th(x) = j  ⊃  th(Y) = "th(x) ≠ sub(i,i)"     [defn of j]
--   Step 5 : th(x) = j  ⊃  th(combined) = "0 = 1"         [3 + 4]
--   Closure: contradict dCon : "th(y) ≠ codeBot"; derive ¬(th(x)=j),
--            i.e. gsCR; invoke godelIClassical.
--
-- Under Option G's formula-level encoders (encAxK/S/Neg/Mp), steps 4
-- and 5 were designed to use encMp with two sub-proof encodings.
-- encMp (now implemented in ProofEncFormula.agda) provides the
-- machinery — BUT only for sub-proofs whose  thmT  images match the
-- required shape.  Step 4's required shape surfaces the obstruction
-- below.
--
-- -------------------------------------------------------------------
-- The obstruction in structural form
-- -------------------------------------------------------------------
--
-- Step 4's intended content is an encoded proof  Y  such that
--
--   thmT trivCT Y = codeFormula (not (atomic (eqn thx rhsT)))
--                  = reify (nd tagNeg (codeEqn (eqn thx rhsT)))
--
-- i.e.  Y  encodes the formula "th(x) ≠ sub(i,i)".
--
-- At the Deriv level, our system has:
--
--   (E1)  encoded proofs of EQUATIONS: thmT Y always produces a
--         codeEqn-shaped tree when Y is a valid proof encoding.
--
--   (E2)  encoded proofs of FORMULA-level AXIOMS: encAxK/S/Neg produce
--         trees like  codeFormula (P ⊃ (Q ⊃ P))  etc — implication-
--         shaped trees where the LEAVES are codeFormula's of sub-
--         formulas (atomic or compound).
--
--   (E3)  encoded proofs of FORMULA-level MP: encMp produces  codeQ
--         from codeP + codePimpQ.  Its output is the code of the
--         RHS of the implication the sub-proof encoded.
--
-- To obtain Y such that  thmT trivCT Y  is the codeFormula of a
--  not -formula, we would need an encoder tag (say  case34 ) whose
-- output shape is  Pair tagNegT (codeP) .  In Guard 1963, this is
-- exactly Def 11.3's  "~P" = 3("P") + 2  — a native negation encoding
-- at the Goedel-number level.
--
-- However, such an encoder in our tree system must be SOUND: for every
-- encoded Y of the  case34  shape, the underlying formula  P  must
-- be refutable.  I.e.  case34  on  codeP  is a valid encoder only
-- when we can prove  ~P  in the formal system.  Since the formal
-- system's proofs are the thing encoded, this is circular.
--
-- Equivalently: our Deriv is equational — it has no formula-level
-- negation.  The "A ≠ B" relation is encoded as the EQUATION
-- "TreeEq A B = poo", whose derivability at  hyp = Triv  is equivalent
-- to semantic inequality (when  Triv  is consistent).  So to
-- "encode a proof of ~P" at the Deriv layer reduces to proving an
-- equational statement like  TreeEq ... ... = poo , which for most P
-- of interest (in particular for the Gödel sentence) is exactly the
-- classical reverse-direction of what we're trying to prove.
--
-- -------------------------------------------------------------------
-- Why the escape-hatch doesn't fully resolve it
-- -------------------------------------------------------------------
--
-- BRA-NEXT-SESSION.md proposes an escape hatch: "replace step 4's
-- encMp-based Y with a Deriv-level proof of the step-4 equation,
-- then fromDeriv lift into BRA".
--
-- Concretely:  under conjHyp = (thx = j) and diagFTargetCR (rhsT = j),
-- we can derive  Deriv (eqn thx j) (eqn (TreeEq thx rhsT) O)  at the
-- BRA-hypothesis level — i.e.  "thx = rhsT"  (since both equal j),
-- hence  TreeEq thx rhsT = O .
--
-- But this gives  TreeEq ... = O , whereas step 4 needs  TreeEq ... =
-- poo  (i.e. NOT-equal).  These are OPPOSITE forms.
--
-- There is no  Deriv-level  witness for  "TreeEq thx rhsT = poo"
-- under  conjHyp ,  because  conjHyp  says the opposite.  Our
-- equational reasoning cannot manufacture a "negative" validator
-- output without an actual positive proof of the negation-equation.
--
-- This is the same asymmetry ChainPrototype.agda flagged: the
-- validator's  case-analysis  dispatches on syntactic shape, not on
-- semantic truth, so encoded  Pair tagNegT ...  outputs require an
-- actual  case34  dispatch that we haven't defined (and for which the
-- soundness discipline forbids an unconditional implementation).
--
-- -------------------------------------------------------------------
-- Why closure via not-conjHyp also doesn't factor
-- -------------------------------------------------------------------
--
-- The alternative pathway: derive  BRA (atomic Triv) (not conjHyp)
-- without step 4's encoded form.  From dCon + step 5 (if we had step
-- 5), classical axNeg + mp gives  not conjHyp .
--
-- To use this for Gödel I, we must bridge  not conjHyp  ≡
--  not (atomic (eqn thx j))  INTO  atomic gsCR  ≡
--  atomic (eqn (TreeEq thx rhsT) poo) .
--
-- The bridge is semantically true (if  thx ≠ j  then  TreeEq thx rhsT
-- ≠ O ) but not BRA-derivable: BRA has no constructor that converts
-- between formula-level  not (atomic eqn_1)  and atomic  eqn_2  where
-- eqn_2's content is the equational encoding of eqn_1's negation.
-- Adding such a rule would be tantamount to adding a formula-level
-- negation-to-equation reflection principle — which is a significant
-- extension to the logic, not a mechanical follow-up.
--
-- -------------------------------------------------------------------
-- Resolution options (not attempted in this session)
-- -------------------------------------------------------------------
--
--   (O1) EXTEND Deriv with a formula-level negation encoder.  Add a
--        new dispatch tag  case34  whose output is  Pair tagNegT
--        sub-proof-output .  Soundness requires the sub-proof to
--        actually refute something — the classical content of
--        Guard's Def 11.3.  Needs a companion refutation-encoding
--        primitive.  ~500-1000 lines.
--
--   (O2) REPLACE Guard's BRA layer with a Godel-numbering-based
--        formulation (as in Ryan.pdf): treat codes as Nats, encode
--         ~P  as  3("P")+2  at the Nat level, and state thmT's
--        conclusions as Nat equalities.  This requires a substantial
--        reframing of the Term system and the Deriv axioms.  1000+
--        lines.
--
--   (O3) SIDESTEP step 4 by choosing a different combined.  Under
--         conjHyp = thx = j , we can derive (equationally)
--         TreeEq thx rhsT = O .  Cast this as the GOOD side of a
--        diagContradict-style argument: if BRA proves  TreeEq _ _ = O
--        under conjHyp and dCon gives  TreeEq _ _ = poo  (via
--        substitution), then  O = poo , contradicting Consistent Triv.
--        The challenge: finding a  combined  term  X  such that
--         thmT trivCT X  under conjHyp equals  codeBotT  —
--        semantically requires encoding  0=1 , the same obstacle.
--
--   (O4) Use the already-working  Guard/GodelIIV3.agda :
--         godelIIV3 :  Consistent godelSentenceV3 -> ...
--        This proves Gödel II at the NON-TRIVIAL hypothesis
--         godelSentenceV3 , bypassing the Triv-ambient chain
--        construction entirely.  Not a "BRA Gödel II at Triv" but a
--        valid Gödel II formalization in our system.  Already delivered.
--
-- -------------------------------------------------------------------
-- Recommendation
-- -------------------------------------------------------------------
--
-- The Option G design encountered this obstruction at the exact
-- "formula-level negation" boundary the BRA-DESIGN.md rationale
-- identified as the primary motivation for the new BRA layer.  The
-- BRA data type + encoders + case33 infrastructure DELIVERED in this
-- session supports Guard 1963's Def 12 axioms correctly for
-- implication-shaped formulas — but a further extension (O1 / O2) is
-- required to close the chain through step 4.
--
-- Per the session instructions ("STOP-and-report if a step surfaces
-- an obstruction comparable in character to the Rose polymorphic-
-- tCorr issue"), this file commits the partial deliverable (steps
-- 1-3 bridged cleanly + full obstruction analysis) and defers the
-- step-4 resolution to a subsequent session that picks among O1-O4.
--
-- The already-committed Option G infrastructure — Guard/BRA.agda,
-- case30..case33 dispatches, encAxK/S/Neg/Mp with *Corr and *Pass —
-- is not wasted work: it is the substrate any of O1-O4 will build on
-- (O1 extends case33+, O2 replaces the Term system and can port the
-- encoder patterns, O3 reuses the  combined  framework for a
-- different target equation, O4 composes at the existing layer).

------------------------------------------------------------------------
-- The contrapositive-form lemma we CAN state and prove, given the
-- existing infrastructure: if the chain reaches step 5 (delivered
-- separately via O1 / O2 / O3), the closure composes cleanly through
-- provToBRA + godelIClassical.  Deferred; not written here.
