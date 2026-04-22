{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ChainPrototype -- de-risk step for the BRA Gödel II chain.
--
-- Per NEXT-SESSION-BRA-GODELII.md, before scaling to the full combined
-- combinator we prototype the innermost  encInst  step and confirm the
-- thmT reduction strategy factors cleanly through case23V3 +
-- substOpCorrect.
--
-- Findings:
--
--   Form 1  (protoInstRed):  X Pair-structured with known thmT image.
--                            Factors cleanly via encRuleInstCorr.
--
--   Form 2  (see comment below):  X abstract (a generic Term variable).
--                                 DOES NOT factor.  The inner thmT of
--                                 Pair aR X  gets stuck at guardNdV3 /
--                                 guardLfV3, whose  IfLf(TreeEq X O, ..)
--                                 check does not reduce for abstract X.
--
-- See the "Implications for Route B" comment block at the bottom for
-- what this means for the chain construction.
--
-- Conventions: --safe --without-K --exact-split, no postulates, no
-- holes.  Use ~/.cabal/bin/agda-2.9.0 to typecheck.

module Guard.ChainPrototype where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstOp using (substOp)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT ; ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)
open import Guard.SubstTForPrecompClassical using (Triv ; trivCT)
open import Guard.ProofEnc using (encRuleInst ; encRuleInstCorr)
open import Guard.ThFunTForV3Pass using (ndDispatchV3PairMiss)

------------------------------------------------------------------------
-- Closed aR for the prototype.
--
-- We choose a fully-closed, Pair-structured aR so that dispMiss follows
-- directly from ndDispatchV3PairMiss.  For the real chain, aR will
-- correspond to the Gödel-diagonal substitution parameters (see
-- godelIClassical's rhsT).  If this prototype factors, we can later
-- substitute godelIClassical's aR by first reducing  ap1 cor (reify t)
-- via corOfReify.

private
  -- aR's first component: any non-O, non-natCode-shaped reified tree.
  -- Choosing  reify (nd (nd lf lf) lf) = Pair (Pair O O) O  ensures
  -- ndDispatchV3PairMiss applies (it needs  Pair (Pair a1 a2) b ).

  aPart : Term
  aPart = ap2 Pair (ap2 Pair O O) O

  bPart : Term
  bPart = ap2 Pair O O

  aR : Term
  aR = ap2 Pair aPart bPart

  dispMiss : (x' rc' : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 trivCT) (ap2 Pair aR x') rc')
                   (ap2 sndArg2 (ap2 Pair aR x') rc'))
  dispMiss x' rc' = ndDispatchV3PairMiss trivCT (ap2 Pair O O) O bPart x' rc'

------------------------------------------------------------------------
-- Form 1: Pair-structured X with known thmT image.
--
-- A direct application of encRuleInstCorr.  This confirms the innermost
-- ruleInst reduction factors WHEN we know X = Pair paR pbR and
-- thmT trivCT X = Pair lC r'C.  These are conditions typical of ProofE3-
-- encoded sub-proofs.

protoInstRed :
  (paR pbR lC r'C : Term) ->
  (subCorr : {h : Equation} ->
    Deriv h (eqn (ap1 (thmT trivCT) (ap2 Pair paR pbR)) (ap2 Pair lC r'C))) ->
  {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (encRuleInst aR (ap2 Pair paR pbR)))
                 (ap2 Pair (ap2 substOp aR lC) (ap2 substOp aR r'C)))
protoInstRed paR pbR lC r'C subCorr =
  encRuleInstCorr trivCT aR paR pbR lC r'C dispMiss subCorr

------------------------------------------------------------------------
-- Form 2: abstract X — THE OBSTRUCTION.
--
-- We would like:
--
--   protoInstRedAbs : (X : Term) -> {hyp : Equation} ->
--     Deriv hyp (eqn (ap1 (thmT trivCT) (encRuleInst aR X))
--                    (ap2 Pair (ap2 substOp aR L(X)) (ap2 substOp aR R(X))))
--
-- for some  L(X), R(X)  involving  thmT trivCT X .
--
-- encRuleInstCorr requires X of the form  ap2 Pair paR pbR  AND a
-- "subCorr" proof  thmT (Pair paR pbR) = Pair lC r'C .  For a fully
-- abstract  X : Term  we have neither: X is not syntactically a Pair,
-- and  thmT trivCT X  does not reduce.
--
-- One might hope to reduce one level further by hand:
--
--   thmT trivCT (encRuleInst aR X)
--     = Rec O (thmTStep trivCT) (Pair (reify (natCode n23)) (Pair aR X))
--     ~~> thmTStep trivCT (Pair tag (Pair aR X))
--                          (Pair (thmT trivCT tag) (thmT trivCT (Pair aR X)))
--
-- thmTStep's guard picks  ndDispatchV3  via  guardNdV3  (data is a Pair).
-- That routes to  case23V3  via  ndDisp23V3  (tag = n23 matches).
--
--   case23V3 orig recs
--     = Pair (ap2 substOp (origA orig recs) (recsBL orig recs))
--            (ap2 substOp (origA orig recs) (recsBR orig recs))
--     where  origA orig recs = Fst(Snd orig) = aR  (fine, syntactic)
--            recsBL/recsBR orig recs  need  Snd(Snd recs)  to be a Pair
--                                          so Fst/Snd can further reduce.
--
-- Snd(Snd recs) = thmT trivCT (Pair aR X) — an INNER Rec call:
--
--   thmT trivCT (Pair aR X)
--     = Rec O (thmTStep trivCT) (Pair aR X)
--     ~~> thmTStep trivCT (Pair aR X) (Pair (thmT trivCT aR) (thmT trivCT X))
--
-- Now thmTStep's guard check:  IfLf(TreeEq (Snd(Pair aR X)) O, ..., ..) .
-- Snd(Pair aR X) = X  (abstract).  The check  TreeEq X O  DOES NOT REDUCE
-- because X is neither syntactically  O  nor a syntactic  ap2 Pair _ _ .
--
-- This is the "IfLf-conditional thicket" the handoff warned about:
-- the validator's lf/nd dispatch stalls on abstract Terms.
--
-- Conclusion: the encRuleInstCorr-based reduction cannot be applied to
-- an abstract X.  Route B's chain, as outlined in the handoff, does not
-- factor as planned for X = var 0.

------------------------------------------------------------------------
-- Implications for Route B of the BRA Gödel II chain
-- =====================================================================
--
-- The handoff's Route B asks for
--
--   combinedCorr : (X : Term) -> {h : Equation} ->
--     Deriv h (eqn (ap2 TreeEq (ap1 (thmT trivCT) (combined X)) codeBotT)
--                  (ap2 TreeEq (ap1 (thmT trivCT) X) (reify cGSCR)))
--
-- polymorphically in X.  combined is supposed to wrap X inside ProofEnc
-- combinators (encRuleInst + encTrans + encSym + ..., mirroring the
-- godelIClassical derivation), with X at the input-proof leaf.  The
-- chain then instantiates this at X = var 0  (the free proof slot of
-- conBRAEqn) or  X = var 1  to keep  treeEqSelf  callsites sound.
--
-- The prototype above shows that encRuleInstCorr — the natural
-- reduction lemma for  encRuleInst  wrapping — requires the wrapped
-- sub-proof to be  Pair-structured  with a known  thmT  image, and
-- this assumption does NOT hold for an abstract  X .  More deeply, the
-- thmT validator's  lf/nd  dispatch is definitional: its IfLf guard
-- does not reduce without syntactic shape information on its input.
--
-- Therefore combinedCorr, stated polymorphically in an arbitrary
-- Term X, is not provable by following the godelIClassical-style
-- encoded-proof construction — the reductions bottom out structurally.
--
-- Redesign options to explore before attempting the full  combined :
--
--   (R1) Require the X-slot to be Pair-structured by construction.
--        Instantiate the chain with  X = Pair var0 var1  (or similar).
--        Adjust gsCR / conBRAEqn's variable schema to match.  Net: the
--        chain variable becomes a sub-component accessor rather than a
--        raw var 0.  Requires rebuilding parts of the diagonal.
--
--   (R2) Abandon the encoded-proof-tree approach for combined; construct
--        combined as a raw  IfLf -based Term that semantically picks
--         codeBotT  iff  thmT trivCT X = reify cGSCR .  No thmT-validator
--        reductions needed; the identity holds by  IfLf 's direct axioms.
--        Net: combined is no longer an encoded proof of 0=1, but a raw
--        Term whose thmT happens to match the target.  The chain would
--        bypass Thm 13 entirely.
--
--   (R3) Stay with Route B but give combinedCorr to only specific X
--        shapes — Pair-structured  X = Pair X1 X2 .  Prove the chain
--        modulo this structure (explicitly requiring the candidate-proof
--        to be a Pair).  The closure step would then only conclude
--         Provable (atomic Triv) (ConBRA'  imp  atomic gsCR') , where
--         ConBRA' / gsCR'  have the Pair-form variable.  This weakens the
--        final theorem's statement but may still imply Gödel II (since
--        every real encoded proof IS a Pair).
--
-- The handoff explicitly anticipates this: "If reduction gets stuck in
-- IfLf-conditional thickets (because validators emit sentinel O on
-- mismatched sub-proofs), redesign before scaling — do NOT spend a
-- session building the full combined only to discover the reduction
-- strategy doesn't factor."
--
-- This file is exactly that redesign checkpoint.  Next step: decide
-- among R1/R2/R3 (or a hybrid) before writing combined in full.
