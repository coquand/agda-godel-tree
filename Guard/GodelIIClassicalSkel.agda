{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIClassicalSkel — architecture check for classical Gödel II.
--
-- This module is parameterised by  Phi : Fun1  and a polymorphic
-- "strong phiCorr" Deriv.  It derives godelIIClassical and its
-- contrapositive.  If this compiles, the top-level architecture is
-- sound; the remaining work is to construct Phi and strongPhiCorr
-- (the hard part — see design note at bottom of this file).
--
-- No postulates, no holes — everything is a module parameter until
-- supplied.  Under --safe, this file is self-contained.

module Guard.GodelIIClassicalSkel where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.GodelIClassical using (godelIClassical ; diagFTargetCR)
open import Guard.ProvV3 using (trueT ; falseT ; codeBotT)

------------------------------------------------------------------------
-- The "strong phiCorr" equation, as a type family.
--
-- Given a candidate Phi : Fun1, this is the Deriv signature that Phi
-- must satisfy for the architecture to go through.  The equation
-- equates, for every ambient hyp and every Term v0, the two TreeEqs:
--   LHS: TreeEq (thmT trivCT v0) (reify cGSCR)   — "v0 is a gsCR proof"
--   RHS: TreeEq (thmT trivCT (ap1 Phi v0)) codeBotT  — "Phi v0 is a bot proof"
--
-- NO object-level implication — it's a raw equation between TreeEqs.
-- Agda's arrow is used only at the meta level: the statement is
-- polymorphic in hyp (Agda's arrow) and universally quantified in v0
-- (Agda's Pi).

StrongPhiCorr : Fun1 -> Set
StrongPhiCorr Phi =
  (v0 : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR))
                 (ap2 TreeEq (ap1 (thmT trivCT) (ap1 Phi v0)) codeBotT))

------------------------------------------------------------------------
-- The theorem: given Phi and strongPhiCorr, classical Gödel II follows.

module WithPhi (Phi : Fun1) (strongPhiCorr : StrongPhiCorr Phi) where

  -- ConTriv: "no proof of ⊥ under Triv".  The classical Gödel II target.
  ConTriv : Equation
  ConTriv = eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT) falseT

  ----------------------------------------------------------------------
  -- Derive  gsCR  from  ConTriv , using Phi + strongPhiCorr.

  private
    v0 : Term ; v0 = var zero

    -- ruleInst ConTriv at var zero := ap1 Phi (var zero).
    -- substEq zero (ap1 Phi v0) replaces every  var zero  in
    -- ConTriv's equation with  ap1 Phi v0 .  The resulting equation
    -- has  v0  still free (because we substituted var 0 with a term
    -- containing var 0).  We need a computational lemma to confirm
    -- the substituted form.

    -- The post-instantiation equation is:
    --   TreeEq (thmT trivCT (ap1 Phi v0)) codeBotT = falseT
    -- Computed via substEq zero X (eqn (TreeEq (thmT trivCT (var 0)) codeBotT) falseT).
    --   substTerm zero (ap1 Phi v0) (var 0) = ap1 Phi v0       (hit)
    --   substTerm zero (ap1 Phi v0) trivCT = trivCT             (closed)
    --   substTerm zero (ap1 Phi v0) codeBotT = codeBotT         (closed)
    --   substTerm zero (ap1 Phi v0) falseT = falseT             (closed)
    -- Provided trivCT, codeBotT, falseT are all closed (no var).

  -- The substituted form.
  conTrivAtPhi : Equation
  conTrivAtPhi = eqn (ap2 TreeEq (ap1 (thmT trivCT) (ap1 Phi v0)) codeBotT) falseT

  -- Hypothesis: substEq zero (ap1 Phi v0) ConTriv = conTrivAtPhi.
  -- This is a purely computational lemma.  We expose it as a field
  -- here; it is derivable from substEq's definition + closedness of
  -- trivCT, codeBotT.  (See abstract block in SubstTForPrecompClassical.)

  -- We prove it outside the skeleton — here we rely on subst being
  -- definitionally the identity on closed terms, which Agda will
  -- accept directly.

  -- The computational lemma: substEq zero (ap1 Phi v0) ConTriv = conTrivAtPhi.
  -- This holds because trivCT, codeBotT, falseT are all closed (no free
  -- var 0).  We take it as a module parameter below because trivCT is
  -- inside an abstract block and Agda cannot unfold it to refl here.

  ruleInstStep :
    (substLemma : Eq (substEq zero (ap1 Phi v0) ConTriv) conTrivAtPhi) ->
    {hyp : Equation} -> Deriv hyp ConTriv -> Deriv hyp conTrivAtPhi
  ruleInstStep substLemma {hyp} dCon =
    eqSubst (Deriv hyp) substLemma (ruleInst zero (ap1 Phi v0) dCon)

  ----------------------------------------------------------------------
  -- From ConTriv and strongPhiCorr, derive the gsCR-like equation with
  -- reify cGSCR on the right (NOT diagBody; we'll bridge at the end).

  xEqFalseT :
    (substLemma : Eq (substEq zero (ap1 Phi v0) ConTriv) conTrivAtPhi) ->
    {hyp : Equation} -> Deriv hyp ConTriv ->
    Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR)) falseT)
  xEqFalseT substLemma dCon =
    ruleTrans (strongPhiCorr v0) (ruleInstStep substLemma dCon)

  ----------------------------------------------------------------------
  -- gsCR's actual form (see SubstTForPrecompClassical.gsCRForm) uses
  -- diagBody (the substOp expression) instead of reify cGSCR.
  -- Bridge via diagFTargetCR, which proves
  --   Deriv hyp (eqn diagBody (reify cGSCR))  polymorphically in hyp.
  --
  -- congR TreeEq (thmT trivCT v0) diagFTargetCR gives us
  --   TreeEq (thmT trivCT v0) diagBody = TreeEq (thmT trivCT v0) (reify cGSCR)
  -- and then ruleTrans with xEqFalseT closes it.

  private
    v1 : Nat ; v1 = suc zero
    tgtT : Tree ; tgtT = natCode v1

    diagBody : Term
    diagBody = ap2 substOp
                 (ap2 Pair (ap1 cor (reify templateCodeCR)) (reify (natCode v1)))
                 (reify templateCodeCR)
      where
      open import Guard.SubstOp using (substOp)
      open import Guard.CodeOfReify using (cor)

  -- gsCR in its literal form (from SubstTForPrecompClassical.gsCRForm):
  --   gsCR = eqn (TreeEq (thmT trivCT v0) diagBody) falseT

  gsCRForm' : Eq gsCR
    (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) diagBody) falseT)
  gsCRForm' = gsCRForm
    where
    open import Guard.SubstOp using (substOp)
    open import Guard.CodeOfReify using (cor)

  ----------------------------------------------------------------------
  -- gsCRFromConTriv : the key lemma.

  gsCRFromConTriv :
    (substLemma : Eq (substEq zero (ap1 Phi v0) ConTriv) conTrivAtPhi) ->
    {hyp : Equation} -> Deriv hyp ConTriv -> Deriv hyp gsCR
  gsCRFromConTriv substLemma {hyp} dCon =
    eqSubst (Deriv hyp) (eqSym gsCRForm') result
    where
    -- Bridge: TreeEq (thmT trivCT v0) diagBody = TreeEq (thmT trivCT v0) (reify cGSCR)
    bridge : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) diagBody)
                            (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR)))
    bridge = congR TreeEq (ap1 (thmT trivCT) v0) diagFTargetCR

    result : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) diagBody) falseT)
    result = ruleTrans bridge (xEqFalseT substLemma dCon)

  ----------------------------------------------------------------------
  -- Classical Gödel II (positive and contrapositive).

  godelIIClassical :
    (substLemma : Eq (substEq zero (ap1 Phi v0) ConTriv) conTrivAtPhi) ->
    Deriv Triv ConTriv -> Deriv Triv (eqn trueT falseT)
  godelIIClassical substLemma dCon =
    godelIClassical (gsCRFromConTriv substLemma dCon)

  godelIIClassicalContra :
    (substLemma : Eq (substEq zero (ap1 Phi v0) ConTriv) conTrivAtPhi) ->
    Consistent Triv -> Deriv Triv ConTriv -> Empty
  godelIIClassicalContra substLemma con dCon =
    con (godelIIClassical substLemma dCon)

------------------------------------------------------------------------
-- Design note on the remaining work (constructing Phi + strongPhiCorr).
--
-- Phi : Fun1 is intended to internalise godelIClassical's action on a
-- proof encoding.  Concretely, Phi v0 should structurally match the
-- encoding produced by  encT (thm14EV3 (godelIClassical dGS))  when v0
-- plays the role of  encT (thm14EV3 dGS)  for some hypothetical dGS.
--
-- For strongPhiCorr to be derivable as a polymorphic Deriv, Phi must
-- be "well-behaved" on BOTH valid and invalid inputs:
--   * Valid v0 (thmT trivCT v0 = reify cGSCR, i.e. v0 encodes a gsCR
--     proof):  Phi v0 evaluates under thmT to codeBotT.  Both TreeEqs
--     equal O.
--   * Invalid v0:  Phi v0 evaluates under thmT to something ≠ codeBotT
--     (e.g. the sentinel O produced by unmatched tags).  Both TreeEqs
--     equal poo.
--
-- This "dichotomy preservation" is the critical property that makes
-- strongPhiCorr derivable without object-level implication.
--
-- Construction options:
--   (A) Phi performs a "verified dispatch": structurally examine v0,
--       apply godelIClassical's encoded steps only to well-formed
--       sub-trees, and produce a sentinel otherwise.  This is large
--       (estimated ~2000 lines) but mechanical.
--   (B) Accept strongPhiCorr as the primary theorem to prove by Schema
--       F / tree induction over v0, leaving Phi somewhat abstract.
--       Smaller (~500 lines) but requires careful lemma design.
--
-- Either way, the SKELETON (this file) proves that ONCE Phi and
-- strongPhiCorr exist, classical Gödel II follows in ~20 lines of
-- combinator application.
