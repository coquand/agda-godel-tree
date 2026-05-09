{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.ExtractDemand -- partial extractor turning an
-- IndBTContext0 (atomic e) bot  into an  (t, IsValue t, DemandEq e t)
-- triple.
--
-- Step 1 (this file): cover the `hole` case directly.  All other
-- constructors return `nothing`.  This is the minimal first version
-- the user requested ((d.2) follow-up).
--
-- Why F is an explicit parameter rather than fixing the output to
-- bot : pattern-matching on  `inst x t ctx`  with output  bot
-- requires Agda to invert  `substF x t Q = bot` , which is a
-- function-equation it cannot solve (analogous to the  `ruleInstB`
-- issue in T1's BoundedReductionAtomicAbsurd probe).  By taking F
-- as a free index and accepting  Eq F bot  as a witness, all
-- constructors of IndBTContext0 become matchable; the equality
-- can be inspected after the case split.  The user-facing entry
-- point  extractDemandSimple  specialises to F = bot via refl.
--
-- Two paths to fully handle  inst (and sym/trans wrappers around it)
-- are noted in the next-session doc:
--
--   (P1) Refactor IndBTContext0's  `inst`  to carry an explicit
--        propositional equality witness for its output index.
--   (P2) Use a discriminator-shape function to dispatch on the
--        constructor without unifying the output.

module BRA2.ExtractDemand where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.IndBTContext0
open import BRA2.DerivT0 using (bot)
open import BRA2.UnfoldAtValue using (botEqn)
open import BRA2.IndBTElimDemo using (DemandEq)

------------------------------------------------------------------------
-- Local Maybe (BRA2.Base does not provide one).

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

------------------------------------------------------------------------
-- decideIsValue: decision procedure for IsValue.
--
-- Used to dynamically check that an extracted closing term is value-
-- shape.  Recurses on  ap2 Pair  via a pair-helper to avoid `with`.

decideIsValuePair :
  (a b : Term) ->
  Maybe (IsValue a) -> Maybe (IsValue b) ->
  Maybe (IsValue (ap2 Pair a b))
decideIsValuePair a b (just va) (just vb) = just (valNd a b va vb)
decideIsValuePair _ _ (just _)  nothing   = nothing
decideIsValuePair _ _ nothing   (just _)  = nothing
decideIsValuePair _ _ nothing   nothing   = nothing

decideIsValue : (t : Term) -> Maybe (IsValue t)
decideIsValue O                       = just valO
decideIsValue (var _)                 = nothing
decideIsValue (ap1 _ _)               = nothing
decideIsValue (ap2 Pair a b)          =
  decideIsValuePair a b (decideIsValue a) (decideIsValue b)
decideIsValue (ap2 Const _ _)         = nothing
decideIsValue (ap2 (Lift _) _ _)      = nothing
decideIsValue (ap2 (Post _ _) _ _)    = nothing
decideIsValue (ap2 (Fan _ _ _) _ _)   = nothing
decideIsValue (ap2 IfLf _ _)          = nothing
decideIsValue (ap2 TreeEq _ _)        = nothing
decideIsValue (ap2 (treeRec _ _) _ _) = nothing

------------------------------------------------------------------------
-- ExtractedDemand: the extractor's result type.

ExtractedDemand : Equation -> Set
ExtractedDemand e =
  Sigma Term (\ t -> Sigma (IsValue t) (\ _ -> DemandEq e t))

------------------------------------------------------------------------
-- extractDemandGeneric: the F-free-index version, accepting
-- Eq F bot as an explicit witness.  Allows matching all 10
-- IndBTContext0 constructors.

extractDemandGeneric :
  (e : Equation) (F : Formula) ->
  IndBTContext0 (atomic e) F ->
  Eq F bot ->
  Maybe (ExtractedDemand e)

-- hole : P = atomic e = F; refl : Eq F bot then forces atomic e = bot,
-- hence e = botEqn.  Demand: t = O, IsValue O = valO, DemandEq is refl
-- (substEq 0 O botEqn = botEqn by computation).
extractDemandGeneric .botEqn .(atomic botEqn) (hole _) refl =
  just (mkSigma O (mkSigma valO refl))

-- All other constructors: return nothing for now.  These are the
-- frames the user listed (sym, transL/R, mpL/R, inst); cong1/L/R
-- have outputs whose LHS is ap1/ap2 which cannot equal bot's O.
extractDemandGeneric _ _ (sym _)        _ = nothing
extractDemandGeneric _ _ (transL _ _)   _ = nothing
extractDemandGeneric _ _ (transR _ _)   _ = nothing
extractDemandGeneric _ _ (cong1 _ _)    _ = nothing
extractDemandGeneric _ _ (congL _ _ _)  _ = nothing
extractDemandGeneric _ _ (congR _ _ _)  _ = nothing
extractDemandGeneric _ _ (mpL _ _)      _ = nothing
extractDemandGeneric _ _ (mpR _ _)      _ = nothing
extractDemandGeneric _ _ (inst _ _ _)   _ = nothing

------------------------------------------------------------------------
-- extractDemandSimple: user-facing entry point with F = bot.

extractDemandSimple :
  (e : Equation) ->
  IndBTContext0 (atomic e) bot ->
  Maybe (ExtractedDemand e)
extractDemandSimple e ctx = extractDemandGeneric e bot ctx refl
