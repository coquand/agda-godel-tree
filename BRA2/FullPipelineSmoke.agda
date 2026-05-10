{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.FullPipelineSmoke -- final smoke test composing the entire
-- partial pipeline:
--
--   DerivTBounded 1 l bot
--   --[ findIndBT ]-->          Maybe (Or (DerivT0 bot) IndBTPackage)
--   --[ extractDemandSimple ]-> Maybe (t, IsValue t, DemandEq e t)
--   --[ indBTElimDemo ]-->      DerivT0 bot
--
-- Synthetic input: a root-indBTB tree at rank 1 over botEqn with
-- v1 = 1, v2 = 2 .  Everything else (premises) is taken as a
-- parameter -- we cannot construct  DerivTBounded 0 _ bot
-- concretely (consistency!), so base/step are abstract.
--
-- The smoke test is twofold:
--
--   (A) smokeFullPipeline : the type-correct composition; if this
--       typechecks, the interfaces compose.
--   (B) smokeFullPipelineJust : a refl-witness that the composition
--       reduces to  just _  on the synthetic input.  This locks in
--       that the partial pipeline actually computes through.
--
-- After this checkpoint, the three known sources of `nothing` are
-- documented and we stop.

module BRA2.FullPipelineSmoke where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.UnfoldAtValue using (botEqn)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)
open import BRA2.IndBTHandlerWithCtx using (indBTHandlerWithCtx)
open import BRA2.FindIndBT using
  (findIndBT ; IndBTPackage ; pkgE ; pkgV1 ; pkgV2 ; pkgWF
  ; pkgBase ; pkgStep ; pkgCtx ; Or ; inl ; inr)
open import BRA2.ClosedPipeline using
  (closedPipelineFromBounded ; ClosedOracle ; defaultClosedOracle)
open import BRA2.OpenPipeline using (openPipelineFromBounded)
open import BRA2.UnifiedPipeline using (unifiedPipelineFromBounded)
open import BRA2.RankOneConditional using (rankOneConditionalDefault)

------------------------------------------------------------------------
-- finalizeFromFind: combine the findIndBT result with
-- indBTHandlerWithCtx to produce  Maybe (DerivT0 bot) .

finalizeFromFind :
  Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
  Maybe (O.DerivT0 bot)
finalizeFromFind nothing             = nothing
finalizeFromFind (just (inl d0))     = just d0
finalizeFromFind (just (inr pkg))    =
  indBTHandlerWithCtx (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg) (pkgWF pkg)
                       (pkgBase pkg) (pkgStep pkg) (pkgCtx pkg)

------------------------------------------------------------------------
-- fullPipeline: the top-level composition.

fullPipeline :
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (O.DerivT0 bot)
fullPipeline d = finalizeFromFind (findIndBT d)

------------------------------------------------------------------------
-- isJust: discriminator for the smoke test.

isJust : {A : Set} -> Maybe A -> Bool
isJust (just _) = true
isJust nothing  = false

------------------------------------------------------------------------
-- (A) Synthetic root-indBTB pipeline test.
--
-- Input:  B.indBTB botEqn 1 2 base step   (rank 1, conclusion bot).
-- Output: Maybe (DerivT0 bot).
--
-- Premises are abstract parameters.  If this typechecks, the
-- interfaces (findIndBT -> extractDemandSimple -> indBTElimDemo)
-- compose end-to-end.

stepFormula : Formula
stepFormula =
  (atomic (substEq zero (var (suc zero)) botEqn))
  imp ((atomic (substEq zero (var (suc (suc zero))) botEqn))
       imp (atomic (substEq zero (ap2 Pair (var (suc zero)) (var (suc (suc zero)))) botEqn)))

smokeFullPipeline :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (O.DerivT0 bot)
smokeFullPipeline _ _ base step =
  fullPipeline (B.indBTB botEqn (suc zero) (suc (suc zero)) base step)

------------------------------------------------------------------------
-- (B) refl-witness that the pipeline returns  just  on the synthetic
-- input.  v1 = 1, v2 = 2 ensure  natEq v2 v1 = false  reduces to
-- just refl  in decideNotEqNat ; FreshEq via geqZero (botEqn closed).

smokeFullPipelineJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJust (smokeFullPipeline l1 l2 base step)) true
smokeFullPipelineJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (C) Wrapped-indBTB smoke test for findIndBT (Case B).
--
-- Input:
--   ruleTransB
--     (indBTB botEqn 1 2 base step)         -- conclusion: atomic botEqn
--     (axReflB 0 0 (ap2 Pair O O))          -- conclusion: eqn (Pair O O) (Pair O O)
--   conclusion: atomic (eqn O (Pair O O)) = atomic botEqn = bot
--
-- Tests that findIndBT successfully descends through ruleTransB,
-- locates the indBTB on the left, and packages it with a transL
-- frame around the right (axReflB) lifted to DerivT0.  Returns
-- just (inr pkg) at the findIndBT level; the full pipeline still
-- returns nothing at this stage because Case C (extractor handling
-- of transL frames) is not yet implemented.

isJustOr : {l : Nat} ->
            Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
            Bool
isJustOr (just _) = true
isJustOr nothing  = false

smokeWrappedTransFind :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
smokeWrappedTransFind _ _ base step =
  let core = B.indBTB botEqn (suc zero) (suc (suc zero)) base step
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in findIndBT (B.ruleTransB core reflRight)

smokeWrappedTransFindJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJustOr {zero} (smokeWrappedTransFind l1 l2 base step)) true
smokeWrappedTransFindJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (D) ruleSymB-wrapped indBTB.  Conclusion-of-indBTB is the swap of
-- botEqn ; ruleSymB then swaps back to bot.
--
-- This exercises the wrapSym helper and the IndBTContext0  sym  frame
-- on pkgCtx.

swappedBotEqn : Equation
swappedBotEqn = eqn (ap2 Pair O O) O

swappedStepFormula : Formula
swappedStepFormula =
  (atomic (substEq zero (var (suc zero)) swappedBotEqn))
  imp ((atomic (substEq zero (var (suc (suc zero))) swappedBotEqn))
       imp (atomic (substEq zero (ap2 Pair (var (suc zero)) (var (suc (suc zero)))) swappedBotEqn)))

smokeWrappedSymFind :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn)) ->
  DerivTBounded zero l2 swappedStepFormula ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
smokeWrappedSymFind _ _ base step =
  let core = B.indBTB swappedBotEqn (suc zero) (suc (suc zero)) base step
  in findIndBT (B.ruleSymB core)

smokeWrappedSymFindJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn))) ->
  (step : DerivTBounded zero l2 swappedStepFormula) ->
  Eq (isJustOr {zero} (smokeWrappedSymFind l1 l2 base step)) true
smokeWrappedSymFindJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (E) Doubly-wrapped: ruleTransB (ruleSymB (indBTB swap_e ...))
--                                (axReflB (Pair O O))
--
-- Tests composition of multiple wrappers on the package's pkgCtx
-- (sym INSIDE transL).  The outermost conclusion is bot ; the
-- pkgCtx accumulates  transL (sym (hole _)) (axRefl (Pair O O)) .

smokeDoubleWrapFind :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn)) ->
  DerivTBounded zero l2 swappedStepFormula ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
smokeDoubleWrapFind _ _ base step =
  let core      = B.indBTB swappedBotEqn (suc zero) (suc (suc zero)) base step
      symCore   = B.ruleSymB core
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in findIndBT (B.ruleTransB symCore reflRight)

smokeDoubleWrapFindJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn))) ->
  (step : DerivTBounded zero l2 swappedStepFormula) ->
  Eq (isJustOr {zero} (smokeDoubleWrapFind l1 l2 base step)) true
smokeDoubleWrapFindJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (F)/(G)/(H) End-to-end via ClosedPipeline.
--
-- For our synthetic inputs, pkgE ends up being either botEqn or
-- swappedBotEqn — both closed in var 0.  We supply a partial
-- ClosedOracle that recognises exactly these two equations and
-- returns refl ; for any other equation it returns nothing.

-- The smoke oracle is the productized defaultClosedOracle from
-- BRA2.ClosedPipeline, which recursively decides closure of
-- equations under  subst zero O .

smokeOracle : ClosedOracle
smokeOracle = defaultClosedOracle

-- (F) Direct (root) indBTB at botEqn end-to-end.

smokeFullPipelineClosed :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (O.DerivT0 bot)
smokeFullPipelineClosed _ _ base step =
  closedPipelineFromBounded smokeOracle
    (B.indBTB botEqn (suc zero) (suc (suc zero)) base step)

smokeFullPipelineClosedJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJust (smokeFullPipelineClosed l1 l2 base step)) true
smokeFullPipelineClosedJust _ _ _ _ = refl

-- (G) ruleTransB-wrapped indBTB end-to-end.

smokeWrappedTransClosed :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (O.DerivT0 bot)
smokeWrappedTransClosed _ _ base step =
  let core      = B.indBTB botEqn (suc zero) (suc (suc zero)) base step
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in closedPipelineFromBounded smokeOracle (B.ruleTransB core reflRight)

smokeWrappedTransClosedJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJust (smokeWrappedTransClosed l1 l2 base step)) true
smokeWrappedTransClosedJust _ _ _ _ = refl

-- (H) ruleSymB-wrapped indBTB at swappedBotEqn end-to-end.

smokeWrappedSymClosed :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn)) ->
  DerivTBounded zero l2 swappedStepFormula ->
  Maybe (O.DerivT0 bot)
smokeWrappedSymClosed _ _ base step =
  let core = B.indBTB swappedBotEqn (suc zero) (suc (suc zero)) base step
  in closedPipelineFromBounded smokeOracle (B.ruleSymB core)

smokeWrappedSymClosedJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O swappedBotEqn))) ->
  (step : DerivTBounded zero l2 swappedStepFormula) ->
  Eq (isJust (smokeWrappedSymClosed l1 l2 base step)) true
smokeWrappedSymClosedJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (I) Open-pkgE smoke test via OpenPipeline.
--
-- Synthetic input:
--   indBTB at  e = eqn (var 0) O   -- var 0 free, NOT closed
--   wrap with  ruleInstB 0 (Pair O O)  -- closes  var 0 := Pair O O
--                                        giving  eqn (Pair O O) O
--                                        (= swappedBotEqn)
--   wrap with  ruleSymB                -- swaps to  eqn O (Pair O O)
--                                        (= bot)
--
-- The resulting pkg has:
--   pkgE = eqn (var 0) O                       -- open
--   pkgCtx = sym (inst 0 (Pair O O) (hole _) refl)
-- which OpenPipeline handles: stripInstZeroHole finds the inst at depth 1,
-- extracts t = Pair O O, builds remainingCtx = sym (hole _) ; the indBT
-- step machinery + unfoldAtValue produce DerivT0 (atomic
-- (substEq 0 (Pair O O) (eqn (var 0) O))) = DerivT0 (atomic (eqn (Pair O O) O));
-- plug0 (sym (hole _)) lifts to DerivT0 (atomic (eqn O (Pair O O))) = DerivT0 bot.

openPkgE : Equation
openPkgE = eqn (var zero) O

openStepFormula : Formula
openStepFormula =
  (atomic (substEq zero (var (suc zero)) openPkgE))
  imp ((atomic (substEq zero (var (suc (suc zero))) openPkgE))
       imp (atomic (substEq zero (ap2 Pair (var (suc zero)) (var (suc (suc zero)))) openPkgE)))

smokeOpenPipeline :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O openPkgE)) ->
  DerivTBounded zero l2 openStepFormula ->
  Maybe (O.DerivT0 bot)
smokeOpenPipeline _ _ base step =
  let core    = B.indBTB openPkgE (suc zero) (suc (suc zero)) base step
      withInst = B.ruleInstB zero (ap2 Pair O O) core
  in openPipelineFromBounded (B.ruleSymB withInst)

smokeOpenPipelineJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O openPkgE))) ->
  (step : DerivTBounded zero l2 openStepFormula) ->
  Eq (isJust (smokeOpenPipeline l1 l2 base step)) true
smokeOpenPipelineJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (J) Unified pipeline: closed-pkgE input dispatched via closed route.

smokeUnifiedClosed :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (O.DerivT0 bot)
smokeUnifiedClosed _ _ base step =
  let core      = B.indBTB botEqn (suc zero) (suc (suc zero)) base step
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in unifiedPipelineFromBounded smokeOracle (B.ruleTransB core reflRight)

smokeUnifiedClosedJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJust (smokeUnifiedClosed l1 l2 base step)) true
smokeUnifiedClosedJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (K) Unified pipeline: open-pkgE input dispatched via open route.

smokeUnifiedOpen :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O openPkgE)) ->
  DerivTBounded zero l2 openStepFormula ->
  Maybe (O.DerivT0 bot)
smokeUnifiedOpen _ _ base step =
  let core    = B.indBTB openPkgE (suc zero) (suc (suc zero)) base step
      withInst = B.ruleInstB zero (ap2 Pair O O) core
  in unifiedPipelineFromBounded smokeOracle (B.ruleSymB withInst)

smokeUnifiedOpenJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O openPkgE))) ->
  (step : DerivTBounded zero l2 openStepFormula) ->
  Eq (isJust (smokeUnifiedOpen l1 l2 base step)) true
smokeUnifiedOpenJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (L) RankOneConditional: end-to-end rank-1 -> rank-0 reduction.
-- Composes unifiedPipelineFromBounded with embedDerivT0 to produce
-- DerivTBounded 0 l' bot (the embedded-back form).

smokeRankOneClosed :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  DerivTBounded zero l2 stepFormula ->
  Maybe (Sigma Nat (\ l' -> DerivTBounded zero l' bot))
smokeRankOneClosed _ _ base step =
  let core      = B.indBTB botEqn (suc zero) (suc (suc zero)) base step
      reflRight = B.axReflB zero zero (ap2 Pair O O)
  in rankOneConditionalDefault (B.ruleTransB core reflRight)

smokeRankOneClosedJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O botEqn))) ->
  (step : DerivTBounded zero l2 stepFormula) ->
  Eq (isJust (smokeRankOneClosed l1 l2 base step)) true
smokeRankOneClosedJust _ _ _ _ = refl

smokeRankOneOpen :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O openPkgE)) ->
  DerivTBounded zero l2 openStepFormula ->
  Maybe (Sigma Nat (\ l' -> DerivTBounded zero l' bot))
smokeRankOneOpen _ _ base step =
  let core    = B.indBTB openPkgE (suc zero) (suc (suc zero)) base step
      withInst = B.ruleInstB zero (ap2 Pair O O) core
  in rankOneConditionalDefault (B.ruleSymB withInst)

smokeRankOneOpenJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O openPkgE))) ->
  (step : DerivTBounded zero l2 openStepFormula) ->
  Eq (isJust (smokeRankOneOpen l1 l2 base step)) true
smokeRankOneOpenJust _ _ _ _ = refl

------------------------------------------------------------------------
-- (M) Open-pkgE with inst-INSIDE-sym (Case C deeper).
--
-- Synthetic input:
--   indBTB at  e = eqn (var 0) O                  -- var 0 free
--   wrap with  ruleSymB                           -- swaps to eqn O (var 0)
--   wrap with  ruleInstB 0 (Pair O O)             -- substitutes var 0 := Pair O O
--                                                   giving eqn O (Pair O O) = bot
--
-- The resulting pkgCtx = inst 0 (Pair O O) (sym (hole _)) refl ;
-- this is exactly the inst-with-sym-hole-inner case the extended
-- stripInstZeroHole now handles.

smokeOpenInstSym :
  (l1 l2 : Nat) ->
  DerivTBounded zero l1 (atomic (substEq zero O openPkgE)) ->
  DerivTBounded zero l2 openStepFormula ->
  Maybe (O.DerivT0 bot)
smokeOpenInstSym _ _ base step =
  let core    = B.indBTB openPkgE (suc zero) (suc (suc zero)) base step
      withSym = B.ruleSymB core
  in unifiedPipelineFromBounded smokeOracle
       (B.ruleInstB zero (ap2 Pair O O) withSym)

smokeOpenInstSymJust :
  (l1 l2 : Nat) ->
  (base : DerivTBounded zero l1 (atomic (substEq zero O openPkgE))) ->
  (step : DerivTBounded zero l2 openStepFormula) ->
  Eq (isJust (smokeOpenInstSym l1 l2 base step)) true
smokeOpenInstSymJust _ _ _ _ = refl
