{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.StripInstZero -- locate an  inst zero t (hole _)  frame
-- somewhere along an  IndBTContext0  path.  When found, return the
-- closing term  t , its IsValue witness, and the remaining outer
-- path (everything outside the inst), reindexed at the post-inst
-- starting formula  substF zero t P .
--
-- Walk semantics: outer-frames-first.  We descend through every
-- structural-rule wrapper (sym / transL / transR / cong1 / congL /
-- congR / mpL / mpR), recursing on the inner sub-context.  When
-- we hit an  inst zero t  frame whose inner is  hole _ , we extract
-- the closing term and the remaining outer path is the wrappers
-- we descended through, applied to a fresh hole at  substF zero t P .
--
-- Conservative restrictions in this version:
--
--   * Only  x = 0  inst frames are extracted.  Higher-variable
--     instantiation requires composition with  unfoldAtValue 's
--     output, which only handles var 0 -- the ind-induction variable.
--
--   * Only  inst zero t (hole _)  with  hole  inner is extracted.
--     Non-hole inner (a wrapper between hole and inst) requires
--     substEq composition reasoning that's deferred.
--
--   * Only the FIRST  inst zero t (hole _)  encountered is returned.
--     If the path contains multiple, the outermost one shielding the
--     hole-adjacent one is found first.

module BRA2.StripInstZero where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0 as O
open import BRA2.IndBTContext0
open import BRA2.ExtractDemand using (Maybe ; just ; nothing ; decideIsValue)

------------------------------------------------------------------------
-- The extraction record.

record InstZeroExtract (P Target : Formula) : Set where
  constructor mkInstZeroExtract
  field
    extractedT      : Term
    extractedTValue : IsValue extractedT
    remainingCtx    : IndBTContext0 (substF zero extractedT P) Target
open InstZeroExtract public

------------------------------------------------------------------------
-- Per-wrapper propagation helpers.  Each takes a Maybe extraction
-- result at the inner level and lifts it to the outer level by
-- wrapping the remaining context with the corresponding frame.

wrapStripSym :
  {P : Formula} {t u : Term} ->
  Maybe (InstZeroExtract P (atomic (eqn t u))) ->
  Maybe (InstZeroExtract P (atomic (eqn u t)))
wrapStripSym nothing = nothing
wrapStripSym (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (sym ctx'))

wrapStripTransL :
  {P : Formula} {t u v : Term} ->
  O.DerivT0 (atomic (eqn u v)) ->
  Maybe (InstZeroExtract P (atomic (eqn t u))) ->
  Maybe (InstZeroExtract P (atomic (eqn t v)))
wrapStripTransL _ nothing = nothing
wrapStripTransL d2 (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (transL ctx' d2))

wrapStripTransR :
  {P : Formula} {t u v : Term} ->
  O.DerivT0 (atomic (eqn t u)) ->
  Maybe (InstZeroExtract P (atomic (eqn u v))) ->
  Maybe (InstZeroExtract P (atomic (eqn t v)))
wrapStripTransR _ nothing = nothing
wrapStripTransR d1 (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (transR d1 ctx'))

wrapStripCong1 :
  {P : Formula} (f : Fun1) {t u : Term} ->
  Maybe (InstZeroExtract P (atomic (eqn t u))) ->
  Maybe (InstZeroExtract P (atomic (eqn (ap1 f t) (ap1 f u))))
wrapStripCong1 _ nothing = nothing
wrapStripCong1 f (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (cong1 f ctx'))

wrapStripCongL :
  {P : Formula} (g : Fun2) {t u : Term} (x : Term) ->
  Maybe (InstZeroExtract P (atomic (eqn t u))) ->
  Maybe (InstZeroExtract P (atomic (eqn (ap2 g t x) (ap2 g u x))))
wrapStripCongL _ _ nothing = nothing
wrapStripCongL g x (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (congL g x ctx'))

wrapStripCongR :
  {P : Formula} (g : Fun2) (x : Term) {t u : Term} ->
  Maybe (InstZeroExtract P (atomic (eqn t u))) ->
  Maybe (InstZeroExtract P (atomic (eqn (ap2 g x t) (ap2 g x u))))
wrapStripCongR _ _ nothing = nothing
wrapStripCongR g x (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (congR g x ctx'))

wrapStripMpL :
  {P A B : Formula} ->
  O.DerivT0 A ->
  Maybe (InstZeroExtract P (A imp B)) ->
  Maybe (InstZeroExtract P B)
wrapStripMpL _ nothing = nothing
wrapStripMpL d_arg (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (mpL ctx' d_arg))

wrapStripMpR :
  {P A B : Formula} ->
  O.DerivT0 (A imp B) ->
  Maybe (InstZeroExtract P A) ->
  Maybe (InstZeroExtract P B)
wrapStripMpR _ nothing = nothing
wrapStripMpR d_imp (just (mkInstZeroExtract r vr ctx')) =
  just (mkInstZeroExtract r vr (mpR d_imp ctx'))

------------------------------------------------------------------------
-- Base-case helper: at  inst zero t (hole _) eqOut , decide if t is
-- value-shape and produce the extraction record.

doExtractAtHole :
  {P Target : Formula} (t : Term) ->
  Eq (substF zero t P) Target ->
  Maybe (IsValue t) ->
  Maybe (InstZeroExtract P Target)
doExtractAtHole _ _ nothing = nothing
doExtractAtHole {P} t eq (just vt) =
  just (mkInstZeroExtract t vt
         (eqSubst (\ F -> IndBTContext0 (substF zero t P) F)
                   eq (hole (substF zero t P))))

------------------------------------------------------------------------
-- The walker.  Every clause is either base (hole, found, or
-- nothing-by-shape) or a wrapper recurse-and-lift.

stripInstZeroHole :
  {P Target : Formula} ->
  IndBTContext0 P Target ->
  Maybe (InstZeroExtract P Target)

-- hole at the top: no inst to strip.
stripInstZeroHole (hole _) = nothing

-- Structural rules: recurse, wrap.
stripInstZeroHole (sym ctx')          = wrapStripSym (stripInstZeroHole ctx')
stripInstZeroHole (transL ctx' d2)    = wrapStripTransL d2 (stripInstZeroHole ctx')
stripInstZeroHole (transR d1 ctx')    = wrapStripTransR d1 (stripInstZeroHole ctx')
stripInstZeroHole (cong1 f ctx')      = wrapStripCong1 f (stripInstZeroHole ctx')
stripInstZeroHole (congL g x ctx')    = wrapStripCongL g x (stripInstZeroHole ctx')
stripInstZeroHole (congR g x ctx')    = wrapStripCongR g x (stripInstZeroHole ctx')
stripInstZeroHole (mpL ctx' d_arg)    = wrapStripMpL d_arg (stripInstZeroHole ctx')
stripInstZeroHole (mpR d_imp ctx')    = wrapStripMpR d_imp (stripInstZeroHole ctx')

-- inst with x = 0 and inner = hole : THE base case.
stripInstZeroHole (inst zero t (hole _) eqOut) =
  doExtractAtHole t eqOut (decideIsValue t)

-- inst with x = 0 and any non-hole inner: deferred (Case C extension).
stripInstZeroHole (inst zero _ (sym _)         _) = nothing
stripInstZeroHole (inst zero _ (transL _ _)    _) = nothing
stripInstZeroHole (inst zero _ (transR _ _)    _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ _)     _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ _)   _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ _)   _) = nothing
stripInstZeroHole (inst zero _ (mpL _ _)       _) = nothing
stripInstZeroHole (inst zero _ (mpR _ _)       _) = nothing
stripInstZeroHole (inst zero _ (inst _ _ _ _)  _) = nothing

-- inst with x > 0 : deferred (only var 0 corresponds to the
-- indBT-induction variable).
stripInstZeroHole (inst (suc _) _ _ _) = nothing
