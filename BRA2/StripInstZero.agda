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

-- inst zero t (sym (hole _)) eqOut : commutes substitution with sym.
-- Original output:    inst applied to (atomic (eqn u1 t1))
--                     = atomic (eqn (subst 0 t u1) (subst 0 t t1))
-- Rewritten path :    sym (hole (atomic (eqn (subst 0 t t1) (subst 0 t u1))))
--                     = atomic (eqn (subst 0 t u1) (subst 0 t t1))
-- (same target ; eqSubst with eqOut transports to the abstract Target)
stripInstZeroHole {Target = Target}
                  (inst zero t (sym {t = t1} {u = u1} (hole _)) eqOut) =
  symInstHoleHelp (decideIsValue t)
  where
    P-sub : Formula
    P-sub = atomic (eqn (subst zero t t1) (subst zero t u1))
    rawCtx : IndBTContext0 P-sub (atomic (eqn (subst zero t u1) (subst zero t t1)))
    rawCtx = sym (hole P-sub)
    cookedCtx : IndBTContext0 P-sub Target
    cookedCtx = eqSubst (\ F -> IndBTContext0 P-sub F) eqOut rawCtx
    symInstHoleHelp :
      Maybe (IsValue t) ->
      Maybe (InstZeroExtract (atomic (eqn t1 u1)) Target)
    symInstHoleHelp nothing   = nothing
    symInstHoleHelp (just vt) = just (mkInstZeroExtract t vt cookedCtx)

-- inst zero t (cong1 f (hole _)) eqOut : commutes substitution past cong1.
-- The ap1 's f gets substituted: ap1 f t1 -> ap1 (substF1 0 t f) (subst 0 t t1).
stripInstZeroHole {Target = Target}
                  (inst zero t (cong1 f {t = t1} {u = u1} (hole _)) eqOut) =
  cong1InstHoleHelp (decideIsValue t)
  where
    P-sub : Formula
    P-sub = atomic (eqn (subst zero t t1) (subst zero t u1))
    Q-sub : Formula
    Q-sub = atomic (eqn (ap1 (substF1 zero t f) (subst zero t t1))
                          (ap1 (substF1 zero t f) (subst zero t u1)))
    rawCtx : IndBTContext0 P-sub Q-sub
    rawCtx = cong1 (substF1 zero t f) (hole P-sub)
    cookedCtx : IndBTContext0 P-sub Target
    cookedCtx = eqSubst (\ F -> IndBTContext0 P-sub F) eqOut rawCtx
    cong1InstHoleHelp :
      Maybe (IsValue t) ->
      Maybe (InstZeroExtract (atomic (eqn t1 u1)) Target)
    cong1InstHoleHelp nothing   = nothing
    cong1InstHoleHelp (just vt) = just (mkInstZeroExtract t vt cookedCtx)

-- inst zero t (congL g x (hole _)) eqOut : commutes substitution past
-- congL.  The g and x both get substituted.
stripInstZeroHole {Target = Target}
                  (inst zero t (congL g {t = t1} {u = u1} x (hole _)) eqOut) =
  congLInstHoleHelp (decideIsValue t)
  where
    P-sub : Formula
    P-sub = atomic (eqn (subst zero t t1) (subst zero t u1))
    Q-sub : Formula
    Q-sub = atomic (eqn (ap2 (substF2 zero t g) (subst zero t t1) (subst zero t x))
                          (ap2 (substF2 zero t g) (subst zero t u1) (subst zero t x)))
    rawCtx : IndBTContext0 P-sub Q-sub
    rawCtx = congL (substF2 zero t g) (subst zero t x) (hole P-sub)
    cookedCtx : IndBTContext0 P-sub Target
    cookedCtx = eqSubst (\ F -> IndBTContext0 P-sub F) eqOut rawCtx
    congLInstHoleHelp :
      Maybe (IsValue t) ->
      Maybe (InstZeroExtract (atomic (eqn t1 u1)) Target)
    congLInstHoleHelp nothing   = nothing
    congLInstHoleHelp (just vt) = just (mkInstZeroExtract t vt cookedCtx)

-- inst zero t (congR g x (hole _)) eqOut : symmetric to congL.
stripInstZeroHole {Target = Target}
                  (inst zero t (congR g x {t = t1} {u = u1} (hole _)) eqOut) =
  congRInstHoleHelp (decideIsValue t)
  where
    P-sub : Formula
    P-sub = atomic (eqn (subst zero t t1) (subst zero t u1))
    Q-sub : Formula
    Q-sub = atomic (eqn (ap2 (substF2 zero t g) (subst zero t x) (subst zero t t1))
                          (ap2 (substF2 zero t g) (subst zero t x) (subst zero t u1)))
    rawCtx : IndBTContext0 P-sub Q-sub
    rawCtx = congR (substF2 zero t g) (subst zero t x) (hole P-sub)
    cookedCtx : IndBTContext0 P-sub Target
    cookedCtx = eqSubst (\ F -> IndBTContext0 P-sub F) eqOut rawCtx
    congRInstHoleHelp :
      Maybe (IsValue t) ->
      Maybe (InstZeroExtract (atomic (eqn t1 u1)) Target)
    congRInstHoleHelp nothing   = nothing
    congRInstHoleHelp (just vt) = just (mkInstZeroExtract t vt cookedCtx)

-- inst zero t (W _) eqOut where W is a non-hole non-unary-with-hole-inner
-- frame : deferred.  Specifically: nested wrappers (sym (sym hole)),
-- binary frames (transL/R, mpL/R), and inst inside inst.
stripInstZeroHole (inst zero _ (sym (sym _))           _) = nothing
stripInstZeroHole (inst zero _ (sym (transL _ _))      _) = nothing
stripInstZeroHole (inst zero _ (sym (transR _ _))      _) = nothing
stripInstZeroHole (inst zero _ (sym (cong1 _ _))       _) = nothing
stripInstZeroHole (inst zero _ (sym (congL _ _ _))     _) = nothing
stripInstZeroHole (inst zero _ (sym (congR _ _ _))     _) = nothing
stripInstZeroHole (inst zero _ (sym (mpL _ _))         _) = nothing
stripInstZeroHole (inst zero _ (sym (mpR _ _))         _) = nothing
stripInstZeroHole (inst zero _ (sym (inst _ _ _ _))    _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (sym _))       _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (transL _ _))  _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (transR _ _))  _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (cong1 _ _))   _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (congL _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (congR _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (mpL _ _))     _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (mpR _ _))     _) = nothing
stripInstZeroHole (inst zero _ (cong1 _ (inst _ _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (sym _))       _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (transL _ _))  _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (transR _ _))  _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (cong1 _ _))   _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (congL _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (congR _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (mpL _ _))     _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (mpR _ _))     _) = nothing
stripInstZeroHole (inst zero _ (congL _ _ (inst _ _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (sym _))       _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (transL _ _))  _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (transR _ _))  _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (cong1 _ _))   _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (congL _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (congR _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (mpL _ _))     _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (mpR _ _))     _) = nothing
stripInstZeroHole (inst zero _ (congR _ _ (inst _ _ _ _)) _) = nothing
stripInstZeroHole (inst zero _ (transL _ _)    _) = nothing
stripInstZeroHole (inst zero _ (transR _ _)    _) = nothing
stripInstZeroHole (inst zero _ (mpL _ _)       _) = nothing
stripInstZeroHole (inst zero _ (mpR _ _)       _) = nothing
stripInstZeroHole (inst zero _ (inst _ _ _ _)  _) = nothing

-- inst with x > 0 : deferred (only var 0 corresponds to the
-- indBT-induction variable).
stripInstZeroHole (inst (suc _) _ _ _) = nothing
