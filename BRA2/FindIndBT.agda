{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.FindIndBT -- find-and-extract traversal locating a topmost
-- indBTB in a  DerivTBounded 1 l F  proof tree, accumulating an
-- IndBTContext0 path from the indBTB to the root.
--
-- Returns:
--   * nothing  -- the input contains an indBTB whose v1, v2, e fail
--                 the WellFormedIndBT side condition, OR an indBT2B
--                 (deferred), OR a binary combiner (ruleTransB / mpB)
--                 with indBTBs on both children (cannot extract two
--                 packages in a single pass; leftmost-with-fail).
--   * just (inl d0)  -- the proof reduces to DerivT0 directly: every
--                       branch is rank-0 / the open fragment.
--   * just (inr pkg) -- a topmost indBTB was found.  pkg.pkgCtx is an
--                       IndBTContext0 (atomic pkg.pkgE) F  recording
--                       the structural-rule path from the indBTB
--                       outward.  Premises are lifted to DerivT0 via
--                       rankZero and packaged with the WellFormedIndBT
--                       witness.
--
-- Compared to the previous handled-shape-only version (which accepted
-- only an indBTB at the root and otherwise returned nothing), this
-- version recursively descends through every structural rule
-- (ruleSymB, cong1B, congLB, congRB, ruleTransB, mpB, ruleInstB) and
-- propagates the result outward via wrapper helpers.
--
-- The signature carries  F  as a free index (rather than fixing
-- F = bot ) so all 40 DerivTBounded constructors are matchable: this
-- sidesteps Agda's substF non-injectivity at  ruleInstB and lets the
-- target travel through wrappers.  The outer entry point  findIndBT
-- specialises  F = bot .

module BRA2.FindIndBT where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.MaxVar using (Geq ; geqZero ; geqSuc)
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded ; natMax)
open import BRA2.NatMaxLemmas
open import BRA2.RankDecrementSymTrans using (natMaxLE_split)
open import BRA2.WellFormedIndBT
open import BRA2.IndBTContext0
open import BRA2.SubstCompose using (maxVarEq)
open import BRA2.BoundedReductionRankZero using (rankZero)
open import BRA2.RankAtMost1Open using (natLE_zero_eq)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- Local Or.

data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

------------------------------------------------------------------------
-- IndBTPackageAt: package parameterised by the eventual target
-- formula.  pkgCtx records the structural-rule path from the
-- indBTB's conclusion (atomic pkgE) to Target.

record IndBTPackageAt (Target : Formula) : Set where
  constructor mkPkg
  field
    pkgE     : Equation
    pkgV1    : Nat
    pkgV2    : Nat
    pkgWF    : WellFormedIndBT pkgE pkgV1 pkgV2
    pkgBase  : O.DerivT0 (atomic (substEq zero O pkgE))
    pkgStep  : O.DerivT0 ((atomic (substEq zero (var pkgV1) pkgE))
                          imp ((atomic (substEq zero (var pkgV2) pkgE))
                               imp (atomic (substEq zero (ap2 Pair (var pkgV1) (var pkgV2)) pkgE))))
    pkgCtx   : IndBTContext0 (atomic pkgE) Target
open IndBTPackageAt public

-- Backward-compatibility alias for callers that fixed the target to bot.
IndBTPackage : Set
IndBTPackage = IndBTPackageAt bot

------------------------------------------------------------------------
-- ResultAt: shorthand for the recursion's return type.

ResultAt : Formula -> Set
ResultAt F = Maybe (Or (O.DerivT0 F) (IndBTPackageAt F))

------------------------------------------------------------------------
-- Decision procedures for WellFormedIndBT components.

decideGeqSuc :
  (n m : Nat) -> Maybe (Geq n m) -> Maybe (Geq (suc n) (suc m))
decideGeqSuc _ _ (just ge) = just (geqSuc ge)
decideGeqSuc _ _ nothing   = nothing

decideGeq : (n m : Nat) -> Maybe (Geq n m)
decideGeq n       zero    = just (geqZero n)
decideGeq zero    (suc _) = nothing
decideGeq (suc n) (suc m) = decideGeqSuc n m (decideGeq n m)

decideNotEqNatHelper : (b : Bool) -> Maybe (Eq b false)
decideNotEqNatHelper false = just refl
decideNotEqNatHelper true  = nothing

decideNotEqNat : (v w : Nat) -> Maybe (Eq (natEq v w) false)
decideNotEqNat v w = decideNotEqNatHelper (natEq v w)

mkWellFormedFromDecisions :
  {e : Equation} {v1 v2 : Nat} ->
  Maybe (FreshEq v1 e) -> Maybe (FreshEq v2 e) -> Maybe (NotEqNat v2 v1) ->
  Maybe (WellFormedIndBT e v1 v2)
mkWellFormedFromDecisions (just f1) (just f2) (just nq) = just (mkWellFormed f1 f2 nq)
mkWellFormedFromDecisions nothing   _         _         = nothing
mkWellFormedFromDecisions (just _)  nothing   _         = nothing
mkWellFormedFromDecisions (just _)  (just _)  nothing   = nothing

decideWellFormed :
  (e : Equation) (v1 v2 : Nat) ->
  Maybe (WellFormedIndBT e v1 v2)
decideWellFormed e v1 v2 =
  mkWellFormedFromDecisions
    (decideGeq v1 (maxVarEq e))
    (decideGeq v2 (maxVarEq e))
    (decideNotEqNat v2 v1)

------------------------------------------------------------------------
-- buildPackageFromIndBT : build IndBTPackageAt (atomic e) directly.
-- The pkgCtx is the trivial  hole (atomic e) ; outer wrappers will
-- accumulate frames.

buildPackageFromIndBT :
  (e : Equation) (v1 v2 : Nat) ->
  WellFormedIndBT e v1 v2 ->
  {l1 l2 : Nat} ->
  DerivTBounded zero l1 (atomic (substEq zero O e)) ->
  DerivTBounded zero l2
    ((atomic (substEq zero (var v1) e))
     imp ((atomic (substEq zero (var v2) e))
          imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  IndBTPackageAt (atomic e)
buildPackageFromIndBT e v1 v2 wf base step =
  mkPkg e v1 v2 wf (rankZero base) (rankZero step) (hole (atomic e))

packageOrFail :
  (e : Equation) (v1 v2 : Nat) ->
  Maybe (WellFormedIndBT e v1 v2) ->
  {l1 l2 : Nat} ->
  DerivTBounded zero l1 (atomic (substEq zero O e)) ->
  DerivTBounded zero l2
    ((atomic (substEq zero (var v1) e))
     imp ((atomic (substEq zero (var v2) e))
          imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  ResultAt (atomic e)
packageOrFail e v1 v2 (just wf) base step =
  just (inr (buildPackageFromIndBT e v1 v2 wf base step))
packageOrFail _ _ _ nothing _ _ = nothing

------------------------------------------------------------------------
-- Wrapper helpers.  Each consumes a recursion result at the inner
-- formula and produces a recursion result at the outer formula by
-- (a) applying the corresponding DerivT0 structural rule to the inl
-- branch and (b) extending the IndBTContext0 of the inr branch with
-- one outer frame.

wrapPkgSym :
  {t u : Term} ->
  IndBTPackageAt (atomic (eqn t u)) ->
  IndBTPackageAt (atomic (eqn u t))
wrapPkgSym pkg =
  mkPkg (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg)
         (pkgWF pkg) (pkgBase pkg) (pkgStep pkg)
         (sym (pkgCtx pkg))

wrapSym :
  {t u : Term} ->
  ResultAt (atomic (eqn t u)) ->
  ResultAt (atomic (eqn u t))
wrapSym nothing            = nothing
wrapSym (just (inl d))     = just (inl (O.ruleSym d))
wrapSym (just (inr pkg))   = just (inr (wrapPkgSym pkg))

wrapPkgCong1 :
  (f : Fun1) {t u : Term} ->
  IndBTPackageAt (atomic (eqn t u)) ->
  IndBTPackageAt (atomic (eqn (ap1 f t) (ap1 f u)))
wrapPkgCong1 f pkg =
  mkPkg (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg)
         (pkgWF pkg) (pkgBase pkg) (pkgStep pkg)
         (cong1 f (pkgCtx pkg))

wrapCong1 :
  (f : Fun1) {t u : Term} ->
  ResultAt (atomic (eqn t u)) ->
  ResultAt (atomic (eqn (ap1 f t) (ap1 f u)))
wrapCong1 _ nothing            = nothing
wrapCong1 f (just (inl d))     = just (inl (O.cong1 f d))
wrapCong1 f (just (inr pkg))   = just (inr (wrapPkgCong1 f pkg))

wrapPkgCongL :
  (g : Fun2) {t u : Term} (x : Term) ->
  IndBTPackageAt (atomic (eqn t u)) ->
  IndBTPackageAt (atomic (eqn (ap2 g t x) (ap2 g u x)))
wrapPkgCongL g x pkg =
  mkPkg (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg)
         (pkgWF pkg) (pkgBase pkg) (pkgStep pkg)
         (congL g x (pkgCtx pkg))

wrapCongL :
  (g : Fun2) {t u : Term} (x : Term) ->
  ResultAt (atomic (eqn t u)) ->
  ResultAt (atomic (eqn (ap2 g t x) (ap2 g u x)))
wrapCongL _ _ nothing          = nothing
wrapCongL g x (just (inl d))   = just (inl (O.congL g x d))
wrapCongL g x (just (inr pkg)) = just (inr (wrapPkgCongL g x pkg))

wrapPkgCongR :
  (g : Fun2) (x : Term) {t u : Term} ->
  IndBTPackageAt (atomic (eqn t u)) ->
  IndBTPackageAt (atomic (eqn (ap2 g x t) (ap2 g x u)))
wrapPkgCongR g x pkg =
  mkPkg (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg)
         (pkgWF pkg) (pkgBase pkg) (pkgStep pkg)
         (congR g x (pkgCtx pkg))

wrapCongR :
  (g : Fun2) (x : Term) {t u : Term} ->
  ResultAt (atomic (eqn t u)) ->
  ResultAt (atomic (eqn (ap2 g x t) (ap2 g x u)))
wrapCongR _ _ nothing          = nothing
wrapCongR g x (just (inl d))   = just (inl (O.congR g x d))
wrapCongR g x (just (inr pkg)) = just (inr (wrapPkgCongR g x pkg))

wrapPkgInst :
  (x : Nat) (t : Term) {P : Formula} ->
  IndBTPackageAt P ->
  IndBTPackageAt (substF x t P)
wrapPkgInst x t pkg =
  mkPkg (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg)
         (pkgWF pkg) (pkgBase pkg) (pkgStep pkg)
         (inst x t (pkgCtx pkg) refl)

wrapInst :
  (x : Nat) (t : Term) {P : Formula} ->
  ResultAt P ->
  ResultAt (substF x t P)
wrapInst _ _ nothing            = nothing
wrapInst x t (just (inl d))     = just (inl (O.ruleInst x t d))
wrapInst x t (just (inr pkg))   = just (inr (wrapPkgInst x t pkg))

------------------------------------------------------------------------
-- Combiners for binary rules.  Leftmost-with-fail convention: if both
-- sides return packages, neither can be eliminated in a single pass
-- (we'd need DerivT0 for the non-extracted side); return nothing.

combineTrans :
  {t u v : Term} ->
  ResultAt (atomic (eqn t u)) ->
  ResultAt (atomic (eqn u v)) ->
  ResultAt (atomic (eqn t v))
combineTrans nothing               _                  = nothing
combineTrans (just (inl _))        nothing            = nothing
combineTrans (just (inr _))        nothing            = nothing
combineTrans (just (inl d1))       (just (inl d2))    =
  just (inl (O.ruleTrans d1 d2))
combineTrans (just (inr pkg1))     (just (inl d2))    =
  just (inr (mkPkg (pkgE pkg1) (pkgV1 pkg1) (pkgV2 pkg1)
                     (pkgWF pkg1) (pkgBase pkg1) (pkgStep pkg1)
                     (transL (pkgCtx pkg1) d2)))
combineTrans (just (inl d1))       (just (inr pkg2))  =
  just (inr (mkPkg (pkgE pkg2) (pkgV1 pkg2) (pkgV2 pkg2)
                     (pkgWF pkg2) (pkgBase pkg2) (pkgStep pkg2)
                     (transR d1 (pkgCtx pkg2))))
combineTrans (just (inr _))        (just (inr _))     = nothing

combineMp :
  {A B : Formula} ->
  ResultAt (A imp B) ->
  ResultAt A ->
  ResultAt B
combineMp nothing               _                  = nothing
combineMp (just (inl _))        nothing            = nothing
combineMp (just (inr _))        nothing            = nothing
combineMp (just (inl d_imp))    (just (inl d_a))   =
  just (inl (O.mp d_imp d_a))
combineMp (just (inr pkg1))     (just (inl d_a))   =
  just (inr (mkPkg (pkgE pkg1) (pkgV1 pkg1) (pkgV2 pkg1)
                     (pkgWF pkg1) (pkgBase pkg1) (pkgStep pkg1)
                     (mpL (pkgCtx pkg1) d_a)))
combineMp (just (inl d_imp))    (just (inr pkg2)) =
  just (inr (mkPkg (pkgE pkg2) (pkgV1 pkg2) (pkgV2 pkg2)
                     (pkgWF pkg2) (pkgBase pkg2) (pkgStep pkg2)
                     (mpR d_imp (pkgCtx pkg2))))
combineMp (just (inr _))        (just (inr _))    = nothing

------------------------------------------------------------------------
-- The main function.
--
-- Doubly-generic: F is a free index; rank is a free index + NatLE r 1
-- bound.  This makes all 40 DerivTBounded constructors matchable.

findIndBTAux :
  (F : Formula) {l : Nat} {r : Nat} ->
  NatLE r (suc zero) ->
  DerivTBounded r l F ->
  ResultAt F

-- Atomic computation axioms : direct lifts to DerivT0.
findIndBTAux _ _ (B.axIB _ _ t)              = just (inl (O.axI t))
findIndBTAux _ _ (B.axFstB _ _ a b)          = just (inl (O.axFst a b))
findIndBTAux _ _ (B.axSndB _ _ a b)          = just (inl (O.axSnd a b))
findIndBTAux _ _ (B.axFstLfB _ _)            = just (inl O.axFstLf)
findIndBTAux _ _ (B.axSndLfB _ _)            = just (inl O.axSndLf)
findIndBTAux _ _ (B.axConstB _ _ a b)        = just (inl (O.axConst a b))
findIndBTAux _ _ (B.axCompB _ _ f g t)       = just (inl (O.axComp f g t))
findIndBTAux _ _ (B.axComp2B _ _ h f g t)    = just (inl (O.axComp2 h f g t))
findIndBTAux _ _ (B.axLiftB _ _ f a b)       = just (inl (O.axLift f a b))
findIndBTAux _ _ (B.axPostB _ _ f h a b)     = just (inl (O.axPost f h a b))
findIndBTAux _ _ (B.axFanB _ _ h1 h2 h a b)  = just (inl (O.axFan h1 h2 h a b))
findIndBTAux _ _ (B.axZB _ _ x)              = just (inl (O.axZ x))
findIndBTAux _ _ (B.axTreeRecLfB _ _ f s p)         =
  just (inl (O.axTreeRecLf f s p))
findIndBTAux _ _ (B.axTreeRecNdB _ _ f s p a b)     =
  just (inl (O.axTreeRecNd f s p a b))
findIndBTAux _ _ (B.axIfLfLB _ _ a b)        = just (inl (O.axIfLfL a b))
findIndBTAux _ _ (B.axIfLfNB _ _ x y a b)    = just (inl (O.axIfLfN x y a b))
findIndBTAux _ _ (B.axIfLfLLB _ _)           = just (inl O.axIfLfLL)
findIndBTAux _ _ (B.axIfLfNLB _ _ x y)       = just (inl (O.axIfLfNL x y))
findIndBTAux _ _ (B.axTreeEqLLB _ _)         = just (inl O.axTreeEqLL)
findIndBTAux _ _ (B.axTreeEqLNB _ _ a b)     = just (inl (O.axTreeEqLN a b))
findIndBTAux _ _ (B.axTreeEqNLB _ _ a b)     = just (inl (O.axTreeEqNL a b))
findIndBTAux _ _ (B.axTreeEqNNB _ _ a1 a2 b1 b2) =
  just (inl (O.axTreeEqNN a1 a2 b1 b2))
findIndBTAux _ _ (B.axGoodsteinB _ _ a b)    = just (inl (O.axGoodstein a b))
findIndBTAux _ _ (B.axReflB _ _ t)           = just (inl (O.axRefl t))

-- Equational implication / propositional axioms : direct lifts.
findIndBTAux _ _ (B.axEqTransB _ _ a b c)    = just (inl (O.axEqTrans a b c))
findIndBTAux _ _ (B.axEqCong1B _ _ f a b)    = just (inl (O.axEqCong1 f a b))
findIndBTAux _ _ (B.axEqCongLB _ _ g a b c)  = just (inl (O.axEqCongL g a b c))
findIndBTAux _ _ (B.axEqCongRB _ _ g a b c)  = just (inl (O.axEqCongR g a b c))
findIndBTAux _ _ (B.axKB _ _ P Q)            = just (inl (O.axK P Q))
findIndBTAux _ _ (B.axSB _ _ P Q R)          = just (inl (O.axS P Q R))
findIndBTAux _ _ (B.axNegB _ _ P Q)          = just (inl (O.axNeg P Q))

-- Structural rules : recursive descent + wrap.
findIndBTAux _ le (B.ruleSymB {t = t} {u = u} d) =
  wrapSym {t} {u} (findIndBTAux (atomic (eqn t u)) le d)

findIndBTAux _ le (B.ruleTransB {r1 = r1} {r2 = r2}
                                  {t = t} {u = u} {v = v} d1 d2) =
  let lePair = natMaxLE_split {r1} {r2} le
      le1    = fst lePair
      le2    = snd lePair
      inner1 = findIndBTAux (atomic (eqn t u)) le1 d1
      inner2 = findIndBTAux (atomic (eqn u v)) le2 d2
  in combineTrans {t} {u} {v} inner1 inner2

findIndBTAux _ le (B.cong1B f {t = t} {u = u} d) =
  wrapCong1 f {t} {u} (findIndBTAux (atomic (eqn t u)) le d)

findIndBTAux _ le (B.congLB g {t = t} {u = u} x d) =
  wrapCongL g {t} {u} x (findIndBTAux (atomic (eqn t u)) le d)

findIndBTAux _ le (B.congRB g x {t = t} {u = u} d) =
  wrapCongR g x {t} {u} (findIndBTAux (atomic (eqn t u)) le d)

-- Rules of inference : recursive descent + wrap.
findIndBTAux _ le (B.mpB {r1 = r1} {r2 = r2} {P = P} {Q = Q} d1 d2) =
  let lePair = natMaxLE_split {r1} {r2} le
      le1    = fst lePair
      le2    = snd lePair
      inner1 = findIndBTAux (P imp Q) le1 d1
      inner2 = findIndBTAux P le2 d2
  in combineMp {P} {Q} inner1 inner2

findIndBTAux _ le (B.ruleInstB x t {P = P} d) =
  wrapInst x t {P} (findIndBTAux P le d)

-- indBTB : the handled root case.  NatLE bound (leSuc le') exposes
-- le' : NatLE (natMax r1 r2) 0, which natLE_zero_eq turns into
-- Eq (natMax r1 r2) 0; natMaxZero then gives (r1 = 0, r2 = 0).
-- Lift premises to rank 0 via eqSubst, then build the package.
findIndBTAux _ (leSuc le') (B.indBTB {r1} {l1} {r2} {l2} e v1 v2 base step) =
  let maxEqZ : Eq (natMax r1 r2) zero
      maxEqZ = natLE_zero_eq le'
      pair    = natMaxZero r1 r2 maxEqZ
      r1Eq0   = fst pair
      r2Eq0   = snd pair
      baseAt0 = eqSubst (\ rk -> DerivTBounded rk l1 (atomic (substEq zero O e))) r1Eq0 base
      stepAt0 = eqSubst (\ rk -> DerivTBounded rk l2 _) r2Eq0 step
  in packageOrFail e v1 v2 (decideWellFormed e v1 v2) baseAt0 stepAt0

-- indBT2B : deferred (Case B does not extend to it; future work).
findIndBTAux _ _ (B.indBT2B _ _ _ _ _ _ _ _ _) = nothing

------------------------------------------------------------------------
-- Public entry point.

findIndBT :
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage)
findIndBT d = findIndBTAux bot (natLERefl (suc zero)) d
