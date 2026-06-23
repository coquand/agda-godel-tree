{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ConvClash -- the end-to-end (meta-input) consistency of the trace-presented
-- equational theory, ASSEMBLED from the green pieces:
--
--   Conv ze (su ze)                       -- a conversion 0 <-> s0
--     --convJoin (ParHeadline, via ParConfl confluence)-->  Join ze (su ze)
--     --stepsToChain (per step: stepParM + parToCert + srcC/tgtC + MEq)-->
--          two transparent traces  ChainM ze# w ,  ChainM (su# ze#) w
--     --joinClash (ChainClash: head-stability + ax_succ_nonzero)-->  Deriv Q .
--
-- i.e.  convClash : Conv ze (su ze) -> (Q : Formula) -> Deriv Q  -- a join of
-- 0 and s0 makes the OBJECT theory prove anything (object ex falso).  Combined
-- with  ParHeadline.zeNotConvSuZe  (no such meta Conv exists), this is the
-- consistency core.  The conclusion is OBJECT (Deriv Q) -- no meta refuter.
--
-- NB this is META-INPUT (the hypothesis is a meta Conv); BRA |- Con(T0)
-- additionally needs the object-input route (compileFuel proof-translation +
-- object confluence), which reuses the same head-stability/clash core.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ConvClash where

open import T4.Base

open import T4.ParReflPres using ( Tm ; ze ; su ; code )
open import T4.ParConfl using ( StepsM ; doneS ; moreS ; stepParM )
  renaming ( car to scar ; prf to sprf ; prjL to sprjL ; prjR to sprjR )
open import T4.ParHeadline using ( Conv ; convJoin ; Join )
open import T4.ParToCert using ( parToCert ; srcParToCert ; tgtParToCert ; MEq ; mrefl )
open import T4.CertTree using ( codeC ; srcC )
open import T4.ParProof using ( tgtC )
open import T4.ParEnds using ( src ; tgt )
open import T4.ChainHeadStab using ( ChainM ; cnil ; ccons )
open import T4.ChainClash using ( JoinChain ; joinClash ; mkSgT ; mkConj )
open import T4.TrsCodeObj using ( ze# ; su# )

------------------------------------------------------------------------
-- Transport a Deriv equation along a meta endpoint equality.

msubst : {A x y : Term} -> MEq x y -> Deriv (eqF A x) -> Deriv (eqF A y)
msubst mrefl d = d

------------------------------------------------------------------------
-- A meta reduction  StepsM t w  becomes a transparent trace  ChainM (code t)(code w).

stepsToChain : {t w : Tm} -> StepsM t w -> ChainM (code t) (code w)
stepsToChain doneS = cnil
stepsToChain (moreS st rest) =
  let c : _
      c = parToCert (stepParM st)
      srcEq : Deriv (eqF (ap1 src (codeC c)) (code _))
      srcEq = msubst (srcParToCert (stepParM st)) (srcC c)
      tgtEq : Deriv (eqF (ap1 tgt (codeC c)) (code _))
      tgtEq = msubst (tgtParToCert (stepParM st)) (tgtC c)
  in ccons c srcEq tgtEq (stepsToChain rest)

------------------------------------------------------------------------
-- The end-to-end clash.

convClash : Conv ze (su ze) -> (Q : Formula) -> Deriv Q
convClash cv Q =
  let j : Join ze (su ze)
      j = convJoin cv
      ch1 : ChainM (code ze) (code (scar j))
      ch1 = stepsToChain (sprjL (sprf j))
      ch2 : ChainM (code (su ze)) (code (scar j))
      ch2 = stepsToChain (sprjR (sprf j))
      jc : JoinChain ze# (su# ze#)
      jc = mkSgT (code (scar j)) (mkConj ch1 ch2)
  in joinClash ze# Q jc
