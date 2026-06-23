{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SizedPres -- the DECISIVE experiment for internal CR over opaque codes.
--
-- POSITIVE RESULT (green here): any FoldRec fold can be UNFOLDED at a
-- genuinely OPAQUE nonzero code, ETA-FREE (no surjective pairing):
--
--   succForm   : d != O  ->  s (predecessor d) = d            (from L_sp)
--   foldOpaque : d != O  ->  fold g h d = h (predecessor d) (Snd (cov_spec g h O (predecessor d)))
--
-- So OPAQUE dispatch + the step body fire with no eta: foldOpaque puts an
-- opaque code into the successor form foldStepRaw needs (via L_sp, a cheap
-- predecessor lemma), then applies foldStepRaw.
--
-- THE WALL (documented, not faked): foldOpaque exposes the step body h, whose
-- recursive child-recovery is `lookupAt`, and lookup_eq_fold recovers
-- `fold child` only under `leq child (predecessor d)` -- a CODE-VALUE bound.
-- For the size coding the cheap descent is on `sz` (= Fst), NOT the code
-- value, so it cannot discharge lookupAt's value-bound; relating `fold d` to
-- `fold child` for an opaque size-coded node still needs the Cantor value
-- descent (the nu / descSnd lemma).  Hence: internal CR over opaque certs via
-- FoldRec functions still needs that value-descent -- OR the functions must be
-- reimplemented to recurse on `sz` (a new sz-fuelled recursion whose recovery
-- is sz-bounded via descSzL/descSzR), not as FoldRec folds.
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.SizedPres where

open import T4.Base

open import BRA3.Church         using ( predecessor )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import T4.FoldRec          using ( fold )
open import T4.CoVSpec          using ( cov_spec )
open import T4.BinTreeCovInd    using ( foldStepRaw )

------------------------------------------------------------------------
-- succForm : an opaque nonzero code is a successor of its predecessor.
--   L_sp : neg (var 0 = O) -> s (predecessor (var 0)) = var 0 ; instantiate.

succForm : (d : Term) -> Deriv (neg (eqF d O)) ->
           Deriv (eqF (ap1 s (ap1 predecessor d)) d)
succForm d ne = mp (ruleInst 0 d L_sp) ne

------------------------------------------------------------------------
-- foldOpaque : ETA-FREE unfold of ANY FoldRec fold at an opaque nonzero code.

foldOpaque : (g : Fun1) (h : Fun2) (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 (fold g h) d)
             (ap2 h (ap1 predecessor d)
                    (ap1 Snd (ap2 (cov_spec g h) O (ap1 predecessor d)))))
foldOpaque g h d ne =
  let dEq : Deriv (eqF d (ap1 s (ap1 predecessor d)))
      dEq = ruleSym (succForm d ne)
      liftFold : Deriv (eqF (ap1 (fold g h) d)
                            (ap1 (fold g h) (ap1 s (ap1 predecessor d))))
      liftFold = cong1 (fold g h) dEq
  in ruleTrans liftFold (foldStepRaw g h (ap1 predecessor d))
