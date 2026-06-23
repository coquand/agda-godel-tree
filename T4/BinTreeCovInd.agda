{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BinTreeCovInd -- towards the OBJECT course-of-values induction principle
-- over binary-tree codes, RAW-PROJECTION style (no surjective pairing).
--
-- RESULT OF THIS INVESTIGATION (precise, honest):
--   * The eta-free GENERIC SUCCESSOR UNFOLD of a FoldRec fold IS provable and
--     is delivered here as  foldStepRaw  (the reusable linchpin): at ANY
--     successor input  s m  (m opaque),
--         fold g h (s m)  =  h m (Snd (cov_spec g h O m))
--     with NO pi-form / surjective-pairing needed -- the predecessor is just
--     m, and the step body  h  fires on the package built from m.  So the
--     fold's DISPATCH (on the head tag  Fst d ) and CHILD EXTRACTION (via
--     Snd-projections of  d ) over an OPAQUE code go through eta-free.
--
--   * THE WALL (genuine, reported, not faked): the recursion RECOVERY needed
--     to feed the induction hypothesis to the children -- i.e. the bound
--         leq child (pred d)        [= leq child m, the table fuel]
--     -- is only obtainable from  T4.LeqMono.leq_pi_right / leq_sigma_right ,
--     which require the BOUND to be literally  pi A B / sigma A B  embedding
--     the child.  That is exactly  d = pi (s A) b  (pi-form), i.e. the
--     surjective-pairing eta  Pair (Fst d) (Snd d) = d .  For an opaque/free
--     code  d  there is no other route to  leq child (pred d) : pred d is
--     opaque and bears no provable order relation to the projections of  d
--     without the pairing structure.
--
--   WHY THE STACK MACHINE (Stability) AVOIDED THIS, yet a TREE induction
--   cannot: T4.Stability proves LOOKUP INVARIANCE, where the position  t  and
--   bound  K  are FREE variables and  leq t K  is a HYPOTHESIS of the property
--   -- the leq bound is GIVEN, never derived from a code's structure.  A
--   tree-structural property (e.g. wf (mirrorF d) = O) must DERIVE each
--   child's bound  leq child (pred d)  FROM the parent's pair structure, and
--   that derivation is precisely surjective pairing.
--
--   CONCLUSION: the object structural induction over OPAQUE tree codes does
--   require surjective pairing (only the child-DESCENT step; dispatch and
--   extraction are eta-free).  The keystone is unavoidable for opaque codes;
--   the alternative is to carry meta structure (T4.BinTree.BinM / CertTree),
--   which sidesteps opacity but does not apply to the certificates the
--   internal confluence produces.
--
-- This file delivers the eta-free part green (foldStepRaw) so a future
-- triF-preservation proof can reuse it for the dispatch/extraction half, and
-- pins the exact missing lemma for the descent half.
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.BinTreeCovInd where

open import T4.Base

open import T4.FoldRec    using ( fold ; fold_unfold )
open import T4.CoVSpec    using ( cov_spec ; readOff_spec ; state_step_spec )
open import T4.CoVSpecUniv using ( cov_spec_step_univ ; readOff_state_step_univ )
open import T4.CoVSpecFst using ( fst_cov_spec_eq )

------------------------------------------------------------------------
-- foldStepRaw : the ETA-FREE generic successor unfold.
--
--   fold g h (s m)  =  h m (Snd (cov_spec g h O m))
--
-- Proof (all lemmas universal in the input, none requiring pi-form):
--   fold g h (s m)
--     = readOff_spec (cov_spec g h O (s m))            [fold_unfold]
--     = readOff_spec (state_step_spec h prev)          [cov_spec_step_univ]
--     = h (Fst prev) (Snd prev)                         [readOff_state_step_univ]
--     = h m (Snd prev)                                  [fst_cov_spec_eq]
--   where prev = cov_spec g h O m.

foldStepRaw :
  (g : Fun1) (h : Fun2) (m : Term) ->
  Deriv (eqF (ap1 (fold g h) (ap1 s m))
             (ap2 h m (ap1 Snd (ap2 (cov_spec g h) O m))))
foldStepRaw g h m =
  let prev : Term
      prev = ap2 (cov_spec g h) O m

      e1 : Deriv (eqF (ap1 (fold g h) (ap1 s m))
                      (ap1 readOff_spec (ap2 (cov_spec g h) O (ap1 s m))))
      e1 = fold_unfold g h (ap1 s m)

      e2 : Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec g h) O (ap1 s m)))
                      (ap1 readOff_spec (ap1 (state_step_spec h) prev)))
      e2 = cong1 readOff_spec (cov_spec_step_univ g h O m)

      e3 : Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec h) prev))
                      (ap2 h (ap1 Fst prev) (ap1 Snd prev)))
      e3 = readOff_state_step_univ h prev

      e4 : Deriv (eqF (ap2 h (ap1 Fst prev) (ap1 Snd prev))
                      (ap2 h m (ap1 Snd prev)))
      e4 = congL h (ap1 Snd prev) (fst_cov_spec_eq g h O m)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))
