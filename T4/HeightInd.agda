{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.HeightInd -- an object HEIGHT measure on binary-tree codes and the
-- ETA-FREE height-descent for nodes (attempt3 §14, framing (B)).
--
--   height (binLeaf n)     = s O                       (height_leaf)
--   height (binNode n l r) = s (sigma (height l) (height r))   (height_node)
-- (sigma = Church addition; an upper bound of both children suffices, so the
--  child-descent below needs only leq_sigma_left/right + s-monotonicity T78,
--  NOT surjective pairing.)
--
--   descHL : leq (s (height l)) (height (binNode n l r))   (eta-free)
--   descHR : leq (s (height r)) (height (binNode n l r))   (eta-free)
--
-- These are GREEN with no surjective pairing: on a BUILT node the descent on
-- the height MEASURE is immediate (max/sum upper bound + T78).
--
-- ====================================================================
-- VERDICT on "does height-indexing give ETA-FREE induction over OPAQUE
-- codes?"  --  NO, not by itself.  Height-indexing fixes the OUTER
-- induction's descent (height child < height node, above), but the
-- FUNCTIONS we induct about (wf, mirrorF, the cert maps) are T4.FoldRec
-- course-of-values folds whose INTERNAL child-recovery (FoldRec.lookup_eq_fold
-- / NP.np_lookup_gen) is bounded by the CODE VALUE: it recovers fold(child)
-- only under  leq child (pred d) .  That value-descent is baked into the fold
-- and is exactly the surjective-pairing keystone; the height bound
-- (leq (height child) (height d)) cannot discharge it.  foldStepRaw
-- (T4.BinTreeCovInd) makes DISPATCH + EXTRACTION eta-free, but the RECURSIVE
-- RECOVERY stays value-bounded.
--
-- CONSEQUENCE: to get eta-free induction over OPAQUE codes the FUNCTIONS
-- themselves must be reimplemented by FUEL/HEIGHT iteration (the CK-machine /
-- evalU pattern, T4.DevMachine/DevStep), so their recovery is height-bounded
-- too.  Then both the outer induction and the inner recovery descend on
-- height and no surjective pairing is needed.  This vindicates the evalU/CK
-- route as THE way to internalise CR over opaque (existential-witness) certs;
-- FoldRec folds cannot be the implementation for those.
--
-- This file delivers targets 1+2 (height + eta-free height-descent) GREEN;
-- the opaque-code validation (target 3) is the wall above, reported not faked.
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.HeightInd where

open import T4.Base

open import T4.BinTree   using ( binLeaf ; binNode ; lIdx ; rIdx )
open import T4.FoldRec   using ( lookupAt )
open import T4.ParsObj   using ( foldOf ; test1 ; module NP )
open import T4.LenR      using ( get_rc )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans ; leq_sigma_left ; leq_sigma_right )

open import BRA3.Church        using ( pi ; sigma ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.ChurchT78     using ( T78 )
open import BRA3.RuleInst2     using ( ruleInst2 )
open import BRA3.PairAlgebra   using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  The height fold.

cellLeafH : Fun1
cellLeafH = constN 1                                           -- leaf -> s O

cellNodeH : Fun1                                               -- node -> s (h l + h r)
cellNodeH = compose1U s (C sigma (lookupAt lIdx) (lookupAt rIdx))

height : Fun1
height = foldOf Z cellLeafH cellNodeH

------------------------------------------------------------------------
-- SECTION 2.  height_leaf :  height (binLeaf n) = s O .

height_leaf : (n : Term) -> Deriv (eqF (ap1 height (binLeaf n)) (natCode 1))
height_leaf n =
  let open NP Z cellLeafH cellNodeH O n
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (constN_eq 1 input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  height_node :  height (binNode n l r) = s (sigma (h l) (h r)) .

height_node : (n l r : Term) ->
  Deriv (eqF (ap1 height (binNode n l r))
             (ap1 s (ap2 sigma (ap1 height l) (ap1 height r))))
height_node n l r =
  let open NP Z cellLeafH cellNodeH (natCode 1) (ap2 Pair n (ap2 Pair l r))

      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair l r))
      sndArg_eq =
        ruleTrans (compose1U_eq Snd get_rc input_pkg)
          (ruleTrans (cong1 Snd np_rc) (axSnd n (ap2 Pair l r)))
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) l)
      lIdx_eq =
        ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
          (ruleTrans (cong1 Fst sndArg_eq) (axFst l r))
      rIdx_eq : Deriv (eqF (ap1 rIdx input_pkg) r)
      rIdx_eq =
        ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
          (ruleTrans (cong1 Snd sndArg_eq) (axSnd l r))
      leq_lr_P : Deriv (leq (ap2 Pair l r) P_outer)
      leq_lr_P = leq_trans (ap2 Pair l r) (ap2 Pair n (ap2 Pair l r)) P_outer
                   (leq_pi_right n (ap2 Pair l r)) leq_b_P
      leq_l_P : Deriv (leq l P_outer)
      leq_l_P = leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P
      leq_r_P : Deriv (leq r P_outer)
      leq_r_P = leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P

      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 height l))
      recL = np_lookup_gen lIdx l lIdx_eq leq_l_P
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 height r))
      recR = np_lookup_gen rIdx r rIdx_eq leq_r_P

      cellNodeH_val :
        Deriv (eqF (ap1 cellNodeH input_pkg)
                   (ap1 s (ap2 sigma (ap1 height l) (ap1 height r))))
      cellNodeH_val =
        ruleTrans (compose1U_eq s (C sigma (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
          (cong1 s
            (ruleTrans (ax_C sigma (lookupAt lIdx) (lookupAt rIdx) input_pkg)
              (ruleTrans (congL sigma (ap1 (lookupAt rIdx) input_pkg) recL)
                         (congR sigma (ap1 height l) recR))))
  in ruleTrans (collapse_snd t1_O) cellNodeH_val

------------------------------------------------------------------------
-- SECTION 4.  THE ETA-FREE HEIGHT-DESCENT (the crux: no surjective pairing).
--   leq (s (height child)) (height (binNode n l r))
-- via: child-height <= sigma(h l)(h r) (leq_sigma_left/right) + s-mono (T78),
-- then rewrite the bound through height_node (sub-congruence; leq a b is
-- definitionally eqF (sub a b) O).

descHL : (n l r : Term) ->
  Deriv (leq (ap1 s (ap1 height l)) (ap1 height (binNode n l r)))
descHL n l r =
  let hl : Term
      hl = ap1 height l
      hr : Term
      hr = ap1 height r
      sumlr : Term
      sumlr = ap2 sigma hl hr
      bound : Deriv (leq hl sumlr)
      bound = leq_sigma_left hl hr
      mono : Deriv (imp (leq hl sumlr) (leq (ap1 s hl) (ap1 s sumlr)))
      mono = ruleInst2 0 hl 1 sumlr refl T78
      leqS : Deriv (leq (ap1 s hl) (ap1 s sumlr))
      leqS = mp mono bound
  in ruleTrans (congR sub (ap1 s hl) (height_node n l r)) leqS

descHR : (n l r : Term) ->
  Deriv (leq (ap1 s (ap1 height r)) (ap1 height (binNode n l r)))
descHR n l r =
  let hl : Term
      hl = ap1 height l
      hr : Term
      hr = ap1 height r
      sumlr : Term
      sumlr = ap2 sigma hl hr
      bound : Deriv (leq hr sumlr)
      bound = leq_sigma_right hl hr
      mono : Deriv (imp (leq hr sumlr) (leq (ap1 s hr) (ap1 s sumlr)))
      mono = ruleInst2 0 hr 1 sumlr refl T78
      leqS : Deriv (leq (ap1 s hr) (ap1 s sumlr))
      leqS = mp mono bound
  in ruleTrans (congR sub (ap1 s hr) (height_node n l r)) leqS
