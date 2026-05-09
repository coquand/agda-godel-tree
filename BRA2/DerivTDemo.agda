{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DerivTDemo -- worked examples in the threshold derivation type.
--
-- Demonstrates that DerivT (BRA2.DerivT) is functional by building
-- non-trivial derivations.  These examples exercise:
--
--   1. axTreeEqLL: a leaf-leaf TreeEq computation (DerivT analog of
--      Deriv's axTreeEqLL).
--   2. forget: lift a DerivT proof to a Deriv proof.
--   3. indBT: tree induction at an atomic predicate.
--
-- Together these show that the threshold system has both the
-- expressiveness (indBT works) and the soundness (forget works) needed
-- to carry a refactored godelII chain.  The remaining engineering is
-- to lift the entire 147-file GoedelIIFull closure across forget, a
-- mechanical refactor.

module BRA2.DerivTDemo where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivT
import BRA2.Deriv as D

------------------------------------------------------------------------
-- Demo 1: the simplest atomic equation, axTreeEqLL.

demo_treeEqLL : DerivT (atomic (eqn (ap2 TreeEq O O) O))
demo_treeEqLL = axTreeEqLL

-- forget(axTreeEqLL) = D.axTreeEqLL  by definition of forget.
demo_treeEqLL_lifted : D.Deriv (atomic (eqn (ap2 TreeEq O O) O))
demo_treeEqLL_lifted = forget demo_treeEqLL

------------------------------------------------------------------------
-- Demo 2: a chained equational derivation — axI x = x followed by
-- ruleTrans/cong1/etc., showing the structural rules work.

demo_doubleI : (t : Term) ->
               DerivT (atomic (eqn (ap1 I (ap1 I t)) t))
demo_doubleI t =
  -- ap1 I (ap1 I t)  =  ap1 I t   (by axI applied inside via cong1)
  -- ap1 I t          =  t          (by axI t)
  ruleTrans (cong1 I (axI t)) (axI t)

demo_doubleI_lifted : (t : Term) ->
                      D.Deriv (atomic (eqn (ap1 I (ap1 I t)) t))
demo_doubleI_lifted t = forget (demo_doubleI t)

------------------------------------------------------------------------
-- Demo 3: an actual use of indBT (atomic-only tree induction).
--
-- Prove  forall x.  ap1 Z x = O   by tree induction on x.
-- Note: this is also derivable directly from axZ; the point is to
-- exercise indBT.

private
  motiveZ : Equation
  motiveZ = eqn (ap1 Z (var zero)) O

  baseZ : DerivT (atomic (substEq zero O motiveZ))
  baseZ = axZ O   -- substEq zero O motiveZ  =  eqn (ap1 Z O) O

  -- Step:  IH1 imp (IH2 imp goal_at_pair).
  -- IH1 = atomic (eqn (ap1 Z (var v1)) O) ;  similar for IH2.
  -- goal_at_pair = atomic (eqn (ap1 Z (Pair v1 v2)) O).
  -- The step doesn't need the IHs (axZ closes goal directly), so we
  -- discharge them by double-axK.

  v1Nat v2Nat : Nat
  v1Nat = suc zero
  v2Nat = suc (suc zero)

  v1T v2T : Term
  v1T = var v1Nat
  v2T = var v2Nat

  pairV : Term
  pairV = ap2 Pair v1T v2T

  IH1 IH2 goalPair : Formula
  IH1     = atomic (eqn (ap1 Z v1T) O)
  IH2     = atomic (eqn (ap1 Z v2T) O)
  goalPair = atomic (eqn (ap1 Z pairV) O)

  goalPair_proof : DerivT goalPair
  goalPair_proof = axZ pairV

  -- Discharge via double-axK: from a proof of goalPair, get
  -- IH1 imp (IH2 imp goalPair).
  step_proof : DerivT (IH1 imp (IH2 imp goalPair))
  step_proof =
    mp (axK (IH2 imp goalPair) IH1)
       (mp (axK goalPair IH2) goalPair_proof)

demo_indBT : DerivT (atomic motiveZ)
demo_indBT = indBT motiveZ v1Nat v2Nat baseZ step_proof

-- forget the indBT proof to get a full Deriv.
demo_indBT_lifted :
  D.Deriv (atomic (eqn (ap1 Z (var zero)) O))
demo_indBT_lifted = forget demo_indBT

------------------------------------------------------------------------
-- Demo 4: indBT2 (diagonal-IH tree induction at an atomic predicate).
--
-- Trivial demo: prove  forall x v. v = v  by 2D tree induction on x
-- (and trivially on v, since motiveRefl uses only var (suc zero)).
-- Provable directly by axRefl; the point is to exercise indBT2.

private
  -- Motive uses var (suc zero), not var zero, so substituting var zero
  -- by t1 leaves it unchanged; substituting var (suc zero) by t2
  -- yields  eqn t2 t2 .
  motiveRefl : Equation
  motiveRefl = eqn (var (suc zero)) (var (suc zero))

  v3Nat v4Nat : Nat
  v3Nat = suc (suc (suc zero))
  v4Nat = suc (suc (suc (suc zero)))

  v3T v4T : Term
  v3T = var v3Nat
  v4T = var v4Nat

  -- Helper: from  axRefl t  build  H1 imp (H2 imp atomic (eqn t t)).
  doubleK : (t : Term) (H1 H2 : Formula) ->
            DerivT (H1 imp (H2 imp (atomic (eqn t t))))
  doubleK t H1 H2 =
    mp (axK (H2 imp (atomic (eqn t t))) H1)
       (mp (axK (atomic (eqn t t)) H2) (axRefl t))

  -- After both substitutions  motiveRefl  reduces:
  --   substEq (suc zero) X (substEq zero Y motiveRefl)  =  eqn X X .
  -- So baseLL : eqn O O ; baseLN/PP at v(suc 0)=Pair v3 v4 : eqn (Pair v3 v4)(Pair v3 v4) ;
  --    baseNL at v(suc 0)=O : eqn O O .

  baseLL_demo : DerivT (atomic (substEq (suc zero) O (substEq zero O motiveRefl)))
  baseLL_demo = axRefl O

  baseLN_demo :
    DerivT ((atomic (substEq (suc zero) v3T (substEq zero O motiveRefl))) imp
            ((atomic (substEq (suc zero) v4T (substEq zero O motiveRefl))) imp
             (atomic (substEq (suc zero) (ap2 Pair v3T v4T)
                                          (substEq zero O motiveRefl)))))
  baseLN_demo = doubleK (ap2 Pair v3T v4T)
                  (atomic (substEq (suc zero) v3T (substEq zero O motiveRefl)))
                  (atomic (substEq (suc zero) v4T (substEq zero O motiveRefl)))

  baseNL_demo :
    DerivT ((atomic (substEq (suc zero) O (substEq zero v1T motiveRefl))) imp
            ((atomic (substEq (suc zero) O (substEq zero v2T motiveRefl))) imp
             (atomic (substEq (suc zero) O
                                          (substEq zero (ap2 Pair v1T v2T) motiveRefl)))))
  baseNL_demo = doubleK O
                  (atomic (substEq (suc zero) O (substEq zero v1T motiveRefl)))
                  (atomic (substEq (suc zero) O (substEq zero v2T motiveRefl)))

  basePP_demo :
    DerivT ((atomic (substEq (suc zero) v3T (substEq zero v1T motiveRefl))) imp
            ((atomic (substEq (suc zero) v4T (substEq zero v2T motiveRefl))) imp
             (atomic (substEq (suc zero) (ap2 Pair v3T v4T)
                                          (substEq zero (ap2 Pair v1T v2T) motiveRefl)))))
  basePP_demo = doubleK (ap2 Pair v3T v4T)
                  (atomic (substEq (suc zero) v3T (substEq zero v1T motiveRefl)))
                  (atomic (substEq (suc zero) v4T (substEq zero v2T motiveRefl)))

demo_indBT2 : DerivT (atomic motiveRefl)
demo_indBT2 = indBT2 motiveRefl v1Nat v2Nat v3Nat v4Nat
                    baseLL_demo baseLN_demo baseNL_demo basePP_demo

demo_indBT2_lifted : D.Deriv (atomic motiveRefl)
demo_indBT2_lifted = forget demo_indBT2
