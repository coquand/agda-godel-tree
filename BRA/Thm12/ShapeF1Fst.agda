{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.ShapeF1Fst -- universal Fst-shape for Parts.Fst.D_Fst
-- (the Df used by FromBridges' thm12_F1 Fst case).
--
-- D_Fst dispatches via IfLf:
--   D_Fst O = parEncAxFstLf O = Pair tagCode_axFstLf O
--   D_Fst (Pair v1 v2) = parEncAxFst (cor v1) (cor v2) = Pair tagCode_axFst (...)
-- Both Fst-extracts are concrete tagCode_* (positive natCode reify),
-- definitionally Pair O <inner>.

module BRA.Thm12.ShapeF1Fst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

open import BRA.Cor using (cor)
open import BRA.Thm12.Parts.Fst
  using ( D_Fst
        ; D_Fst_reduce_O
        ; D_Fst_reduce_Pair )
open import BRA.Thm12.Param.AxFstLf using (parEncAxFstLf)
open import BRA.Thm12.Param.AxFst   using (parEncAxFst)
open import BRA.FromBaseAndPair using (fromBaseAndPair)

------------------------------------------------------------------------
-- Pair-eta.

private
  pair_eta : (a b : Term) ->
    Deriv (atomic (eqn (ap2 Pair a b)
                       (ap2 Pair (ap1 Fst (ap2 Pair a b))
                                 (ap1 Snd (ap2 Pair a b)))))
  pair_eta a b =
    let
      fstEq = axFst a b
      sndEq = axSnd a b
      step1 : Deriv (atomic (eqn (ap2 Pair a b)
                                 (ap2 Pair (ap1 Fst (ap2 Pair a b)) b)))
      step1 = congL Pair b (ruleSym fstEq)
      step2 : Deriv (atomic (eqn (ap2 Pair (ap1 Fst (ap2 Pair a b)) b)
                                 (ap2 Pair (ap1 Fst (ap2 Pair a b))
                                           (ap1 Snd (ap2 Pair a b)))))
      step2 = congR Pair (ap1 Fst (ap2 Pair a b)) (ruleSym sndEq)
    in ruleTrans step1 step2

------------------------------------------------------------------------
-- The shape formula.

P_shape_Fst : Formula
P_shape_Fst =
  atomic (eqn (ap1 Fst (ap1 D_Fst (var zero)))
              (ap2 Pair (ap1 Fst (ap1 Fst (ap1 D_Fst (var zero))))
                        (ap1 Snd (ap1 Fst (ap1 D_Fst (var zero))))))

------------------------------------------------------------------------
-- Generic leaf shape lifter.

private
  leaf_shape :
    (X : Term) (parEnc : Term) ->
    Deriv (atomic (eqn (ap1 D_Fst X) parEnc)) ->
    (pTag pBody : Term) ->
    Deriv (atomic (eqn parEnc (ap2 Pair pTag pBody))) ->
    (tA tB : Term) ->
    Deriv (atomic (eqn pTag (ap2 Pair tA tB))) ->
    Deriv (atomic
      (eqn (ap1 Fst (ap1 D_Fst X))
           (ap2 Pair
             (ap1 Fst (ap1 Fst (ap1 D_Fst X)))
             (ap1 Snd (ap1 Fst (ap1 D_Fst X))))))
  leaf_shape X parEnc reduce pTag pBody parEncIsPair tA tB pTagIsPair =
    let
      s1 = cong1 Fst reduce
      s2a = cong1 Fst parEncIsPair
      s2b = axFst pTag pBody
      s2 = ruleTrans s2a s2b
      s12 = ruleTrans s1 s2

      etaTag = pair_eta tA tB
      bridge_fst = cong1 Fst (ruleSym pTagIsPair)
      bridge_snd = cong1 Snd (ruleSym pTagIsPair)
      etaTagBridged : Deriv (atomic (eqn pTag
                                          (ap2 Pair (ap1 Fst pTag) (ap1 Snd pTag))))
      etaTagBridged =
        ruleTrans pTagIsPair
          (ruleTrans etaTag
            (ruleTrans (congL Pair (ap1 Snd (ap2 Pair tA tB)) bridge_fst)
                       (congR Pair (ap1 Fst pTag) bridge_snd)))

      s123 = ruleTrans s12 etaTagBridged
      s12_sym = ruleSym s12
      rhs_fst = cong1 Fst s12_sym
      rhs_snd = cong1 Snd s12_sym
      rhs_pair =
        ruleTrans (congL Pair (ap1 Snd pTag) rhs_fst)
                  (congR Pair (ap1 Fst (ap1 Fst (ap1 D_Fst X))) rhs_snd)
    in ruleTrans s123 rhs_pair

------------------------------------------------------------------------
-- Lf and Pair leaf cases.

shape_lf :
  Deriv (atomic (eqn (ap1 Fst (ap1 D_Fst O))
                     (ap2 Pair (ap1 Fst (ap1 Fst (ap1 D_Fst O)))
                               (ap1 Snd (ap1 Fst (ap1 D_Fst O))))))
shape_lf =
  leaf_shape O (parEncAxFstLf O) D_Fst_reduce_O
             _ _ (axRefl _)
             _ _ (axRefl _)

shape_pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap1 D_Fst (ap2 Pair v1 v2)))
                     (ap2 Pair (ap1 Fst (ap1 Fst (ap1 D_Fst (ap2 Pair v1 v2))))
                               (ap1 Snd (ap1 Fst (ap1 D_Fst (ap2 Pair v1 v2)))))))
shape_pair v1 v2 =
  leaf_shape (ap2 Pair v1 v2)
             (parEncAxFst (ap1 cor v1) (ap1 cor v2))
             (D_Fst_reduce_Pair v1 v2)
             _ _ (axRefl _)
             _ _ (axRefl _)

------------------------------------------------------------------------
-- Schematic shape via fromBaseAndPair.

shape_baseLf : Deriv (substF zero O P_shape_Fst)
shape_baseLf = shape_lf

shape_basePair : (v1Idx v2Idx : Nat) ->
  Deriv (substF zero (ap2 Pair (var v1Idx) (var v2Idx)) P_shape_Fst)
shape_basePair v1Idx v2Idx = shape_pair (var v1Idx) (var v2Idx)

shape_D_F1_Fst_var0 : Deriv P_shape_Fst
shape_D_F1_Fst_var0 =
  fromBaseAndPair P_shape_Fst (suc (suc zero)) (suc (suc (suc zero)))
    shape_baseLf
    (shape_basePair (suc (suc zero)) (suc (suc (suc zero))))
