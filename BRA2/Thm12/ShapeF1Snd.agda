{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.ShapeF1Snd -- mirror of ShapeF1Fst for Parts.Snd.D_Snd.

module BRA2.Thm12.ShapeF1Snd where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv

open import BRA2.Cor using (cor)
open import BRA2.Thm12.Parts.Snd
  using ( D_Snd
        ; D_Snd_reduce_O
        ; D_Snd_reduce_Pair )
open import BRA2.Thm12.Param.AxSndLf using (parEncAxSndLf)
open import BRA2.Thm12.Param.AxSnd   using (parEncAxSnd)
open import BRA2.FromBaseAndPair using (fromBaseAndPair)

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
-- Shape formula.

P_shape_Snd : Formula
P_shape_Snd =
  atomic (eqn (ap1 Fst (ap1 D_Snd (var zero)))
              (ap2 Pair (ap1 Fst (ap1 Fst (ap1 D_Snd (var zero))))
                        (ap1 Snd (ap1 Fst (ap1 D_Snd (var zero))))))

private
  leaf_shape :
    (X : Term) (parEnc : Term) ->
    Deriv (atomic (eqn (ap1 D_Snd X) parEnc)) ->
    (pTag pBody : Term) ->
    Deriv (atomic (eqn parEnc (ap2 Pair pTag pBody))) ->
    (tA tB : Term) ->
    Deriv (atomic (eqn pTag (ap2 Pair tA tB))) ->
    Deriv (atomic
      (eqn (ap1 Fst (ap1 D_Snd X))
           (ap2 Pair
             (ap1 Fst (ap1 Fst (ap1 D_Snd X)))
             (ap1 Snd (ap1 Fst (ap1 D_Snd X))))))
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
                  (congR Pair (ap1 Fst (ap1 Fst (ap1 D_Snd X))) rhs_snd)
    in ruleTrans s123 rhs_pair

shape_lf :
  Deriv (atomic (eqn (ap1 Fst (ap1 D_Snd O))
                     (ap2 Pair (ap1 Fst (ap1 Fst (ap1 D_Snd O)))
                               (ap1 Snd (ap1 Fst (ap1 D_Snd O))))))
shape_lf =
  leaf_shape O (parEncAxSndLf O) D_Snd_reduce_O
             _ _ (axRefl _)
             _ _ (axRefl _)

shape_pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap1 D_Snd (ap2 Pair v1 v2)))
                     (ap2 Pair (ap1 Fst (ap1 Fst (ap1 D_Snd (ap2 Pair v1 v2))))
                               (ap1 Snd (ap1 Fst (ap1 D_Snd (ap2 Pair v1 v2)))))))
shape_pair v1 v2 =
  leaf_shape (ap2 Pair v1 v2)
             (parEncAxSnd (ap1 cor v1) (ap1 cor v2))
             (D_Snd_reduce_Pair v1 v2)
             _ _ (axRefl _)
             _ _ (axRefl _)

shape_baseLf : Deriv (substF zero O P_shape_Snd)
shape_baseLf = shape_lf

shape_basePair : (v1Idx v2Idx : Nat) ->
  Deriv (substF zero (ap2 Pair (var v1Idx) (var v2Idx)) P_shape_Snd)
shape_basePair v1Idx v2Idx = shape_pair (var v1Idx) (var v2Idx)

shape_D_F1_Snd_var0 : Deriv P_shape_Snd
shape_D_F1_Snd_var0 =
  fromBaseAndPair P_shape_Snd (suc (suc zero)) (suc (suc (suc zero)))
    shape_baseLf
    (shape_basePair (suc (suc zero)) (suc (suc (suc zero))))
