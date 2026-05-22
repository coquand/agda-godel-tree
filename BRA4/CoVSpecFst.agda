{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CoVSpecFst -- the counter-preservation invariant for cov_spec.
--
--   fst_cov_spec_eq : (spec K : Term) ->
--     Deriv (eqF (ap1 Fst (ap2 (cov_spec base step) spec K)) K)
--
-- Universal in spec, K : Term.  No Closed premise.  Proof via ruleIndNat
-- on var 0 = K, with var 1 = spec, plus the freshness c-rename to lift
-- to arbitrary Terms.

module BRA4.CoVSpecFst where

open import BRA4.Base
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using ( axFst ; axSnd )
open import BRA3.Logic           using ( prependEqLeft ; impTrans )
open import BRA3.Contrapositive  using ( liftP )

open import BRA3.RuleInst2       using ( ruleInst2 )
import BRA3.RuleInst2
open BRA3.RuleInst2 using
  ( NatLe ; le-suc-right ; le-trans ; maxN ; maxN-le-left ; maxN-le-right
  ; maxVarT ; substT_above_max ; natEq-refl )

------------------------------------------------------------------------
-- v01 form:  Deriv (eqF (Fst (cov_spec base step var1 var0)) var0) ,
-- universal in var 0 = K.
--
-- Proof by ruleIndNat 0.

fst_cov_spec_eq_v01 :
  (baseFun : Fun1) (stepFun : Fun2) ->
  Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) (var (suc zero)) (var zero))) (var zero))
fst_cov_spec_eq_v01 baseFun stepFun =
  ruleIndNat 0 {P = Pform} baseCase stepImp
  where
    specT : Term
    specT = var (suc zero)

    Pform : Formula
    Pform = eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT (var zero))) (var zero)

    -- Base K = O: Fst (cov_spec base step spec O) = O.
    baseCase :
      Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT O)) O)
    baseCase =
      let base_eq :
            Deriv (eqF (ap2 (cov_spec baseFun stepFun) specT O)
                        (ap2 pi O (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))))
          base_eq = cov_spec_base baseFun stepFun specT

          fst_base :
            Deriv (eqF (ap1 Fst (ap2 pi O (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))))
                        O)
          fst_base = axFst O (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))
      in ruleTrans (cong1 Fst base_eq) fst_base

    -- Step: under IH (Fst (cov_spec ... K) = K), prove for s K.
    stepImp :
      Deriv (imp Pform (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero))))
                              (ap1 s (var zero))))
    stepImp =
      let prev : Term
          prev = ap2 (cov_spec baseFun stepFun) specT (var zero)

          -- cov_spec spec (s var0) = state_step_spec step prev.
          step_eq :
            Deriv (eqF (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))
                        (ap1 (state_step_spec stepFun) prev))
          step_eq = cov_spec_step_univ baseFun stepFun specT (var zero)

          -- Fst (cov_spec ... (s var0)) = Fst (state_step_spec step prev).
          fst_step :
            Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero))))
                        (ap1 Fst (ap1 (state_step_spec stepFun) prev)))
          fst_step = cong1 Fst step_eq

          -- Fst (state_step_spec step prev) = s (Fst prev).
          -- via state_step_spec_eq + axFst.
          shape :
            Deriv (eqF (ap1 (state_step_spec stepFun) prev)
                        (ap2 pi (ap1 s (ap1 Fst prev))
                                (ap2 pi (ap1 Fst (ap1 Snd prev))
                                        (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                                (ap1 Snd (ap1 Snd prev))))))
          shape = state_step_spec_eq stepFun prev

          fst_shape :
            Deriv (eqF (ap1 Fst (ap1 (state_step_spec stepFun) prev))
                        (ap1 Fst (ap2 pi (ap1 s (ap1 Fst prev))
                                  (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev)))))))
          fst_shape = cong1 Fst shape

          fst_pi :
            Deriv (eqF (ap1 Fst (ap2 pi (ap1 s (ap1 Fst prev))
                                  (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev))))))
                        (ap1 s (ap1 Fst prev)))
          fst_pi = axFst (ap1 s (ap1 Fst prev))
                          (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))

          fst_step_to_s :
            Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero))))
                        (ap1 s (ap1 Fst prev)))
          fst_step_to_s = ruleTrans fst_step (ruleTrans fst_shape fst_pi)

          -- Under IH (Pform = eqF (Fst prev) (var 0)),  s (Fst prev) = s var0.
          cong_s : Deriv (imp Pform (eqF (ap1 s (ap1 Fst prev)) (ap1 s (var zero))))
          cong_s = ax_eqCong1 s (ap1 Fst prev) (var zero)

          -- prependEqLeft: from fst_step_to_s (= eqF LHS (s (Fst prev))),
          -- get imp (eqF (s (Fst prev)) (s var0)) (eqF LHS (s var0)).
          prepend :
            Deriv (imp (eqF (ap1 s (ap1 Fst prev)) (ap1 s (var zero)))
                        (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero))))
                              (ap1 s (var zero))))
          prepend = prependEqLeft
                      (ap1 Fst (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero))))
                      (ap1 s (ap1 Fst prev))
                      (ap1 s (var zero))
                      fst_step_to_s
      in impTrans cong_s prepend

------------------------------------------------------------------------
-- fst_cov_spec_eq : universal-in-Term form.
--
-- For any spec, K : Term:
--   Deriv (eqF (Fst (cov_spec base step spec K)) K)
--
-- Proof: c-renaming.  Pick c fresh in K and spec.  Rename var 1 := var c,
-- then ruleInst 0 K (instantiating the fuel argument), then ruleInst c
-- spec (using substT_above_max to bridge substT c spec K = K).

private
  freshKS : Term -> Term -> Nat
  freshKS K spec = suc (suc (maxN (maxVarT K) (maxVarT spec)))

  freshKS_above_K : (K spec : Term) -> NatLe (maxVarT K) (freshKS K spec)
  freshKS_above_K K spec =
    le-suc-right (le-suc-right (maxN-le-left (maxVarT K) (maxVarT spec)))

fst_cov_spec_eq :
  (baseFun : Fun1) (stepFun : Fun2) (spec K : Term) ->
  Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) spec K)) K)
fst_cov_spec_eq baseFun stepFun spec K =
  let c : Nat
      c = freshKS K spec

      -- step1: rename var 1 to var c.
      step1 :
        Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) (var c) (var zero))) (var zero))
      step1 = ruleInst 1 (var c) (fst_cov_spec_eq_v01 baseFun stepFun)

      -- step2: ruleInst 0 K.  This substitutes var 0 := K, possibly
      -- transforming (var c) substT inside... but substT 0 K (var c) = var c
      -- since c ≥ 2 > 0 (natEq 0 c reduces to false).
      step2 :
        Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) (var c) K)) K)
      step2 = ruleInst 0 K step1

      -- step3: ruleInst c spec.  Substitutes var c := spec; also touches
      -- the K substituent (substT c spec K) and the var c position
      -- (substT c spec (var c)).  Bridge via substT_above_max + natEq-refl.
      step3_raw :
        Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) (substT c spec (var c)) (substT c spec K))) (substT c spec K))
      step3_raw = ruleInst c spec step2

      bridge_K : Eq (substT c spec K) K
      bridge_K = substT_above_max c K spec (freshKS_above_K K spec)

      bridge_vc : Eq (substT c spec (var c)) spec
      bridge_vc = eqCong (\ b -> boolCase b spec (var c)) (natEq-refl c)

      step3 :
        Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) (substT c spec (var c)) K)) K)
      step3 = eqSubst (\ x -> Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) (substT c spec (var c)) x)) x))
                       bridge_K step3_raw
  in eqSubst (\ x -> Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) x K)) K))
              bridge_vc step3
