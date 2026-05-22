{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CoVSpecSpec -- the spec-preservation invariant for cov_spec.
--
--   fstSnd_cov_spec_eq : (spec K : Term) ->
--     Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec base step) spec K))) spec)
--
-- Universal in spec, K : Term.  No Closed premise.  Proof via ruleIndNat
-- on var 0 = K, with var 1 = spec, plus the freshness c-rename.  Mirrors
-- the structure of  BRA4.CoVSpecFst.fst_cov_spec_eq , but proves the
-- spec-projection invariant (Fst Snd) instead of the counter-projection
-- invariant (Fst).
--
-- Used by  BRA4.SbF  to bridge  get_spec input_pkg = spec  inside
-- stepFun_sbf 's atomic branch.

module BRA4.CoVSpecSpec where

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
-- v01 form:  Deriv (eqF (Fst (Snd (cov_spec base step var1 var0))) var1) ,
-- universal in var 0 = K.
--
-- Proof by ruleIndNat 0.

fstSnd_cov_spec_eq_v01 :
  (baseFun : Fun1) (stepFun : Fun2) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun)
                                      (var (suc zero)) (var zero))))
              (var (suc zero)))
fstSnd_cov_spec_eq_v01 baseFun stepFun =
  ruleIndNat 0 {P = Pform} baseCase stepImp
  where
    specT : Term
    specT = var (suc zero)

    Pform : Formula
    Pform = eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (var zero))))
                 specT

    ------------------------------------------------------------------
    -- Base K = O:  Fst (Snd (cov_spec base step spec O)) = spec.
    --   cov_spec base step spec O = pi O (pi spec (pi (base spec) O))
    --   Snd of that = pi spec (pi (base spec) O)
    --   Fst of that = spec.

    baseCase :
      Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT O))) specT)
    baseCase =
      let base_eq :
            Deriv (eqF (ap2 (cov_spec baseFun stepFun) specT O)
                        (ap2 pi O (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))))
          base_eq = cov_spec_base baseFun stepFun specT

          snd_base :
            Deriv (eqF (ap1 Snd (ap2 pi O (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))))
                        (ap2 pi specT (ap2 pi (ap1 baseFun specT) O)))
          snd_base = axSnd O (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))

          fst_snd_base :
            Deriv (eqF (ap1 Fst (ap2 pi specT (ap2 pi (ap1 baseFun specT) O))) specT)
          fst_snd_base = axFst specT (ap2 pi (ap1 baseFun specT) O)

          snd_cov :
            Deriv (eqF (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT O))
                        (ap2 pi specT (ap2 pi (ap1 baseFun specT) O)))
          snd_cov = ruleTrans (cong1 Snd base_eq) snd_base

          fst_snd_cov :
            Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT O))) specT)
          fst_snd_cov = ruleTrans (cong1 Fst snd_cov) fst_snd_base
      in fst_snd_cov

    ------------------------------------------------------------------
    -- Step: under IH (Fst (Snd prev) = specT), prove for  s var0 .
    --
    --   cov_spec ... specT (s var0) = state_step_spec step prev
    --   Fst (Snd (state_step_spec step prev)) = Fst (Snd prev)   [state_step_spec_specPreserve]
    --   = specT by IH.

    stepImp :
      Deriv (imp Pform
              (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))))
                    specT))
    stepImp =
      let prev : Term
          prev = ap2 (cov_spec baseFun stepFun) specT (var zero)

          -- cov_spec ... specT (s var0) = state_step_spec step prev.
          step_eq :
            Deriv (eqF (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))
                        (ap1 (state_step_spec stepFun) prev))
          step_eq = cov_spec_step_univ baseFun stepFun specT (var zero)

          -- Snd lifted.
          snd_step :
            Deriv (eqF (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero))))
                        (ap1 Snd (ap1 (state_step_spec stepFun) prev)))
          snd_step = cong1 Snd step_eq

          -- Fst (Snd ...) lifted.
          fst_snd_step :
            Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))))
                        (ap1 Fst (ap1 Snd (ap1 (state_step_spec stepFun) prev))))
          fst_snd_step = cong1 Fst snd_step

          -- state_step_spec_specPreserve: Fst (Snd (state_step_spec step prev)) = Fst (Snd prev).
          preserve :
            Deriv (eqF (ap1 Fst (ap1 Snd (ap1 (state_step_spec stepFun) prev)))
                        (ap1 Fst (ap1 Snd prev)))
          preserve = state_step_spec_specPreserve stepFun prev

          -- Chain to: Fst (Snd (cov_spec ... (s var0))) = Fst (Snd prev).
          fst_snd_step_to_prev :
            Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))))
                        (ap1 Fst (ap1 Snd prev)))
          fst_snd_step_to_prev = ruleTrans fst_snd_step preserve

          -- Under IH (Pform = eqF (Fst (Snd prev)) specT),  prependEqLeft :
          --   imp (eqF (Fst (Snd prev)) specT) (eqF LHS specT).
          prepend :
            Deriv (imp (eqF (ap1 Fst (ap1 Snd prev)) specT)
                        (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))))
                              specT))
          prepend = prependEqLeft
                      (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) specT (ap1 s (var zero)))))
                      (ap1 Fst (ap1 Snd prev))
                      specT
                      fst_snd_step_to_prev
      in prepend

------------------------------------------------------------------------
-- fstSnd_cov_spec_eq : universal-in-Term form.
--
-- For any spec, K : Term:
--   Deriv (eqF (Fst (Snd (cov_spec base step spec K))) spec)
--
-- Proof: c-renaming.  Pick c fresh in K and spec.  Rename var 1 := var c,
-- then ruleInst 0 K, then ruleInst c spec, with bridges via substT_above_max.

private
  freshKS : Term -> Term -> Nat
  freshKS K spec = suc (suc (maxN (maxVarT K) (maxVarT spec)))

  freshKS_above_K : (K spec : Term) -> NatLe (maxVarT K) (freshKS K spec)
  freshKS_above_K K spec =
    le-suc-right (le-suc-right (maxN-le-left (maxVarT K) (maxVarT spec)))

fstSnd_cov_spec_eq :
  (baseFun : Fun1) (stepFun : Fun2) (spec K : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec K))) spec)
fstSnd_cov_spec_eq baseFun stepFun spec K =
  let c : Nat
      c = freshKS K spec

      -- step1: rename var 1 to var c.
      step1 :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) (var c) (var zero))))
                    (var c))
      step1 = ruleInst 1 (var c) (fstSnd_cov_spec_eq_v01 baseFun stepFun)

      -- step2: ruleInst 0 K.
      step2 :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) (var c) K))) (var c))
      step2 = ruleInst 0 K step1

      -- step3: ruleInst c spec.
      step3_raw :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun)
                                            (substT c spec (var c))
                                            (substT c spec K))))
                    (substT c spec (var c)))
      step3_raw = ruleInst c spec step2

      bridge_K : Eq (substT c spec K) K
      bridge_K = substT_above_max c K spec (freshKS_above_K K spec)

      bridge_vc : Eq (substT c spec (var c)) spec
      bridge_vc = eqCong (\ b -> boolCase b spec (var c)) (natEq-refl c)

      -- Bridge K substitution.
      step3 :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun)
                                            (substT c spec (var c)) K)))
                    (substT c spec (var c)))
      step3 = eqSubst (\ x -> Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun)
                                                                  (substT c spec (var c)) x)))
                                            (substT c spec (var c))))
                       bridge_K step3_raw

      -- Bridge var c.
      step4 :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec K))) spec)
      step4 = eqSubst (\ x -> Deriv (eqF (ap1 Fst (ap1 Snd (ap2 (cov_spec baseFun stepFun) x K))) x))
                       bridge_vc step3
  in step4
