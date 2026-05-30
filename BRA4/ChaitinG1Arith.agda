{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ChaitinG1Arith -- universal arithmetic preliminaries used by the
-- Chaitin-Goedel I discharge:
--
--   * sub_le_arg1     : leq (sub a b) a
--   * subSuccBridge   : under (leq (s y) k), s (sub k (s y)) = sub k y
--   * leqDecrease     : under (leq (s y) k), leq y k             (= T80)
--   * subBoundsAux    : under (leq (s y) k), leq (s (sub k (s y))) k.
--
-- All proved at fixed (var 0, var 1) and specialised via ruleInst2.

module BRA4.ChaitinG1Arith where

open import BRA4.Base

open import BRA3.Church          using ( predecessor ; T_sub_S_v01 ; sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchT73       using ( T73 )
open import BRA3.ChurchT80       using ( T80 )
open import BRA3.ChurchT87       using ( T87 )
open import BRA3.ChurchT84       using ( T84 )
open import BRA3.ChurchSubSucc   using ( T_sub_O ; T57sub )
open import BRA3.ChurchPredMono  using ( predLeqSelf )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.Contrapositive  using ( compI ; liftP )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )

------------------------------------------------------------------------
-- sub_le_arg1 -- sub a b <= a.

sub_le_arg1_univ : Deriv (leq (ap2 sub (var zero) (var (suc zero))) (var zero))
sub_le_arg1_univ = ruleIndNat (suc zero) {P = Pform} baseCase stepImp
  where
    v0 : Term
    v0 = var zero
    v1 : Term
    v1 = var (suc zero)

    Pform : Formula
    Pform = leq (ap2 sub v0 v1) v0

    baseCase : Deriv (leq (ap2 sub v0 O) v0)
    baseCase =
      let e_sub : Deriv (eqF (ap2 sub v0 O) v0)
          e_sub = T_sub_O v0
          e_subsub : Deriv (eqF (ap2 sub (ap2 sub v0 O) v0)
                                (ap2 sub v0 v0))
          e_subsub = congL sub v0 e_sub
          e_self : Deriv (eqF (ap2 sub v0 v0) O)
          e_self = sub_self v0
      in ruleTrans e_subsub e_self

    stepImp : Deriv (imp Pform (substF (suc zero) (ap1 s v1) Pform))
    stepImp =
      let sv1 : Term
          sv1 = ap1 s v1

          X : Term
          X = ap2 sub v0 v1

          e_subS : Deriv (eqF (ap2 sub v0 sv1) (ap1 predecessor X))
          e_subS = T_sub_S_v01

          leq_pred_X : Deriv (leq (ap1 predecessor X) X)
          leq_pred_X = ruleInst zero X predLeqSelf

          T84_fresh :
            Deriv (imp (leq (var 5) (var 6))
                       (imp (leq (var 6) (var 7)) (leq (var 5) (var 7))))
          T84_fresh =
            ruleInst 2 (var 7)
              (ruleInst (suc zero) (var 6)
                (ruleInst zero (var 5) T84))

          T84_inst :
            Deriv (imp (leq (ap1 predecessor X) X)
                       (imp (leq X v0) (leq (ap1 predecessor X) v0)))
          T84_inst =
            ruleInst 7 v0
              (ruleInst 6 X
                (ruleInst 5 (ap1 predecessor X) T84_fresh))

          chain_pred : Deriv (imp (leq X v0) (leq (ap1 predecessor X) v0))
          chain_pred = mp T84_inst leq_pred_X

          rewriteLeq :
            Deriv (imp (leq (ap1 predecessor X) v0)
                       (leq (ap2 sub v0 sv1) v0))
          rewriteLeq =
            prependEqLeft
              (ap2 sub (ap2 sub v0 sv1) v0)
              (ap2 sub (ap1 predecessor X) v0)
              O
              (congL sub v0 e_subS)
      in compI chain_pred rewriteLeq

sub_le_arg1 : (a b : Term) -> Deriv (leq (ap2 sub a b) a)
sub_le_arg1 a b =
  ruleInst2 zero a (suc zero) b refl sub_le_arg1_univ

------------------------------------------------------------------------
-- subSuccBridge -- via T87 + T57sub.

subSuccBridge_univ :
  Deriv (imp (leq (ap1 s (var zero)) (var (suc zero)))
             (eqF (ap1 s (ap2 sub (var (suc zero)) (ap1 s (var zero))))
                  (ap2 sub (var (suc zero)) (var zero))))
subSuccBridge_univ =
  let v0 : Term
      v0 = var zero
      v1 : Term
      v1 = var (suc zero)
      sv0 : Term
      sv0 = ap1 s v0

      T87_inst :
        Deriv (imp (leq sv0 v1)
                   (eqF (ap1 s (ap2 sub v1 sv0))
                        (ap2 sub (ap1 s v1) sv0)))
      T87_inst = ruleInst2 zero sv0 (suc zero) v1 refl T87

      T57sub_inst :
        Deriv (eqF (ap2 sub (ap1 s v1) sv0) (ap2 sub v1 v0))
      T57sub_inst = ruleInst2 zero v1 (suc zero) v0 refl T57sub

      bridgeStep :
        Deriv (imp (eqF (ap1 s (ap2 sub v1 sv0)) (ap2 sub (ap1 s v1) sv0))
                   (eqF (ap1 s (ap2 sub v1 sv0)) (ap2 sub v1 v0)))
      bridgeStep =
        appendEqRight
          (ap1 s (ap2 sub v1 sv0))
          (ap2 sub (ap1 s v1) sv0)
          (ap2 sub v1 v0)
          T57sub_inst
  in compI T87_inst bridgeStep

subSuccBridge :
  (y k : Term) ->
  Deriv (imp (leq (ap1 s y) k)
             (eqF (ap1 s (ap2 sub k (ap1 s y)))
                  (ap2 sub k y)))
subSuccBridge y k =
  ruleInst2 zero y (suc zero) k refl subSuccBridge_univ

------------------------------------------------------------------------
-- leqDecrease  via T80.

leqDecrease : (y k : Term) -> Deriv (imp (leq (ap1 s y) k) (leq y k))
leqDecrease y k =
  ruleInst2 zero y (suc zero) k refl T80

------------------------------------------------------------------------
-- Local imp-form symmetry of equality (BRA3 doesn't expose one).

eqSymImpL : (a b : Term) -> Deriv (imp (eqF a b) (eqF b a))
eqSymImpL a b =
  let ax : Deriv (imp (eqF a b) (imp (eqF a a) (eqF b a)))
      ax = ax_eqTrans a b a
      lifted : Deriv (imp (eqF a b) (eqF a a))
      lifted = liftP (eqF a b) (axRefl a)
      step1 : Deriv (imp (imp (eqF a b) (imp (eqF a a) (eqF b a)))
                         (imp (imp (eqF a b) (eqF a a))
                              (imp (eqF a b) (eqF b a))))
      step1 = axS (eqF a b) (eqF a a) (eqF b a)
  in mp (mp step1 ax) lifted

------------------------------------------------------------------------
-- subBoundsAux -- via subSuccBridge + sub_le_arg1.

subBoundsAux :
  (y k : Term) ->
  Deriv (imp (leq (ap1 s y) k) (leq (ap1 s (ap2 sub k (ap1 s y))) k))
subBoundsAux y k =
  let sy : Term
      sy = ap1 s y
      A : Term
      A = ap1 s (ap2 sub k sy)
      B : Term
      B = ap2 sub k y

      bridge : Deriv (imp (leq sy k) (eqF A B))
      bridge = subSuccBridge y k

      leqB : Deriv (leq B k)
      leqB = sub_le_arg1 k y

      leqB_imp : Deriv (imp (leq sy k) (leq B k))
      leqB_imp = liftP (leq sy k) leqB

      -- Under hyp, sub A k = sub B k.
      cong_under : Deriv (imp (leq sy k)
                              (eqF (ap2 sub A k) (ap2 sub B k)))
      cong_under = compI bridge (ax_eqCongL sub A B k)

      -- NEUTRAL bridge:  imp (A=B) (imp (B=O) (A=O))  via eqSymImpL + ax_eqTrans.
      neutralBridge :
        Deriv (imp (eqF (ap2 sub A k) (ap2 sub B k))
                   (imp (eqF (ap2 sub B k) O) (eqF (ap2 sub A k) O)))
      neutralBridge =
        compI (eqSymImpL (ap2 sub A k) (ap2 sub B k))
              (ax_eqTrans (ap2 sub B k) (ap2 sub A k) O)

      eqTr : Deriv (imp (leq sy k)
                       (imp (eqF (ap2 sub B k) O)
                            (eqF (ap2 sub A k) O)))
      eqTr = compI cong_under neutralBridge

      axS_inst :
        Deriv (imp (imp (leq sy k)
                        (imp (eqF (ap2 sub B k) O)
                             (eqF (ap2 sub A k) O)))
                   (imp (imp (leq sy k) (eqF (ap2 sub B k) O))
                        (imp (leq sy k) (eqF (ap2 sub A k) O))))
      axS_inst = axS (leq sy k) (eqF (ap2 sub B k) O)
                     (eqF (ap2 sub A k) O)

      chain : Deriv (imp (leq sy k) (eqF (ap2 sub A k) O))
      chain = mp (mp axS_inst eqTr) leqB_imp
  in chain
