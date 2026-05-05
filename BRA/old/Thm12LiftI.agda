{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12LiftI
--
-- Pre-flight: Theorem 12 for the COMPOSITE  Lift I  at parametric
-- variables  v1, v2 .  This is the simplest "axiom-RHS-mentions-
-- sub-functor" case (the Lift defining axiom is
--   axLift f a b : (Lift f) a b = f a ).
--
-- The construction uses thm12_I_param as the IH (the Theorem-12
-- witness for  I  at  var zero ), via  ruleInst .  It chains the
-- IH with the encoded form of  axLift  via thmTDispRuleTrans_param.
--
-- The point of the pre-flight: confirm or refute the working
-- hypothesis (THM12-ASYM-FEASIBILITY.md sec. 8) that the seven
-- "composition" cases need new infrastructure (a parametric mp
-- dispatch).  If this file typechecks using only existing
-- dispatchers, the hypothesis is wrong and the remaining cases
-- are all of comparable complexity to this one.

module BRA.Thm12LiftI where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm12AsymParametric using (thm12_I_param)
open import BRA.Thm.ThmT using
  ( thmT ; thClosed
  ; tagCode_axI ; tagCode_axLift ; tagCode_ruleTrans
  ; thmTDispAxLift_param ; thmTDispRuleTrans_param )

------------------------------------------------------------------------
-- thm12_Lift_I_param: Theorem 12 for  Lift I  at variables  v1, v2 .

module LiftICase (v1 v2 : Nat) where

  v1T : Term
  v1T = var v1

  v2T : Term
  v2T = var v2

  ----------------------------------------------------------------------
  -- IH at v1: instantiate thm12_I_param's Deriv with var 0 := v1T,
  -- using ruleInst.  Need thClosed to coerce  substF1 0 v1T thmT  to
  --  thmT  (otherwise Agda may not see them as definitionally equal).

  -- Df_I_at_zero is fst thm12_I_param = ap2 Pair tagCode_axI (cor (var zero)).
  -- After substitution, becomes ap2 Pair tagCode_axI (cor v1T).
  Df_I_at_v1 : Term
  Df_I_at_v1 = ap2 Pair tagCode_axI (ap1 cor v1T)

  -- IH at v1, before any thmT-coercion.  Type produced by ruleInst.
  ih_raw : Deriv (substF zero v1T
            (atomic (eqn (ap1 thmT (fst thm12_I_param))
                          (codeFTeq1Asym I (var zero)))))
  ih_raw = ruleInst zero v1T (snd thm12_I_param)

  -- Target shape after substitution.  We claim Agda will reduce
  -- substF1 0 v1T thmT  to  thmT  definitionally (since  thmT  =
  -- Rec O stepProto  with closed  stepProto ).  If not, we use
  -- thClosed via eqSubst.

  -- Codomain Term we want IH at v1 to land in (= asym encoding of I).
  ih_target_RHS : Term
  ih_target_RHS = ap2 Pair (ap2 Pair (reify tagAp1)
                                      (ap2 Pair (reify (codeF1 I)) (ap1 cor v1T)))
                            (ap1 cor (ap1 I v1T))
  -- This is exactly  codeFTeq1Asym I v1T .

  -- Defensive: coerce ih_raw to the form (ap1 thmT Df_I_at_v1) = ih_target_RHS,
  -- using thClosed if needed.

  ih_at_v1 : Deriv (atomic (eqn (ap1 thmT Df_I_at_v1) ih_target_RHS))
  ih_at_v1 =
    let th_eq : Eq (substF1 zero v1T thmT) thmT
        th_eq = thClosed zero v1T

        coerce :
          Eq (atomic (eqn (ap1 (substF1 zero v1T thmT) Df_I_at_v1) ih_target_RHS))
             (atomic (eqn (ap1 thmT Df_I_at_v1) ih_target_RHS))
        coerce = eqCong (\ f -> atomic (eqn (ap1 f Df_I_at_v1) ih_target_RHS)) th_eq
    in eqSubst (\ F -> Deriv F) coerce ih_raw

  ----------------------------------------------------------------------
  -- Sub-derivation for Lift's defining axiom encoded at f=I, aT=cor v1, bT=cor v2.

  Df_lift_ax : Term
  Df_lift_ax = ap2 Pair tagCode_axLift
                   (ap2 Pair (reify (codeF1 I))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  -- mid_term: encoded RHS of  axLift I (cor v1) (cor v2)  =  I (cor v1) ;
  -- it equals codeFTeq1Asym I v1T's LHS subterm.
  mid_term : Term
  mid_term = ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 I)) (ap1 cor v1T))

  -- LHS subterm of disp_lift's RHS: encoded  ap2 (Lift I) (cor v1) (cor v2).
  lift_lhs : Term
  lift_lhs = ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Lift I))))
                                       (reify (codeF1 I)))
                             (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  disp_lift : Deriv (atomic (eqn (ap1 thmT Df_lift_ax)
                                  (ap2 Pair lift_lhs mid_term)))
  disp_lift = thmTDispAxLift_param I (ap1 cor v1T) (ap1 cor v2T)

  ----------------------------------------------------------------------
  -- Head-shape proof on Df_lift_ax for thmTDispRuleTrans_param.
  --   ap1 Fst Df_lift_ax  =  tagCode_axLift  (by axFst)
  --   tagCode_axLift definitionally =  ap2 Pair O (rest)
  -- so we extract  x' = O ,  y1' = (rest tree of natCode tagAxLift).

  shape_y1' : Term
  shape_y1' = reify (natCode (suc (suc (suc (suc (suc (suc zero))))))) -- = natCode 6 = rest

  shape_proof : Deriv (atomic (eqn (ap1 Fst Df_lift_ax)
                                    (ap2 Pair O shape_y1')))
  shape_proof = axFst tagCode_axLift
                  (ap2 Pair (reify (codeF1 I))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  ----------------------------------------------------------------------
  -- Compose disp_lift with ih_at_v1 via thmTDispRuleTrans_param.

  Df_term : Term
  Df_term = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_lift_ax Df_I_at_v1)

  -- ih_target_RHS = ap2 Pair mid_term (ap1 cor (ap1 I v1T)).
  -- We feed:
  --   y1T = Df_lift_ax       u1 = lift_lhs        u2 = mid_term
  --   y2T = Df_I_at_v1       u3 = mid_term        u4 = ap1 cor (ap1 I v1T)
  -- thmTDispRuleTrans_param outputs Pair u1 u4 = Pair lift_lhs (cor (I v1)).

  cor_I_v1 : Term
  cor_I_v1 = ap1 cor (ap1 I v1T)

  merged : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (ap2 Pair lift_lhs cor_I_v1)))
  merged = thmTDispRuleTrans_param Df_lift_ax Df_I_at_v1
            lift_lhs mid_term mid_term cor_I_v1
            shape_y1' O shape_proof
            disp_lift ih_at_v1

  ----------------------------------------------------------------------
  -- Bridge: cor (I v1) -> cor (Lift I v1 v2) via cong1 cor + axI/axLift.

  -- axLift I v1 v2 : ap2 (Lift I) v1 v2 = ap1 I v1 .
  -- ruleSym       : ap1 I v1 = ap2 (Lift I) v1 v2 .
  -- cong1 cor     : cor (ap1 I v1) = cor (ap2 (Lift I) v1 v2) .

  bridge_RHS : Deriv (atomic (eqn cor_I_v1
                                   (ap1 cor (ap2 (Lift I) v1T v2T))))
  bridge_RHS = cong1 cor (ruleSym (axLift I v1T v2T))

  ----------------------------------------------------------------------
  -- Final assembly.

  bridge : Deriv (atomic (eqn (ap2 Pair lift_lhs cor_I_v1)
                               (codeFTeq2Asym (Lift I) v1T v2T)))
  bridge = congR Pair lift_lhs bridge_RHS

  thm12_Lift_I_param :
    Sigma Term (\ Df ->
      Deriv (atomic (eqn (ap1 thmT Df)
                          (codeFTeq2Asym (Lift I) v1T v2T))))
  thm12_Lift_I_param = mkSigma Df_term (ruleTrans merged bridge)
