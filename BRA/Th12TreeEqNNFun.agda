{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12TreeEqNNFun -- closed Fun2 for the (Pair, Pair) NN case of
-- Theorem 12 for TreeEq.
--
-- Phase 2 of the schematic Theorem 12 for TreeEq programme (the
-- ruleIndBT2 path).  See BRA/NEXT-SESSION-TREEEQ-CONT.md.
--
-- Provides:
--   * D_TreeEq_NN_fun : Fun2  -- closed.
--   * D_TreeEq_NN_closed       -- substF2 commutativity (trivially refl).
--   * D_TreeEq_NN_reduce_NN    -- BRA-eq reduction at (Pair v1 v2)(Pair w1 w2).
--
-- The chain Df emitted at NN input is the basic axTreeEqNN-encoded
-- payload:  Pair tagCode_axTreeEqNN (Pair v1 (Pair v2 (Pair w1 w2))) .
-- The basePP_imp proof in a follow-up file bridges this to
-- codeFTeq2Asym TreeEq (Pair v1 v2)(Pair w1 w2) using diagonal cross-IHs
-- + ruleTrans + cor reductions.
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.Th12TreeEqNNFun where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxTreeEqNN)
open import BRA.Thm.ThmT using (tagCode_axTreeEqNN)

------------------------------------------------------------------------
-- Closed Fun2 emitting axTreeEqNN-encoded payload at NN input.
--
-- At runtime input  (orig = Pair v1 v2, recs = Pair w1 w2) :
--   ap2 D_TreeEq_NN_fun orig recs
--     = Pair tagCode_axTreeEqNN (Pair v1 (Pair v2 recs))    [BRA-eq]
--     = Pair tagCode_axTreeEqNN (Pair v1 (Pair v2 (Pair w1 w2))) .
--
-- Construction:
--   inner_payload = Fan (Lift Fst)                       -- v1
--                       (Fan (Lift Snd) (Post Snd Pair)
--                            Pair)                        -- (Pair v2 recs)
--                       Pair                              -- assembles Pair v1 _
--   D_TreeEq_NN_fun = Fan (Lift (KT tagCode_axTreeEqNN))  -- emits the tag
--                          inner_payload                    -- emits the payload
--                          Pair
--
-- The recs slot stays as recs (not unpacked into Pair w1 w2) because
-- the input arrives as Pair w1 w2 already and downstream consumers
-- match on the Pair shape directly.

inner_payload_NN : Fun2
inner_payload_NN =
  Fan (Lift Fst)
      (Fan (Lift Snd) (Post Snd Pair) Pair)
      Pair

D_TreeEq_NN_fun : Fun2
D_TreeEq_NN_fun =
  Fan (Lift (KT tagCode_axTreeEqNN))
      inner_payload_NN
      Pair

------------------------------------------------------------------------
-- Closure: D_TreeEq_NN_fun is a closed Fun2 (no free vars), so substF2
-- on any (x, r) returns it unchanged.

D_TreeEq_NN_closed : (x : Nat) (r : Term) ->
  Eq (substF2 x r D_TreeEq_NN_fun) D_TreeEq_NN_fun
D_TreeEq_NN_closed x r = refl

------------------------------------------------------------------------
-- Reduction at NN input.
--
-- ap2 D_TreeEq_NN_fun (ap2 Pair v1 v2) (ap2 Pair w1 w2)
--   =BRA Pair tagCode_axTreeEqNN (Pair v1 (Pair v2 (Pair w1 w2))) .

D_TreeEq_NN_reduce : (v1 v2 w1 w2 : Term) ->
  Deriv (atomic (eqn
    (ap2 D_TreeEq_NN_fun (ap2 Pair v1 v2) (ap2 Pair w1 w2))
    (ap2 Pair tagCode_axTreeEqNN
              (ap2 Pair v1
                        (ap2 Pair v2 (ap2 Pair w1 w2))))))
D_TreeEq_NN_reduce v1 v2 w1 w2 =
  let
    orig : Term
    orig = ap2 Pair v1 v2

    recs : Term
    recs = ap2 Pair w1 w2

    -- Outer Fan: ap2 D_TreeEq_NN_fun orig recs
    --   = Pair (ap2 (Lift (KT tagCode_axTreeEqNN)) orig recs)
    --          (ap2 inner_payload_NN orig recs).
    s_fan : Deriv (atomic (eqn
              (ap2 D_TreeEq_NN_fun orig recs)
              (ap2 Pair (ap2 (Lift (KT tagCode_axTreeEqNN)) orig recs)
                        (ap2 inner_payload_NN orig recs))))
    s_fan = axFan (Lift (KT tagCode_axTreeEqNN)) inner_payload_NN Pair orig recs

    -- (Lift (KT tagCode_axTreeEqNN)) orig recs = tagCode_axTreeEqNN.
    s_tag_lift : Deriv (atomic (eqn
              (ap2 (Lift (KT tagCode_axTreeEqNN)) orig recs)
              (ap1 (KT tagCode_axTreeEqNN) orig)))
    s_tag_lift = axLift (KT tagCode_axTreeEqNN) orig recs

    s_tag_kt : Deriv (atomic (eqn
              (ap1 (KT tagCode_axTreeEqNN) orig)
              tagCode_axTreeEqNN))
    s_tag_kt = axKT (natCode tagAxTreeEqNN) orig

    s_tag : Deriv (atomic (eqn
              (ap2 (Lift (KT tagCode_axTreeEqNN)) orig recs)
              tagCode_axTreeEqNN))
    s_tag = ruleTrans s_tag_lift s_tag_kt

    -- inner_payload_NN orig recs = Pair v1 (Pair v2 recs).
    s_inner_fan : Deriv (atomic (eqn
              (ap2 inner_payload_NN orig recs)
              (ap2 Pair (ap2 (Lift Fst) orig recs)
                        (ap2 (Fan (Lift Snd) (Post Snd Pair) Pair) orig recs))))
    s_inner_fan = axFan (Lift Fst)
                       (Fan (Lift Snd) (Post Snd Pair) Pair)
                       Pair orig recs

    -- (Lift Fst) orig recs = ap1 Fst orig = Fst (Pair v1 v2) = v1.
    s_v1 : Deriv (atomic (eqn (ap2 (Lift Fst) orig recs) v1))
    s_v1 = ruleTrans (axLift Fst orig recs) (axFst v1 v2)

    -- (Fan (Lift Snd) (Post Snd Pair) Pair) orig recs = Pair v2 recs.
    s_inner2_fan : Deriv (atomic (eqn
              (ap2 (Fan (Lift Snd) (Post Snd Pair) Pair) orig recs)
              (ap2 Pair (ap2 (Lift Snd) orig recs)
                        (ap2 (Post Snd Pair) orig recs))))
    s_inner2_fan = axFan (Lift Snd) (Post Snd Pair) Pair orig recs

    s_v2 : Deriv (atomic (eqn (ap2 (Lift Snd) orig recs) v2))
    s_v2 = ruleTrans (axLift Snd orig recs) (axSnd v1 v2)

    -- (Post Snd Pair) orig recs = ap1 Snd (ap2 Pair orig recs) = Snd (Pair orig recs) = recs.
    s_recs : Deriv (atomic (eqn (ap2 (Post Snd Pair) orig recs) recs))
    s_recs = ruleTrans (axPost Snd Pair orig recs) (axSnd orig recs)

    -- Combine: Pair v2 recs.
    s_inner2 : Deriv (atomic (eqn
              (ap2 (Fan (Lift Snd) (Post Snd Pair) Pair) orig recs)
              (ap2 Pair v2 recs)))
    s_inner2 = ruleTrans s_inner2_fan
                  (ruleTrans (congL Pair (ap2 (Post Snd Pair) orig recs) s_v2)
                             (congR Pair v2 s_recs))

    -- Combine: Pair v1 (Pair v2 recs).
    s_inner : Deriv (atomic (eqn
              (ap2 inner_payload_NN orig recs)
              (ap2 Pair v1 (ap2 Pair v2 recs))))
    s_inner = ruleTrans s_inner_fan
                  (ruleTrans (congL Pair (ap2 (Fan (Lift Snd) (Post Snd Pair) Pair) orig recs) s_v1)
                             (congR Pair v1 s_inner2))

    -- Final: Pair tagCode_axTreeEqNN (Pair v1 (Pair v2 recs)).
    s_final : Deriv (atomic (eqn
              (ap2 D_TreeEq_NN_fun orig recs)
              (ap2 Pair tagCode_axTreeEqNN (ap2 Pair v1 (ap2 Pair v2 recs)))))
    s_final = ruleTrans s_fan
                (ruleTrans (congL Pair (ap2 inner_payload_NN orig recs) s_tag)
                           (congR Pair tagCode_axTreeEqNN s_inner))
  in s_final
