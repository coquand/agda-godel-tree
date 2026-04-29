{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SbRuntime
--
-- Smallest concrete case of schematic Theorem 12: build  Df_F1_I : Fun1
-- such that  thmT (Df_F1_I x)  BRA-equals the runtime substitution of
--  cor x  for var 0 in the closed-axiom code  reify (outAxI (var 0)) .
--
-- This is the runtime-substitution bridge that the prior session memo
--  feedback_thm12_phase7c_obstruction.md  was missing.  The bridge is
-- supplied entirely by  thmTDispRuleInst_param  (already in
--  BRA.Thm.ThmT ), which takes a Term substituent  tT  (rather than a
-- meta-encoded  code t ).  At  tT := cor x  it gives precisely what
-- Theorem 12 requires:  thmT applied to the runtime tree =  subT
-- applied at the runtime substituent.
--
-- Equation derived (final RHS of  Df_F1_I_runtime  below):
--
--   ap1 thmT (ap1 Df_F1_I x)
--     =  ap2 subT (ap2 Pair (reify (code (var 0))) (ap1 cor x))
--                 (reify (outAxI (var 0)))
--
-- The remaining bridge from this  subT-form  RHS to the "hybrid"
-- expression  codeFTeq1Asym I (var 0)  is a separate lemma --
-- it traces  subT 's primitive recursion on the specific closed
--  reify (outAxI (var 0))  tree, splicing  ap1 cor x  at variable
-- positions.  Deferred to a follow-up.  This file delivers the
-- substantive piece: the runtime bridge actually goes through.
--
-- No postulates, no holes.

module BRA.SbRuntime where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.SubT         using (subT)
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Tag      using (tagAxI ; tagRuleInst)
open import BRA.Thm.Parts.AxI using (encAxI ; outAxI)
open import BRA.Thm.ThmT     using
  ( thmT
  ; thmTDispAxI
  ; thmTDispRuleInst_param
  ; tagCode_ruleInst )

------------------------------------------------------------------------
-- Closed Term constants used by Df_F1_I.
--
--   T1 = tagCode_ruleInst        : "this proof code is a substitution step"
--   T2 = reify (code (var 0))    : the variable to substitute
--   T3 = reify (encAxI (var 0))  : the inner axiom proof code (for axI at var 0)

T1 : Term
T1 = tagCode_ruleInst

T2 : Term
T2 = reify (code (var zero))

T3 : Term
T3 = reify (encAxI (var zero))

------------------------------------------------------------------------
-- Df_F1_I : Fun1
--
-- A Fun1 expression that, at any input x, evaluates to the runtime
-- proof-code Term:
--
--   ap1 Df_F1_I x = ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))
--
-- The  ap1 cor x  is the runtime substituent (= num(x) in Guard's
-- notation).  This is exactly the format thmTDispRuleInst_param expects.
--
-- Built using  Comp2 Pair  for assembly,  KT _  for closed constants,
-- and  cor  itself at the substituent slot.

Df_F1_I : Fun1
Df_F1_I = Comp2 Pair
            (KT T1)
            (Comp2 Pair
              (KT T2)
              (Comp2 Pair
                (KT T3)
                cor))

------------------------------------------------------------------------
-- Df_F1_I_unfold :
--   ap1 Df_F1_I x = ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))
--
-- by four applications of axComp2 + three applications of ktRed.

Df_F1_I_unfold : (x : Term) ->
  Deriv (atomic (eqn (ap1 Df_F1_I x)
                     (ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x))))))
Df_F1_I_unfold x =
  let
    inner3 : Fun1
    inner3 = Comp2 Pair (KT T3) cor

    inner2 : Fun1
    inner2 = Comp2 Pair (KT T2) inner3

    -- Step 1: axComp2 at the outermost Comp2.
    s1 : Deriv (atomic (eqn (ap1 Df_F1_I x)
                            (ap2 Pair (ap1 (KT T1) x) (ap1 inner2 x))))
    s1 = axComp2 Pair (KT T1) inner2 x

    -- Step 2: ktRed for KT T1.
    --   T1 = tagCode_ruleInst = reify (natCode tagRuleInst).
    s2_kt1 : Deriv (atomic (eqn (ap1 (KT T1) x) T1))
    s2_kt1 = ktRed (natCode tagRuleInst) x

    -- Step 3: axComp2 at the next-outer Comp2 (inner2).
    s3 : Deriv (atomic (eqn (ap1 inner2 x)
                            (ap2 Pair (ap1 (KT T2) x) (ap1 inner3 x))))
    s3 = axComp2 Pair (KT T2) inner3 x

    -- Step 4: ktRed for KT T2.
    --   T2 = reify (code (var zero)).
    s4_kt2 : Deriv (atomic (eqn (ap1 (KT T2) x) T2))
    s4_kt2 = ktRed (code (var zero)) x

    -- Step 5: axComp2 at the innermost Comp2 (inner3).
    s5 : Deriv (atomic (eqn (ap1 inner3 x)
                            (ap2 Pair (ap1 (KT T3) x) (ap1 cor x))))
    s5 = axComp2 Pair (KT T3) cor x

    -- Step 6: ktRed for KT T3.
    --   T3 = reify (encAxI (var zero)).
    s6_kt3 : Deriv (atomic (eqn (ap1 (KT T3) x) T3))
    s6_kt3 = ktRed (encAxI (var zero)) x

    -- Compose: at the innermost Comp2, simplify (KT T3) and pair with cor.
    inner3_simp : Deriv (atomic (eqn (ap1 inner3 x) (ap2 Pair T3 (ap1 cor x))))
    inner3_simp = ruleTrans s5 (congL Pair (ap1 cor x) s6_kt3)

    -- At the next-outer Comp2, simplify (KT T2) and pair with inner3.
    inner2_step1 : Deriv (atomic (eqn (ap1 inner2 x)
                                       (ap2 Pair T2 (ap1 inner3 x))))
    inner2_step1 = ruleTrans s3 (congL Pair (ap1 inner3 x) s4_kt2)

    inner2_step2 : Deriv (atomic (eqn (ap2 Pair T2 (ap1 inner3 x))
                                       (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))))
    inner2_step2 = congR Pair T2 inner3_simp

    inner2_simp : Deriv (atomic (eqn (ap1 inner2 x)
                                      (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))))
    inner2_simp = ruleTrans inner2_step1 inner2_step2

    -- Outermost: simplify (KT T1) and pair with inner2.
    s_kt1 : Deriv (atomic (eqn (ap1 Df_F1_I x)
                                (ap2 Pair T1 (ap1 inner2 x))))
    s_kt1 = ruleTrans s1 (congL Pair (ap1 inner2 x) s2_kt1)

    s_final : Deriv (atomic (eqn (ap2 Pair T1 (ap1 inner2 x))
                                  (ap2 Pair T1 (ap2 Pair T2
                                    (ap2 Pair T3 (ap1 cor x))))))
    s_final = congR Pair T1 inner2_simp
  in ruleTrans s_kt1 s_final

------------------------------------------------------------------------
-- xShape for thmTDispRuleInst_param at xT = T3 = reify (encAxI (var zero)).
--
-- T3 = reify (nd (natCode tagAxI) (code (var zero)))
--    = ap2 Pair (reify (natCode tagAxI)) (reify (code (var zero)))
--
-- So  ap1 Fst T3 = reify (natCode tagAxI)  by axFst, and that
-- happens to equal  ap2 Pair O O  (since natCode (suc zero) = nd lf lf,
-- so reify of it is ap2 Pair O O).  We use axFst at the explicit Pair
-- form of T3.

xShape_F1_I : Sigma Term (\ y' -> Sigma Term (\ x' ->
  Deriv (atomic (eqn (ap1 Fst T3) (ap2 Pair x' y')))))
xShape_F1_I =
  mkSigma O (mkSigma O
    (axFst (ap2 Pair O O) (reify (code (var zero)))))

------------------------------------------------------------------------
-- Df_F1_I_dispatch : the runtime bridge.
--
-- Apply thmTDispRuleInst_param at the runtime substituent  ap1 cor x ,
-- the inner proof code  T3  (reify of encAxI (var 0)), and variable
-- index 0.  The result: thmT applied to the runtime tree
--   ap2 Pair tagCode_ruleInst (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))
-- BRA-equals
--   subT (Pair T2 (ap1 cor x)) (thmT T3) .

Df_F1_I_dispatch : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))))
    (ap2 subT (ap2 Pair T2 (ap1 cor x)) (ap1 thmT T3))))
Df_F1_I_dispatch x =
  thmTDispRuleInst_param zero (ap1 cor x) T3 xShape_F1_I

------------------------------------------------------------------------
-- Df_F1_I_axI_thmT :  thmT T3 = reify (outAxI (var zero)) .
--
-- Direct application of thmTDispAxI at the variable term.

Df_F1_I_axI_thmT : Deriv (atomic (eqn (ap1 thmT T3)
                                       (reify (outAxI (var zero)))))
Df_F1_I_axI_thmT = thmTDispAxI (var zero)

------------------------------------------------------------------------
-- Df_F1_I_runtime :  the smallest concrete schematic Theorem 12 case.
--
--   ap1 thmT (ap1 Df_F1_I x)
--     = ap2 subT (ap2 Pair T2 (ap1 cor x)) (reify (outAxI (var zero)))
--
-- LHS: thmT applied to a runtime-built proof code (with  ap1 cor x
-- un-encoded at the substituent slot).
-- RHS: subT applied at the runtime substituent  ap1 cor x  to the
-- closed reified outAxI form.
--
-- The RHS computes (by subT's primitive recursion on the closed
-- second argument) to a BRA term with  ap1 cor x  un-encoded at
-- variable positions of the I-axiom's encoded equation -- i.e., to
--   codeFTeq1Asym I x  (modulo the subT-on-closed-codeP bridge,
--   deferred to a follow-up file).
--
-- This is the FIRST genuine schematic Theorem-12 step in the codebase:
-- a runtime substituent passes through  thmT  via the dispatcher
-- without losing its runtime form.

Df_F1_I_runtime : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap1 Df_F1_I x))
    (ap2 subT (ap2 Pair T2 (ap1 cor x)) (reify (outAxI (var zero))))))
Df_F1_I_runtime x =
  let
    runtimeTree : Term
    runtimeTree = ap2 Pair T1 (ap2 Pair T2 (ap2 Pair T3 (ap1 cor x)))

    -- Step 1: rewrite  ap1 thmT (ap1 Df_F1_I x)  to  ap1 thmT runtimeTree
    -- using Df_F1_I_unfold.
    s1 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_I x))
                             (ap1 thmT runtimeTree)))
    s1 = cong1 thmT (Df_F1_I_unfold x)

    -- Step 2: thmT(runtimeTree) = subT(...) (thmT T3) by dispatch.
    s2 : Deriv (atomic (eqn (ap1 thmT runtimeTree)
                             (ap2 subT (ap2 Pair T2 (ap1 cor x))
                                       (ap1 thmT T3))))
    s2 = Df_F1_I_dispatch x

    -- Step 3: replace ap1 thmT T3 by reify (outAxI (var zero)).
    s3 : Deriv (atomic (eqn (ap2 subT (ap2 Pair T2 (ap1 cor x))
                                       (ap1 thmT T3))
                             (ap2 subT (ap2 Pair T2 (ap1 cor x))
                                       (reify (outAxI (var zero))))))
    s3 = congR subT (ap2 Pair T2 (ap1 cor x)) Df_F1_I_axI_thmT
  in ruleTrans s1 (ruleTrans s2 s3)
