{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SbRuntime
--
-- Smallest concrete case of schematic Theorem 12: build  Df_F1_I : Fun1
-- such that  thmT (Df_F1_I x)  BRA-equals the runtime substitution of
--  cor x  for var 0 in the closed-axiom code  reify (outAxI (var 0)) .
--
-- The bridge is supplied entirely by  thmTDispRuleInst_param  (already
-- in  BRA.Thm.ThmT ), which in the new (2026-05-02) encoding takes a
-- Term substituent  tT  with NO shape obligation on the proof index.
--
-- Equation derived (final RHS of  Df_F1_I_runtime  below):
--
--   ap1 thmT (ap1 Df_F1_I x)
--     =  ap2 subT (ap2 Pair (reify (code (var 0))) (ap1 cor x))
--                 (reify (outAxI (var 0)))
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
-- NEW LAYOUT (refactor 2026-05-02): proof-index at OUTER Snd, closed
-- (varCode, substituent) at inner Fst.
--
--   ap1 Df_F1_I x = ap2 Pair T1 (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3)
--
-- The  ap1 cor x  is the runtime substituent (= num(x) in Guard's
-- notation).  This is the format thmTDispRuleInst_param expects.
--
-- Built using  Comp2 Pair  for assembly,  KT _  for closed constants,
-- and  cor  itself at the substituent slot.

Df_F1_I : Fun1
Df_F1_I = Comp2 Pair
            (KT T1)
            (Comp2 Pair
              (Comp2 Pair (KT T2) cor)
              (KT T3))

------------------------------------------------------------------------
-- Df_F1_I_unfold :
--   ap1 Df_F1_I x = ap2 Pair T1 (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3)
--
-- by axComp2 + ktRed unfolding.

Df_F1_I_unfold : (x : Term) ->
  Deriv (atomic (eqn (ap1 Df_F1_I x)
                     (ap2 Pair T1 (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3))))
Df_F1_I_unfold x =
  let
    argsF1 : Fun1
    argsF1 = Comp2 Pair (KT T2) cor

    inner2 : Fun1
    inner2 = Comp2 Pair argsF1 (KT T3)

    -- Step 1: axComp2 at the outermost Comp2.
    s1 : Deriv (atomic (eqn (ap1 Df_F1_I x)
                            (ap2 Pair (ap1 (KT T1) x) (ap1 inner2 x))))
    s1 = axComp2 Pair (KT T1) inner2 x

    -- Step 2: ktRed for KT T1.
    s2_kt1 : Deriv (atomic (eqn (ap1 (KT T1) x) T1))
    s2_kt1 = ktRed (natCode tagRuleInst) x

    -- Step 3: axComp2 at the next-outer Comp2 (inner2).
    s3 : Deriv (atomic (eqn (ap1 inner2 x)
                            (ap2 Pair (ap1 argsF1 x) (ap1 (KT T3) x))))
    s3 = axComp2 Pair argsF1 (KT T3) x

    -- Step 4: ktRed for KT T3.
    s4_kt3 : Deriv (atomic (eqn (ap1 (KT T3) x) T3))
    s4_kt3 = ktRed (encAxI (var zero)) x

    -- Step 5: axComp2 at the argsF1 Comp2.
    s5 : Deriv (atomic (eqn (ap1 argsF1 x)
                            (ap2 Pair (ap1 (KT T2) x) (ap1 cor x))))
    s5 = axComp2 Pair (KT T2) cor x

    -- Step 6: ktRed for KT T2.
    s6_kt2 : Deriv (atomic (eqn (ap1 (KT T2) x) T2))
    s6_kt2 = ktRed (code (var zero)) x

    -- Compose: simplify argsF1.
    argsF1_simp : Deriv (atomic (eqn (ap1 argsF1 x)
                                      (ap2 Pair T2 (ap1 cor x))))
    argsF1_simp = ruleTrans s5 (congL Pair (ap1 cor x) s6_kt2)

    -- inner2 simplification.
    inner2_step1 : Deriv (atomic (eqn (ap1 inner2 x)
                                       (ap2 Pair (ap1 argsF1 x) T3)))
    inner2_step1 = ruleTrans s3 (congR Pair (ap1 argsF1 x) s4_kt3)

    inner2_simp : Deriv (atomic (eqn (ap1 inner2 x)
                                      (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3)))
    inner2_simp = ruleTrans inner2_step1 (congL Pair T3 argsF1_simp)

    -- Outermost: simplify (KT T1) and pair with inner2.
    s_kt1 : Deriv (atomic (eqn (ap1 Df_F1_I x)
                                (ap2 Pair T1 (ap1 inner2 x))))
    s_kt1 = ruleTrans s1 (congL Pair (ap1 inner2 x) s2_kt1)

    s_final : Deriv (atomic (eqn (ap2 Pair T1 (ap1 inner2 x))
                                  (ap2 Pair T1
                                    (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3))))
    s_final = congR Pair T1 inner2_simp
  in ruleTrans s_kt1 s_final

------------------------------------------------------------------------
-- Df_F1_I_dispatch : the runtime bridge.
--
-- Apply thmTDispRuleInst_param at the runtime substituent  ap1 cor x ,
-- the inner proof code  T3  (reify of encAxI (var 0)), and variable
-- index 0.  In the new encoding, no xShape needed.
--
--   thmT (Pair T1 (Pair (Pair T2 (cor x)) T3))
--     = subT (Pair T2 (cor x)) (thmT T3) .

Df_F1_I_dispatch : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair T1 (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3)))
    (ap2 subT (ap2 Pair T2 (ap1 cor x)) (ap1 thmT T3))))
Df_F1_I_dispatch x =
  let
    -- Inner-check witness for verifying body_ruleInst:
    -- thmT T3 = reify (outAxI (var zero)) is Pair-shaped definitionally,
    -- since outAxI = codeFormula (atomic ...) = nd _ _.
    fp : Term
    fp = reify (code (ap1 I (var zero)))
    sp : Term
    sp = reify (code (var zero))
    eThm : Deriv (atomic (eqn (ap1 thmT T3) (reify (outAxI (var zero)))))
    eThm = thmTDispAxI (var zero)
    eRefl : Deriv (atomic (eqn (reify (outAxI (var zero))) (ap2 Pair fp sp)))
    eRefl = axRefl (ap2 Pair fp sp)
    dh : Deriv (atomic (eqn (ap1 thmT T3) (ap2 Pair fp sp)))
    dh = ruleTrans eThm eRefl
  in thmTDispRuleInst_param zero (ap1 cor x) T3 fp sp dh

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

Df_F1_I_runtime : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap1 Df_F1_I x))
    (ap2 subT (ap2 Pair T2 (ap1 cor x)) (reify (outAxI (var zero))))))
Df_F1_I_runtime x =
  let
    runtimeTree : Term
    runtimeTree = ap2 Pair T1 (ap2 Pair (ap2 Pair T2 (ap1 cor x)) T3)

    -- Step 1: rewrite  ap1 thmT (ap1 Df_F1_I x)  to  ap1 thmT runtimeTree.
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
