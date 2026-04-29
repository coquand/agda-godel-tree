{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12I -- the first concrete schematic Theorem 12 in the codebase.
--
-- Th12_F1_I :  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_I (var zero)))
--                                  (codeFTeq1Asym I (var zero))))
--
-- This is Guard's Theorem 12 at f := I .  The construction mirrors
-- Guard's three-step recipe exactly:
--
--   (1) Take the BRA-derivation  axI (var 0)  of  I(var 0) = var 0 .
--   (2) Encode it as proof code  encAxI (var 0)  (closed Tree).
--   (3) Apply  sb  with substituent  cor x  for  var 0 .  By  sb 's
--       defining equation (subTDef_term below), the result is the
--       hybrid Term with  cor x  un-encoded at variable positions
--       of the encoded I-axiom -- exactly  codeFTeq1Asym I x .
--
-- The proof structure is short:
--   * Df_F1_I_runtime   (BRA.SbRuntime, prior file): runtime bridge
--                       from  thmT(D x)  to subT-form via thmTDispRuleInst_param.
--   * subTDef_term      (this file): generalizes subTDef from canonical
--                       codeA : Tree to runtime substituent uT : Term .
--                       ~85 lines, mirrors subTDef proof structure.
--   * Th12_F1_I_at_var0 (this file): assembles the chain at  x := var zero .
--
-- No postulates, no holes.

module BRA.Th12I where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.SubT
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Tag      using (tagAxI ; tagRuleInst)
open import BRA.Thm.Parts.AxI using (encAxI ; outAxI)
open import BRA.Thm.ThmT     using
  ( thmT
  ; thmTDispAxI
  ; thmTDispRuleInst_param
  ; tagCode_ruleInst )
open import BRA.Thm14CodeFTeqAsym using (codeFTeq1Asym ; mkAp1T ; mkEqT)
open import BRA.SbRuntime using (Df_F1_I ; Df_F1_I_runtime ; T2)

------------------------------------------------------------------------
-- codedSubstT : Term -> Tree -> Tree -> Term
--
-- Term-valued analog of  codedSubst  (BRA.Term).  Performs substitution
-- of a runtime substituent Term  uT  for code-of-var-n at variable
-- positions of a closed Tree codeB.  At leaves it returns O (= reify lf).
-- At nodes that match  varCode , it returns  uT  un-encoded.  At other
-- nodes it descends and rebuilds with  ap2 Pair .

codedSubstT : Term -> Tree -> Tree -> Term
codedSubstT uT varCode lf = O
codedSubstT uT varCode (nd a b) =
  boolCase (treeEq varCode (nd a b))
    uT
    (ap2 Pair (codedSubstT uT varCode a) (codedSubstT uT varCode b))

------------------------------------------------------------------------
-- subTDef_term : (n : Nat) (uT : Term) (codeB : Tree) ->
--   Deriv (atomic (eqn
--     (ap2 subT (ap2 Pair (reify (code (var n))) uT) (reify codeB))
--     (codedSubstT uT (code (var n)) codeB)))
--
-- The runtime defining equation for sb / subT.  Mirrors  subTDef  but
-- replaces  codeAT = reify codeA  with arbitrary  uT : Term .  The
-- recursion is on codeB (a Tree); the substituent  uT  is propagated
-- un-encoded throughout.

subTDef_term : (n : Nat) (uT : Term) (codeB : Tree) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) uT) (reify codeB))
    (codedSubstT uT (code (var n)) codeB)))
subTDef_term n uT lf =
  axRecPLf stepSubT (ap2 Pair (reify (code (var n))) uT)
subTDef_term n uT (nd a b) =
  ruleTrans s1 (ruleTrans s2 (ruleTrans s6 (ruleTrans s7 s8)))
  where
    varT : Term
    varT = reify (code (var n))

    p : Term
    p = ap2 Pair varT uT

    reifyA : Term
    reifyA = reify a

    reifyB : Term
    reifyB = reify b

    orig : Term
    orig = ap2 Pair reifyA reifyB

    arg1 : Term
    arg1 = ap2 Pair p orig

    varCode : Tree
    varCode = code (var n)

    recA : Term
    recA = ap2 (RecP stepSubT) p reifyA

    recB : Term
    recB = ap2 (RecP stepSubT) p reifyB

    recs : Term
    recs = ap2 Pair recA recB

    treeEqB : Bool
    treeEqB = treeEq varCode (nd a b)

    ihA : Deriv (atomic (eqn recA (codedSubstT uT varCode a)))
    ihA = subTDef_term n uT a

    ihB : Deriv (atomic (eqn recB (codedSubstT uT varCode b)))
    ihB = subTDef_term n uT b

    -- Step 1: axRecPNd unfolds subT at the node.
    s1 : Deriv (atomic (eqn (ap2 subT p orig) (ap2 stepSubT arg1 recs)))
    s1 = axRecPNd stepSubT p reifyA reifyB

    -- Step 2: stepSubT = Fan checkEqSubT contSubT IfLf, axFan unfolds.
    s2 : Deriv (atomic (eqn (ap2 stepSubT arg1 recs)
                            (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))))
    s2 = axFan checkEqSubT contSubT IfLf arg1 recs

    -- Step 3: rewrite the IfLf condition to TreeEq varT orig, then to boolCase.
    fstP : Deriv (atomic (eqn (ap1 Fst p) varT))
    fstP = axFst varT uT

    checkEqVarT : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                      (ap2 TreeEq varT orig)))
    checkEqVarT = ruleTrans (checkEqAt p orig recs) (congL TreeEq orig fstP)

    checkEqB : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                   (boolCase treeEqB O falseT)))
    checkEqB = ruleTrans checkEqVarT (treeEqRed varCode (nd a b))

    -- Step 5: rewrite the IfLf alternatives.
    sndP : Deriv (atomic (eqn (ap1 Snd p) uT))
    sndP = axSnd varT uT

    contUT : Deriv (atomic (eqn (ap2 contSubT arg1 recs) (ap2 Pair uT recs)))
    contUT = ruleTrans (contAt p orig recs) (congL Pair recs sndP)

    -- Step 6: combine condition + alternatives into a clean IfLf.
    s6 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))
                            (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair uT recs))))
    s6 = ruleTrans (congL IfLf (ap2 contSubT arg1 recs) checkEqB)
                   (congR IfLf (boolCase treeEqB O falseT) contUT)

    -- Step 7: ifLfDispatch yields boolCase treeEqB uT recs.
    s7 : Deriv (atomic (eqn (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair uT recs))
                            (boolCase treeEqB uT recs)))
    s7 = ifLfDispatch treeEqB uT recs

    -- Step 8: case-analysis on treeEqB; in the false branch use ihA, ihB.
    finishCaseT : (b' : Bool) ->
      Deriv (atomic (eqn (boolCase b' uT recs)
                          (boolCase b' uT
                            (ap2 Pair (codedSubstT uT varCode a)
                                       (codedSubstT uT varCode b)))))
    finishCaseT true  = axRefl uT
    finishCaseT false =
      ruleTrans (congL Pair recB ihA)
                (congR Pair (codedSubstT uT varCode a) ihB)

    s8 : Deriv (atomic (eqn (boolCase treeEqB uT recs)
                             (codedSubstT uT varCode (nd a b))))
    s8 = finishCaseT treeEqB

------------------------------------------------------------------------
-- Th12_F1_I_at_var0 :
--   Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_I (var zero)))
--                       (codeFTeq1Asym I (var zero))))
--
-- The first concrete schematic Theorem 12 in the codebase.  Composes:
--   (1) Df_F1_I_runtime  at  x := var zero
--   (2) subTDef_term     at  uT := ap1 cor (var zero), n := zero,
--                            codeB := outAxI (var zero)
--   (3) Cosmetic bridge  ap1 cor (var zero) = ap1 cor (ap1 I (var zero))
--       via  cong1 cor (axI (var zero))  (ruleSym to flip direction).
--
-- Step (2)'s RHS reduces (Agda definitional unfolding of codedSubstT
-- on the closed outAxI (var zero) Tree, with treeEq matching exactly
-- at the two var-0 positions in the equation) to
--    mkEqT (mkAp1T (reify (codeF1 I)) (ap1 cor (var zero)))
--          (ap1 cor (var zero))
-- which differs from codeFTeq1Asym I (var zero) only in the RHS slot:
--    (ap1 cor (var zero))  vs  (ap1 cor (ap1 I (var zero))).
-- Step (3) bridges that.

Th12_F1_I_at_var0 :
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_I (var zero)))
                     (codeFTeq1Asym I (var zero))))
Th12_F1_I_at_var0 =
  let
    x : Term
    x = var zero

    runtimeRHS : Term
    runtimeRHS = ap2 subT (ap2 Pair T2 (ap1 cor x)) (reify (outAxI x))

    -- (1) Runtime bridge: thmT(D x) = subT-form RHS.
    step1 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_I x)) runtimeRHS))
    step1 = Df_F1_I_runtime x

    -- (2) subTDef_term: subT-form RHS = codedSubstT-form.
    step2 : Deriv (atomic (eqn runtimeRHS
                                (codedSubstT (ap1 cor x) (code (var zero))
                                              (outAxI x))))
    step2 = subTDef_term zero (ap1 cor x) (outAxI x)

    -- The codedSubstT term reduces (Agda definitional unfolding) to
    --   mkEqT (mkAp1T (reify (codeF1 I)) (ap1 cor x)) (ap1 cor x) .
    -- Use this reduced form as the bridge target.

    reducedT : Term
    reducedT = mkEqT (mkAp1T (reify (codeF1 I)) (ap1 cor x)) (ap1 cor x)

    -- step3: codedSubstT-form = reducedT.  By Agda's evaluator on the
    -- closed outAxI (var zero) tree, codedSubstT unfolds definitionally;
    -- hence axRefl.
    step3 : Deriv (atomic (eqn (codedSubstT (ap1 cor x) (code (var zero))
                                              (outAxI x))
                                reducedT))
    step3 = axRefl reducedT

    -- step4: bridge the RHS slot from  ap1 cor x  to  ap1 cor (ap1 I x).
    --   axI x      :  ap1 I x = x
    --   cong1 cor  :  ap1 cor (ap1 I x) = ap1 cor x
    --   ruleSym    :  ap1 cor x = ap1 cor (ap1 I x)

    bridgeR : Deriv (atomic (eqn (ap1 cor x) (ap1 cor (ap1 I x))))
    bridgeR = ruleSym (cong1 cor (axI x))

    step4 : Deriv (atomic (eqn reducedT
                                (mkEqT (mkAp1T (reify (codeF1 I)) (ap1 cor x))
                                       (ap1 cor (ap1 I x)))))
    step4 = congR Pair (mkAp1T (reify (codeF1 I)) (ap1 cor x)) bridgeR

  in ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))
