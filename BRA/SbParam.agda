{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SbParam
--
-- Parametric extensions of  subTDef  /  sbDef  : the substituting term
-- (the codeA argument) is allowed to be an arbitrary  Term , not just
--  reify codeA  for closed  codeA : Tree .
--
-- Required for the asymmetric Theorem 12 proof, where the substitute
-- is  ap1 cor (var n)  -- an OPEN BRA term that does not reduce.
--
-- The proof structure mirrors  BRA.SubT.subTDef  /  BRA.Sb.sbDef
-- exactly, with  reify codeA  replaced by  repl : Term  throughout,
-- and  reify (codedSubst codeA varCode codeP)  replaced by the
-- Term-level analog  codedSubstT repl varCode codeP .
--
-- Inspection: the only place the closed-input version of  subTDef
-- relies on  codeA : Tree  is at  reify codeA  (a Term).  Allowing
-- arbitrary  repl : Term  in that position requires no new Deriv
-- axioms; the recursion is on the formula GN  codeP : Tree , not on
-- codeA.
--
-- No postulates, no holes.

module BRA.SbParam where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.StepReduce
open import BRA.SubT
open import BRA.Sb
  using (sb ; tagVarT ; buildVarCodeSb ; repackageSb ; rightSb
       ; buildVarCodeSbAt ; repackageSbAt ; rightSbAt)

------------------------------------------------------------------------
-- Term-level codedSubst.
--
-- For closed  repl = reify codeA , this satisfies
--   codedSubstT (reify codeA) varCode codeP
--     = reify (codedSubst codeA varCode codeP)
-- definitionally (provable by induction on codeP).  We do not need
-- that lemma here, but it is the conceptual sanity check.

codedSubstT : Term -> Tree -> Tree -> Term
codedSubstT repl varCode lf       = O
codedSubstT repl varCode (nd a b) =
  boolCase (treeEq varCode (nd a b))
    repl
    (ap2 Pair (codedSubstT repl varCode a) (codedSubstT repl varCode b))

------------------------------------------------------------------------
-- subTDefParam : parametric subT defining equation.

subTDefParam :
  (repl : Term) (n : Nat) (codeP : Tree) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) repl)
                                (reify codeP))
                      (codedSubstT repl (code (var n)) codeP)))
subTDefParam repl n lf =
  axRecPLf stepSubT (ap2 Pair (reify (code (var n))) repl)
subTDefParam repl n (nd a b) =
  ruleTrans s1 (ruleTrans s2 (ruleTrans s6 (ruleTrans s7 s8)))
  where
    varT : Term
    varT = reify (code (var n))

    p : Term
    p = ap2 Pair varT repl

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

    recsA : Term
    recsA = codedSubstT repl varCode a

    recsB : Term
    recsB = codedSubstT repl varCode b

    recA : Term
    recA = ap2 (RecP stepSubT) p reifyA

    recB : Term
    recB = ap2 (RecP stepSubT) p reifyB

    recs : Term
    recs = ap2 Pair recA recB

    treeEqB : Bool
    treeEqB = treeEq varCode (nd a b)

    ihA : Deriv (atomic (eqn recA recsA))
    ihA = subTDefParam repl n a

    ihB : Deriv (atomic (eqn recB recsB))
    ihB = subTDefParam repl n b

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
    fstP = axFst varT repl

    checkEqVarT : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                      (ap2 TreeEq varT orig)))
    checkEqVarT = ruleTrans (checkEqAt p orig recs) (congL TreeEq orig fstP)

    checkEqB : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                   (boolCase treeEqB O falseT)))
    checkEqB = ruleTrans checkEqVarT (treeEqRed varCode (nd a b))

    -- Step 5: rewrite the IfLf alternatives.
    sndP : Deriv (atomic (eqn (ap1 Snd p) repl))
    sndP = axSnd varT repl

    contRepl : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                   (ap2 Pair repl recs)))
    contRepl = ruleTrans (contAt p orig recs) (congL Pair recs sndP)

    -- Step 6: combine condition + alternatives into a clean IfLf.
    s6 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))
                            (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair repl recs))))
    s6 = ruleTrans (congL IfLf (ap2 contSubT arg1 recs) checkEqB)
                   (congR IfLf (boolCase treeEqB O falseT) contRepl)

    -- Step 7: ifLfDispatch yields boolCase treeEqB repl recs.
    s7 : Deriv (atomic (eqn (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair repl recs))
                            (boolCase treeEqB repl recs)))
    s7 = ifLfDispatch treeEqB repl recs

    -- Step 8: boolCase-by-cases.
    -- codedSubstT repl varCode (nd a b) = boolCase treeEqB repl
    --                                       (ap2 Pair recsA recsB)  (defn).
    finishCase : (b' : Bool) ->
      Deriv (atomic (eqn (boolCase b' repl recs)
                          (boolCase b' repl
                            (ap2 Pair recsA recsB))))
    finishCase true  = axRefl repl
    finishCase false =
      ruleTrans (congL Pair recB ihA)
                (congR Pair recsA ihB)

    s8 : Deriv (atomic (eqn (boolCase treeEqB repl recs)
                             (codedSubstT repl varCode (nd a b))))
    s8 = finishCase treeEqB

------------------------------------------------------------------------
-- sbDefParam : parametric sb defining equation.

sbDefParam :
  (repl : Term) (n : Nat) (codeP : Tree) ->
  Deriv (atomic (eqn (ap2 sb (ap2 Pair repl (reify (natCode n)))
                              (reify codeP))
                      (codedSubstT repl (code (var n)) codeP)))
sbDefParam repl n codeP =
  let nT : Term
      nT = reify (natCode n)

      codePT : Term
      codePT = reify codeP

      arg1 : Term
      arg1 = ap2 Pair repl nT

      -- Step 1: sb = Fan repackageSb rightSb subT, axFan unfolds.
      s1 : Deriv (atomic (eqn (ap2 sb arg1 codePT)
                              (ap2 subT (ap2 repackageSb arg1 codePT)
                                        (ap2 rightSb     arg1 codePT))))
      s1 = axFan repackageSb rightSb subT arg1 codePT

      -- Step 2: reduce repackageSb to (Pair (Pair tagVarT nT) repl).
      lhsFinal : Term
      lhsFinal = ap2 Pair (ap2 Pair tagVarT nT) repl

      lhsR : Deriv (atomic (eqn (ap2 repackageSb arg1 codePT) lhsFinal))
      lhsR = repackageSbAt repl nT codePT

      -- Step 3: reduce rightSb to codePT.
      rhsR : Deriv (atomic (eqn (ap2 rightSb arg1 codePT) codePT))
      rhsR = rightSbAt arg1 codePT

      -- Step 4: assemble the subT call.
      s2 : Deriv (atomic (eqn (ap2 subT (ap2 repackageSb arg1 codePT)
                                        (ap2 rightSb     arg1 codePT))
                              (ap2 subT lhsFinal codePT)))
      s2 = ruleTrans (congL subT (ap2 rightSb arg1 codePT) lhsR)
                     (congR subT lhsFinal rhsR)

      -- Step 5: subTDefParam closes the goal.
      --   lhsFinal = ap2 Pair (ap2 Pair tagVarT nT) repl
      --           = ap2 Pair (reify (code (var n))) repl  (definitional,
      --             since reify (code (var n)) = ap2 Pair tagVarT nT).
      s3 : Deriv (atomic (eqn (ap2 subT lhsFinal codePT)
                              (codedSubstT repl (code (var n)) codeP)))
      s3 = subTDefParam repl n codeP

  in ruleTrans s1 (ruleTrans s2 s3)
