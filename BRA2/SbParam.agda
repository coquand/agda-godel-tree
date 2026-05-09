{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SbParam
--
-- Parametric extensions of  subTDef  /  sbDef  : the substituting term
-- (the codeA argument) is allowed to be an arbitrary  Term , not just
--  reify codeA  for closed  codeA : Tree .
--
-- Required for the asymmetric Theorem 12 proof, where the substitute
-- is  ap1 cor (var n)  -- an OPEN BRA term that does not reduce.
--
-- The proof structure mirrors  BRA2.SubT.subTDef  /  BRA2.Sb.sbDef
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

module BRA2.SbParam where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.StepReduce
open import BRA2.SubT
open import BRA2.Sb
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

codedSubstT : Term -> Term -> Term -> Term
codedSubstT repl varCode O                       = O
codedSubstT repl varCode (var n)                 = var n
codedSubstT repl varCode (ap1 f t)               = ap1 f t
codedSubstT repl varCode (ap2 Pair a b)          =
  boolCase (treeEq varCode (ap2 Pair a b))
    repl
    (ap2 Pair (codedSubstT repl varCode a) (codedSubstT repl varCode b))
codedSubstT repl varCode (ap2 Const a b)         = ap2 Const a b
codedSubstT repl varCode (ap2 (Lift f) a b)      = ap2 (Lift f) a b
codedSubstT repl varCode (ap2 (Post f h) a b)    = ap2 (Post f h) a b
codedSubstT repl varCode (ap2 (Fan h1 h2 h) a b) = ap2 (Fan h1 h2 h) a b
codedSubstT repl varCode (ap2 IfLf a b)          = ap2 IfLf a b
codedSubstT repl varCode (ap2 TreeEq a b)        = ap2 TreeEq a b
codedSubstT repl varCode (ap2 (treeRec f s) a b) = ap2 (treeRec f s) a b

------------------------------------------------------------------------
-- subTDefParam : parametric subT defining equation.

subTDefParam :
  (repl : Term) (n : Nat) (codeP : Term) -> IsValue codeP ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair (code (var n)) repl) codeP)
                      (codedSubstT repl (code (var n)) codeP)))
subTDefParam repl n .O                  valO                 =
  axRecPLf stepSubT (ap2 Pair (code (var n)) repl)
subTDefParam repl n (ap2 Pair a b)     (valNd .a .b va vb)   =
  ruleTrans s1 (ruleTrans s2 (ruleTrans s6 (ruleTrans s7 s8)))
  where
    varT : Term
    varT = code (var n)

    varT_isValue : IsValue varT
    varT_isValue = code_isValue (var n)

    p : Term
    p = ap2 Pair varT repl

    orig : Term
    orig = ap2 Pair a b

    orig_isValue : IsValue orig
    orig_isValue = valNd a b va vb

    arg1 : Term
    arg1 = ap2 Pair p orig

    varCode : Term
    varCode = code (var n)

    recsA : Term
    recsA = codedSubstT repl varCode a

    recsB : Term
    recsB = codedSubstT repl varCode b

    recA : Term
    recA = ap2 (RecP stepSubT) p a

    recB : Term
    recB = ap2 (RecP stepSubT) p b

    recs : Term
    recs = ap2 Pair recA recB

    treeEqB : Bool
    treeEqB = treeEq varCode (ap2 Pair a b)

    ihA : Deriv (atomic (eqn recA recsA))
    ihA = subTDefParam repl n a va

    ihB : Deriv (atomic (eqn recB recsB))
    ihB = subTDefParam repl n b vb

    s1 : Deriv (atomic (eqn (ap2 subT p orig) (ap2 stepSubT arg1 recs)))
    s1 = axRecPNd stepSubT p a b

    s2 : Deriv (atomic (eqn (ap2 stepSubT arg1 recs)
                            (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))))
    s2 = axFan checkEqSubT contSubT IfLf arg1 recs

    fstP : Deriv (atomic (eqn (ap1 Fst p) varT))
    fstP = axFst varT repl

    checkEqVarT : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                      (ap2 TreeEq varT orig)))
    checkEqVarT = ruleTrans (checkEqAt p orig recs) (congL TreeEq orig fstP)

    checkEqB : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                   (boolCase treeEqB O falseT)))
    checkEqB = ruleTrans checkEqVarT (treeEqRed varCode varT_isValue (ap2 Pair a b) orig_isValue)

    sndP : Deriv (atomic (eqn (ap1 Snd p) repl))
    sndP = axSnd varT repl

    contRepl : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                   (ap2 Pair repl recs)))
    contRepl = ruleTrans (contAt p orig recs) (congL Pair recs sndP)

    s6 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                       (ap2 contSubT arg1 recs))
                            (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair repl recs))))
    s6 = ruleTrans (congL IfLf (ap2 contSubT arg1 recs) checkEqB)
                   (congR IfLf (boolCase treeEqB O falseT) contRepl)

    s7 : Deriv (atomic (eqn (ap2 IfLf (boolCase treeEqB O falseT)
                                       (ap2 Pair repl recs))
                            (boolCase treeEqB repl recs)))
    s7 = ifLfDispatch treeEqB repl recs

    finishCase : (b' : Bool) ->
      Deriv (atomic (eqn (boolCase b' repl recs)
                          (boolCase b' repl
                            (ap2 Pair recsA recsB))))
    finishCase true  = axRefl repl
    finishCase false =
      ruleTrans (congL Pair recB ihA)
                (congR Pair recsA ihB)

    s8 : Deriv (atomic (eqn (boolCase treeEqB repl recs)
                             (codedSubstT repl varCode (ap2 Pair a b))))
    s8 = finishCase treeEqB

------------------------------------------------------------------------
-- sbDefParam : parametric sb defining equation.

sbDefParam :
  (repl : Term) (n : Nat) (codeP : Term) -> IsValue codeP ->
  Deriv (atomic (eqn (ap2 sb (ap2 Pair repl (natCode n)) codeP)
                      (codedSubstT repl (code (var n)) codeP)))
sbDefParam repl n codeP cP =
  let nT : Term
      nT = natCode n

      codePT : Term
      codePT = codeP

      arg1 : Term
      arg1 = ap2 Pair repl nT

      s1 : Deriv (atomic (eqn (ap2 sb arg1 codePT)
                              (ap2 subT (ap2 repackageSb arg1 codePT)
                                        (ap2 rightSb     arg1 codePT))))
      s1 = axFan repackageSb rightSb subT arg1 codePT

      lhsFinal : Term
      lhsFinal = ap2 Pair (ap2 Pair tagVarT nT) repl

      lhsR : Deriv (atomic (eqn (ap2 repackageSb arg1 codePT) lhsFinal))
      lhsR = repackageSbAt repl nT codePT

      rhsR : Deriv (atomic (eqn (ap2 rightSb arg1 codePT) codePT))
      rhsR = rightSbAt arg1 codePT

      s2 : Deriv (atomic (eqn (ap2 subT (ap2 repackageSb arg1 codePT)
                                        (ap2 rightSb     arg1 codePT))
                              (ap2 subT lhsFinal codePT)))
      s2 = ruleTrans (congL subT (ap2 rightSb arg1 codePT) lhsR)
                     (congR subT lhsFinal rhsR)

      s3 : Deriv (atomic (eqn (ap2 subT lhsFinal codePT)
                              (codedSubstT repl (code (var n)) codeP)))
      s3 = subTDefParam repl n codeP cP

  in ruleTrans s1 (ruleTrans s2 s3)
