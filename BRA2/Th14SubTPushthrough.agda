{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th14SubTPushthrough
--
-- subT structural-distribution lemmas, parametric in the substituent
-- Term tT.  These are the "subT-canonicalization" infrastructure
-- needed by Phase C of the Theorem 14 closure
-- (NEXT-SESSION-PHASE-C-CONTINUE.md).
--
-- The closed-form  subTDef  (BRA/SubT.agda:154) requires the substituent
-- to be  reify codeA  for some Tree codeA, returning  reify (codedSubst
-- codeA varCode codeB) .  When the substituent is parametric (e.g.,
-- (cor x) in step3_l), subTDef does not apply, but the recursive
-- structure of subT can still be unfolded one node at a time.
--
-- This file delivers two general-purpose lemmas:
--
--   subT_node_no_match :
--     subT (Pair varCodeT tT) (reify (nd a b))
--       =  Pair (subT (Pair varCodeT tT) (reify a))
--                (subT (Pair varCodeT tT) (reify b))
--     when treeEq (code (var n)) (nd a b) is meta-false.
--
--   subT_node_match :
--     subT (Pair (reify (code (var n))) tT) (reify (code (var n)))
--       =  tT .
--
-- and a leaf base case
--
--   subT_leaf :
--     subT (Pair varCodeT tT) (reify lf)  =  reify lf .
--
-- ASCII only.  No postulates, no holes.

module BRA2.Th14SubTPushthrough where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.SubT
  using ( subT ; stepSubT ; checkEqSubT ; contSubT ; checkEqAt ; contAt
        ; treeEqRed ; ifLfDispatch )

----------------------------------------------------------------------
-- treeEq is reflexive on identical trees (meta-level lemma).

treeEqRefl : (t : Term) -> IsValue t -> Eq (treeEq t t) true
treeEqRefl .O                 valO                = refl
treeEqRefl (ap2 Pair a b)    (valNd .a .b va vb)  =
  eqTrans (eqCong (\ y -> boolAnd y (treeEq b b)) (treeEqRefl a va))
          (treeEqRefl b vb)

----------------------------------------------------------------------
-- natCodeEq (inlined to avoid CodeCommutes circular dep).

natCodeEqLocal : (n m : Nat) ->
                  Eq (treeEq (natCode n) (natCode m)) (natEq n m)
natCodeEqLocal zero    zero    = refl
natCodeEqLocal zero    (suc _) = refl
natCodeEqLocal (suc _) zero    = refl
natCodeEqLocal (suc n) (suc m) = natCodeEqLocal n m

----------------------------------------------------------------------
-- subT_leaf : the lf base case of subT.
--
-- subT (Pair varCodeT tT) (reify lf)  =  reify lf
-- by axRecPLf  (and reify lf = O, so subT(p, O) = O).

subT_leaf : (p : Term) ->
  Deriv (atomic (eqn (ap2 subT p (reify lf)) (reify lf)))
subT_leaf p = axRecPLf stepSubT p

----------------------------------------------------------------------
-- subT_node_unfold : the structural unfold of subT at a Pair-shaped
-- target, BEFORE deciding on the match/no-match boolean.
--
--   subT (Pair varCodeT tT) (reify (nd a b))
--     =  IfLf (boolCase (treeEq (Fst varCodeT?) ...) ...) (Pair tT recs)
--
-- We give the form parametric in p (the Pair varCodeT tT), with the
-- TreeEq evaluation done outside.  Restricting to varCodeT = reify
-- (code (var n)) delivers the boolCase.

subT_node_unfold : (p : Term) (a b : Tree) ->
  Deriv (atomic (eqn
    (ap2 subT p (reify (nd a b)))
    (ap2 IfLf
      (ap2 TreeEq (ap1 Fst p) (reify (nd a b)))
      (ap2 Pair (ap1 Snd p)
                (ap2 Pair (ap2 subT p (reify a)) (ap2 subT p (reify b)))))))
subT_node_unfold p a b =
  let
      reifyA : Term
      reifyA = reify a

      reifyB : Term
      reifyB = reify b

      orig : Term
      orig = ap2 Pair reifyA reifyB

      arg1 : Term
      arg1 = ap2 Pair p orig

      recA : Term
      recA = ap2 subT p reifyA

      recB : Term
      recB = ap2 subT p reifyB

      recs : Term
      recs = ap2 Pair recA recB

      -- Step 1: axRecPNd unfolds subT at the node.
      s1 : Deriv (atomic (eqn (ap2 subT p orig) (ap2 stepSubT arg1 recs)))
      s1 = axRecPNd stepSubT p reifyA reifyB

      -- Step 2: axFan unfolds stepSubT.
      s2 : Deriv (atomic (eqn (ap2 stepSubT arg1 recs)
                              (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                         (ap2 contSubT arg1 recs))))
      s2 = axFan checkEqSubT contSubT IfLf arg1 recs

      -- Step 3: rewrite checkEqSubT to TreeEq (Fst p) orig.
      s3_check : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                     (ap2 TreeEq (ap1 Fst p) orig)))
      s3_check = checkEqAt p orig recs

      -- Step 4: rewrite contSubT to Pair (Snd p) recs.
      s4_cont : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                    (ap2 Pair (ap1 Snd p) recs)))
      s4_cont = contAt p orig recs

      -- Combine s3 + s4 into the IfLf form.
      s5 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                         (ap2 contSubT arg1 recs))
                              (ap2 IfLf (ap2 TreeEq (ap1 Fst p) orig)
                                         (ap2 Pair (ap1 Snd p) recs))))
      s5 = ruleTrans (congL IfLf (ap2 contSubT arg1 recs) s3_check)
                     (congR IfLf (ap2 TreeEq (ap1 Fst p) orig) s4_cont)
  in ruleTrans s1 (ruleTrans s2 s5)

----------------------------------------------------------------------
-- subT_node_match : the match case.
--
-- When the target IS literally  reify (code (var n))  (= reify (nd
-- tagVar (natCode n))), the TreeEq check returns true (= O), and the
-- IfLf dispatches to the substituent  tT .

subT_node_match : (n : Nat) (tT : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify (code (var n))))
    tT))
subT_node_match n tT =
  let
      varCode : Tree
      varCode = code (var n)

      varCodeT : Term
      varCodeT = reify varCode

      p : Term
      p = ap2 Pair varCodeT tT

      a : Tree
      a = leftT varCode

      b : Tree
      b = rightT varCode

      -- code (var n) = nd tagVar (natCode n), so leftT = tagVar,
      -- rightT = natCode n.  We work directly on the ndForm via
      -- subT_node_unfold at (a, b) := (tagVar, natCode n).

      -- Step 1: subT_node_unfold at the (tagVar, natCode n) tree.
      step1 : Deriv (atomic (eqn
        (ap2 subT p (reify (nd tagVar (natCode n))))
        (ap2 IfLf (ap2 TreeEq (ap1 Fst p) (reify (nd tagVar (natCode n))))
                   (ap2 Pair (ap1 Snd p)
                              (ap2 Pair
                                (ap2 subT p (reify tagVar))
                                (ap2 subT p (reify (natCode n))))))))
      step1 = subT_node_unfold p tagVar (natCode n)

      -- Step 2: TreeEq (Fst p) (reify (nd tagVar (natCode n))) =
      --         TreeEq varCodeT (reify (nd tagVar (natCode n))) =
      --         boolCase (treeEq (nd tagVar (natCode n)) (nd tagVar (natCode n))) O falseT
      --         = boolCase true O falseT = O.

      fstP : Deriv (atomic (eqn (ap1 Fst p) varCodeT))
      fstP = axFst varCodeT tT

      sndP : Deriv (atomic (eqn (ap1 Snd p) tT))
      sndP = axSnd varCodeT tT

      -- TreeEq result.
      treeEqResult : Deriv (atomic (eqn (ap2 TreeEq (ap1 Fst p) (reify (nd tagVar (natCode n))))
                                         (ap2 TreeEq varCodeT (reify (nd tagVar (natCode n))))))
      treeEqResult = congL TreeEq (reify (nd tagVar (natCode n))) fstP

      treeEqRedC : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT (reify (nd tagVar (natCode n))))
        (boolCase (treeEq (nd tagVar (natCode n)) (nd tagVar (natCode n)))
                  O falseT)))
      treeEqRedC = treeEqRed (nd tagVar (natCode n))
                              (valNd tagVar (natCode n) tagVar_isValue (natCode_isValue n))
                              (nd tagVar (natCode n))
                              (valNd tagVar (natCode n) tagVar_isValue (natCode_isValue n))

      treeEqIsTrue : Eq (treeEq (nd tagVar (natCode n)) (nd tagVar (natCode n))) true
      treeEqIsTrue = treeEqRefl (nd tagVar (natCode n))
                                 (valNd tagVar (natCode n) tagVar_isValue (natCode_isValue n))

      -- boolCase with the true reduction.
      boolCaseEq : Eq (boolCase (treeEq (nd tagVar (natCode n)) (nd tagVar (natCode n)))
                                O falseT) O
      boolCaseEq = eqCong (\ b' -> boolCase b' O falseT) treeEqIsTrue

      treeEqIsO : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT (reify (nd tagVar (natCode n)))) O))
      treeEqIsO = eqSubst
                    (\ T -> Deriv (atomic (eqn
                       (ap2 TreeEq varCodeT (reify (nd tagVar (natCode n)))) T)))
                    boolCaseEq treeEqRedC

      treeEqFromFst : Deriv (atomic (eqn
        (ap2 TreeEq (ap1 Fst p) (reify (nd tagVar (natCode n)))) O))
      treeEqFromFst = ruleTrans treeEqResult treeEqIsO

      -- Bridge the IfLf condition slot.
      step2_bridge : Deriv (atomic (eqn
        (ap2 IfLf (ap2 TreeEq (ap1 Fst p) (reify (nd tagVar (natCode n))))
                   (ap2 Pair (ap1 Snd p)
                              (ap2 Pair (ap2 subT p (reify tagVar))
                                         (ap2 subT p (reify (natCode n))))))
        (ap2 IfLf O
                   (ap2 Pair (ap1 Snd p)
                              (ap2 Pair (ap2 subT p (reify tagVar))
                                         (ap2 subT p (reify (natCode n))))))))
      step2_bridge = congL IfLf
        (ap2 Pair (ap1 Snd p)
                  (ap2 Pair (ap2 subT p (reify tagVar))
                             (ap2 subT p (reify (natCode n)))))
        treeEqFromFst

      -- Bridge the Snd p slot to tT.
      step3_sndBridge : Deriv (atomic (eqn
        (ap2 IfLf O
                   (ap2 Pair (ap1 Snd p)
                              (ap2 Pair (ap2 subT p (reify tagVar))
                                         (ap2 subT p (reify (natCode n))))))
        (ap2 IfLf O
                   (ap2 Pair tT
                              (ap2 Pair (ap2 subT p (reify tagVar))
                                         (ap2 subT p (reify (natCode n))))))))
      step3_sndBridge = congR IfLf O
        (congL Pair
          (ap2 Pair (ap2 subT p (reify tagVar))
                     (ap2 subT p (reify (natCode n))))
          sndP)

      -- axIfLfL: IfLf O (Pair tT recsInner) = tT.
      step4_ifLfL : Deriv (atomic (eqn
        (ap2 IfLf O
                   (ap2 Pair tT
                              (ap2 Pair (ap2 subT p (reify tagVar))
                                         (ap2 subT p (reify (natCode n))))))
        tT))
      step4_ifLfL = axIfLfL tT
        (ap2 Pair (ap2 subT p (reify tagVar))
                   (ap2 subT p (reify (natCode n))))

  in ruleTrans step1 (ruleTrans step2_bridge (ruleTrans step3_sndBridge step4_ifLfL))

----------------------------------------------------------------------
-- subT_node_no_match : the no-match case.
--
-- When the target  reify (nd a b)  has  treeEq (code (var n)) (nd a b)
-- = false  meta-level, the TreeEq check returns Pair O O, and the
-- IfLf dispatches to the recursive Pair, giving the structural
-- distribution.

subT_node_no_match : (n : Nat) (tT : Term) (a : Term) -> IsValue a ->
                     (b : Term) -> IsValue b ->
  Eq (treeEq (code (var n)) (nd a b)) false ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify (nd a b)))
    (ap2 Pair (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify a))
              (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify b)))))
subT_node_no_match n tT a va b vb treeEqIsFalse =
  let
      varCode : Tree
      varCode = code (var n)

      varCodeT : Term
      varCodeT = reify varCode

      p : Term
      p = ap2 Pair varCodeT tT

      recA : Term
      recA = ap2 subT p (reify a)

      recB : Term
      recB = ap2 subT p (reify b)

      recs : Term
      recs = ap2 Pair recA recB

      -- Step 1: structural unfold.
      step1 : Deriv (atomic (eqn
        (ap2 subT p (reify (nd a b)))
        (ap2 IfLf (ap2 TreeEq (ap1 Fst p) (reify (nd a b)))
                   (ap2 Pair (ap1 Snd p) recs))))
      step1 = subT_node_unfold p a b

      fstP : Deriv (atomic (eqn (ap1 Fst p) varCodeT))
      fstP = axFst varCodeT tT

      sndP : Deriv (atomic (eqn (ap1 Snd p) tT))
      sndP = axSnd varCodeT tT

      treeEqBridge : Deriv (atomic (eqn
        (ap2 TreeEq (ap1 Fst p) (reify (nd a b)))
        (ap2 TreeEq varCodeT (reify (nd a b)))))
      treeEqBridge = congL TreeEq (reify (nd a b)) fstP

      treeEqRedC : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT (reify (nd a b)))
        (boolCase (treeEq varCode (nd a b)) O falseT)))
      treeEqRedC = treeEqRed varCode (code_isValue (var n))
                              (nd a b) (valNd a b va vb)

      -- boolCase false O falseT = falseT = Pair O O.
      boolCaseEq : Eq (boolCase (treeEq varCode (nd a b)) O falseT) falseT
      boolCaseEq = eqCong (\ b' -> boolCase b' O falseT) treeEqIsFalse

      treeEqIsFalseT : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT (reify (nd a b))) falseT))
      treeEqIsFalseT = eqSubst
                         (\ T -> Deriv (atomic (eqn
                            (ap2 TreeEq varCodeT (reify (nd a b))) T)))
                         boolCaseEq treeEqRedC

      treeEqFromFst : Deriv (atomic (eqn
        (ap2 TreeEq (ap1 Fst p) (reify (nd a b))) falseT))
      treeEqFromFst = ruleTrans treeEqBridge treeEqIsFalseT

      -- Bridge IfLf condition slot to falseT = Pair O O.
      step2_bridge : Deriv (atomic (eqn
        (ap2 IfLf (ap2 TreeEq (ap1 Fst p) (reify (nd a b)))
                   (ap2 Pair (ap1 Snd p) recs))
        (ap2 IfLf falseT
                   (ap2 Pair (ap1 Snd p) recs))))
      step2_bridge = congL IfLf
        (ap2 Pair (ap1 Snd p) recs)
        treeEqFromFst

      -- axIfLfN: IfLf (Pair O O) (Pair x y) = y.  falseT = Pair O O.
      step3_ifLfN : Deriv (atomic (eqn
        (ap2 IfLf falseT (ap2 Pair (ap1 Snd p) recs))
        recs))
      step3_ifLfN = axIfLfN O O (ap1 Snd p) recs

  in ruleTrans step1 (ruleTrans step2_bridge step3_ifLfN)

----------------------------------------------------------------------
-- A useful corollary: subT_node_no_match for closed Trees with concrete
-- treeEq mismatch.
--
-- Any specific  nd a b  whose meta-treeEq with  code (var n)  is false
-- automatically satisfies the hypothesis via  refl .  E.g., for
-- (nd a b) = nd tagAp1 ... , we have
--   treeEq (code (var n)) (nd tagAp1 ...) = false  by refl
-- since code(var n) starts with tagVar = nd (nd (nd lf lf) lf) lf, while
-- tagAp1 = nd lf (nd lf lf), and tagVar's leftT = nd (nd lf lf) lf
-- mismatches tagAp1's leftT = lf at the first comparison.

----------------------------------------------------------------------
-- subT_node_no_match_var : specialisation when target = code (var k)
-- for k != n .

natEqRefl : (n : Nat) -> Eq (natEq n n) true
natEqRefl zero    = refl
natEqRefl (suc n) = natEqRefl n

natEqIsFalse_of_diff : (n k : Nat) -> Eq (natEq n k) false ->
                        Eq (treeEq (code (var n)) (code (var k))) false
natEqIsFalse_of_diff n k diff =
  let
      -- treeEq (code (var n)) (code (var k))
      --   = treeEq (nd tagVar (natCode n)) (nd tagVar (natCode k))
      --   = boolAnd (treeEq tagVar tagVar) (treeEq (natCode n) (natCode k))
      --   = boolAnd true (treeEq (natCode n) (natCode k))
      --   = treeEq (natCode n) (natCode k)
      --   = natEq n k     by natCodeEq
      --   = false        by hypothesis

      treeEqTagVarRefl : Eq (treeEq tagVar tagVar) true
      treeEqTagVarRefl = treeEqRefl tagVar tagVar_isValue

      -- After reducing treeEq tagVar tagVar to true, boolAnd true x = x.
      step1 : Eq (treeEq (code (var n)) (code (var k)))
                 (treeEq (natCode n) (natCode k))
      step1 = eqCong (\ b' -> boolAnd b' (treeEq (natCode n) (natCode k)))
                     treeEqTagVarRefl

      step2 : Eq (treeEq (natCode n) (natCode k)) (natEq n k)
      step2 = natCodeEqLocal n k

  in eqTrans step1 (eqTrans step2 diff)

----------------------------------------------------------------------
-- Specific instances of treeEq mismatch with code(var n) at the
-- outer-tag-tree shapes used by codeFormula:
--
--   tagImp = nd (nd lf lf) (nd lf lf)
--   tagNeg = nd (nd lf lf) lf
--   tagAp1 = nd lf (nd lf lf)
--   tagAp2 = nd lf (nd lf (nd lf lf))
--   tagVar = nd (nd (nd lf lf) lf) lf
--
-- code (var n) = nd tagVar (natCode n).  The shapes above all differ
-- from tagVar at the first child or earlier, so treeEq evaluates to
-- false uniformly in n (and the rest of the tree).

treeEq_codeVar_tagImpHead :
  (n : Nat) (rest : Tree) ->
  Eq (treeEq (code (var n)) (nd tagImp rest)) false
treeEq_codeVar_tagImpHead n rest = refl

treeEq_codeVar_tagNegHead :
  (n : Nat) (rest : Tree) ->
  Eq (treeEq (code (var n)) (nd tagNeg rest)) false
treeEq_codeVar_tagNegHead n rest = refl

treeEq_codeVar_tagAp1Head :
  (n : Nat) (rest : Tree) ->
  Eq (treeEq (code (var n)) (nd tagAp1 rest)) false
treeEq_codeVar_tagAp1Head n rest = refl

treeEq_codeVar_tagAp2Head :
  (n : Nat) (rest : Tree) ->
  Eq (treeEq (code (var n)) (nd tagAp2 rest)) false
treeEq_codeVar_tagAp2Head n rest = refl

----------------------------------------------------------------------
-- Closed-passthrough lemma: subT preserves reify of a Tree that has
-- no  code (var n)  subtree.  Stated directly for the specific tag
-- trees used by codeFormula's outer structure (tagImp, tagNeg).

subT_preserves_tagImp : (n : Nat) (tT : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify tagImp))
    (reify tagImp)))
subT_preserves_tagImp n tT =
  let
      p : Term
      p = ap2 Pair (reify (code (var n))) tT

      -- tagImp = nd (nd lf lf) (nd lf lf)
      -- subT distributes (no var-n match at outer):
      step1 : Deriv (atomic (eqn
        (ap2 subT p (reify (nd (nd lf lf) (nd lf lf))))
        (ap2 Pair (ap2 subT p (reify (nd lf lf)))
                  (ap2 subT p (reify (nd lf lf))))))
      step1 = subT_node_no_match n tT (nd lf lf) (valNd lf lf valO valO)
                                       (nd lf lf) (valNd lf lf valO valO)
                                       refl

      step2_inner : Deriv (atomic (eqn
        (ap2 subT p (reify (nd lf lf)))
        (ap2 Pair (ap2 subT p (reify lf)) (ap2 subT p (reify lf)))))
      step2_inner = subT_node_no_match n tT lf valO lf valO refl

      step2_leaf : Deriv (atomic (eqn (ap2 subT p (reify lf)) (reify lf)))
      step2_leaf = subT_leaf p

      -- Bridge inner to reify (nd lf lf).
      step2 : Deriv (atomic (eqn (ap2 subT p (reify (nd lf lf)))
                                  (reify (nd lf lf))))
      step2 = ruleTrans step2_inner
                (ruleTrans (congL Pair (ap2 subT p (reify lf)) step2_leaf)
                           (congR Pair (reify lf) step2_leaf))

      -- Combine: outer Pair with both children = reify (nd lf lf).
      step3 : Deriv (atomic (eqn
        (ap2 Pair (ap2 subT p (reify (nd lf lf)))
                  (ap2 subT p (reify (nd lf lf))))
        (ap2 Pair (reify (nd lf lf)) (reify (nd lf lf)))))
      step3 = ruleTrans (congL Pair (ap2 subT p (reify (nd lf lf))) step2)
                        (congR Pair (reify (nd lf lf)) step2)

  in ruleTrans step1 step3

----------------------------------------------------------------------
-- subT_codeFormula_imp : subT distributes structurally on
-- reify (codeFormula (P imp Q)) , preserving the outer tagImp head and
-- exposing the imp-shape Pair needed by thmTDispMp_param.
--
--   subT (Pair (reify (code (var n))) tT) (reify (codeFormula (P imp Q)))
--     =  Pair (reify tagImp)
--             (Pair (subT ... (reify (codeFormula P)))
--                   (subT ... (reify (codeFormula Q))))

subT_codeFormula_imp : (n : Nat) (tT : Term) (P Q : Formula) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT)
              (reify (codeFormula (P imp Q))))
    (ap2 Pair (reify tagImp)
              (ap2 Pair
                (ap2 subT (ap2 Pair (reify (code (var n))) tT)
                           (reify (codeFormula P)))
                (ap2 subT (ap2 Pair (reify (code (var n))) tT)
                           (reify (codeFormula Q)))))))
subT_codeFormula_imp n tT P Q =
  let
      p : Term
      p = ap2 Pair (reify (code (var n))) tT

      cP : Tree
      cP = codeFormula P

      cQ : Tree
      cQ = codeFormula Q

      -- Step 1: outer no-match split:
      --   subT (reify (nd tagImp (nd cP cQ)))
      --     =  Pair (subT (reify tagImp)) (subT (reify (nd cP cQ)))
      step1 : Deriv (atomic (eqn
        (ap2 subT p (reify (nd tagImp (nd cP cQ))))
        (ap2 Pair (ap2 subT p (reify tagImp))
                  (ap2 subT p (reify (nd cP cQ))))))
      step1 = subT_node_no_match n tT tagImp tagImp_isValue
                                       (nd cP cQ)
                                       (valNd cP cQ (codeFormula_isValue P) (codeFormula_isValue Q))
                                       (treeEq_codeVar_tagImpHead n (nd cP cQ))

      -- Step 2: inner no-match split:
      --   subT (reify (nd cP cQ))
      --     =  Pair (subT (reify cP)) (subT (reify cQ))
      --
      -- This requires treeEq (code (var n)) (nd cP cQ) = false , which
      -- generally depends on cP / cQ.  However, codeFormula P always
      -- starts with one of {nd tagAtomic*, tagNeg, tagImp, ...}, none
      -- of which equal tagVar — so treeEq fails at the FIRST step.
      --
      -- Equivalently: since cP = codeFormula P, the head of (nd cP cQ)
      -- IS cP, which itself starts with nd <something-not-tagVar> _.
      -- So treeEq (code (var n)) (nd cP cQ) compares
      --   nd tagVar (natCode n)  with  nd cP cQ ,
      -- which boolAnds (treeEq tagVar cP) and (treeEq (natCode n) cQ).
      -- The first factor evaluates to false uniformly:  cP starts with
      -- nd (and tagVar = nd (nd (nd lf lf) lf) lf), so the comparison
      -- boils down to treeEq (left of tagVar) (left of cP) =
      -- treeEq (nd (nd lf lf) lf) <left of cP> .  Whether codeFormula's
      -- outer tag is tagImp / tagNeg / tagAp1 / tagAp2 / codeF1 / codeF2
      -- depends on P 's constructor; in each case the first child
      -- mismatch propagates.
      --
      -- To avoid case-analysis on P, we restrict here to the case
      -- relevant for f_part / h_part: P / Q themselves are imp / atomic
      -- forms.  A fully general lemma would be ~50 LoC of case-split.
      --
      -- For Phase C step5_l, we apply subT_codeFormula_imp recursively;
      -- the inner subT calls are then fed forward to the eventual
      -- atomic-equation level (where a separate subT_codeFormula_atomic
      -- lemma — to be written next session — handles the equation form).

      -- Step 2: the inner Pair (cP cQ) split is provided by the caller
      -- at consumption (we cannot prove it here without case-analysing
      -- P 's constructor).  The result form below thus has
      -- subT (reify (nd cP cQ)) instead of the further-distributed Pair.
      --
      -- Bridge: we expose the structural decomposition WITH the inner
      -- nd cP cQ already split, by relying on the FACT that codeFormula
      -- of any Formula starts with a non-tagVar tag.

      -- Lift restriction: state the no-match for nd cP cQ via the
      -- codeFormula_no_var lemma below.
      step2_innerSplit : Deriv (atomic (eqn
        (ap2 subT p (reify (nd cP cQ)))
        (ap2 Pair (ap2 subT p (reify cP))
                  (ap2 subT p (reify cQ)))))
      step2_innerSplit = subT_node_no_match n tT cP (codeFormula_isValue P)
                                                cQ (codeFormula_isValue Q)
                           (codeFormula_pair_no_var n P Q)

      -- Bridge subT (reify tagImp) to reify tagImp.
      step3 : Deriv (atomic (eqn
        (ap2 Pair (ap2 subT p (reify tagImp))
                  (ap2 subT p (reify (nd cP cQ))))
        (ap2 Pair (reify tagImp)
                  (ap2 subT p (reify (nd cP cQ))))))
      step3 = congL Pair (ap2 subT p (reify (nd cP cQ)))
                (subT_preserves_tagImp n tT)

      -- Bridge subT (reify (nd cP cQ)) to the inner Pair.
      step4 : Deriv (atomic (eqn
        (ap2 Pair (reify tagImp) (ap2 subT p (reify (nd cP cQ))))
        (ap2 Pair (reify tagImp)
                  (ap2 Pair (ap2 subT p (reify cP))
                            (ap2 subT p (reify cQ))))))
      step4 = congR Pair (reify tagImp) step2_innerSplit

  in ruleTrans step1 (ruleTrans step3 step4)
  where
    -- treeEq (code (var n)) (nd cP cQ) = false  for cP = codeFormula P.
    -- By case-analysis on P's outer constructor, cP's head tag is
    -- always non-tagVar, so the boolAnd (treeEq tagVar cP) (...) factor
    -- evaluates to false.
    codeFormula_pair_no_var :
      (n : Nat) (P Q : Formula) ->
      Eq (treeEq (code (var n)) (nd (codeFormula P) (codeFormula Q))) false
    codeFormula_pair_no_var n (atomic (eqn O           _)) Q = refl
    codeFormula_pair_no_var n (atomic (eqn (var _)     _)) Q = refl
    codeFormula_pair_no_var n (atomic (eqn (ap1 _ _)   _)) Q = refl
    codeFormula_pair_no_var n (atomic (eqn (ap2 _ _ _) _)) Q = refl
    -- For `not P` we need codeFormula P != lf; case-split one level.
    codeFormula_pair_no_var n (not (atomic (eqn _ _))) Q = refl
    codeFormula_pair_no_var n (not (not _))            Q = refl
    codeFormula_pair_no_var n (not (_ imp _))          Q = refl
    codeFormula_pair_no_var n (_ imp _)                Q = refl

----------------------------------------------------------------------
-- subT distribution through a Pair-tagImp form (nested subT case).
--
-- For step5_l we apply subT three times to (reify (codeFormula t_formula)).
-- After the FIRST subT, the result is  Pair (reify tagImp) (Pair X Y) ,
-- which is no longer reify-of-tree.  Subsequent subT applications need
-- to distribute through this Pair-tagImp form, preserving the imp head
-- and recursing on the Pair-children.
--
--   subT (Pair (reify (code (var n))) tT)
--        (ap2 Pair (reify tagImp) (ap2 Pair X Y))
--   =  ap2 Pair (reify tagImp)
--               (ap2 Pair (subT (...) X) (subT (...) Y))
--
-- Proof: axRecPNd unfolds; checkEqSubT delivers a TreeEq result that
-- evaluates to Pair O O (mismatch — varCodeT vs Pair tagImp _) via
-- axTreeEqNN + treeEqRed; contSubT delivers Pair tT recs; IfLf at
-- (Pair O O) drops the substituent and returns recs; subT_preserves_tagImp
-- converts subT(p)(reify tagImp) to reify tagImp.

subT_dist_Pair_tagImp : (n : Nat) (tT : Term) (X Y : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT)
              (ap2 Pair (reify tagImp) (ap2 Pair X Y)))
    (ap2 Pair (reify tagImp)
              (ap2 subT (ap2 Pair (reify (code (var n))) tT)
                         (ap2 Pair X Y)))))
subT_dist_Pair_tagImp n tT X Y =
  let
      varCodeT : Term
      varCodeT = reify (code (var n))

      p : Term
      p = ap2 Pair varCodeT tT

      orig : Term
      orig = ap2 Pair (reify tagImp) (ap2 Pair X Y)

      arg1 : Term
      arg1 = ap2 Pair p orig

      recA : Term
      recA = ap2 subT p (reify tagImp)

      recB : Term
      recB = ap2 subT p (ap2 Pair X Y)

      recs : Term
      recs = ap2 Pair recA recB

      -- Step 1: axRecPNd unfolds subT at the Pair-shape.
      s1 : Deriv (atomic (eqn (ap2 subT p orig) (ap2 stepSubT arg1 recs)))
      s1 = axRecPNd stepSubT p (reify tagImp) (ap2 Pair X Y)

      -- Step 2: axFan unfolds stepSubT.
      s2 : Deriv (atomic (eqn (ap2 stepSubT arg1 recs)
                              (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                         (ap2 contSubT arg1 recs))))
      s2 = axFan checkEqSubT contSubT IfLf arg1 recs

      -- Step 3: rewrite checkEqSubT to TreeEq (Fst p) orig.
      s3_check : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                     (ap2 TreeEq (ap1 Fst p) orig)))
      s3_check = checkEqAt p orig recs

      fstP : Deriv (atomic (eqn (ap1 Fst p) varCodeT))
      fstP = axFst varCodeT tT

      sndP : Deriv (atomic (eqn (ap1 Snd p) tT))
      sndP = axSnd varCodeT tT

      -- Bridge to varCodeT.
      s3_check2 : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                      (ap2 TreeEq varCodeT orig)))
      s3_check2 = ruleTrans s3_check (congL TreeEq orig fstP)

      -- Now evaluate ap2 TreeEq varCodeT (Pair tagImpT (Pair X Y)).
      -- varCodeT = ap2 Pair (reify tagVar) (reify (natCode n)).
      -- By axTreeEqNN, this becomes
      --   IfLf (TreeEq (reify tagVar) (reify tagImp))
      --        (Pair (TreeEq (reify (natCode n)) (Pair X Y)) (Pair O O))

      tagImpT : Term
      tagImpT = reify tagImp

      natCodeNT : Term
      natCodeNT = reify (natCode n)

      tagVarT : Term
      tagVarT = reify tagVar

      -- TreeEq on the outer Pair-Pair: axTreeEqNN.
      eq_NN : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT orig)
        (ap2 IfLf (ap2 TreeEq tagVarT tagImpT)
                   (ap2 Pair (ap2 TreeEq natCodeNT (ap2 Pair X Y))
                              (ap2 Pair O O)))))
      eq_NN = axTreeEqNN tagVarT natCodeNT tagImpT (ap2 Pair X Y)

      -- TreeEq tagVarT tagImpT = falseT  (= Pair O O), by treeEqRed +
      -- meta-treeEq tagVar tagImp = false.
      treeEqRedTV : Deriv (atomic (eqn
        (ap2 TreeEq tagVarT tagImpT)
        (boolCase (treeEq tagVar tagImp) O falseT)))
      treeEqRedTV = treeEqRed tagVar tagVar_isValue tagImp tagImp_isValue

      -- meta: treeEq tagVar tagImp = false (refl).
      treeEqTagVarImpFalse : Eq (treeEq tagVar tagImp) false
      treeEqTagVarImpFalse = refl

      treeEqTagVarImpToFalseT : Eq (boolCase (treeEq tagVar tagImp) O falseT) falseT
      treeEqTagVarImpToFalseT =
        eqCong (\ b' -> boolCase b' O falseT) treeEqTagVarImpFalse

      treeEq_TVI_eq_falseT : Deriv (atomic (eqn (ap2 TreeEq tagVarT tagImpT) falseT))
      treeEq_TVI_eq_falseT =
        eqSubst (\ T -> Deriv (atomic (eqn (ap2 TreeEq tagVarT tagImpT) T)))
                treeEqTagVarImpToFalseT treeEqRedTV

      -- Substitute into eq_NN's IfLf condition.
      tail_pair : Term
      tail_pair = ap2 Pair (ap2 TreeEq natCodeNT (ap2 Pair X Y)) (ap2 Pair O O)

      eq_NN_falseT : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT orig)
        (ap2 IfLf falseT tail_pair)))
      eq_NN_falseT = ruleTrans eq_NN
        (congL IfLf tail_pair treeEq_TVI_eq_falseT)

      -- IfLf falseT (Pair x y) = y  via axIfLfN.  falseT = Pair O O.
      ifLfFalseT : Deriv (atomic (eqn
        (ap2 IfLf falseT tail_pair) (ap2 Pair O O)))
      ifLfFalseT = axIfLfN O O (ap2 TreeEq natCodeNT (ap2 Pair X Y))
                                (ap2 Pair O O)

      -- Combine: TreeEq varCodeT orig = Pair O O = falseT.
      treeEqVarOrig_to_falseT : Deriv (atomic (eqn
        (ap2 TreeEq varCodeT orig) falseT))
      treeEqVarOrig_to_falseT = ruleTrans eq_NN_falseT ifLfFalseT

      -- checkEqSubT to falseT (= Pair O O).
      checkEq_to_falseT : Deriv (atomic (eqn
        (ap2 checkEqSubT arg1 recs) falseT))
      checkEq_to_falseT = ruleTrans s3_check2 treeEqVarOrig_to_falseT

      -- Step 4: rewrite contSubT to Pair tT recs.
      s4_cont : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                    (ap2 Pair (ap1 Snd p) recs)))
      s4_cont = contAt p orig recs

      s4_cont_tT : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                       (ap2 Pair tT recs)))
      s4_cont_tT = ruleTrans s4_cont (congL Pair recs sndP)

      -- Combine the IfLf:
      ifLfBridge : Deriv (atomic (eqn
        (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                   (ap2 contSubT arg1 recs))
        (ap2 IfLf falseT (ap2 Pair tT recs))))
      ifLfBridge = ruleTrans
        (congL IfLf (ap2 contSubT arg1 recs) checkEq_to_falseT)
        (congR IfLf falseT s4_cont_tT)

      -- IfLf falseT (Pair tT recs) = recs.  falseT = Pair O O.
      ifLfRecs : Deriv (atomic (eqn (ap2 IfLf falseT (ap2 Pair tT recs)) recs))
      ifLfRecs = axIfLfN O O tT recs

      -- Combine s1 + s2 + ifLfBridge + ifLfRecs:
      step_to_recs : Deriv (atomic (eqn (ap2 subT p orig) recs))
      step_to_recs = ruleTrans s1 (ruleTrans s2 (ruleTrans ifLfBridge ifLfRecs))

      -- recs = Pair recA recB = Pair (subT p (reify tagImp)) (subT p (Pair X Y)).
      -- We need: Pair (reify tagImp) (Pair (subT p X) (subT p Y)).
      -- Bridge recA via subT_preserves_tagImp.
      recA_simp : Deriv (atomic (eqn recA tagImpT))
      recA_simp = subT_preserves_tagImp n tT

      -- Bridge recB: subT p (Pair X Y) by subT_node_unfold + treeEq evaluation.
      -- Hmm: this requires distribution of subT through (Pair X Y).
      -- For X, Y arbitrary Terms, the TreeEq comparison varCodeT vs (Pair X Y)
      -- depends on X, Y's structure.  We make this lemma parametric: state
      -- subT p (Pair X Y) is preserved as a Pair if treeEq (varCode) (Pair X Y)
      -- evaluates to falseT.
      --
      -- For subT_dist_Pair_tagImp specifically, our X, Y come from the
      -- f_part chain — they're outputs of previous subT applications.
      -- The CALLER will supply a subT_node_unfold-based bridge for this
      -- specific use site.
      --
      -- Strategy: define subT_dist_Pair_tagImp's RHS as
      --    Pair (reify tagImp) (subT p (Pair X Y))
      -- and let the caller chain a subT_dist_Pair_inner lemma for the
      -- (Pair X Y) component.

      -- Final result: bridge recA via subT_preserves_tagImp.
      finalBridge : Deriv (atomic (eqn recs (ap2 Pair tagImpT recB)))
      finalBridge = congL Pair recB recA_simp

  in ruleTrans step_to_recs finalBridge

----------------------------------------------------------------------
-- subT_dist_Pair_tagImp_full : fully-distributed version, requiring
-- the caller to certify that  subT (...)(Pair X Y) = Pair (subT X) (subT Y).
--
-- This is given by  subT_dist_Pair_inner  below, which handles the
-- (Pair X Y) inner case.

-- Inner Pair distribution: when treeEq varCodeT (Pair X Y) evaluates
-- to falseT, subT distributes.
--
-- The caller supplies the Eq-witness  treeEq (varCode) (... whatever
-- meta-tree X, Y have ...)  =  false .  For our use case (X, Y are
-- subT-applied-to-codeFormula-pieces), the meta-shape is determined
-- by codeFormula — this lemma states the local distribution given the
-- TreeEq result.

subT_dist_Pair_inner_via_TreeEq :
  (n : Nat) (tT : Term) (X Y : Term) ->
  -- Hypothesis: ap2 TreeEq varCodeT (Pair X Y) is BRA-equal to falseT.
  Deriv (atomic (eqn
    (ap2 TreeEq (reify (code (var n))) (ap2 Pair X Y)) falseT)) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) (ap2 Pair X Y))
    (ap2 Pair
       (ap2 subT (ap2 Pair (reify (code (var n))) tT) X)
       (ap2 subT (ap2 Pair (reify (code (var n))) tT) Y))))
subT_dist_Pair_inner_via_TreeEq n tT X Y treeEqFalse =
  let
      varCodeT : Term
      varCodeT = reify (code (var n))

      p : Term
      p = ap2 Pair varCodeT tT

      orig : Term
      orig = ap2 Pair X Y

      arg1 : Term
      arg1 = ap2 Pair p orig

      recA : Term
      recA = ap2 subT p X

      recB : Term
      recB = ap2 subT p Y

      recs : Term
      recs = ap2 Pair recA recB

      s1 : Deriv (atomic (eqn (ap2 subT p orig) (ap2 stepSubT arg1 recs)))
      s1 = axRecPNd stepSubT p X Y

      s2 : Deriv (atomic (eqn (ap2 stepSubT arg1 recs)
                              (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                                         (ap2 contSubT arg1 recs))))
      s2 = axFan checkEqSubT contSubT IfLf arg1 recs

      fstP : Deriv (atomic (eqn (ap1 Fst p) varCodeT))
      fstP = axFst varCodeT tT

      sndP : Deriv (atomic (eqn (ap1 Snd p) tT))
      sndP = axSnd varCodeT tT

      s3_check : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                     (ap2 TreeEq (ap1 Fst p) orig)))
      s3_check = checkEqAt p orig recs

      s3_check2 : Deriv (atomic (eqn (ap2 checkEqSubT arg1 recs)
                                      (ap2 TreeEq varCodeT orig)))
      s3_check2 = ruleTrans s3_check (congL TreeEq orig fstP)

      checkEq_to_falseT : Deriv (atomic (eqn
        (ap2 checkEqSubT arg1 recs) falseT))
      checkEq_to_falseT = ruleTrans s3_check2 treeEqFalse

      s4_cont : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                    (ap2 Pair (ap1 Snd p) recs)))
      s4_cont = contAt p orig recs

      s4_cont_tT : Deriv (atomic (eqn (ap2 contSubT arg1 recs)
                                       (ap2 Pair tT recs)))
      s4_cont_tT = ruleTrans s4_cont (congL Pair recs sndP)

      ifLfBridge : Deriv (atomic (eqn
        (ap2 IfLf (ap2 checkEqSubT arg1 recs)
                   (ap2 contSubT arg1 recs))
        (ap2 IfLf falseT (ap2 Pair tT recs))))
      ifLfBridge = ruleTrans
        (congL IfLf (ap2 contSubT arg1 recs) checkEq_to_falseT)
        (congR IfLf falseT s4_cont_tT)

      ifLfRecs : Deriv (atomic (eqn (ap2 IfLf falseT (ap2 Pair tT recs)) recs))
      ifLfRecs = axIfLfN O O tT recs

  in ruleTrans s1 (ruleTrans s2 (ruleTrans ifLfBridge ifLfRecs))

----------------------------------------------------------------------
-- subT_preserves_tagNeg : closed passthrough for tagNeg.
--
-- tagNeg = nd (nd lf lf) lf .  Distribute via subT_node_no_match (the
-- outer head shape mismatches code(var n) at the first child level)
-- + subT_node_no_match on the inner (nd lf lf) + subT_leaf on the
-- (lf, lf) leaves.

subT_preserves_tagNeg : (n : Nat) (tT : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify tagNeg))
    (reify tagNeg)))
subT_preserves_tagNeg n tT =
  let
      p : Term
      p = ap2 Pair (reify (code (var n))) tT

      -- tagNeg = nd (nd lf lf) lf .
      -- Outer no-match split: (a = nd lf lf, b = lf).
      step1 : Deriv (atomic (eqn
        (ap2 subT p (reify (nd (nd lf lf) lf)))
        (ap2 Pair (ap2 subT p (reify (nd lf lf)))
                  (ap2 subT p (reify lf)))))
      step1 = subT_node_no_match n tT (nd lf lf) (valNd lf lf valO valO)
                                       lf valO refl

      step2_inner : Deriv (atomic (eqn
        (ap2 subT p (reify (nd lf lf)))
        (ap2 Pair (ap2 subT p (reify lf)) (ap2 subT p (reify lf)))))
      step2_inner = subT_node_no_match n tT lf valO lf valO refl

      step2_leaf : Deriv (atomic (eqn (ap2 subT p (reify lf)) (reify lf)))
      step2_leaf = subT_leaf p

      step2 : Deriv (atomic (eqn (ap2 subT p (reify (nd lf lf)))
                                  (reify (nd lf lf))))
      step2 = ruleTrans step2_inner
                (ruleTrans (congL Pair (ap2 subT p (reify lf)) step2_leaf)
                           (congR Pair (reify lf) step2_leaf))

      -- Combine: outer Pair becomes Pair (reify (nd lf lf)) (reify lf) =
      -- reify (nd (nd lf lf) lf) = reify tagNeg.
      step3 : Deriv (atomic (eqn
        (ap2 Pair (ap2 subT p (reify (nd lf lf)))
                  (ap2 subT p (reify lf)))
        (ap2 Pair (reify (nd lf lf)) (reify lf))))
      step3 = ruleTrans (congL Pair (ap2 subT p (reify lf)) step2)
                        (congR Pair (reify (nd lf lf)) step2_leaf)

  in ruleTrans step1 step3

----------------------------------------------------------------------
-- subT_codeFormula_neg : subT distributes structurally on
-- reify (codeFormula (not P)) , preserving the tagNeg head and
-- exposing the inner codeFormula P .
--
--   subT (Pair (reify (code (var n))) tT) (reify (codeFormula (not P)))
--     =  Pair (reify tagNeg)
--             (subT ... (reify (codeFormula P)))

subT_codeFormula_neg : (n : Nat) (tT : Term) (P : Formula) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT)
              (reify (codeFormula (not P))))
    (ap2 Pair (reify tagNeg)
              (ap2 subT (ap2 Pair (reify (code (var n))) tT)
                         (reify (codeFormula P))))))
subT_codeFormula_neg n tT P =
  let
      p : Term
      p = ap2 Pair (reify (code (var n))) tT

      cP : Tree
      cP = codeFormula P

      -- Step 1: outer no-match at (tagNeg, cP).  Mismatch at head
      -- via treeEq_codeVar_tagNegHead.
      step1 : Deriv (atomic (eqn
        (ap2 subT p (reify (nd tagNeg cP)))
        (ap2 Pair (ap2 subT p (reify tagNeg))
                  (ap2 subT p (reify cP)))))
      step1 = subT_node_no_match n tT tagNeg tagNeg_isValue
                                       cP (codeFormula_isValue P)
                                       (treeEq_codeVar_tagNegHead n cP)

      -- Step 2: subT p (reify tagNeg) = reify tagNeg .
      step2 : Deriv (atomic (eqn (ap2 subT p (reify tagNeg))
                                  (reify tagNeg)))
      step2 = subT_preserves_tagNeg n tT

      -- Step 3: bridge.
      step3 : Deriv (atomic (eqn
        (ap2 Pair (ap2 subT p (reify tagNeg)) (ap2 subT p (reify cP)))
        (ap2 Pair (reify tagNeg)               (ap2 subT p (reify cP)))))
      step3 = congL Pair (ap2 subT p (reify cP)) step2

  in ruleTrans step1 step3

----------------------------------------------------------------------
-- subT_codeFormula_atomic : subT distributes structurally on
-- reify (codeFormula (atomic (eqn a b))) = reify (nd (code a) (code b)) .
--
--   subT (Pair (reify (code (var n))) tT) (reify (codeFormula (atomic (eqn a b))))
--     =  Pair (subT (...) (reify (code a))) (subT (...) (reify (code b)))
--
-- Proof: subT_node_no_match at (code a, code b).  The TreeEq mismatch
-- is provided by code_atomic_pair_no_var (case-split on a's outer
-- constructor; tagVar mismatches every code-of-Term head shape).

subT_codeFormula_atomic : (n : Nat) (tT : Term) (a b : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT)
              (reify (codeFormula (atomic (eqn a b)))))
    (ap2 Pair
       (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify (code a)))
       (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify (code b))))))
subT_codeFormula_atomic n tT a b =
  subT_node_no_match n tT (code a) (code_isValue a)
                          (code b) (code_isValue b)
    (code_atomic_pair_no_var n a b)
  where
    -- treeEq (code (var n)) (nd (code a) (code b)) = false  for any
    -- Term a, b: case-split on a's outer constructor (4 cases).
    code_atomic_pair_no_var :
      (n : Nat) (a b : Term) ->
      Eq (treeEq (code (var n)) (nd (code a) (code b))) false
    code_atomic_pair_no_var n O           b = refl
    code_atomic_pair_no_var n (var _)     b = refl
    code_atomic_pair_no_var n (ap1 _ _)   b = refl
    code_atomic_pair_no_var n (ap2 _ _ _) b = refl

