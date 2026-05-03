{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14SubTLeaf
--
-- Phase C step 3 leaf-level lemmas (NEXT-SESSION-PHASE-C-STEP3.md).
--
-- Provides Aux 1 (varCode preservation) and Aux 2 (closed reify-of-tree
-- preservation) lemmas for the structural distribution of subT in the
-- step3 canonicalization.
--
-- The recursive meta-induction lemmas  codedSubstT_codeReify  /
-- codedSubst_codeReify_passthrough  /  codedSubstT_reify_codeA  are
-- placed in `abstract` blocks so Agda treats them as opaque outside the
-- file.  This keeps typecheck times for downstream consumers (Stages
-- A/B/C in Th14Step3Canon) linear in the meta-tree size, rather than
-- exploding as Agda tries to evaluate codeFormula G.
--
-- ASCII only.  No postulates, no holes, no with-abstraction, no dot
-- patterns.

module BRA.Th14SubTLeaf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.SubT     using (subT)
open import BRA.SbParam  using (subTDefParam ; codedSubstT)

----------------------------------------------------------------------
-- Generic combinator: subT preservation via meta-Eq witness on codedSubstT.

subT_preserves_via_meta :
  (n : Nat) (repl : Term) (codeP : Tree) ->
  Eq (codedSubstT repl (code (var n)) codeP) (reify codeP) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) repl) (reify codeP))
                      (reify codeP)))
subT_preserves_via_meta n repl codeP witness =
  eqSubst (\ T -> Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) repl) (reify codeP)) T)))
          witness
          (subTDefParam repl n codeP)

-- General version: bridge to an explicit target Term via a meta-Eq.

subT_to_meta :
  (n : Nat) (repl : Term) (codeP : Tree) (target : Term) ->
  Eq (codedSubstT repl (code (var n)) codeP) target ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) repl) (reify codeP))
                      target))
subT_to_meta n repl codeP target witness =
  eqSubst (\ T -> Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) repl) (reify codeP)) T)))
          witness
          (subTDefParam repl n codeP)

----------------------------------------------------------------------
-- Aux 1: varCode preservation.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

  varCode2T : Term
  varCode2T = reify (code (var (suc (suc zero))))

sub_v2_v0 : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode2T tT) varCode0T) varCode0T))
sub_v2_v0 tT =
  subT_preserves_via_meta (suc (suc zero)) tT (code (var zero)) refl

sub_v2_v1 : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode2T tT) varCode1T) varCode1T))
sub_v2_v1 tT =
  subT_preserves_via_meta (suc (suc zero)) tT (code (var (suc zero))) refl

sub_v1_v0 : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode1T tT) varCode0T) varCode0T))
sub_v1_v0 tT =
  subT_preserves_via_meta (suc zero) tT (code (var zero)) refl

sub_v1_v2 : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode1T tT) varCode2T) varCode2T))
sub_v1_v2 tT =
  subT_preserves_via_meta (suc zero) tT (code (var (suc (suc zero)))) refl

sub_v0_v1 : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode0T tT) varCode1T) varCode1T))
sub_v0_v1 tT =
  subT_preserves_via_meta zero tT (code (var (suc zero))) refl

sub_v0_v2 : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode0T tT) varCode2T) varCode2T))
sub_v0_v2 tT =
  subT_preserves_via_meta zero tT (code (var (suc (suc zero)))) refl

----------------------------------------------------------------------
-- Aux 1 (cont.): tagImp preservation.

sub_v0_tagImp : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode0T tT) (reify tagImp)) (reify tagImp)))
sub_v0_tagImp tT =
  subT_preserves_via_meta zero tT tagImp refl

sub_v1_tagImp : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode1T tT) (reify tagImp)) (reify tagImp)))
sub_v1_tagImp tT =
  subT_preserves_via_meta (suc zero) tT tagImp refl

sub_v2_tagImp : (tT : Term) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode2T tT) (reify tagImp)) (reify tagImp)))
sub_v2_tagImp tT =
  subT_preserves_via_meta (suc (suc zero)) tT tagImp refl

----------------------------------------------------------------------
-- Aux 2: closed reify preservation (the meta-induction on Tree T).
--
-- Wrapped in `abstract` blocks so they don't unfold at call sites.

abstract

  treeEq_tagVar_codeReify_false : (T : Tree) ->
    Eq (treeEq tagVar (code (reify T))) false
  treeEq_tagVar_codeReify_false lf       = refl
  treeEq_tagVar_codeReify_false (nd a b) = refl

  codedSubstT_codeReify : (repl : Term) (n : Nat) (T : Tree) ->
    Eq (codedSubstT repl (code (var n)) (code (reify T))) (reify (code (reify T)))
  codedSubstT_codeReify repl n lf       = refl
  codedSubstT_codeReify repl n (nd a b) =
    let
        ihA : Eq (codedSubstT repl (code (var n)) (code (reify a))) (reify (code (reify a)))
        ihA = codedSubstT_codeReify repl n a

        ihB : Eq (codedSubstT repl (code (var n)) (code (reify b))) (reify (code (reify b)))
        ihB = codedSubstT_codeReify repl n b

        X : Term
        X = codedSubstT repl (code (var n)) (code (reify a))

        Y : Term
        Y = codedSubstT repl (code (var n)) (code (reify b))

        tev_false : Eq (boolAnd (treeEq tagVar (code (reify a)))
                                (treeEq (natCode n) (code (reify b))))
                       false
        tev_false = eqCong (\ b' -> boolAnd b' (treeEq (natCode n) (code (reify b))))
                           (treeEq_tagVar_codeReify_false a)

        boolCase_eq : Eq (boolCase (boolAnd (treeEq tagVar (code (reify a)))
                                            (treeEq (natCode n) (code (reify b))))
                                   repl
                                   (ap2 Pair X Y))
                         (ap2 Pair X Y)
        boolCase_eq = eqCong (\ b' -> boolCase b' repl (ap2 Pair X Y)) tev_false

        xy_eq : Eq (ap2 Pair X Y)
                   (ap2 Pair (reify (code (reify a))) (reify (code (reify b))))
        xy_eq = eqCong2 (ap2 Pair) ihA ihB

        inner_eq : Eq (boolCase (boolAnd (treeEq tagVar (code (reify a)))
                                         (treeEq (natCode n) (code (reify b))))
                                repl
                                (ap2 Pair X Y))
                      (ap2 Pair (reify (code (reify a))) (reify (code (reify b))))
        inner_eq = eqTrans boolCase_eq xy_eq

    in eqCong (\ Z -> ap2 Pair (reify tagAp2)
                               (ap2 Pair (reify (codeF2 Pair)) Z))
              inner_eq

  codedSubst_codeReify_passthrough : (codeA : Tree) (n : Nat) (T : Tree) ->
    Eq (codedSubst codeA (code (var n)) (code (reify T))) (code (reify T))
  codedSubst_codeReify_passthrough codeA n lf       = refl
  codedSubst_codeReify_passthrough codeA n (nd a b) =
    let
        ihA : Eq (codedSubst codeA (code (var n)) (code (reify a))) (code (reify a))
        ihA = codedSubst_codeReify_passthrough codeA n a

        ihB : Eq (codedSubst codeA (code (var n)) (code (reify b))) (code (reify b))
        ihB = codedSubst_codeReify_passthrough codeA n b

        A : Tree
        A = codedSubst codeA (code (var n)) (code (reify a))

        B : Tree
        B = codedSubst codeA (code (var n)) (code (reify b))

        tev_false : Eq (boolAnd (treeEq tagVar (code (reify a)))
                                (treeEq (natCode n) (code (reify b))))
                       false
        tev_false = eqCong (\ b' -> boolAnd b' (treeEq (natCode n) (code (reify b))))
                           (treeEq_tagVar_codeReify_false a)

        boolCase_eq : Eq (boolCase (boolAnd (treeEq tagVar (code (reify a)))
                                            (treeEq (natCode n) (code (reify b))))
                                   codeA
                                   (nd A B))
                         (nd A B)
        boolCase_eq = eqCong (\ b' -> boolCase b' codeA (nd A B)) tev_false

        ab_eq : Eq (nd A B) (nd (code (reify a)) (code (reify b)))
        ab_eq = eqCong2 nd ihA ihB

        inner_eq : Eq (boolCase (boolAnd (treeEq tagVar (code (reify a)))
                                         (treeEq (natCode n) (code (reify b))))
                                codeA
                                (nd A B))
                      (nd (code (reify a)) (code (reify b)))
        inner_eq = eqTrans boolCase_eq ab_eq
    in eqCong (\ Z -> nd tagAp2 (nd (codeF2 Pair) Z))
              inner_eq

  codedSubstT_reify_codeA : (codeA : Tree) (n : Nat) (codeP : Tree) ->
    Eq (codedSubstT (reify codeA) (code (var n)) codeP)
       (reify (codedSubst codeA (code (var n)) codeP))
  codedSubstT_reify_codeA codeA n lf       = refl
  codedSubstT_reify_codeA codeA n (nd a b) =
    finishCase (treeEq (code (var n)) (nd a b))
    where
      ihA : Eq (codedSubstT (reify codeA) (code (var n)) a)
               (reify (codedSubst codeA (code (var n)) a))
      ihA = codedSubstT_reify_codeA codeA n a

      ihB : Eq (codedSubstT (reify codeA) (code (var n)) b)
               (reify (codedSubst codeA (code (var n)) b))
      ihB = codedSubstT_reify_codeA codeA n b

      reifyA' : Term
      reifyA' = codedSubstT (reify codeA) (code (var n)) a

      reifyB' : Term
      reifyB' = codedSubstT (reify codeA) (code (var n)) b

      branch_eq : Eq (ap2 Pair reifyA' reifyB')
                     (ap2 Pair (reify (codedSubst codeA (code (var n)) a))
                               (reify (codedSubst codeA (code (var n)) b)))
      branch_eq = eqCong2 (ap2 Pair) ihA ihB

      finishCase : (b' : Bool) ->
        Eq (boolCase b' (reify codeA) (ap2 Pair reifyA' reifyB'))
           (reify (boolCase b' codeA
                            (nd (codedSubst codeA (code (var n)) a)
                                (codedSubst codeA (code (var n)) b))))
      finishCase true  = refl
      finishCase false = branch_eq

----------------------------------------------------------------------
-- Aux 2: subT preservation for (reify (code (reify T))) for any Tree T.

subT_preserves_codeReify :
  (n : Nat) (tT : Term) (T : Tree) ->
  Deriv (atomic (eqn (ap2 subT (ap2 Pair (reify (code (var n))) tT)
                                (reify (code (reify T))))
                      (reify (code (reify T)))))
subT_preserves_codeReify n tT T =
  subT_preserves_via_meta n tT (code (reify T)) (codedSubstT_codeReify tT n T)

----------------------------------------------------------------------
-- Aux 2 extended: codedSubstT preserves  code (ap2 g (reify ja) (reify jb))
-- when codeF2 g doesn't contain (code (var n)).
--
-- Used for encoded_sub_ii = reify (code (ap2 sub i i)) with i = reify j.
--
-- The proof chains through tagAp2 (closed), codeF2 g (closed by hypothesis),
-- and the two (code (reify j_*)) leaves (via codedSubstT_codeReify).

abstract

  treeEq_codeVar_tagAp2_false : (n : Nat) (rest : Tree) ->
    Eq (treeEq (code (var n)) (nd tagAp2 rest)) false
  treeEq_codeVar_tagAp2_false n rest = refl

  -- Key lemma for the encoded_sub_ii case: codedSubstT preserves
  -- (code (ap2 g (reify ja) (reify jb))) when:
  --   (i)  codeF2 g is preserved (closed eval witness).
  --   (ii) treeEq tagVar (codeF2 g) = false (head check).
  -- Both hypotheses are typically `refl` for closed concrete g.

  codedSubstT_code_ap2_reify_reify :
    (repl : Term) (n : Nat) (g : Fun2) (ja jb : Tree) ->
    Eq (codedSubstT repl (code (var n)) (codeF2 g)) (reify (codeF2 g)) ->
    Eq (treeEq tagVar (codeF2 g)) false ->
    Eq (codedSubstT repl (code (var n)) (code (ap2 g (reify ja) (reify jb))))
       (reify (code (ap2 g (reify ja) (reify jb))))
  codedSubstT_code_ap2_reify_reify repl n g ja jb codeF2_eq tev_codeF2_g_false =
    let
        ih_a : Eq (codedSubstT repl (code (var n)) (code (reify ja))) (reify (code (reify ja)))
        ih_a = codedSubstT_codeReify repl n ja

        ih_b : Eq (codedSubstT repl (code (var n)) (code (reify jb))) (reify (code (reify jb)))
        ih_b = codedSubstT_codeReify repl n jb

        -- Inner Pair: nd (code (reify ja)) (code (reify jb)).
        -- treeEq false (since treeEq tagVar (code (reify ja)) = false).
        innerJ_X : Term
        innerJ_X = codedSubstT repl (code (var n)) (code (reify ja))

        innerJ_Y : Term
        innerJ_Y = codedSubstT repl (code (var n)) (code (reify jb))

        innerJ_false : Eq (boolAnd (treeEq tagVar (code (reify ja)))
                                   (treeEq (natCode n) (code (reify jb))))
                          false
        innerJ_false = eqCong (\ b' -> boolAnd b' (treeEq (natCode n) (code (reify jb))))
                              (treeEq_tagVar_codeReify_false ja)

        innerJ_boolCase : Eq (boolCase (boolAnd (treeEq tagVar (code (reify ja)))
                                                (treeEq (natCode n) (code (reify jb))))
                                       repl
                                       (ap2 Pair innerJ_X innerJ_Y))
                             (ap2 Pair innerJ_X innerJ_Y)
        innerJ_boolCase = eqCong (\ b' -> boolCase b' repl (ap2 Pair innerJ_X innerJ_Y))
                                 innerJ_false

        innerJ_xy_eq : Eq (ap2 Pair innerJ_X innerJ_Y)
                          (ap2 Pair (reify (code (reify ja))) (reify (code (reify jb))))
        innerJ_xy_eq = eqCong2 (ap2 Pair) ih_a ih_b

        innerJ_eq : Eq (boolCase (boolAnd (treeEq tagVar (code (reify ja)))
                                          (treeEq (natCode n) (code (reify jb))))
                                 repl
                                 (ap2 Pair innerJ_X innerJ_Y))
                       (ap2 Pair (reify (code (reify ja))) (reify (code (reify jb))))
        innerJ_eq = eqTrans innerJ_boolCase innerJ_xy_eq

        -- Middle: codedSubstT _ (nd (codeF2 g) (nd (code (reify ja)) (code (reify jb)))).
        -- After Agda's reductions, this becomes:
        --   boolCase (boolAnd (treeEq tagVar (codeF2 g)) (treeEq (natCode n) (nd (code (reify ja)) (code (reify jb)))))
        --            repl
        --            (ap2 Pair (codedSubstT _ (codeF2 g)) (codedSubstT _ (nd (code (reify ja)) (code (reify jb)))))
        --
        -- We need this to equal:
        --   ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code (reify ja))) (reify (code (reify jb))))
        midM_X : Term
        midM_X = codedSubstT repl (code (var n)) (codeF2 g)

        midM_Y : Term
        midM_Y = codedSubstT repl (code (var n)) (nd (code (reify ja)) (code (reify jb)))

        midM_false : Eq (boolAnd (treeEq tagVar (codeF2 g))
                                 (treeEq (natCode n) (nd (code (reify ja)) (code (reify jb)))))
                        false
        midM_false = eqCong (\ b' -> boolAnd b' (treeEq (natCode n) (nd (code (reify ja)) (code (reify jb)))))
                            tev_codeF2_g_false

        midM_boolCase : Eq (boolCase (boolAnd (treeEq tagVar (codeF2 g))
                                              (treeEq (natCode n) (nd (code (reify ja)) (code (reify jb)))))
                                     repl
                                     (ap2 Pair midM_X midM_Y))
                           (ap2 Pair midM_X midM_Y)
        midM_boolCase = eqCong (\ b' -> boolCase b' repl (ap2 Pair midM_X midM_Y)) midM_false

        midM_xy_eq : Eq (ap2 Pair midM_X midM_Y)
                        (ap2 Pair (reify (codeF2 g))
                                  (ap2 Pair (reify (code (reify ja))) (reify (code (reify jb)))))
        midM_xy_eq = eqCong2 (ap2 Pair) codeF2_eq innerJ_eq

        midM_eq : Eq (boolCase (boolAnd (treeEq tagVar (codeF2 g))
                                        (treeEq (natCode n) (nd (code (reify ja)) (code (reify jb)))))
                               repl
                               (ap2 Pair midM_X midM_Y))
                     (ap2 Pair (reify (codeF2 g))
                               (ap2 Pair (reify (code (reify ja))) (reify (code (reify jb)))))
        midM_eq = eqTrans midM_boolCase midM_xy_eq

        -- Wrap with the outer Pair (reify tagAp2) (...).  Outer treeEq tagVar tagAp2 = false (closed eval).
    in eqCong (\ Z -> ap2 Pair (reify tagAp2) Z) midM_eq

