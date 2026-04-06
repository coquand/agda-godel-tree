{-# OPTIONS --safe --without-K --exact-split #-}

-- substReify: substitution is identity on reified trees.
-- This is the key lemma for avoiding expensive refl-based
-- normalization on large closed terms like reify(crTC).

module Guard.SubstReify where

open import Guard.Base
open import Guard.Term
open import Guard.SubstTForCorrect using (closedSubstTFor)

------------------------------------------------------------------------
-- subst x r (reify t) = reify t
--
-- Proof: reify produces only O and ap2 Pair ... terms.
-- subst x r O = O (definitional).
-- substF2 x r Pair = Pair (definitional).
-- So subst passes through the entire reify output unchanged.

substReify : (x : Nat) (r : Term) (t : Tree) ->
  Eq (subst x r (reify t)) (reify t)
substReify x r lf = refl
substReify x r (nd a b) =
  eqCong2 (ap2 Pair) (substReify x r a) (substReify x r b)

------------------------------------------------------------------------
-- Corollary: substF1 x r (KT (reify t)) = KT (reify t)

substF1KTReify : (x : Nat) (r : Term) (t : Tree) ->
  Eq (substF1 x r (KT (reify t))) (KT (reify t))
substF1KTReify x r t = eqCong KT (substReify x r t)

------------------------------------------------------------------------
-- Compositional substF2 lemmas for closedSubstTFor step function.
--
-- closedSubstTFor repl tgt = Rec O cStep where cStep is built from
-- Fan, Lift, Post, KT, Const, Pair, IfLf, TreeEq, Fst, Snd.
--
-- When repl = reify rTree and tgt = reify tTree, all KT leaves
-- contain reify of some tree, so substF2 is identity on cStep.

-- Helper: substF2 on Lift (KT (reify t))
substF2LiftKTReify : (x : Nat) (r : Term) (t : Tree) ->
  Eq (substF2 x r (Lift (KT (reify t)))) (Lift (KT (reify t)))
substF2LiftKTReify x r t = eqCong Lift (substF1KTReify x r t)

-- The full step function of closedSubstTFor
cStepOf : Term -> Term -> Fun2
cStepOf repl tgt =
  Fan (Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq)
      (Fan (Fan (Fan (Lift Snd) (Lift (KT tgt)) TreeEq)
                (Fan (Lift (KT repl)) Const Pair) IfLf)
           (Post Snd Pair) Pair) IfLf

-- substF2 is identity on the inner matchTgt+replOrig layer
private
  -- D = Fan (Lift Snd) (Lift (KT tgt)) TreeEq
  substD : (x : Nat) (r : Term) (tgtT : Tree) ->
    Eq (substF2 x r (Fan (Lift Snd) (Lift (KT (reify tgtT))) TreeEq))
       (Fan (Lift Snd) (Lift (KT (reify tgtT))) TreeEq)
  substD x r tgtT = eqCong (\h -> Fan (Lift Snd) h TreeEq)
                            (substF2LiftKTReify x r tgtT)

  -- E = Fan (Lift (KT repl)) Const Pair
  substE : (x : Nat) (r : Term) (replT : Tree) ->
    Eq (substF2 x r (Fan (Lift (KT (reify replT))) Const Pair))
       (Fan (Lift (KT (reify replT))) Const Pair)
  substE x r replT = eqCong (\h -> Fan h Const Pair)
                             (substF2LiftKTReify x r replT)

  -- C = Fan D E IfLf
  substC : (x : Nat) (r : Term) (replT tgtT : Tree) ->
    Eq (substF2 x r (Fan (Fan (Lift Snd) (Lift (KT (reify tgtT))) TreeEq)
                         (Fan (Lift (KT (reify replT))) Const Pair) IfLf))
       (Fan (Fan (Lift Snd) (Lift (KT (reify tgtT))) TreeEq)
            (Fan (Lift (KT (reify replT))) Const Pair) IfLf)
  substC x r replT tgtT =
    eqCong2 (\d e -> Fan d e IfLf)
            (substD x r tgtT) (substE x r replT)

  -- A = Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq
  substA : (x : Nat) (r : Term) ->
    Eq (substF2 x r (Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq))
       (Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq)
  substA x r = eqCong (\h -> Fan (Lift Fst) h TreeEq)
                       (substF2LiftKTReify x r tagVar)

  -- B = Fan C (Post Snd Pair) Pair
  substB : (x : Nat) (r : Term) (replT tgtT : Tree) ->
    Eq (substF2 x r (Fan (Fan (Fan (Lift Snd) (Lift (KT (reify tgtT))) TreeEq)
                              (Fan (Lift (KT (reify replT))) Const Pair) IfLf)
                         (Post Snd Pair) Pair))
       (Fan (Fan (Fan (Lift Snd) (Lift (KT (reify tgtT))) TreeEq)
                 (Fan (Lift (KT (reify replT))) Const Pair) IfLf)
            (Post Snd Pair) Pair)
  substB x r replT tgtT =
    eqCong (\c -> Fan c (Post Snd Pair) Pair)
           (substC x r replT tgtT)

------------------------------------------------------------------------
-- Main result: substF2 is identity on the full cStep

substCStep : (x : Nat) (r : Term) (replT tgtT : Tree) ->
  Eq (substF2 x r (cStepOf (reify replT) (reify tgtT)))
     (cStepOf (reify replT) (reify tgtT))
substCStep x r replT tgtT =
  eqCong2 (\a b -> Fan a b IfLf)
           (substA x r) (substB x r replT tgtT)

------------------------------------------------------------------------
-- substF1 is identity on closedSubstTFor when args are reified trees

-- Verify cStepOf matches the where-clause of closedSubstTFor
cStepCheck : (repl tgt : Term) ->
  Eq (closedSubstTFor repl tgt) (Rec O (cStepOf repl tgt))
cStepCheck repl tgt = refl

-- substF1 is identity on closedSubstTFor when args are reified trees
substClosedSTF : (x : Nat) (r : Term) (replT tgtT : Tree) ->
  Eq (substF1 x r (closedSubstTFor (reify replT) (reify tgtT)))
     (closedSubstTFor (reify replT) (reify tgtT))
substClosedSTF x r replT tgtT =
  eqCong (Rec O) (substCStep x r replT tgtT)
