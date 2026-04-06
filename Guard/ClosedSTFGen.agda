{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ClosedSTFGen where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect
open import Guard.SubstTForCorrect

------------------------------------------------------------------------
-- Generalized closedSTFCode: works with repl : Term and
-- replEq : Deriv hyp (eqn repl (reify replT)) instead of
-- requiring repl = reify replT definitionally.
--
-- The proof mirrors closedSTFCode exactly, differing only at
-- variable-match points where replEq is used instead of axRefl.

private
  poo : Term
  poo = ap2 Pair O O

  tagVarT : Term
  tagVarT = reify tagVar

------------------------------------------------------------------------
-- Generalized closedSTFNd

closedSTFNdGen : (repl : Term) (replT tgtT a b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify a) tagVarT) poo) ->
  Eq (treeEq a tagVar) false ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify a)) (reify (codedSubst replT tgtT a))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (ap2 Pair (reify a) (reify b))) (reify (codedSubst replT tgtT (nd a b))))
closedSTFNdGen repl replT tgtT a b neqD neqB ihA ihB =
  let cstf = closedSubstTFor repl (reify tgtT)
  in ruleTrans (stepNotVar repl (reify tgtT) (reify a) (reify b) neqD)
     (ruleTrans (congL Pair (ap1 cstf (reify b)) ihA)
     (ruleTrans (congR Pair (reify (codedSubst replT tgtT a)) ihB)
     (eqSubst (\v -> Deriv _ (eqn (ap2 Pair (reify (codedSubst replT tgtT a)) (reify (codedSubst replT tgtT b))) (reify v)))
              (eqSym (codedSubstNd replT tgtT a b neqB)) (axRefl _))))

------------------------------------------------------------------------
-- Convenience wrappers

closedSTFNdF1Gen : (repl : Term) (replT tgtT : Tree) (f : Fun1) (b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (codeF1 f))) (reify (codedSubst replT tgtT (codeF1 f)))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (ap2 Pair (reify (codeF1 f)) (reify b))) (reify (codedSubst replT tgtT (nd (codeF1 f) b))))
closedSTFNdF1Gen repl replT tgtT f b = closedSTFNdGen repl replT tgtT (codeF1 f) b (codeF1NeqTagVar f) (codeF1NotVar f)

closedSTFNdF2Gen : (repl : Term) (replT tgtT : Tree) (g : Fun2) (b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (codeF2 g))) (reify (codedSubst replT tgtT (codeF2 g)))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (ap2 Pair (reify (codeF2 g)) (reify b))) (reify (codedSubst replT tgtT (nd (codeF2 g) b))))
closedSTFNdF2Gen repl replT tgtT g b = closedSTFNdGen repl replT tgtT (codeF2 g) b (codeF2NeqTagVar g) (codeF2NotVar g)

closedSTFNdCodeGen : (repl : Term) (replT tgtT : Tree) (t : Term) (b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (code t))) (reify (codedSubst replT tgtT (code t)))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (ap2 Pair (reify (code t)) (reify b))) (reify (codedSubst replT tgtT (nd (code t) b))))
closedSTFNdCodeGen repl replT tgtT t b = closedSTFNdGen repl replT tgtT (code t) b (codeNeqTagVarGen t) (codeNotVar t)

closedSTFNatCodeGen : (repl : Term) (replT tgtT : Tree) (n : Nat) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (natCode n))) (reify (codedSubst replT tgtT (natCode n))))
closedSTFNatCodeGen repl replT tgtT zero = axRecLf O _
closedSTFNatCodeGen repl replT tgtT (suc n) = closedSTFNdGen repl replT tgtT lf (natCode n) oNeqTagVar refl (axRecLf O _) (closedSTFNatCodeGen repl replT tgtT n)

closedSTFTagAp1Gen : (repl : Term) (rT tT : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tT)) (reify tagAp1)) (reify (codedSubst rT tT tagAp1)))
closedSTFTagAp1Gen repl rT tT = closedSTFNdGen repl rT tT lf (nd lf lf) oNeqTagVar refl (axRecLf O _) (closedSTFNdGen repl rT tT lf lf oNeqTagVar refl (axRecLf O _) (axRecLf O _))

closedSTFTagAp2Gen : (repl : Term) (rT tT : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tT)) (reify tagAp2)) (reify (codedSubst rT tT tagAp2)))
closedSTFTagAp2Gen repl rT tT = closedSTFNdGen repl rT tT lf (nd lf (nd lf lf)) oNeqTagVar refl (axRecLf O _) (closedSTFNdGen repl rT tT lf (nd lf lf) oNeqTagVar refl (axRecLf O _) (closedSTFNdGen repl rT tT lf lf oNeqTagVar refl (axRecLf O _) (axRecLf O _)))

------------------------------------------------------------------------
-- Mutual induction (abstract to prevent normalization blowup)

abstract
 closedSTFCodeGen : (repl : Term) (replT tgtT : Tree) (l : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn repl (reify replT)) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (code l))) (reify (codedSubst replT tgtT (code l))))
 closedSTFF1Gen : (repl : Term) (replT tgtT : Tree) (f : Fun1) -> {hyp : Equation} ->
  Deriv hyp (eqn repl (reify replT)) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (codeF1 f))) (reify (codedSubst replT tgtT (codeF1 f))))
 closedSTFF2Gen : (repl : Term) (replT tgtT : Tree) (g : Fun2) -> {hyp : Equation} ->
  Deriv hyp (eqn repl (reify replT)) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor repl (reify tgtT)) (reify (codeF2 g))) (reify (codedSubst replT tgtT (codeF2 g))))

 -- O
 closedSTFCodeGen repl replT tgtT O rEq = closedSTFNdGen repl replT tgtT lf lf oNeqTagVar refl (axRecLf O _) (axRecLf O _)

 -- var n: the ONLY case that differs from closedSTFCode.
 closedSTFCodeGen repl replT tgtT (var n) {hyp} rEq =
  ruleTrans (stepIsVar repl (reify tgtT) (reify (natCode n)))
  (ruleTrans (ifLfTreeEq (natCode n) tgtT repl (ap2 Pair (reify tagVar) (reify (natCode n))))
  (varCase (treeEq (natCode n) tgtT) refl))
  where
  varCase : (v : Bool) -> Eq (treeEq (natCode n) tgtT) v ->
    Deriv hyp (eqn (boolCase v repl (ap2 Pair (reify tagVar) (reify (natCode n))))
                   (reify (codedSubst replT tgtT (nd tagVar (natCode n)))))
  varCase true p =
    eqSubst (\w -> Deriv hyp (eqn repl (reify (boolCase w replT (nd tagVar (natCode n)))))) (eqSym p) rEq
  varCase false p =
    eqSubst (\w -> Deriv hyp (eqn (ap2 Pair (reify tagVar) (reify (natCode n))) (reify (boolCase w replT (nd tagVar (natCode n)))))) (eqSym p) (axRefl _)

 -- ap1
 closedSTFCodeGen repl replT tgtT (ap1 f t) rEq =
  closedSTFNdGen repl replT tgtT tagAp1 (nd (codeF1 f) (code t)) tagAp1NeqTagVar refl
    (closedSTFTagAp1Gen repl replT tgtT)
    (closedSTFNdF1Gen repl replT tgtT f (code t) (closedSTFF1Gen repl replT tgtT f rEq) (closedSTFCodeGen repl replT tgtT t rEq))

 -- ap2
 closedSTFCodeGen repl replT tgtT (ap2 g a b) rEq =
  closedSTFNdGen repl replT tgtT tagAp2 (nd (codeF2 g) (nd (code a) (code b))) tagAp2NeqTagVar refl
    (closedSTFTagAp2Gen repl replT tgtT)
    (closedSTFNdF2Gen repl replT tgtT g (nd (code a) (code b)) (closedSTFF2Gen repl replT tgtT g rEq)
      (closedSTFNdCodeGen repl replT tgtT a (code b) (closedSTFCodeGen repl replT tgtT a rEq) (closedSTFCodeGen repl replT tgtT b rEq)))

 -- Fun1 cases (n26-n32 defined inline to stay inside abstract)
 private
  n26' : Nat ; n26' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))
  n27' : Nat ; n27' = suc n26' ; n28' : Nat ; n28' = suc n27' ; n29' : Nat ; n29' = suc n28'
  n30' : Nat ; n30' = suc n29' ; n31' : Nat ; n31' = suc n30' ; n32' : Nat ; n32' = suc n31'

 closedSTFF1Gen repl replT tgtT I rEq = closedSTFNdGen repl replT tgtT (natCode n26') lf (natCodeNeqTagVar n26') refl (closedSTFNatCodeGen repl replT tgtT n26') (axRecLf O _)
 closedSTFF1Gen repl replT tgtT Fst rEq = closedSTFNdGen repl replT tgtT (natCode n27') lf (natCodeNeqTagVar n27') refl (closedSTFNatCodeGen repl replT tgtT n27') (axRecLf O _)
 closedSTFF1Gen repl replT tgtT Snd rEq = closedSTFNdGen repl replT tgtT (natCode n28') lf (natCodeNeqTagVar n28') refl (closedSTFNatCodeGen repl replT tgtT n28') (axRecLf O _)
 closedSTFF1Gen repl replT tgtT (Comp f g) rEq = closedSTFNdGen repl replT tgtT (natCode n29') _ (natCodeNeqTagVar n29') refl (closedSTFNatCodeGen repl replT tgtT n29') (closedSTFNdF1Gen repl replT tgtT f _ (closedSTFF1Gen repl replT tgtT f rEq) (closedSTFF1Gen repl replT tgtT g rEq))
 closedSTFF1Gen repl replT tgtT (Comp2 h f g) rEq = closedSTFNdGen repl replT tgtT (natCode n30') _ (natCodeNeqTagVar n30') refl (closedSTFNatCodeGen repl replT tgtT n30') (closedSTFNdF2Gen repl replT tgtT h _ (closedSTFF2Gen repl replT tgtT h rEq) (closedSTFNdF1Gen repl replT tgtT f _ (closedSTFF1Gen repl replT tgtT f rEq) (closedSTFF1Gen repl replT tgtT g rEq)))
 closedSTFF1Gen repl replT tgtT (Rec z s) rEq = closedSTFNdGen repl replT tgtT (natCode n31') _ (natCodeNeqTagVar n31') refl (closedSTFNatCodeGen repl replT tgtT n31') (closedSTFNdCodeGen repl replT tgtT z _ (closedSTFCodeGen repl replT tgtT z rEq) (closedSTFF2Gen repl replT tgtT s rEq))
 closedSTFF1Gen repl replT tgtT (KT t) rEq = closedSTFNdGen repl replT tgtT (natCode n32') _ (natCodeNeqTagVar n32') refl (closedSTFNatCodeGen repl replT tgtT n32') (closedSTFCodeGen repl replT tgtT t rEq)

 -- Fun2 cases
 closedSTFF2Gen repl replT tgtT Pair rEq = closedSTFNdGen repl replT tgtT (natCode n26') lf (natCodeNeqTagVar n26') refl (closedSTFNatCodeGen repl replT tgtT n26') (axRecLf O _)
 closedSTFF2Gen repl replT tgtT Const rEq = closedSTFNdGen repl replT tgtT (natCode n27') lf (natCodeNeqTagVar n27') refl (closedSTFNatCodeGen repl replT tgtT n27') (axRecLf O _)
 closedSTFF2Gen repl replT tgtT (Lift f) rEq = closedSTFNdGen repl replT tgtT (natCode n28') _ (natCodeNeqTagVar n28') refl (closedSTFNatCodeGen repl replT tgtT n28') (closedSTFF1Gen repl replT tgtT f rEq)
 closedSTFF2Gen repl replT tgtT (Post f h) rEq = closedSTFNdGen repl replT tgtT (natCode n29') _ (natCodeNeqTagVar n29') refl (closedSTFNatCodeGen repl replT tgtT n29') (closedSTFNdF1Gen repl replT tgtT f _ (closedSTFF1Gen repl replT tgtT f rEq) (closedSTFF2Gen repl replT tgtT h rEq))
 closedSTFF2Gen repl replT tgtT (Fan h1 h2 h) rEq = closedSTFNdGen repl replT tgtT (natCode n30') _ (natCodeNeqTagVar n30') refl (closedSTFNatCodeGen repl replT tgtT n30') (closedSTFNdF2Gen repl replT tgtT h1 _ (closedSTFF2Gen repl replT tgtT h1 rEq) (closedSTFNdF2Gen repl replT tgtT h2 _ (closedSTFF2Gen repl replT tgtT h2 rEq) (closedSTFF2Gen repl replT tgtT h rEq)))
 closedSTFF2Gen repl replT tgtT IfLf rEq = closedSTFNdGen repl replT tgtT (natCode n31') lf (natCodeNeqTagVar n31') refl (closedSTFNatCodeGen repl replT tgtT n31') (axRecLf O _)
 closedSTFF2Gen repl replT tgtT TreeEq rEq = closedSTFNdGen repl replT tgtT (natCode n32') lf (natCodeNeqTagVar n32') refl (closedSTFNatCodeGen repl replT tgtT n32') (axRecLf O _)
