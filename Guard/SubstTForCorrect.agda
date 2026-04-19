{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.SubstTForCorrect where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.SubstCorrect

------------------------------------------------------------------------
-- Closed substTFor: replacement repl and target tgt as parameters.

closedSubstTFor : Term -> Term -> Fun1
closedSubstTFor repl tgt = Rec O cStep
  where
  cStep : Fun2
  cStep = Fan (Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq)
              (Fan (Fan (Fan (Lift Snd) (Lift (KT tgt)) TreeEq)
                        (Fan (Lift (KT repl)) Const Pair) IfLf)
                   (Post Snd Pair) Pair) IfLf

------------------------------------------------------------------------
private
  tagVarT : Term ; tagVarT = reify tagVar
  poo : Term ; poo = ap2 Pair O O

------------------------------------------------------------------------
-- TreeEq helpers

tEqOO : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq O O) O)
tEqOO = axTreeEqLL

tEqPairOO : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq poo poo) O)
tEqPairOO = ruleTrans (axTreeEqNN O O O O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) tEqOO) (ruleTrans (axIfLfL (ap2 TreeEq O O) poo) tEqOO))

tagVarSelfEq : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq tagVarT tagVarT) O)
tagVarSelfEq =
  let tEqI : {h : Equation} -> Deriv h (eqn (ap2 TreeEq (ap2 Pair poo O) (ap2 Pair poo O)) O)
      tEqI = ruleTrans (axTreeEqNN poo O poo O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) tEqPairOO) (ruleTrans (axIfLfL (ap2 TreeEq O O) poo) tEqOO))
  in ruleTrans (axTreeEqNN (ap2 Pair poo O) O (ap2 Pair poo O) O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) tEqI) (ruleTrans (axIfLfL (ap2 TreeEq O O) poo) tEqOO))

oNeqTagVar : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq O tagVarT) poo)
oNeqTagVar = axTreeEqLN (ap2 Pair (ap2 Pair O O) O) O

tagAp1NeqTagVar : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq (reify tagAp1) tagVarT) poo)
tagAp1NeqTagVar = ruleTrans (axTreeEqNN O (ap2 Pair O O) (ap2 Pair (ap2 Pair O O) O) O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O O) O) poo) (axTreeEqLN (ap2 Pair O O) O)) (axIfLfN O O (ap2 TreeEq (ap2 Pair O O) O) poo))

tagAp2NeqTagVar : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq (reify tagAp2) tagVarT) poo)
tagAp2NeqTagVar = ruleTrans (axTreeEqNN O (ap2 Pair O (ap2 Pair O O)) (ap2 Pair (ap2 Pair O O) O) O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O (ap2 Pair O O)) O) poo) (axTreeEqLN (ap2 Pair O O) O)) (axIfLfN O O (ap2 TreeEq (ap2 Pair O (ap2 Pair O O)) O) poo))

-- reify(codeF1 f) always starts with Pair(Pair(O, X), Y) — inner pair starts with O
-- TreeEq(Pair(Pair(O,X),Y), tagVarT) = poo via two levels of comparison
f1f2NeqTagVar : (a2 b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair (ap2 Pair O a2) b) tagVarT) poo)
f1f2NeqTagVar a2 b =
  ruleTrans (axTreeEqNN (ap2 Pair O a2) b (ap2 Pair (ap2 Pair O O) O) O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq b O) poo)
    (ruleTrans (axTreeEqNN O a2 (ap2 Pair O O) O)
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq a2 O) poo) (axTreeEqLN O O))
               (axIfLfN O O (ap2 TreeEq a2 O) poo))))
  (axIfLfN O O (ap2 TreeEq b O) poo))

codeF1NeqTagVar : (f : Fun1) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq (reify (codeF1 f)) tagVarT) poo)
codeF1NeqTagVar I = f1f2NeqTagVar _ O
codeF1NeqTagVar Fst = f1f2NeqTagVar _ O
codeF1NeqTagVar Snd = f1f2NeqTagVar _ O
codeF1NeqTagVar (Comp f g) = f1f2NeqTagVar _ _
codeF1NeqTagVar (Comp2 h f g) = f1f2NeqTagVar _ _
codeF1NeqTagVar (Rec z s) = f1f2NeqTagVar _ _
codeF1NeqTagVar (KT t) = f1f2NeqTagVar _ _

codeF2NeqTagVar : (g : Fun2) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq (reify (codeF2 g)) tagVarT) poo)
codeF2NeqTagVar Pair = f1f2NeqTagVar _ O
codeF2NeqTagVar Const = f1f2NeqTagVar _ O
codeF2NeqTagVar (Lift f) = f1f2NeqTagVar _ _
codeF2NeqTagVar (Post f h) = f1f2NeqTagVar _ _
codeF2NeqTagVar (Fan h1 h2 h) = f1f2NeqTagVar _ _
codeF2NeqTagVar IfLf = f1f2NeqTagVar _ O
codeF2NeqTagVar TreeEq = f1f2NeqTagVar _ O
codeF2NeqTagVar (RecP s) = f1f2NeqTagVar _ _

codeNeqTagVarGen : (t : Term) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq (reify (code t)) tagVarT) poo)
codeNeqTagVarGen O =
  ruleTrans (axTreeEqNN O O (ap2 Pair (ap2 Pair O O) O) O)
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) (axTreeEqLN (ap2 Pair O O) O))
             (axIfLfN O O (ap2 TreeEq O O) poo))
codeNeqTagVarGen (var _) =
  let inner : {h : Equation} -> Deriv h (eqn (ap2 TreeEq tagVarT (ap2 Pair poo O)) poo)
      inner = ruleTrans (axTreeEqNN (ap2 Pair poo O) O poo O)
              (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo)
                (ruleTrans (axTreeEqNN poo O O O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) (axTreeEqNL O O)) (axIfLfN O O (ap2 TreeEq O O) poo))))
              (axIfLfN O O (ap2 TreeEq O O) poo))
  in ruleTrans (axTreeEqNN tagVarT _ (ap2 Pair poo O) O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq _ O) poo) inner) (axIfLfN O O (ap2 TreeEq _ O) poo))
codeNeqTagVarGen (ap1 f t) = f1f2NeqTagVar _ _
codeNeqTagVarGen (ap2 g a b) = f1f2NeqTagVar _ _

natCodeNeqTagVar : (n : Nat) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq (reify (natCode n)) tagVarT) poo)
natCodeNeqTagVar zero = oNeqTagVar
natCodeNeqTagVar (suc n) = ruleTrans (axTreeEqNN O (reify (natCode n)) (ap2 Pair (ap2 Pair O O) O) O) (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify (natCode n)) O) poo) (axTreeEqLN (ap2 Pair O O) O)) (axIfLfN O O (ap2 TreeEq (reify (natCode n)) O) poo))

------------------------------------------------------------------------
-- Step evaluation: when tag ≠ tagVar, step returns recs

stepNotVar : (repl tgt reifyA reifyB : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq reifyA tagVarT) poo) ->
  let cstf = closedSubstTFor repl tgt ; orig = ap2 Pair reifyA reifyB
      recT = ap2 Pair (ap1 cstf reifyA) (ap1 cstf reifyB)
  in Deriv hyp (eqn (ap1 cstf (ap2 Pair reifyA reifyB)) recT)
stepNotVar repl tgt reifyA reifyB neqPf =
  let cstf = closedSubstTFor repl tgt ; orig = ap2 Pair reifyA reifyB
      recT = ap2 Pair (ap1 cstf reifyA) (ap1 cstf reifyB)
      isVarF = Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq
      innerF = Fan (Fan (Lift Snd) (Lift (KT tgt)) TreeEq) (Fan (Lift (KT repl)) Const Pair) IfLf
      sndArgF = Post Snd Pair ; outerF = Fan innerF sndArgF Pair
      cStepF = Fan isVarF outerF IfLf
      isVarEval : Deriv _ (eqn (ap2 isVarF orig recT) (ap2 TreeEq reifyA (reify tagVar)))
      isVarEval = ruleTrans (fanRed (Lift Fst) (Lift (KT (reify tagVar))) TreeEq orig recT)
        (ruleTrans (congL TreeEq (ap2 (Lift (KT (reify tagVar))) orig recT) (ruleTrans (liftRed Fst orig recT) (axFst reifyA reifyB)))
        (congR TreeEq reifyA (ruleTrans (liftRed (KT (reify tagVar)) orig recT) (axKT (reify tagVar) orig))))
  in ruleTrans (recNdRed O cStepF reifyA reifyB)
     (ruleTrans (fanRed isVarF outerF IfLf orig recT)
     (ruleTrans (congL IfLf (ap2 outerF orig recT) (ruleTrans isVarEval neqPf))
     (ruleTrans (congR IfLf poo (fanRed innerF sndArgF Pair orig recT))
     (ruleTrans (axIfLfN O O (ap2 innerF orig recT) (ap2 sndArgF orig recT))
     (ruleTrans (postRed Snd Pair orig recT) (axSnd orig recT))))))

------------------------------------------------------------------------
-- closedSTFNd: when treeEq a tagVar = false, recurse. Uses codedSubstNd.

closedSTFNd : (replT tgtT a b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify a) tagVarT) poo) ->
  Eq (treeEq a tagVar) false ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify a)) (reify (codedSubst replT tgtT a))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (ap2 Pair (reify a) (reify b))) (reify (codedSubst replT tgtT (nd a b))))
closedSTFNd replT tgtT a b neqD neqB ihA ihB =
  let cstf = closedSubstTFor (reify replT) (reify tgtT)
  in ruleTrans (stepNotVar (reify replT) (reify tgtT) (reify a) (reify b) neqD)
     (ruleTrans (congL Pair (ap1 cstf (reify b)) ihA)
     (ruleTrans (congR Pair (reify (codedSubst replT tgtT a)) ihB)
     (eqSubst (\v -> Deriv _ (eqn (ap2 Pair (reify (codedSubst replT tgtT a)) (reify (codedSubst replT tgtT b))) (reify v)))
              (eqSym (codedSubstNd replT tgtT a b neqB)) (axRefl _))))

------------------------------------------------------------------------
-- Convenience wrappers

closedSTFNdF1 : (replT tgtT : Tree) (f : Fun1) (b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (codeF1 f))) (reify (codedSubst replT tgtT (codeF1 f)))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (ap2 Pair (reify (codeF1 f)) (reify b))) (reify (codedSubst replT tgtT (nd (codeF1 f) b))))
closedSTFNdF1 replT tgtT f b = closedSTFNd replT tgtT (codeF1 f) b (codeF1NeqTagVar f) (codeF1NotVar f)

closedSTFNdF2 : (replT tgtT : Tree) (g : Fun2) (b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (codeF2 g))) (reify (codedSubst replT tgtT (codeF2 g)))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (ap2 Pair (reify (codeF2 g)) (reify b))) (reify (codedSubst replT tgtT (nd (codeF2 g) b))))
closedSTFNdF2 replT tgtT g b = closedSTFNd replT tgtT (codeF2 g) b (codeF2NeqTagVar g) (codeF2NotVar g)

closedSTFNdCode : (replT tgtT : Tree) (t : Term) (b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (code t))) (reify (codedSubst replT tgtT (code t)))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify b)) (reify (codedSubst replT tgtT b))) ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (ap2 Pair (reify (code t)) (reify b))) (reify (codedSubst replT tgtT (nd (code t) b))))
closedSTFNdCode replT tgtT t b = closedSTFNd replT tgtT (code t) b (codeNeqTagVarGen t) (codeNotVar t)

------------------------------------------------------------------------
-- natCode and tag helpers

closedSTFNatCode : (replT tgtT : Tree) (n : Nat) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (natCode n))) (reify (codedSubst replT tgtT (natCode n))))
closedSTFNatCode replT tgtT zero = axRecLf O _
closedSTFNatCode replT tgtT (suc n) = closedSTFNd replT tgtT lf (natCode n) oNeqTagVar refl (axRecLf O _) (closedSTFNatCode replT tgtT n)

closedSTFTagAp1 : (rT tT : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify rT) (reify tT)) (reify tagAp1)) (reify (codedSubst rT tT tagAp1)))
closedSTFTagAp1 rT tT = closedSTFNd rT tT lf (nd lf lf) oNeqTagVar refl (axRecLf O _) (closedSTFNd rT tT lf lf oNeqTagVar refl (axRecLf O _) (axRecLf O _))

closedSTFTagAp2 : (rT tT : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify rT) (reify tT)) (reify tagAp2)) (reify (codedSubst rT tT tagAp2)))
closedSTFTagAp2 rT tT = closedSTFNd rT tT lf (nd lf (nd lf lf)) oNeqTagVar refl (axRecLf O _) (closedSTFNd rT tT lf (nd lf lf) oNeqTagVar refl (axRecLf O _) (closedSTFNd rT tT lf lf oNeqTagVar refl (axRecLf O _) (axRecLf O _)))

------------------------------------------------------------------------
-- treeEq-to-TreeEq correspondence: relates metalevel treeEq with object-level TreeEq.

treeEqReify : (a b : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (reify a) (reify b))
                 (reify (boolCase (treeEq a b) lf (nd lf lf))))
treeEqReify lf lf = tEqOO
treeEqReify lf (nd b1 b2) = axTreeEqLN (reify b1) (reify b2)
treeEqReify (nd a1 a2) lf = axTreeEqNL (reify a1) (reify a2)
treeEqReify (nd a1 a2) (nd b1 b2) =
  -- TreeEq(Pair(rA1,rA2), Pair(rB1,rB2)) = IfLf(TreeEq(rA1,rB1), Pair(TreeEq(rA2,rB2), Pair(O,O)))
  -- treeEq(nd a1 a2)(nd b1 b2) = boolAnd (treeEq a1 b1) (treeEq a2 b2)
  -- Need to relate IfLf-chain with boolAnd-chain
  ruleTrans (axTreeEqNN (reify a1) (reify a2) (reify b1) (reify b2))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify a2) (reify b2)) poo) (treeEqReify a1 b1))
  (treeEqReifyInner (treeEq a1 b1) (treeEq a2 b2) (reify a2) (reify b2) (treeEqReify a2 b2)))
  where
  treeEqReifyInner : (v1 v2 : Bool) (rA2 rB2 : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq rA2 rB2) (reify (boolCase v2 lf (nd lf lf)))) ->
    Deriv hyp (eqn (ap2 IfLf (reify (boolCase v1 lf (nd lf lf))) (ap2 Pair (ap2 TreeEq rA2 rB2) poo))
                   (reify (boolCase (boolAnd v1 v2) lf (nd lf lf))))
  treeEqReifyInner true v2 rA2 rB2 ih2 =
    -- IfLf(O, Pair(TreeEq(rA2,rB2), poo)) = TreeEq(rA2,rB2) [by axIfLfL]
    -- boolAnd true v2 = v2
    ruleTrans (axIfLfL (ap2 TreeEq rA2 rB2) poo) ih2
  treeEqReifyInner false v2 rA2 rB2 ih2 =
    -- IfLf(Pair(O,O), Pair(TreeEq(rA2,rB2), poo)) = poo [by axIfLfN]
    -- boolAnd false v2 = false
    -- reify(boolCase false lf (nd lf lf)) = Pair(O,O) = poo
    axIfLfN O O (ap2 TreeEq rA2 rB2) poo

-- Step evaluation when isVar matches (tag = tagVar).
-- Result: IfLf(TreeEq(reifyB, tgt), Pair(repl, orig))
stepIsVar : (repl tgt reifyB : Term) -> {hyp : Equation} ->
  let cstf = closedSubstTFor repl tgt ; orig = ap2 Pair tagVarT reifyB
      recT = ap2 Pair (ap1 cstf tagVarT) (ap1 cstf reifyB)
  in Deriv hyp (eqn (ap1 cstf (ap2 Pair tagVarT reifyB))
                    (ap2 IfLf (ap2 TreeEq reifyB tgt) (ap2 Pair repl orig)))
stepIsVar repl tgt reifyB =
  let cstf = closedSubstTFor repl tgt ; orig = ap2 Pair tagVarT reifyB
      recT = ap2 Pair (ap1 cstf tagVarT) (ap1 cstf reifyB)
      isVarF = Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq
      matchF = Fan (Lift Snd) (Lift (KT tgt)) TreeEq
      replOrigF = Fan (Lift (KT repl)) Const Pair
      innerF = Fan matchF replOrigF IfLf
      sndArgF = Post Snd Pair ; outerF = Fan innerF sndArgF Pair
      cStepF = Fan isVarF outerF IfLf
      isVarEval : Deriv _ (eqn (ap2 isVarF orig recT) (ap2 TreeEq tagVarT (reify tagVar)))
      isVarEval = ruleTrans (fanRed (Lift Fst) (Lift (KT (reify tagVar))) TreeEq orig recT)
        (ruleTrans (congL TreeEq (ap2 (Lift (KT (reify tagVar))) orig recT) (ruleTrans (liftRed Fst orig recT) (axFst tagVarT reifyB)))
        (congR TreeEq tagVarT (ruleTrans (liftRed (KT (reify tagVar)) orig recT) (axKT (reify tagVar) orig))))
      matchEval : Deriv _ (eqn (ap2 matchF orig recT) (ap2 TreeEq reifyB tgt))
      matchEval = ruleTrans (fanRed (Lift Snd) (Lift (KT tgt)) TreeEq orig recT)
        (ruleTrans (congL TreeEq (ap2 (Lift (KT tgt)) orig recT) (ruleTrans (liftRed Snd orig recT) (axSnd tagVarT reifyB)))
        (congR TreeEq reifyB (ruleTrans (liftRed (KT tgt) orig recT) (axKT tgt orig))))
      replOrigEval : Deriv _ (eqn (ap2 replOrigF orig recT) (ap2 Pair repl orig))
      replOrigEval = ruleTrans (fanRed (Lift (KT repl)) Const Pair orig recT)
        (ruleTrans (congL Pair (ap2 Const orig recT) (ruleTrans (liftRed (KT repl) orig recT) (axKT repl orig)))
                   (congR Pair repl (axConst orig recT)))
  in ruleTrans (recNdRed O cStepF tagVarT reifyB)
     (ruleTrans (fanRed isVarF outerF IfLf orig recT)
     (ruleTrans (congL IfLf (ap2 outerF orig recT) (ruleTrans isVarEval tagVarSelfEq))
     (ruleTrans (congR IfLf O (fanRed innerF sndArgF Pair orig recT))
     (ruleTrans (axIfLfL (ap2 innerF orig recT) (ap2 sndArgF orig recT))
     (ruleTrans (fanRed matchF replOrigF IfLf orig recT)
     (ruleTrans (congL IfLf (ap2 replOrigF orig recT) matchEval)
                (congR IfLf (ap2 TreeEq reifyB tgt) replOrigEval)))))))

-- IfLf + treeEqReify: connects IfLf(TreeEq(reify a, reify b), Pair(X, Y)) to boolCase(treeEq a b, ...)
ifLfTreeEq : (a b : Tree) (x y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 IfLf (ap2 TreeEq (reify a) (reify b)) (ap2 Pair x y))
                 (boolCase (treeEq a b) x y))
ifLfTreeEq a b x y =
  ruleTrans (congL IfLf (ap2 Pair x y) (treeEqReify a b))
  (ifLfBool (treeEq a b) x y)
  where
  ifLfBool : (v : Bool) (x y : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 IfLf (reify (boolCase v lf (nd lf lf))) (ap2 Pair x y))
                   (boolCase v x y))
  ifLfBool true x y = axIfLfL x y
  ifLfBool false x y = axIfLfN O O x y

------------------------------------------------------------------------
-- Mutual induction

closedSTFCode : (replT tgtT : Tree) (l : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (code l))) (reify (codedSubst replT tgtT (code l))))
closedSTFF1 : (replT tgtT : Tree) (f : Fun1) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (codeF1 f))) (reify (codedSubst replT tgtT (codeF1 f))))
closedSTFF2 : (replT tgtT : Tree) (g : Fun2) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify (codeF2 g))) (reify (codedSubst replT tgtT (codeF2 g))))

-- O: code O = nd(lf, lf)
closedSTFCode replT tgtT O = closedSTFNd replT tgtT lf lf oNeqTagVar refl (axRecLf O _) (axRecLf O _)

-- var n: code(var n) = nd(tagVar, natCode n). Tag matches!
-- stepIsVar gives: IfLf(TreeEq(reify(natCode n), reify(tgtT)), Pair(reify(replT), orig))
-- ifLfTreeEq converts to: boolCase(treeEq (natCode n) tgtT) (reify replT) orig
-- codedSubstVar gives: codedSubst = boolCase(treeEq (natCode n) tgtT) replT (nd tagVar (natCode n))
closedSTFCode replT tgtT (var n) =
  ruleTrans (stepIsVar (reify replT) (reify tgtT) (reify (natCode n)))
  (ruleTrans (ifLfTreeEq (natCode n) tgtT (reify replT) (ap2 Pair tagVarT (reify (natCode n))))
  (boolCaseReify (treeEq (natCode n) tgtT) replT (nd tagVar (natCode n))))
  where
  boolCaseReify : (v : Bool) (x y : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (boolCase v (reify x) (reify y)) (reify (boolCase v x y)))
  boolCaseReify true x y = axRefl _
  boolCaseReify false x y = axRefl _

-- ap1 f t: code = nd(tagAp1, nd(codeF1 f, code t))
closedSTFCode replT tgtT (ap1 f t) =
  closedSTFNd replT tgtT tagAp1 (nd (codeF1 f) (code t)) tagAp1NeqTagVar refl
    (closedSTFTagAp1 replT tgtT)
    (closedSTFNdF1 replT tgtT f (code t) (closedSTFF1 replT tgtT f) (closedSTFCode replT tgtT t))

-- ap2 g a b: code = nd(tagAp2, nd(codeF2 g, nd(code a, code b)))
closedSTFCode replT tgtT (ap2 g a b) =
  closedSTFNd replT tgtT tagAp2 (nd (codeF2 g) (nd (code a) (code b))) tagAp2NeqTagVar refl
    (closedSTFTagAp2 replT tgtT)
    (closedSTFNdF2 replT tgtT g (nd (code a) (code b)) (closedSTFF2 replT tgtT g)
      (closedSTFNdCode replT tgtT a (code b) (closedSTFCode replT tgtT a) (closedSTFCode replT tgtT b)))

-- Fun1 cases
private
  n26 : Nat ; n26 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))
  n27 : Nat ; n27 = suc n26 ; n28 : Nat ; n28 = suc n27 ; n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29 ; n31 : Nat ; n31 = suc n30 ; n32 : Nat ; n32 = suc n31
  n33 : Nat ; n33 = suc n32

closedSTFF1 replT tgtT I = closedSTFNd replT tgtT (natCode n26) lf (natCodeNeqTagVar n26) refl (closedSTFNatCode replT tgtT n26) (axRecLf O _)
closedSTFF1 replT tgtT Fst = closedSTFNd replT tgtT (natCode n27) lf (natCodeNeqTagVar n27) refl (closedSTFNatCode replT tgtT n27) (axRecLf O _)
closedSTFF1 replT tgtT Snd = closedSTFNd replT tgtT (natCode n28) lf (natCodeNeqTagVar n28) refl (closedSTFNatCode replT tgtT n28) (axRecLf O _)
closedSTFF1 replT tgtT (Comp f g) = closedSTFNd replT tgtT (natCode n29) _ (natCodeNeqTagVar n29) refl (closedSTFNatCode replT tgtT n29) (closedSTFNdF1 replT tgtT f _ (closedSTFF1 replT tgtT f) (closedSTFF1 replT tgtT g))
closedSTFF1 replT tgtT (Comp2 h f g) = closedSTFNd replT tgtT (natCode n30) _ (natCodeNeqTagVar n30) refl (closedSTFNatCode replT tgtT n30) (closedSTFNdF2 replT tgtT h _ (closedSTFF2 replT tgtT h) (closedSTFNdF1 replT tgtT f _ (closedSTFF1 replT tgtT f) (closedSTFF1 replT tgtT g)))
closedSTFF1 replT tgtT (Rec z s) = closedSTFNd replT tgtT (natCode n31) _ (natCodeNeqTagVar n31) refl (closedSTFNatCode replT tgtT n31) (closedSTFNdCode replT tgtT z _ (closedSTFCode replT tgtT z) (closedSTFF2 replT tgtT s))
closedSTFF1 replT tgtT (KT t) = closedSTFNd replT tgtT (natCode n32) _ (natCodeNeqTagVar n32) refl (closedSTFNatCode replT tgtT n32) (closedSTFCode replT tgtT t)

-- Fun2 cases
closedSTFF2 replT tgtT Pair = closedSTFNd replT tgtT (natCode n26) lf (natCodeNeqTagVar n26) refl (closedSTFNatCode replT tgtT n26) (axRecLf O _)
closedSTFF2 replT tgtT Const = closedSTFNd replT tgtT (natCode n27) lf (natCodeNeqTagVar n27) refl (closedSTFNatCode replT tgtT n27) (axRecLf O _)
closedSTFF2 replT tgtT (Lift f) = closedSTFNd replT tgtT (natCode n28) _ (natCodeNeqTagVar n28) refl (closedSTFNatCode replT tgtT n28) (closedSTFF1 replT tgtT f)
closedSTFF2 replT tgtT (Post f h) = closedSTFNd replT tgtT (natCode n29) _ (natCodeNeqTagVar n29) refl (closedSTFNatCode replT tgtT n29) (closedSTFNdF1 replT tgtT f _ (closedSTFF1 replT tgtT f) (closedSTFF2 replT tgtT h))
closedSTFF2 replT tgtT (Fan h1 h2 h) = closedSTFNd replT tgtT (natCode n30) _ (natCodeNeqTagVar n30) refl (closedSTFNatCode replT tgtT n30) (closedSTFNdF2 replT tgtT h1 _ (closedSTFF2 replT tgtT h1) (closedSTFNdF2 replT tgtT h2 _ (closedSTFF2 replT tgtT h2) (closedSTFF2 replT tgtT h)))
closedSTFF2 replT tgtT IfLf = closedSTFNd replT tgtT (natCode n31) lf (natCodeNeqTagVar n31) refl (closedSTFNatCode replT tgtT n31) (axRecLf O _)
closedSTFF2 replT tgtT TreeEq = closedSTFNd replT tgtT (natCode n32) lf (natCodeNeqTagVar n32) refl (closedSTFNatCode replT tgtT n32) (axRecLf O _)
closedSTFF2 replT tgtT (RecP s) = closedSTFNd replT tgtT (natCode n33) _ (natCodeNeqTagVar n33) refl (closedSTFNatCode replT tgtT n33) (closedSTFF2 replT tgtT s)
