{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonWCBoundary.agda
-- The Nelson-WC Boundary Theorem.
--
-- Connects:
--   (1) Deriv (syntactic proofs)
--   (2) WC (well-chained certificates with explicit side conditions)
--   (3) Gödel II (no internal consistency proof)
--
-- Main results:
--
-- Part 1 (Local soundness): WC p → SemTrue p
--   semSound in WellChained.agda.
--
-- Part 2 (Completeness for proofs): Deriv → ProofE
--   thm14E in Thm14E.agda.
--
-- Part 3 (Bridge): ProofE + EvalOK → WC
--   proofEToWC below.
--
-- Part 4 (Obstruction): EvalOK is the exact locus of incompleteness.
--   evalCode(code(t)) = evalCode(code(u)) fails for invalid equations.
--   For valid equations, it must be supplied per-instance.

module Guard.Nelson.NelsonWCBoundary where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.Nelson.EvalCode
open import Guard.Nelson.WellChained
open import Guard.Thm14E
open import Guard.Nelson.EvalCodeCorrect using (evalCodeO)
open import Guard.ThFunTForCorrectDefs using (branchMiss ; branchHit)
open import Guard.Nelson.NelsonExtractors using (sndArg2Red)

------------------------------------------------------------------------
-- EvalOK: the semantic side condition.
-- For equation t = u, evalCode must agree on the codes.

EvalOK : Term -> Term -> Equation -> Set
EvalOK t u hyp = Deriv hyp (eqn (ap1 evalCode (reify (code t)))
                                 (ap1 evalCode (reify (code u))))

------------------------------------------------------------------------
-- Part 3: ProofE + EvalOK → WC
--
-- ProofE contains the Nelson proof:
--   thFunTFor(enc) = reify(codeEqn(eqn t u)) = Pair(reify(code t), reify(code u))
-- wcBase takes: Nelson proof + evalCode condition.
-- Bridge is direct.

proofEToWC : {t u : Term} -> {hyp : Equation} ->
  (pe : ProofE (eqn t u)) ->
  EvalOK t u hyp ->
  WC (ap2 Pair (reify (fst pe)) (reify (fst (snd pe)))) hyp
proofEToWC {t} {u} pe evalSide =
  wcBase (ap2 Pair (reify (fst pe)) (reify (fst (snd pe))))
         (reify (code t)) (reify (code u))
         (fst (snd (snd (snd pe))))
         evalSide

------------------------------------------------------------------------
-- Parts 2 + 3 combined: Deriv → WC (with EvalOK obligation)

derivToWC : {t u : Term} -> {hyp : Equation} ->
  Deriv hyp (eqn t u) ->
  ProofE hyp ->
  EvalOK t u hyp ->
  Sigma Term (\enc -> WC enc hyp)
derivToWC d ph evalSide =
  let pe = thm14E d ph
      enc = ap2 Pair (reify (fst pe)) (reify (fst (snd pe)))
  in mkSigma enc (proofEToWC pe evalSide)

------------------------------------------------------------------------
-- Part 1 + 2 + 3 combined: the full Nelson pipeline
--
-- Deriv → ProofE → WC → SemTrue

derivToSemTrue : {t u : Term} -> {hyp : Equation} ->
  Deriv hyp (eqn t u) ->
  ProofE hyp ->
  EvalOK t u hyp ->
  Sigma Term (\enc -> SemTrue enc hyp)
derivToSemTrue d ph evalSide =
  let result = derivToWC d ph evalSide
      enc = fst result
      wc = snd result
  in mkSigma enc (semSound enc wc)

------------------------------------------------------------------------
-- Part 4: The obstruction.
--
-- EvalOK t u hyp says: evalCode(code(t)) = evalCode(code(u)) is derivable.
--
-- For VALID equations (t genuinely equals u in the model):
--   EvalOK is satisfiable per-instance, but the proof depends on
--   the specific t and u.
--
-- For INVALID equations (like O = Pair(O,O)):
--   evalCode(code(O)) = O   [tagO case]
--   evalCode(code(Pair O O)) = non-O Pair   [tagAp2 passthrough]
--   So EvalOK O (ap2 Pair O O) requires O = non-O, which is not
--   derivable in a consistent system.
--
-- Therefore:
--   (∀ t u, Deriv hyp (eqn t u) → EvalOK t u hyp)
--   would be FALSE for any consistent hyp, since Deriv can derive
--   anything from an inconsistent hypothesis, but a consistent system
--   cannot derive O = Pair(O,O).
--
-- More precisely: if we could INTERNALIZE the universal EvalOK as
-- a Deriv-provable statement, the system could prove its own
-- consistency — contradicting Gödel II.
--
-- The EXACT obstruction is: EvalOK is non-structural in (t, u).
-- It depends on evaluating code(t) and code(u) through evalCode,
-- which performs tree-structural dispatch (tagO/tagAp1/passthrough).
-- This dispatch cannot be captured as a single Deriv equation because:
--   1. evalCode uses Rec (tree recursion) → not a simple equation
--   2. The tag dispatch conflates code structure with data structure
--   3. substTFor (for ruleInst) doesn't commute with evalCode
--
-- This is the Nelson-Gödel boundary: the system can verify each
-- specific proof (Nelson's success) but cannot verify all proofs
-- uniformly (Gödel's obstruction), and the EXACT reason is that
-- validity checking requires non-structural evaluation of coded terms.

------------------------------------------------------------------------
-- Formal obstruction: EvalOK for a false equation implies inconsistency.

private
  poo : Term ; poo = ap2 Pair O O
  tagAp2T : Term ; tagAp2T = reify tagAp2

  -- Key lemma: O = Pair(X, Y) implies O = Pair(O, O).
  oPairBot : {hyp : Equation} -> (x y : Term) ->
    Deriv hyp (eqn O (ap2 Pair x y)) ->
    Deriv hyp (eqn O poo)
  oPairBot x y oPair =
    ruleTrans (ruleSym axTreeEqLL)
    (ruleTrans (congR TreeEq O oPair)
               (axTreeEqLN x y))

  -- isTagO reduction for evalStep dispatch
  isTagORed' : (tag data' recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 isTagO (ap2 Pair tag data') recs) (ap2 TreeEq tag O))
  isTagORed' tag data' recs =
    ruleTrans (fanRed (Lift Fst) (kF2 O) TreeEq (ap2 Pair tag data') recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 O) (ap2 Pair tag data') recs)
                 (ruleTrans (liftRed Fst (ap2 Pair tag data') recs) (axFst tag data')))
               (congR TreeEq tag (constF2Red O (ap2 Pair tag data') recs)))

  isTagAp1Red' : (tag data' recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 isTagAp1 (ap2 Pair tag data') recs) (ap2 TreeEq tag tagAp1T))
  isTagAp1Red' tag data' recs =
    ruleTrans (fanRed (Lift Fst) (kF2 tagAp1T) TreeEq (ap2 Pair tag data') recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 tagAp1T) (ap2 Pair tag data') recs)
                 (ruleTrans (liftRed Fst (ap2 Pair tag data') recs) (axFst tag data')))
               (congR TreeEq tag (constF2Red tagAp1T (ap2 Pair tag data') recs)))

  -- tagAp2T misses tagO: TreeEq(tagAp2T, O) = Pair(O,O)
  -- tagAp2T = Pair(O, Pair(O, Pair(O, O)))
  tagAp2MissO : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq tagAp2T O) poo)
  tagAp2MissO = axTreeEqNL O (ap2 Pair O (ap2 Pair O O))

  -- tagAp2T misses tagAp1: TreeEq(tagAp2T, tagAp1T) = Pair(O,O)
  -- tagAp2T = Pair(O, Pair(O, Pair(O,O))), tagAp1T = Pair(O, Pair(O, O))
  -- IfLf(TreeEq(O,O), Pair(TreeEq(Pair(O,Pair(O,O)), Pair(O,O)), Pair(O,O)))
  -- = IfLf(O, ...) = TreeEq(Pair(O,Pair(O,O)), Pair(O,O))
  -- = IfLf(TreeEq(O,O), ...) = TreeEq(Pair(O,O), O) = Pair(O,O)
  tagAp2MissAp1 : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq tagAp2T tagAp1T) poo)
  tagAp2MissAp1 =
    ruleTrans (axTreeEqNN O (ap2 Pair O (ap2 Pair O O)) O (ap2 Pair O O))
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O (ap2 Pair O O)) (ap2 Pair O O)) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq (ap2 Pair O (ap2 Pair O O)) (ap2 Pair O O)) poo)
    (ruleTrans (axTreeEqNN O (ap2 Pair O O) O O)
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O O) O) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq (ap2 Pair O O) O) poo)
               (axTreeEqNL O O))))))

  -- evalCode passthrough for tagAp2T-headed Pair:
  -- evalCode(Pair(tagAp2T, Y)) = Pair(evalCode(tagAp2T), evalCode(Y))
  evalCodeAp2Pass : (y : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 evalCode (ap2 Pair tagAp2T y))
                   (ap2 Pair (ap1 evalCode tagAp2T) (ap1 evalCode y)))
  evalCodeAp2Pass y =
    let orig = ap2 Pair tagAp2T y
        recs = ap2 Pair (ap1 evalCode tagAp2T) (ap1 evalCode y)
        missO = branchMiss isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)
                  orig recs
                  (ruleTrans (isTagORed' tagAp2T y recs) tagAp2MissO)
        missAp1 = branchMiss isTagAp1 tagAp1Case sndArg2
                    orig recs
                    (ruleTrans (isTagAp1Red' tagAp2T y recs) tagAp2MissAp1)
        deflt = sndArg2Red orig recs
    in ruleTrans (axRecNd O evalStep tagAp2T y)
       (ruleTrans missO (ruleTrans missAp1 deflt))

------------------------------------------------------------------------
-- THE OBSTRUCTION THEOREM
--
-- EvalOK for the false equation O = Pair(O,O) implies inconsistency.
--
-- Proof:
-- 1. evalCode(code O) = O                    [evalCodeO]
-- 2. EvalOK gives evalCode(code O) = evalCode(code(Pair O O))
-- 3. evalCode(code(Pair O O)) is a Pair      [tagAp2 passthrough]
-- 4. So O = Pair(something, something)
-- 5. TreeEq trick: O = Pair(X,Y) → O = Pair(O,O)
-- 6. Consistent hyp → Empty

obstruction : {hyp : Equation} ->
  EvalOK O (ap2 Pair O O) hyp ->
  Consistent hyp -> Empty
obstruction evalOK con =
  let -- evalCode(reify(code O)) = evalCode(Pair(O,O)) = O
      ecO = evalCodeO
      -- reify(code(ap2 Pair O O)) = Pair(tagAp2T, inner) for some inner
      inner = reify (nd (codeF2 Pair) (nd (code O) (code O)))
      -- evalCode(Pair(tagAp2T, inner)) = Pair(evalCode(tagAp2T), evalCode(inner))
      ecPairOO = evalCodeAp2Pass inner
      -- Chain: O = evalCode(Pair(O,O)) = evalCode(Pair(tagAp2T, inner)) = Pair(A, B)
      chain = ruleTrans (ruleSym ecO) (ruleTrans evalOK ecPairOO)
      -- O = Pair(evalCode(tagAp2T), evalCode(inner)) → O = Pair(O,O)
      bot = oPairBot (ap1 evalCode tagAp2T) (ap1 evalCode inner) chain
  in con bot
