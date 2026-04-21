{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ImpTProp -- propositional theorems for object-level implication.
--
-- Layer 2 of the Rose/Ryan Goedel II plan (see NEXT-SESSION-IMPT-GODELII.md).
--
-- Every theorem here is a derivation schema about  impT A B = IfLf A
-- (Pair B O)  from Guard/ImpT.agda, built using existing axioms
-- (axIfLfL, axIfLfN, axTreeEq{LL,LN,NL,NN}) + congruences (cong1,
-- congL, congR) + structural rules (ruleTrans, ruleSym, axRefl).  No
-- new Deriv constructors, no postulates, no holes.
--
-- The organisational principle: propositional theorems that hold for
-- ARBITRARY Terms are few -- axIfLfL / axIfLfN only fire on explicit
-- head shapes.  Most theorems here are therefore SCHEMATIC in a shape
-- witness (typically  A = trueT  or  A = falseT  as a Deriv), or
-- parameterised by known-shape Pair operands.  This matches Rose's
-- proof: characteristic values of equations always have known shape
-- (O or poo), so propositional reasoning is possible once a proof of
-- shape is in hand.

module Guard.ImpTProp where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ImpT

------------------------------------------------------------------------
-- Congruence for impT
--
-- impT is defined as  ap2 IfLf A (ap2 Pair B O).  Rewriting either
-- slot proceeds via congL / congR.

-- Rewrite the antecedent:  A = A'  ->  impT A B = impT A' B.

impTCongL : (B : Term) {A A' : Term} {hyp : Equation} ->
  Deriv hyp (eqn A A') ->
  Deriv hyp (eqn (impT A B) (impT A' B))
impTCongL B dA = congL IfLf (ap2 Pair B O) dA

-- Rewrite the consequent:  B = B'  ->  impT A B = impT A B'.

impTCongR : (A : Term) {B B' : Term} {hyp : Equation} ->
  Deriv hyp (eqn B B') ->
  Deriv hyp (eqn (impT A B) (impT A B'))
impTCongR A dB = congR IfLf A (congL Pair O dB)

------------------------------------------------------------------------
-- Introduction by consequent, for the two known-shape cases of A.
--
-- If  B = trueT  (i.e. B is classically true), then  impT A B = trueT
-- for any A whose head shape is known.

-- Case 1: A is literally  trueT = O.
--   impT trueT B = B = trueT.

impTIntroByConseqTrue : (B : Term) {hyp : Equation} ->
  Deriv hyp (eqn B trueT) ->
  Deriv hyp (eqn (impT trueT B) trueT)
impTIntroByConseqTrue B dB =
  ruleTrans (impTTrueAnt B) dB

-- Case 2: A is any Pair (= falseT or other non-true Pair).
--   impT (Pair x y) B = trueT vacuously.

impTIntroByConseqFalse : (x y B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT (ap2 Pair x y) B) trueT)
impTIntroByConseqFalse x y B = impTFalseAnt x y B

-- Case 3 (dispatch via a Deriv witness for A's shape):
--   If  A = trueT  (as a derivation) and  B = trueT , derive
--   impT A B = trueT  by rewriting A to trueT first.

impTIntroByConseqVia : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn B trueT) ->
  Deriv hyp (eqn (impT A B) trueT)
impTIntroByConseqVia A B dA dB =
  ruleTrans (impTCongL B dA) (impTIntroByConseqTrue B dB)

-- Dispatch via a witness that A is a specific Pair.

impTIntroByAntPair : (A B x y : Term) {hyp : Equation} ->
  Deriv hyp (eqn A (ap2 Pair x y)) ->
  Deriv hyp (eqn (impT A B) trueT)
impTIntroByAntPair A B x y dA =
  ruleTrans (impTCongL B dA) (impTFalseAnt x y B)

------------------------------------------------------------------------
-- Reflexivity of implication -- only for values whose shape is known.
--
-- Generic  impT A A = trueT  is NOT derivable, but the specialisations
-- are:

impTReflTrueExplicit : {hyp : Equation} ->
  Deriv hyp (eqn (impT trueT trueT) trueT)
impTReflTrueExplicit = impTIntroByConseqTrue trueT (axRefl trueT)

impTReflFalseExplicit : {hyp : Equation} ->
  Deriv hyp (eqn (impT falseT falseT) trueT)
impTReflFalseExplicit = impTFalseAnt O O falseT

-- Reflexivity at any  A  for which we have a derivation  A = trueT.

impTReflViaTrue : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn (impT A A) trueT)
impTReflViaTrue A dA = impTIntroByConseqVia A A dA dA

------------------------------------------------------------------------
-- K axiom:  A -> (B -> A)  when A's and B's truth values are known.
--
-- Fully polymorphic K is not derivable, but the two useful instances
-- are:

-- K1:  trueT -> (B -> trueT)  when B's shape is known.
--      Inner  impT B trueT  reduces to trueT in both shape cases.

kAxiomB0 : {hyp : Equation} ->
  Deriv hyp (eqn (impT trueT (impT trueT trueT)) trueT)
kAxiomB0 = impTIntroByConseqTrue (impT trueT trueT) impTReflTrueExplicit

kAxiomBPair : (x y : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT trueT (impT (ap2 Pair x y) trueT)) trueT)
kAxiomBPair x y =
  impTIntroByConseqTrue (impT (ap2 Pair x y) trueT)
                        (impTFalseAnt x y trueT)

-- K generic:  given  A = trueT  and  B = trueT -witness for any
-- shape of B (via a Deriv), derive the K-like statement.

kAxiomTrueTViaConseq : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn (impT B A) trueT) ->
  Deriv hyp (eqn (impT A (impT B A)) trueT)
kAxiomTrueTViaConseq A B dA dBA =
  impTIntroByConseqVia A (impT B A) dA dBA

------------------------------------------------------------------------
-- Modus ponens, already in ImpT, restated here for convenience.

mpT : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT A B) trueT) ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn B trueT)
mpT = modusPonens

------------------------------------------------------------------------
-- Hypothetical syllogism (chain):  A -> B ,  B -> C  |-  A -> C.
--
-- Fully polymorphic chain needs A to have known head shape.  We
-- provide the two concrete shapes + a Deriv-dispatch version.

-- Chain when A = trueT.
--   impT trueT B = B , so  B = trueT  (from impT A B)
--   impT B C = trueT  at B=trueT gives C = trueT (modus ponens).
--   impT trueT C = C = trueT.

chainImpTTrue : (B C : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT trueT B) trueT) ->
  Deriv hyp (eqn (impT B C) trueT) ->
  Deriv hyp (eqn (impT trueT C) trueT)
chainImpTTrue B C dAB dBC =
  impTIntroByConseqTrue C dC
  where
  dB : _
  dB = ruleTrans (ruleSym (impTTrueAnt B)) dAB
  -- dB : B = trueT  obtained by rewriting impT trueT B = B and transitivity.
  dC : _
  dC = mpT B C dBC dB

-- Chain when A = Pair x y (vacuously true).

chainImpTPair : (x y B C : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT (ap2 Pair x y) C) trueT)
chainImpTPair x y B C = impTFalseAnt x y C

-- Chain via a Deriv that establishes A = trueT.

chainImpTViaTrue : (A B C : Term) {hyp : Equation} ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn (impT A B) trueT) ->
  Deriv hyp (eqn (impT B C) trueT) ->
  Deriv hyp (eqn (impT A C) trueT)
chainImpTViaTrue A B C dA dAB dBC =
  impTIntroByConseqVia A C dA dC
  where
  dB : _
  dB = mpT A B dAB dA
  dC : _
  dC = mpT B C dBC dB

------------------------------------------------------------------------
-- Negation and contrapositive
--
-- notT A := impT A falseT.  "A implies falseT" = "A is false".

notT : Term -> Term
notT A = impT A falseT

-- notT trueT = impT trueT falseT = falseT.

notTTrue : {hyp : Equation} ->
  Deriv hyp (eqn (notT trueT) falseT)
notTTrue = impTTrueAnt falseT

-- notT (Pair x y) = impT (Pair x y) falseT = trueT.

notTFalse : (x y : Term) {hyp : Equation} ->
  Deriv hyp (eqn (notT (ap2 Pair x y)) trueT)
notTFalse x y = impTFalseAnt x y falseT

-- Reductio ad absurdum internally: notT A = trueT  and  A = trueT
-- together give falseT = trueT (a clash with Consistency at the
-- meta-level).  This is exactly reductioBranch from ImpT.

reductioInternal : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn (notT A) trueT) ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn falseT trueT)
reductioInternal A dNotA dA = reductioBranch A dNotA dA

------------------------------------------------------------------------
-- Contrapositive: (A -> B) -> (notT B -> notT A).
--
-- Known-shape case we actually use in Goedel II: A = trueT.
--   premise  impT trueT B = trueT  gives B = trueT.
--   Then notT B = falseT.  Then  notT B -> notT A  has antecedent
--   falseT = Pair O O, so it's trueT by impTFalseAnt.

contrapositiveAtTrue : (B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT trueT B) trueT) ->
  Deriv hyp (eqn (impT (notT B) (notT trueT)) trueT)
contrapositiveAtTrue B dTrueB =
  impTIntroByAntPair (notT B) (notT trueT) O O bridge
  where
  dB : _
  dB = ruleTrans (ruleSym (impTTrueAnt B)) dTrueB
  -- notT B = impT B falseT ; rewrite B to trueT: impT trueT falseT = falseT = Pair O O.
  bridge : _
  bridge = ruleTrans (impTCongL falseT dB) notTTrue

------------------------------------------------------------------------
-- Implication swap with a known-true antecedent / consequent.
--
-- swapAntTrue : if we can establish A = trueT, then any  impT A B
-- equation rewrites to  impT trueT B .  Useful bookkeeping.

swapAntTrue : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn A trueT) ->
  Deriv hyp (eqn (impT A B) (impT trueT B))
swapAntTrue A B dA = impTCongL B dA

swapConseqTrue : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn B trueT) ->
  Deriv hyp (eqn (impT A B) (impT A trueT))
swapConseqTrue A B dB = impTCongR A dB

------------------------------------------------------------------------
-- Dispatch on TreeEq outputs.
--
-- ap2 TreeEq X Y always reduces, under the axTreeEq{LL,LN,NL,NN} rules,
-- to one of:
--   * O       when X = O, Y = O
--   * poo     (= Pair O O = falseT)  when exactly one side is O
--   * IfLf (TreeEq X1 Y1) (Pair (TreeEq X2 Y2) poo)   for nested Pairs
--
-- So for known-shape X and Y, TreeEq produces trueT or falseT directly.

treeEqLL : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq O O) trueT)
treeEqLL = axTreeEqLL

treeEqLN : (a b : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq O (ap2 Pair a b)) falseT)
treeEqLN a b = axTreeEqLN a b

treeEqNL : (a b : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair a b) O) falseT)
treeEqNL a b = axTreeEqNL a b

-- TreeEq result turned into an implication antecedent:
--   if X = O and Y = O, TreeEq X Y = trueT, so  impT (TreeEq X Y) P  is
--   equivalent to  impT trueT P = P .

impTOfTreeEqLL : (P : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT (ap2 TreeEq O O) P) P)
impTOfTreeEqLL P =
  ruleTrans (impTCongL P axTreeEqLL) (impTTrueAnt P)

impTOfTreeEqLN : (a b P : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT (ap2 TreeEq O (ap2 Pair a b)) P) trueT)
impTOfTreeEqLN a b P =
  ruleTrans (impTCongL P (axTreeEqLN a b)) (impTFalseAnt O O P)

impTOfTreeEqNL : (a b P : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT (ap2 TreeEq (ap2 Pair a b) O) P) trueT)
impTOfTreeEqNL a b P =
  ruleTrans (impTCongL P (axTreeEqNL a b)) (impTFalseAnt O O P)

------------------------------------------------------------------------
-- Distribution laws (usable only at known shapes).
--
-- Curry / uncurry for impT with a trueT premise.

-- curryTrue : (trueT ∧ B) -> C  ~>  trueT -> (B -> C).  We do not have
-- object-level conjunction, but we have Pair, and we can define
-- "andT a b" := Pair a b with trueT = O encoded at one specific shape.
-- Instead of building a full andT calculus, we provide the practical
-- "two-hypothesis" MP:

mpT2 : (A1 A2 B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT A1 (impT A2 B)) trueT) ->
  Deriv hyp (eqn A1 trueT) ->
  Deriv hyp (eqn A2 trueT) ->
  Deriv hyp (eqn B trueT)
mpT2 A1 A2 B dImp dA1 dA2 =
  mpT A2 B (mpT A1 (impT A2 B) dImp dA1) dA2

mpT3 : (A1 A2 A3 B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT A1 (impT A2 (impT A3 B))) trueT) ->
  Deriv hyp (eqn A1 trueT) ->
  Deriv hyp (eqn A2 trueT) ->
  Deriv hyp (eqn A3 trueT) ->
  Deriv hyp (eqn B trueT)
mpT3 A1 A2 A3 B dImp dA1 dA2 dA3 =
  mpT A3 B (mpT2 A1 A2 (impT A3 B) dImp dA1 dA2) dA3

mpT4 : (A1 A2 A3 A4 B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT A1 (impT A2 (impT A3 (impT A4 B)))) trueT) ->
  Deriv hyp (eqn A1 trueT) ->
  Deriv hyp (eqn A2 trueT) ->
  Deriv hyp (eqn A3 trueT) ->
  Deriv hyp (eqn A4 trueT) ->
  Deriv hyp (eqn B trueT)
mpT4 A1 A2 A3 A4 B dImp dA1 dA2 dA3 dA4 =
  mpT A4 B (mpT3 A1 A2 A3 (impT A4 B) dImp dA1 dA2 dA3) dA4

------------------------------------------------------------------------
-- Summary
--
-- Toolbox provided for the Rose/Ryan Goedel II plan (layers 3-5):
--
--   * impTCongL / impTCongR               -- congruences
--   * impTIntroByConseqTrue|False|Via     -- introduction via consequent
--   * impTIntroByAntPair                  -- antecedent-is-Pair shortcut
--   * impTReflViaTrue                     -- A -> A when A = trueT
--   * kAxiom{B0,BPair,TrueTViaConseq}     -- K instances
--   * mpT, mpT2, mpT3, mpT4               -- iterated modus ponens
--   * chainImpT{True,Pair,ViaTrue}        -- hypothetical syllogism
--   * notT, notTTrue, notTFalse           -- negation
--   * reductioInternal                    -- reductio ad absurdum
--   * contrapositiveAtTrue                -- contrapositive (A=trueT case)
--   * swapAntTrue / swapConseqTrue        -- rewrite helpers
--   * treeEq{LL,LN,NL} + impTOfTreeEq{*}  -- TreeEq dispatch
--
-- All theorems compile under  --safe --without-K --exact-split .
-- No postulates, no holes.
