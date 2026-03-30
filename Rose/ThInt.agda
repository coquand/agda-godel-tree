{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.ThInt where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst;
         Sigma; mkSigma)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval
  using (Env; emptyEnv; extEnv; extEnv2; extEnv4;
         eval; evalEnv; evalCas; evalRec; evalNiter)
open import Rose.Code using (codeTerm; codeEquation; tagLeaf; tagPair; tagCase; tagRec)
open import Rose.DiagCode using (codeReify; codeReify-correct)
open import Rose.Reify using (reify)
open import Rose.TreeEq using (trueT; falseT; eqTree; eqTree-refl; eqTree-sound)

------------------------------------------------------------------------
-- Metalevel helpers.

defaultCode : Tree
defaultCode = nd (nd lf lf) (nd lf lf)

swapCode : Tree -> Tree
swapCode lf       = defaultCode
swapCode (nd l r) = nd r l

codeLhs : Tree -> Tree
codeLhs lf       = nd lf lf
codeLhs (nd l r) = l

codeRhs : Tree -> Tree
codeRhs lf       = nd lf lf
codeRhs (nd l r) = r

------------------------------------------------------------------------
-- Computation axiom equation codes.

casLeafCode : Tree -> Tree -> Tree
casLeafCode codeU codeV =
  nd (nd tagCase (nd (nd tagLeaf lf) (nd codeU codeV))) codeU

recLeafCode : Tree -> Tree -> Tree
recLeafCode codeZ codeS =
  nd (nd tagRec (nd (nd tagLeaf lf) (nd codeZ codeS))) codeZ

------------------------------------------------------------------------
-- Transitivity combinator (aligned with term behavior).

transHelp : Tree -> Tree -> Tree -> Tree
transHelp lf e1 e2 = nd (codeLhs e1) (codeRhs e2)
transHelp (nd a b) e1 e2 = defaultCode

transCode : Tree -> Tree -> Tree
transCode lf eq2 = defaultCode
transCode (nd l1 r1) lf = defaultCode
transCode (nd l1 r1) (nd l2 r2) =
  transHelp (eqTree r1 l2) (nd l1 r1) (nd l2 r2)

------------------------------------------------------------------------
-- Strengthened metalevel theorem enumerator.

thS : Tree -> Tree
thS lf = defaultCode
thS (nd lf payload) = nd (codeReify payload) (codeReify payload)
thS (nd (nd lf lf) payload) = swapCode (thS payload)
-- Axiom dispatch: tag = nd lf (nd a b), split on a and b.
thS (nd (nd lf (nd lf lf)) payload) = defaultCode
thS (nd (nd lf (nd lf (nd codeU codeV))) payload) = casLeafCode codeU codeV
thS (nd (nd lf (nd (nd lf lf) lf)) payload) = defaultCode
thS (nd (nd lf (nd (nd lf lf) (nd codeZ codeS))) payload) = recLeafCode codeZ codeS
thS (nd (nd lf (nd (nd lf (nd c d)) e)) payload) = defaultCode
thS (nd (nd lf (nd (nd (nd c d) e) f)) payload) = defaultCode
-- Transitivity.
thS (nd (nd (nd a b) c) payload) =
  transCode (thS (nd (nd a b) c)) (thS payload)

------------------------------------------------------------------------
-- Var helpers.

v0 : {n : Nat} -> Term (suc n)
v0 = var fz

v1 : {n : Nat} -> Term (suc (suc n))
v1 = var (fs fz)

v2 : {n : Nat} -> Term (suc (suc (suc n)))
v2 = var (fs (fs fz))

v3 : {n : Nat} -> Term (suc (suc (suc (suc n))))
v3 = var (fs (fs (fs fz)))

v4 : {n : Nat} -> Term (suc (suc (suc (suc (suc n)))))
v4 = var (fs (fs (fs (fs fz))))

v5 : {n : Nat} -> Term (suc (suc (suc (suc (suc (suc n))))))
v5 = var (fs (fs (fs (fs (fs fz)))))

v6 : {n : Nat} -> Term (suc (suc (suc (suc (suc (suc (suc n)))))))
v6 = var (fs (fs (fs (fs (fs (fs fz))))))

mkDefault : {n : Nat} -> Term n
mkDefault = pair (pair leaf leaf) (pair leaf leaf)

------------------------------------------------------------------------
-- Term infrastructure.

open import Rose.TreeEqInt using (linearizeTerm; processStep)

crBase : {n : Nat} -> Term n
crBase = pair leaf leaf

crStep : {n : Nat} -> Term (suc (suc (suc (suc n))))
crStep = pair (pair leaf (pair leaf leaf)) (pair v1 v0)

eqCheck : {n : Nat} -> Term n -> Term n -> Term n
eqCheck t1 t2 =
  niter (linearizeTerm (pair t1 t2))
        (pair leaf (pair (pair t1 t2) leaf))
        processStep

extractFlag : {n : Nat} -> Term n -> Term n
extractFlag result = cas result leaf v1

------------------------------------------------------------------------
-- Axiom output terms.
--
-- After cas dispatches, v0 and v1 hold the axiom data.
-- casLeafOutput: builds casLeafCode v1 v0 (v1=codeU, v0=codeV)
-- recLeafOutput: builds recLeafCode v1 v0 (v1=codeZ, v0=codeS)

casLeafOutput : {n : Nat} -> Term (suc (suc n))
casLeafOutput =
  pair (pair (pair leaf (pair leaf (pair leaf leaf)))
            (pair (pair leaf leaf) (pair v1 v0)))
       v1

recLeafOutput : {n : Nat} -> Term (suc (suc n))
recLeafOutput =
  pair (pair (pair leaf (pair leaf (pair leaf (pair leaf leaf))))
            (pair (pair leaf leaf) (pair v1 v0)))
       v1

-- Axiom dispatch term: replaces mkDefault in the "left=lf, right=nd" branch.
-- At this point: v1 = axiom selector (left of tag's right part),
--                v0 = axiom data (right of tag's right part).
axiomDispatch : {n : Nat} -> Term (suc (suc (suc (suc n))))
axiomDispatch =
  cas v1
    -- v1 = lf: cas-leaf candidate
    (cas v0 mkDefault casLeafOutput)
    -- v1 = nd: sub-dispatch (new v1=left(v1), v0=right(v1), v2=old data)
    (cas v1
      -- left = lf
      (cas v0
        -- right = lf: v1 was nd lf lf -> rec-leaf candidate, check v2 (= old data)
        (cas v2 mkDefault recLeafOutput)
        -- right = nd: default
        mkDefault)
      -- left = nd: default
      mkDefault)

------------------------------------------------------------------------
-- thStep5Full: the full step with transitivity + axioms.

thStep5Full : Term (suc (suc (suc (suc (suc zero)))))
thStep5Full =
  cas v3
    (pair (rec v2 crBase crStep) (rec v2 crBase crStep))
    (cas v1
      (cas v0
        (cas v2 mkDefault (pair v0 v1))
        axiomDispatch)
      (cas v5
        mkDefault
        (cas (var (fs (fs (fs (fs (fs (fs fz)))))))
          mkDefault
          (cas (extractFlag (eqCheck v2 v1))
            (pair v3 v0)
            mkDefault))))

thTermFull : Term (suc zero)
thTermFull = rec v0 mkDefault thStep5Full

------------------------------------------------------------------------
-- thStep5Simple: reflexivity + symmetry only.

thSimple : Tree -> Tree
thSimple lf = defaultCode
thSimple (nd lf payload) = nd (codeReify payload) (codeReify payload)
thSimple (nd (nd lf b) payload) = swapCode (thSimple payload)
thSimple (nd (nd (nd a b) c) payload) = defaultCode

thStep5Simple : Term (suc (suc (suc (suc (suc zero)))))
thStep5Simple =
  cas v3
    (pair (rec v2 crBase crStep) (rec v2 crBase crStep))
    (cas v1
      (cas v2 mkDefault (pair v0 v1))
      mkDefault)

thTerm : Term (suc zero)
thTerm = rec v0 mkDefault thStep5Full

------------------------------------------------------------------------
-- Unit tests.

evalWith : Tree -> Term (suc zero) -> Tree
evalWith t tm = evalEnv (extEnv emptyEnv t) tm

-- Tests for thTerm (now full, with transitivity).
test1 : Eq (evalWith lf thTerm) (thS lf)
test1 = refl

test2 : Eq (evalWith (nd lf lf) thTerm) (thS (nd lf lf))
test2 = refl

test3 : Eq (evalWith (nd lf (nd lf lf)) thTerm) (thS (nd lf (nd lf lf)))
test3 = refl

test4 : Eq (evalWith (nd (nd lf lf) (nd lf (nd lf lf))) thTerm)
           (thS (nd (nd lf lf) (nd lf (nd lf lf))))
test4 = refl

test5 : Eq (evalWith (nd (nd (nd lf lf) lf) lf) thTerm) (thS (nd (nd (nd lf lf) lf) lf))
test5 = refl

-- Tests for thTermFull (with transitivity).
evalFull : Tree -> Tree
evalFull t = evalWith t thTermFull

testF1 : Eq (evalFull lf) (thS lf)
testF1 = refl

testF2 : Eq (evalFull (nd lf lf)) (thS (nd lf lf))
testF2 = refl

testF3 : Eq (evalFull (nd lf (nd lf lf))) (thS (nd lf (nd lf lf)))
testF3 = refl

testF4 : Eq (evalFull (nd (nd lf lf) (nd lf (nd lf lf))))
            (thS (nd (nd lf lf) (nd lf (nd lf lf))))
testF4 = refl

testF5 : Eq (evalFull (nd (nd lf (nd lf lf)) lf)) (thS (nd (nd lf (nd lf lf)) lf))
testF5 = refl

-- Transitivity: matching middle terms.
testF6 : Eq (evalFull (nd (nd (nd lf lf) (nd lf lf)) (nd lf lf)))
            (thS (nd (nd (nd lf lf) (nd lf lf)) (nd lf lf)))
testF6 = refl

testF7 : Eq (evalFull (nd (nd (nd lf lf) (nd lf (nd lf lf))) (nd lf (nd lf lf))))
            (thS (nd (nd (nd lf lf) (nd lf (nd lf lf))) (nd lf (nd lf lf))))
testF7 = refl

-- Transitivity: mismatching middle terms.
testF8 : Eq (evalFull (nd (nd (nd lf lf) (nd lf lf)) (nd lf (nd (nd lf lf) lf))))
            (thS (nd (nd (nd lf lf) (nd lf lf)) (nd lf (nd (nd lf lf) lf))))
testF8 = refl

-- Axiom tests: cas-leaf.
-- Proof tree for cas-leaf with codeU=lf, codeV=lf:
-- nd (nd lf (nd lf (nd lf lf))) anything
testAxCL1 : Eq (evalFull (nd (nd lf (nd lf (nd lf lf))) lf))
               (thS (nd (nd lf (nd lf (nd lf lf))) lf))
testAxCL1 = refl

-- cas-leaf with codeU = nd lf lf, codeV = nd lf (nd lf lf)
testAxCL2 : Eq (evalFull (nd (nd lf (nd lf (nd (nd lf lf) (nd lf (nd lf lf))))) lf))
               (thS (nd (nd lf (nd lf (nd (nd lf lf) (nd lf (nd lf lf))))) lf))
testAxCL2 = refl

-- Axiom tests: rec-leaf.
-- Proof tree for rec-leaf with codeZ=lf, codeS=lf:
-- nd (nd lf (nd (nd lf lf) (nd lf lf))) anything
testAxRL1 : Eq (evalFull (nd (nd lf (nd (nd lf lf) (nd lf lf))) lf))
               (thS (nd (nd lf (nd (nd lf lf) (nd lf lf))) lf))
testAxRL1 = refl

-- rec-leaf with codeZ = nd lf lf, codeS = nd lf (nd lf lf)
testAxRL2 : Eq (evalFull (nd (nd lf (nd (nd lf lf) (nd (nd lf lf) (nd lf (nd lf lf))))) lf))
               (thS (nd (nd lf (nd (nd lf lf) (nd (nd lf lf) (nd lf (nd lf lf))))) lf))
testAxRL2 = refl

-- Symmetry of a cas-leaf axiom (tests swap on non-refl output).
testAxSym : Eq (evalFull (nd (nd lf lf) (nd (nd lf (nd lf (nd lf lf))) lf)))
               (thS (nd (nd lf lf) (nd (nd lf (nd lf (nd lf lf))) lf)))
testAxSym = refl

------------------------------------------------------------------------
-- Correctness proofs.

codeReifyStep : {n : Nat} -> Term (suc (suc (suc (suc n))))
codeReifyStep = pair (pair leaf (pair leaf leaf)) (pair v1 v0)

codeReifyViaRec : {n : Nat} -> (env : Env n) -> (t : Tree) ->
  Eq (evalRec env t (pair leaf leaf) codeReifyStep) (codeReify t)
codeReifyViaRec env lf = refl
codeReifyViaRec env (nd a b) =
  eqCong2 (\ x y -> nd (nd lf (nd lf lf)) (nd x y))
    (codeReifyViaRec env a)
    (codeReifyViaRec env b)

swapCasLem : {n : Nat} -> (env : Env (suc (suc n))) -> (t : Tree) ->
  Eq (evalCas env t mkDefault (pair v0 v1)) (swapCode t)
swapCasLem env lf = refl
swapCasLem env (nd a b) = refl

-- Correctness of thTerm (simple version): FULLY PROVED.
thGenSimple : (env : Env (suc zero)) -> (t : Tree) ->
  Eq (evalRec env t mkDefault thStep5Simple) (thSimple t)
thGenSimple env lf = refl
thGenSimple env (nd lf payload) =
  eqCong2 nd (codeReifyViaRec _ payload) (codeReifyViaRec _ payload)
thGenSimple env (nd (nd lf b') payload) =
  eqTrans (swapCasLem _ (evalRec env payload mkDefault thStep5Simple))
          (eqCong swapCode (thGenSimple env payload))
thGenSimple env (nd (nd (nd a b') c) payload) = refl

------------------------------------------------------------------------
-- Combined eqCheck evaluation lemma.
--
-- The eqCheck term, evaluated in any env, computes eqTree.

open import Rose.TreeEqInt
  using (linearize-eval; niter-eval; extractFlag-eval;
         runNiter; extractFlagMeta; linearize)
open import Rose.EqCheckCorrect using (eqCheck-main)

eqCheckEval : {m : Nat} -> (env : Env m) -> (a b : Tree) ->
  Eq (evalCas env
       (evalNiter env
         (evalRec env (nd a b) leaf (pair leaf (niter v1 v0 (pair leaf v1))))
         (nd lf (nd (nd a b) lf))
         processStep)
       leaf v1)
     (eqTree a b)
eqCheckEval env a b =
  let clock = evalRec env (nd a b) leaf
                (pair leaf (niter (Rose.TreeEqInt.v1) (Rose.TreeEqInt.v0)
                  (pair leaf (Rose.TreeEqInt.v1))))
      initSt = nd lf (nd (nd a b) lf)
      niterResult = evalNiter env clock initSt processStep
  in eqTrans
    (extractFlag-eval env niterResult)
    (eqTrans
      (eqCong extractFlagMeta (niter-eval env clock initSt))
      (eqTrans
        (eqCong (\ c -> extractFlagMeta (runNiter c initSt))
          (linearize-eval env (nd a b)))
        (eqCheck-main a b)))

------------------------------------------------------------------------
-- Full correctness: thGenFull.

thGenFull : (env : Env (suc zero)) -> (t : Tree) ->
  Eq (evalRec env t mkDefault thStep5Full) (thS t)
thGenFull env lf = refl
thGenFull env (nd lf payload) =
  eqCong2 nd (codeReifyViaRec _ payload) (codeReifyViaRec _ payload)
thGenFull env (nd (nd lf lf) payload) =
  eqTrans (swapCasLem _ (evalRec env payload mkDefault thStep5Full))
          (eqCong swapCode (thGenFull env payload))
thGenFull env (nd (nd lf (nd lf lf)) payload) = refl
thGenFull env (nd (nd lf (nd lf (nd codeU codeV))) payload) = refl
thGenFull env (nd (nd lf (nd (nd lf lf) lf)) payload) = refl
thGenFull env (nd (nd lf (nd (nd lf lf) (nd codeZ codeS))) payload) = refl
thGenFull env (nd (nd lf (nd (nd lf (nd c d)) e)) payload) = refl
thGenFull env (nd (nd lf (nd (nd (nd c d) e) f)) payload) = refl
thGenFull env (nd (nd (nd a b) c) payload) =
  -- Transport IH via eqSubst, then case-split on thS values.
  eqSubst
    (\ x -> Eq (evalEnv (extEnv4 env (nd (nd a b) c) payload
                  (evalRec env (nd (nd a b) c) mkDefault thStep5Full) x)
                thStep5Full)
               (transCode (thS (nd (nd a b) c)) (thS payload)))
    (eqSym (thGenFull env payload))
    (eqSubst
      (\ y -> Eq (evalEnv (extEnv4 env (nd (nd a b) c) payload
                    y (thS payload))
                  thStep5Full)
                 (transCode (thS (nd (nd a b) c)) (thS payload)))
      (eqSym (thGenFull env (nd (nd a b) c)))
      (transMatch (thS (nd (nd a b) c)) (thS payload)))
  where
    -- After transport: env has thS values. Case-split on them.
    -- The tag is nd (nd a b) c at position 3, so cas dispatches reduce.
    -- In the transitivity branch, v5 = eq1, v4 = eq2 (shifted).
    transMatch : (eq1 eq2 : Tree) ->
      Eq (evalEnv (extEnv4 env (nd (nd a b) c) payload eq1 eq2) thStep5Full)
         (transCode eq1 eq2)
    transMatch lf eq2 = refl
    transMatch (nd l1 r1) lf = refl
    transMatch (nd l1 r1) (nd l2 r2) =
      eqTrans
        (eqCong (\ flag -> evalCas env13 flag (pair v3 v0) mkDefault)
          (eqCheckEval env13 r1 l2))
        (transMatchFlag (eqTree r1 l2))
      where
        env9 : Env (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
        env9 = extEnv2 (extEnv2
          (extEnv4 env (nd (nd a b) c) payload (nd l1 r1) (nd l2 r2))
          (nd a b) c) a b
        env13 : Env (suc (suc (suc (suc (suc (suc (suc (suc
                 (suc (suc (suc (suc (suc zero)))))))))))))
        env13 = extEnv2 (extEnv2 env9 l1 r1) l2 r2
        transMatchFlag : (flag : Tree) ->
          Eq (evalCas env13 flag (pair v3 v0) mkDefault)
             (transHelp flag (nd l1 r1) (nd l2 r2))
        transMatchFlag lf = refl
        transMatchFlag (nd x y) = refl

abstract

  thTerm-correct : (t : Tree) -> Eq (evalWith t thTerm) (thS t)
  thTerm-correct t = thGenFull (extEnv emptyEnv t) t

  thTermFull-correct : (t : Tree) -> Eq (evalWith t thTermFull) (thS t)
  thTermFull-correct t = thGenFull (extEnv emptyEnv t) t

------------------------------------------------------------------------
-- Soundness of thS.
--
-- With computation axioms (cas-leaf, rec-leaf), thS no longer produces
-- only reflexivity codes. We prove: every thS output is nd-headed,
-- so eqTree (thS y) lf = falseT. This suffices for Godel sentence eval.

-- Swap always produces nd-headed output.
eqTree-swap-lf : (c : Tree) -> Eq (eqTree (swapCode c) lf) falseT
eqTree-swap-lf lf = refl
eqTree-swap-lf (nd a b) = refl

-- TransHelp always produces nd-headed output.
eqTree-transHelp-lf : (flag l1 r1 l2 r2 : Tree) ->
  Eq (eqTree (transHelp flag (nd l1 r1) (nd l2 r2)) lf) falseT
eqTree-transHelp-lf lf l1 r1 l2 r2 = refl
eqTree-transHelp-lf (nd x y) l1 r1 l2 r2 = refl

-- TransCode always produces nd-headed output.
eqTree-trans-lf : (e1 e2 : Tree) -> Eq (eqTree (transCode e1 e2) lf) falseT
eqTree-trans-lf lf e2 = refl
eqTree-trans-lf (nd l r) lf = refl
eqTree-trans-lf (nd l1 r1) (nd l2 r2) =
  eqTree-transHelp-lf (eqTree r1 l2) l1 r1 l2 r2

-- Main soundness: eqTree (thS y) lf = falseT for all y.
eqTree-thS-lf : (y : Tree) -> Eq (eqTree (thS y) lf) falseT
eqTree-thS-lf lf = refl
eqTree-thS-lf (nd lf payload) = refl
eqTree-thS-lf (nd (nd lf lf) payload) = eqTree-swap-lf (thS payload)
eqTree-thS-lf (nd (nd lf (nd lf lf)) payload) = refl
eqTree-thS-lf (nd (nd lf (nd lf (nd u v))) payload) = refl
eqTree-thS-lf (nd (nd lf (nd (nd lf lf) lf)) payload) = refl
eqTree-thS-lf (nd (nd lf (nd (nd lf lf) (nd z s))) payload) = refl
eqTree-thS-lf (nd (nd lf (nd (nd lf (nd c d)) e)) payload) = refl
eqTree-thS-lf (nd (nd lf (nd (nd (nd c d) e) f)) payload) = refl
eqTree-thS-lf (nd (nd (nd a b) c) payload) =
  eqTree-trans-lf (thS (nd (nd a b) c)) (thS payload)

------------------------------------------------------------------------
-- Semantic soundness predicate (TrueEqCode).
--
-- An equation code nd L R is "true" if both sides decode to closed terms
-- that evaluate to the same tree. Uses vacuous truth when either decode
-- fails.
--
-- NOTE: This predicate is preserved by swapCode (symmetry) but NOT by
-- transCode (transitivity), because the vacuous truth for "one side
-- decodes, other doesn't" breaks composition. Full soundness for thS
-- requires either restricting to valid proof trees or a stronger
-- invariant. See eqTree-thS-lf for the currently-proved soundness.

open import Rose.Base using (Unit; tt; Maybe; nothing; just; maybeMap)
open import Rose.Code using (decodeTerm)

evalCode : Tree -> Maybe Tree
evalCode c = maybeMap eval (decodeTerm zero c)

trueEqMaybe : Maybe Tree -> Maybe Tree -> Set
trueEqMaybe nothing nothing = Unit
trueEqMaybe nothing (just b) = Unit
trueEqMaybe (just a) nothing = Unit
trueEqMaybe (just a) (just b) = Eq a b

TrueEqCode : Tree -> Set
TrueEqCode lf = Unit
TrueEqCode (nd l r) = trueEqMaybe (evalCode l) (evalCode r)

-- Both sides the same => trivially true.
trueEqMaybe-refl : (x : Maybe Tree) -> trueEqMaybe x x
trueEqMaybe-refl nothing = tt
trueEqMaybe-refl (just a) = refl

-- Symmetry: swap sides.
trueEqMaybe-sym : (x y : Maybe Tree) -> trueEqMaybe x y -> trueEqMaybe y x
trueEqMaybe-sym nothing nothing p = tt
trueEqMaybe-sym nothing (just b) p = tt
trueEqMaybe-sym (just a) nothing p = tt
trueEqMaybe-sym (just a) (just b) p = eqSym p

-- Reflexivity codes are trivially true (both sides identical).
trueEq-refl : (payload : Tree) ->
  TrueEqCode (nd (codeReify payload) (codeReify payload))
trueEq-refl payload = trueEqMaybe-refl (evalCode (codeReify payload))

-- SwapCode preserves TrueEqCode.
trueEq-swap : (c : Tree) -> TrueEqCode c -> TrueEqCode (swapCode c)
trueEq-swap lf p = trueEqMaybe-refl (evalCode (nd lf lf))
trueEq-swap (nd l r) p = trueEqMaybe-sym (evalCode l) (evalCode r) p

-- DefaultCode is a true equation code (it's a reflexivity code).
trueEq-default : TrueEqCode defaultCode
trueEq-default = trueEqMaybe-refl (evalCode (nd lf lf))

-- Round-trip corollary: evalCode (codeTerm t) = just (eval t).
open import Rose.CodeProps using (decodeTerm-codeTerm)

evalCode-codeTerm : (t : Term zero) -> Eq (evalCode (codeTerm t)) (just (eval t))
evalCode-codeTerm t = eqCong (maybeMap eval) (decodeTerm-codeTerm t)

------------------------------------------------------------------------
-- Valid proof trees.
--
-- A tree is a valid proof tree if it matches one of the thS branches
-- and any axiom data it carries are actual term codes.

IsTermCode : Nat -> Tree -> Set
IsTermCode n c = Sigma (Term n) (\ t -> Eq (codeTerm t) c)

data ValidProof : Tree -> Set where
  vpBase : ValidProof lf
  vpRefl : (payload : Tree) -> ValidProof (nd lf payload)
  vpSym : (payload : Tree) -> ValidProof payload ->
           ValidProof (nd (nd lf lf) payload)
  vpCasLeaf : (u v payload : Tree) ->
              IsTermCode zero u -> IsTermCode (suc (suc zero)) v ->
              ValidProof (nd (nd lf (nd lf (nd u v))) payload)
  vpRecLeaf : (z s payload : Tree) ->
              IsTermCode zero z ->
              IsTermCode (suc (suc (suc (suc zero)))) s ->
              ValidProof (nd (nd lf (nd (nd lf lf) (nd z s))) payload)
  vpAxDef1 : (payload : Tree) ->
             ValidProof (nd (nd lf (nd lf lf)) payload)
  vpAxDef2 : (payload : Tree) ->
             ValidProof (nd (nd lf (nd (nd lf lf) lf)) payload)
  vpAxDef3 : (c d e payload : Tree) ->
             ValidProof (nd (nd lf (nd (nd lf (nd c d)) e)) payload)
  vpAxDef4 : (c d e f payload : Tree) ->
             ValidProof (nd (nd lf (nd (nd (nd c d) e) f)) payload)
  vpTrans : (a b c payload : Tree) ->
            ValidProof (nd (nd a b) c) -> ValidProof payload ->
            ValidProof (nd (nd (nd a b) c) payload)

------------------------------------------------------------------------
-- ThSResult: characterizes thS output on valid proofs.
--
-- Every valid thS output is nd (codeTerm l) (codeTerm r) with eval l = eval r.
-- This is strictly stronger than TrueEqCode (no vacuous truth).

data ThSResult (c : Tree) : Set where
  thSR : (l r : Term zero) -> Eq c (nd (codeTerm l) (codeTerm r)) ->
         Eq (eval l) (eval r) -> ThSResult c

------------------------------------------------------------------------
-- Helpers for ThSResult composition.

just-inj : {A : Set} {a b : A} -> Eq (just a) (just b) -> Eq a b
just-inj refl = refl

-- If codeTerm r1 = codeTerm l2 as trees, then eval r1 = eval l2.
codeTermEvalEq : (t1 t2 : Term zero) -> Eq (codeTerm t1) (codeTerm t2) ->
  Eq (eval t1) (eval t2)
codeTermEvalEq t1 t2 eq =
  just-inj (eqTrans (eqSym (evalCode-codeTerm t1))
           (eqTrans (eqCong evalCode eq)
                    (evalCode-codeTerm t2)))

-- Swap preserves ThSResult.
swap-thSResult : (c : Tree) -> ThSResult c -> ThSResult (swapCode c)
swap-thSResult _ (thSR l r eq evalEq) =
  eqSubst (\ x -> ThSResult (swapCode x)) (eqSym eq)
    (thSR r l refl (eqSym evalEq))

-- TransCode preserves ThSResult.
trans-thSResult : (e1 e2 : Tree) -> ThSResult e1 -> ThSResult e2 ->
  ThSResult (transCode e1 e2)
trans-thSResult e1 e2 (thSR l1 r1 eq1 p1) (thSR l2 r2 eq2 p2) =
  eqSubst (\ x -> ThSResult (transCode x e2)) (eqSym eq1)
    (eqSubst (\ x -> ThSResult (transCode (nd (codeTerm l1) (codeTerm r1)) x))
             (eqSym eq2)
      (transOnCoded l1 r1 l2 r2 p1 p2))
  where
    transOnCoded : (l1 r1 l2 r2 : Term zero) ->
      Eq (eval l1) (eval r1) -> Eq (eval l2) (eval r2) ->
      ThSResult (transCode (nd (codeTerm l1) (codeTerm r1))
                           (nd (codeTerm l2) (codeTerm r2)))
    transOnCoded l1 r1 l2 r2 p1 p2 =
      transOnFlag (eqTree (codeTerm r1) (codeTerm l2)) l1 r1 l2 r2 p1 p2 refl
      where
        transOnFlag : (flag : Tree) ->
          (l1 r1 l2 r2 : Term zero) ->
          Eq (eval l1) (eval r1) -> Eq (eval l2) (eval r2) ->
          Eq flag (eqTree (codeTerm r1) (codeTerm l2)) ->
          ThSResult (transHelp flag
            (nd (codeTerm l1) (codeTerm r1))
            (nd (codeTerm l2) (codeTerm r2)))
        transOnFlag lf l1 r1 l2 r2 p1 p2 flagEq =
          thSR l1 r2 refl
            (eqTrans p1
              (eqTrans (codeTermEvalEq r1 l2
                (eqTree-sound (codeTerm r1) (codeTerm l2) (eqSym flagEq)))
              p2))
        transOnFlag (nd x y) l1 r1 l2 r2 p1 p2 flagEq =
          thSR leaf leaf refl refl

------------------------------------------------------------------------
-- Main theorem: thS-valid.

thS-valid : (p : Tree) -> ValidProof p -> ThSResult (thS p)
thS-valid lf vpBase = thSR leaf leaf refl refl
thS-valid (nd lf payload) (vpRefl _) =
  thSR (reify payload) (reify payload)
    (eqCong2 nd (codeReify-correct payload) (codeReify-correct payload))
    refl
thS-valid (nd (nd lf lf) payload) (vpSym _ vp) =
  swap-thSResult (thS payload) (thS-valid payload vp)
thS-valid (nd (nd lf (nd lf lf)) payload) (vpAxDef1 _) =
  thSR leaf leaf refl refl
thS-valid (nd (nd lf (nd lf (nd u v))) payload)
          (vpCasLeaf _ _ _ (mkSigma U eqU) (mkSigma V eqV)) =
  thSR (cas leaf U V) U
    (eqCong2 nd
      (eqCong (\ p -> nd tagCase (nd (nd tagLeaf lf) p))
              (eqCong2 nd (eqSym eqU) (eqSym eqV)))
      (eqSym eqU))
    refl
thS-valid (nd (nd lf (nd (nd lf lf) lf)) payload) (vpAxDef2 _) =
  thSR leaf leaf refl refl
thS-valid (nd (nd lf (nd (nd lf lf) (nd z s))) payload)
          (vpRecLeaf _ _ _ (mkSigma Z eqZ) (mkSigma S eqS)) =
  thSR (rec leaf Z S) Z
    (eqCong2 nd
      (eqCong (\ p -> nd tagRec (nd (nd tagLeaf lf) p))
              (eqCong2 nd (eqSym eqZ) (eqSym eqS)))
      (eqSym eqZ))
    refl
thS-valid (nd (nd lf (nd (nd lf (nd c d)) e)) payload) (vpAxDef3 _ _ _ _) =
  thSR leaf leaf refl refl
thS-valid (nd (nd lf (nd (nd (nd c d) e) f)) payload) (vpAxDef4 _ _ _ _ _) =
  thSR leaf leaf refl refl
thS-valid (nd (nd (nd a b) c) payload) (vpTrans _ _ _ _ vp1 vp2) =
  trans-thSResult (thS (nd (nd a b) c)) (thS payload)
    (thS-valid (nd (nd a b) c) vp1) (thS-valid payload vp2)

------------------------------------------------------------------------
-- Conversion: ThSResult implies TrueEqCode.

thSResult-trueEq : (c : Tree) -> ThSResult c -> TrueEqCode c
thSResult-trueEq _ (thSR l r eq evalEq) =
  eqSubst TrueEqCode (eqSym eq)
    (eqSubst (\ x -> trueEqMaybe x (evalCode (codeTerm r)))
      (eqSym (evalCode-codeTerm l))
      (eqSubst (\ x -> trueEqMaybe (just (eval l)) x)
        (eqSym (evalCode-codeTerm r))
        evalEq))

------------------------------------------------------------------------
-- Full soundness: valid proof trees produce true equation codes.

thS-true : (p : Tree) -> ValidProof p -> TrueEqCode (thS p)
thS-true p vp = thSResult-trueEq (thS p) (thS-valid p vp)

------------------------------------------------------------------------
-- D_thS: the proof-quoting operator (Priority 3).
--
-- Given proof tree p, dThS(p) is a new proof tree whose theorem is
-- the reflexivity equation "thS(p) = thS(p)".
--
-- At the metalevel: dThS p = nd lf (thS p), using the refl branch.
-- Internally: dThSTerm = pair leaf thTerm.

dThS : Tree -> Tree
dThS p = nd lf (thS p)

dThSTerm : Term (suc zero)
dThSTerm = pair leaf thTerm

-- Metalevel correctness: thS (dThS p) is a reflexivity code for thS(p).
dThS-thS : (p : Tree) ->
  Eq (thS (dThS p)) (nd (codeReify (thS p)) (codeReify (thS p)))
dThS-thS p = refl

-- Internal correctness: dThSTerm computes dThS.
dThSTerm-correct : (p : Tree) -> Eq (evalWith p dThSTerm) (dThS p)
dThSTerm-correct p = eqCong (nd lf) (thTerm-correct p)

-- Validity: dThS always produces a valid proof (reflexivity).
dThS-valid : (p : Tree) -> ValidProof (dThS p)
dThS-valid p = vpRefl (thS p)

-- The equation proved by dThS(p) is always true.
dThS-trueEq : (p : Tree) -> TrueEqCode (thS (dThS p))
dThS-trueEq p = trueEq-refl (thS p)

