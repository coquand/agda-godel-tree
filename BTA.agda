{-# OPTIONS --without-K --exact-split #-}

-- BTA.agda -- Binary Tree Arithmetic (Stage 1)
--
-- Extends CExpP with code destructors (cleft, cright, cisNode)
-- and provides a tree induction rule for ProofTP.
--
-- The destructors allow FormulaP to express structural properties
-- of codes (atom vs node, children). The induction rule is added
-- as a constructor of ProofTI (extending ProofTP), with soundness
-- proved via GoodGI.

module BTA where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekGodel2Genuine
open import CExpPair
open import SelfDestruct
open import SelfDestructExp
open import Godel2Internal

------------------------------------------------------------------------
-- CExpI: CExpP extended with code destructors
------------------------------------------------------------------------

data CExpI : Set where
  cvarI   : CVar -> CExpI
  clitI   : Code -> CExpI
  ccheckI : CExpI -> CExpI
  csubI   : CExpI -> CExpI -> CExpI
  cpairI  : CExpI -> CExpI -> CExpI     -- from CExpP: builds cnode
  cleft   : CExpI -> CExpI              -- left child of cnode
  cright  : CExpI -> CExpI              -- right child of cnode
  cisNode : CExpI -> CExpI              -- returns catom zero for nodes,
                                         -- nothing for atoms

------------------------------------------------------------------------
-- Embedding from CExpP into CExpI
------------------------------------------------------------------------

pToI : CExpP -> CExpI
pToI (cvarP v)     = cvarI v
pToI (clitP c)     = clitI c
pToI (ccheckP e)   = ccheckI (pToI e)
pToI (csubP e1 e2) = csubI (pToI e1) (pToI e2)
pToI (cpair e1 e2) = cpairI (pToI e1) (pToI e2)

------------------------------------------------------------------------
-- Lifting and substitution for CExpI
------------------------------------------------------------------------

liftCExpI : CExpI -> CExpI
liftCExpI (cvarI v)     = cvarI (cvs v)
liftCExpI (clitI c)     = clitI c
liftCExpI (ccheckI e)   = ccheckI (liftCExpI e)
liftCExpI (csubI e1 e2) = csubI (liftCExpI e1) (liftCExpI e2)
liftCExpI (cpairI e1 e2) = cpairI (liftCExpI e1) (liftCExpI e2)
liftCExpI (cleft e)     = cleft (liftCExpI e)
liftCExpI (cright e)    = cright (liftCExpI e)
liftCExpI (cisNode e)   = cisNode (liftCExpI e)

substCExpI0 : CExpI -> CExpI -> CExpI
substCExpI0 s (cvarI cvz)     = s
substCExpI0 s (cvarI (cvs v)) = cvarI v
substCExpI0 s (clitI c)       = clitI c
substCExpI0 s (ccheckI e)     = ccheckI (substCExpI0 s e)
substCExpI0 s (csubI e1 e2)   = csubI (substCExpI0 s e1) (substCExpI0 s e2)
substCExpI0 s (cpairI e1 e2)  = cpairI (substCExpI0 s e1) (substCExpI0 s e2)
substCExpI0 s (cleft e)       = cleft (substCExpI0 s e)
substCExpI0 s (cright e)      = cright (substCExpI0 s e)
substCExpI0 s (cisNode e)     = cisNode (substCExpI0 s e)

------------------------------------------------------------------------
-- Helper: code destructors as functions on Code
------------------------------------------------------------------------

leftChild : Code -> Maybe Code
leftChild (catom _)    = nothing
leftChild (cnode a b)  = just a

rightChild : Code -> Maybe Code
rightChild (catom _)   = nothing
rightChild (cnode a b) = just b

nodeTag : Code -> Maybe Code
nodeTag (catom _)    = nothing
nodeTag (cnode _ _)  = just (catom zero)

------------------------------------------------------------------------
-- Extended evaluator
------------------------------------------------------------------------

evalGI : Nat -> CExpI -> Maybe Code
evalGI zero _ = nothing
evalGI (suc n) (cvarI _) = nothing
evalGI (suc n) (clitI c) = just c
evalGI (suc n) (ccheckI e) =
  maybeBind (evalGI n e) (\ p ->
  maybeBind (checkG n p) (\ a ->
  just (encFormula a)))
evalGI (suc n) (csubI e1 e2) =
  maybeBind (evalGI n e1) (\ c1 ->
  maybeBind (evalGI n e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))
evalGI (suc n) (cpairI e1 e2) =
  maybeBind (evalGI n e1) (\ c1 ->
  maybeBind (evalGI n e2) (\ c2 ->
  just (cnode c1 c2)))
evalGI (suc n) (cleft e) =
  maybeBind (evalGI n e) leftChild
evalGI (suc n) (cright e) =
  maybeBind (evalGI n e) rightChild
evalGI (suc n) (cisNode e) =
  maybeBind (evalGI n e) nodeTag

------------------------------------------------------------------------
-- evalGI agrees with evalGP on CExpP terms
------------------------------------------------------------------------

evalGI-pToI : (n : Nat) -> (e : CExpP) ->
  Eq (evalGI n (pToI e)) (evalGP n e)
evalGI-pToI zero e = refl
evalGI-pToI (suc n) (cvarP _) = refl
evalGI-pToI (suc n) (clitP c) = refl
evalGI-pToI (suc n) (ccheckP e) =
  eqCong (\ r -> maybeBind r (\ p -> maybeBind (checkG n p)
            (\ a -> just (encFormula a))))
         (evalGI-pToI n e)
evalGI-pToI (suc n) (csubP e1 e2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ c1 ->
              maybeBind (evalGI n (pToI e2)) (\ c2 ->
              maybeBind (decFormula c1) (\ a ->
              just (encFormula (substFormulaCode0 (clit c2) a))))))
            (evalGI-pToI n e1))
    (eqCong (\ r -> maybeBind (evalGP n e1) (\ c1 ->
              maybeBind r (\ c2 ->
              maybeBind (decFormula c1) (\ a ->
              just (encFormula (substFormulaCode0 (clit c2) a))))))
            (evalGI-pToI n e2))
evalGI-pToI (suc n) (cpair e1 e2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ c1 ->
              maybeBind (evalGI n (pToI e2)) (\ c2 ->
              just (cnode c1 c2))))
            (evalGI-pToI n e1))
    (eqCong (\ r -> maybeBind (evalGP n e1) (\ c1 ->
              maybeBind r (\ c2 ->
              just (cnode c1 c2))))
            (evalGI-pToI n e2))

------------------------------------------------------------------------
-- Evaluation lemmas for destructors
------------------------------------------------------------------------

evalGI-cleft : (n : Nat) -> (e : CExpI) -> (a b : Code) ->
  Eq (evalGI n e) (just (cnode a b)) ->
  Eq (evalGI (suc n) (cleft e)) (just a)
evalGI-cleft n e a b h =
  eqCong (\ r -> maybeBind r leftChild) h

evalGI-cright : (n : Nat) -> (e : CExpI) -> (a b : Code) ->
  Eq (evalGI n e) (just (cnode a b)) ->
  Eq (evalGI (suc n) (cright e)) (just b)
evalGI-cright n e a b h =
  eqCong (\ r -> maybeBind r rightChild) h

evalGI-cisNode-node : (n : Nat) -> (e : CExpI) -> (a b : Code) ->
  Eq (evalGI n e) (just (cnode a b)) ->
  Eq (evalGI (suc n) (cisNode e)) (just (catom zero))
evalGI-cisNode-node n e a b h =
  eqCong (\ r -> maybeBind r nodeTag) h

evalGI-cisNode-atom : (n : Nat) -> (e : CExpI) -> (k : Nat) ->
  Eq (evalGI n e) (just (catom k)) ->
  Eq (evalGI (suc n) (cisNode e)) nothing
evalGI-cisNode-atom n e k h =
  eqCong (\ r -> maybeBind r nodeTag) h

------------------------------------------------------------------------
-- FormulaI: formulas using CExpI
------------------------------------------------------------------------

data FormulaI : Set where
  fbotI  : FormulaI
  feqI   : Term -> Term -> FormulaI
  fimpI  : FormulaI -> FormulaI -> FormulaI
  fallI  : FormulaI -> FormulaI
  fcodeI : Code -> FormulaI
  fceqI  : CExpI -> CExpI -> FormulaI
  fcAllI : FormulaI -> FormulaI

-- Embedding from FormulaP
pToIF : FormulaP -> FormulaI
pToIF fbotP         = fbotI
pToIF (feqP s t)    = feqI s t
pToIF (fimpP a b)   = fimpI (pToIF a) (pToIF b)
pToIF (fallP a)     = fallI (pToIF a)
pToIF (fcodeP c)    = fcodeI c
pToIF (fceqP e1 e2) = fceqI (pToI e1) (pToI e2)
pToIF (fcAllP a)    = fcAllI (pToIF a)

-- Substitution for CExpI in FormulaI
substFormulaICode0 : CExpI -> FormulaI -> FormulaI
substFormulaICode0 s fbotI         = fbotI
substFormulaICode0 s (feqI t u)    = feqI t u
substFormulaICode0 s (fimpI a b)   = fimpI (substFormulaICode0 s a)
                                            (substFormulaICode0 s b)
substFormulaICode0 s (fallI a)     = fallI (substFormulaICode0 s a)
substFormulaICode0 s (fcodeI c)    = fcodeI c
substFormulaICode0 s (fceqI e1 e2) = fceqI (substCExpI0 s e1)
                                             (substCExpI0 s e2)
substFormulaICode0 s (fcAllI a)    = fcAllI (substFormulaICode0 (liftCExpI s) a)

------------------------------------------------------------------------
-- Lift FormulaI under a binder (shift free code variables up by 1)
------------------------------------------------------------------------

liftFormulaI : FormulaI -> FormulaI
liftFormulaI fbotI         = fbotI
liftFormulaI (feqI s t)    = feqI s t
liftFormulaI (fimpI a b)   = fimpI (liftFormulaI a) (liftFormulaI b)
liftFormulaI (fallI a)     = fallI (liftFormulaI a)
liftFormulaI (fcodeI c)    = fcodeI c
liftFormulaI (fceqI e1 e2) = fceqI (liftCExpI e1) (liftCExpI e2)
liftFormulaI (fcAllI a)    = fcAllI (liftFormulaI a)

------------------------------------------------------------------------
-- Convenience: "c is a node" as a FormulaI
------------------------------------------------------------------------

-- isNodeF : FormulaI that says "the code in variable 0 is a node"
-- i.e., cisNode (cvarI cvz) evaluates to catom zero
isNodeF : FormulaI
isNodeF = fceqI (cisNode (cvarI cvz)) (clitI (catom zero))

------------------------------------------------------------------------
-- ProofTI: proof system with FormulaI + destructors + tree induction
------------------------------------------------------------------------

data ProofTI (n : Nat) : FormulaI -> Set where
  -- Lift from ProofTP
  liftTI   : {A : FormulaP} -> ProofTP n A -> ProofTI n (pToIF A)

  -- Standard rules
  mpTI     : {A B : FormulaI} -> ProofTI n (fimpI A B) ->
             ProofTI n A -> ProofTI n B
  cgenTI   : {A : FormulaI} -> ProofTI n A -> ProofTI n (fcAllI A)
  cinstTI  : {A : FormulaI} -> ProofTI n (fcAllI A) -> (e : CExpI) ->
             ProofTI n (substFormulaICode0 e A)

  -- K and S axioms for FormulaI
  axKI     : (A B : FormulaI) -> ProofTI n (fimpI A (fimpI B A))
  axSI     : (A B C : FormulaI) ->
             ProofTI n (fimpI (fimpI A (fimpI B C))
                              (fimpI (fimpI A B) (fimpI A C)))

  -- Template-closure (lifted from ProofTP)
  axSdExpI : {e : CExpI} ->
    ProofTI n (fimpI (fceqI (ccheckI e)
                             (pToI (oldToNew (csub (clit phiCode)
                                                    (clit phiCode)))))
                      (fceqI (ccheckI (pToI (sdExp (cvarP cvz))))
                             (clitI (encFormula fbot))))

  -- Tree induction rule:
  --   If P holds for all atoms (vacuously: when cisNode is nothing),
  --   and P is preserved at nodes (given P for children),
  --   then P holds for all codes.
  --
  -- Concretely, we add structural induction on Code as a single rule:
  --
  --   Base case: for all c, (cisNode c = nothing) -> P(c)
  --     Since FormulaI can't directly express "cisNode c = nothing",
  --     we formulate the atom case as:
  --       for all c, P(catom-wrapped c)
  --     But we can't quantify over atoms directly...
  --
  -- SIMPLEST APPROACH: the induction rule takes three premises:
  --   (1) P holds at catom zero (the base atom)
  --   (2) P at catom n implies P at catom (suc n)   [not expressible]
  --
  -- Since we can't express Nat induction in FormulaI, use a different
  -- formulation: COMPLETE INDUCTION on Code with cleft/cright.
  --
  -- The rule: if for all c,
  --   (for all d, d = cleft c or d = cright c -> P(d)) -> P(c)
  -- then for all c, P(c).
  --
  -- Even simpler: just postulate the two halves separately.
  --
  -- FINAL APPROACH: we add the induction rule as a SEMANTIC rule.
  -- The rule says: given a proof that P is preserved under cnode
  -- (from P(left) and P(right) to P(cnode left right)), and
  -- given that P holds for all atoms, conclude P holds for all codes.
  --
  -- We express "P holds for all atoms" via a separate code quantifier
  -- that ranges only over atoms. But we don't have that...
  --
  -- PRACTICAL APPROACH: add tree induction as a two-premise rule
  -- where both premises are meta-level Agda functions, validated
  -- by the soundness proof. This mirrors how axEvalG works.

  axTreeInd : {P : FormulaI} ->
    -- Atom case: for every natural number k, P(catom k)
    ((k : Nat) -> ProofTI n (substFormulaICode0 (clitI (catom k)) P)) ->
    -- Node case: for all codes a b, P(a) -> P(b) -> P(cnode a b)
    -- Expressed as: forall c, cisNode(c) = catom 0 ->
    --   P(cleft c) -> P(cright c) -> P(c)
    -- Under one fcAllI binder with c = cvarI cvz:
    ProofTI n (fcAllI
                (fimpI (fceqI (cisNode (cvarI cvz)) (clitI (catom zero)))
                       (fimpI (substFormulaICode0 (cleft (cvarI cvz))
                                (liftFormulaI P))
                              (fimpI (substFormulaICode0 (cright (cvarI cvz))
                                       (liftFormulaI P))
                                     P)))) ->
    ProofTI n (fcAllI P)

------------------------------------------------------------------------
-- GoodGI valuation for ProofTI
------------------------------------------------------------------------

GoodGI : CEnvG -> FormulaI -> Set
GoodGI env fbotI         = EmptyG2
GoodGI env (feqI _ _)    = UnitG2
GoodGI env (fimpI a b)   = GoodGI env a -> GoodGI env b
GoodGI env (fallI _)     = UnitG2
GoodGI env (fcodeI _)    = UnitG2
GoodGI env (fceqI _ _)   = UnitG2
GoodGI env (fcAllI a)    = (c : Code) -> GoodGI (extendCEnvG env c) a

-- GoodGI for lifted FormulaP agrees with GoodGP
goodGI-pToIF : (env : CEnvG) -> (A : FormulaP) ->
  GoodGP env A -> GoodGI env (pToIF A)
goodGI-pToIF env fbotP g = g
goodGI-pToIF env (feqP _ _) g = g
goodGI-pToIF env (fimpP a b) g =
  \ x -> goodGI-pToIF env b (g (goodGP-pToIF env a x))
  where
  goodGP-pToIF : (env : CEnvG) -> (A : FormulaP) ->
    GoodGI env (pToIF A) -> GoodGP env A
  goodGP-pToIF env fbotP g = g
  goodGP-pToIF env (feqP _ _) g = g
  goodGP-pToIF env (fimpP a b) g =
    \ x -> goodGP-pToIF env b (g (goodGI-pToIF env a x))
  goodGP-pToIF env (fallP _) g = g
  goodGP-pToIF env (fcodeP _) g = g
  goodGP-pToIF env (fceqP _ _) g = g
  goodGP-pToIF env (fcAllP a) g =
    \ c -> goodGP-pToIF env a (g c)
goodGI-pToIF env (fallP _) g = g
goodGI-pToIF env (fcodeP _) g = g
goodGI-pToIF env (fceqP _ _) g = g
goodGI-pToIF env (fcAllP a) g =
  \ c -> goodGI-pToIF env a (g c)

-- Substitution lemma for GoodGI
substGoodGI : (A : FormulaI) -> (env : CEnvG) -> (e : CExpI) ->
  ((c : Code) -> GoodGI (extendCEnvG env c) A) ->
  GoodGI env (substFormulaICode0 e A)
substGoodGI fbotI env e g = g (catom zero)
substGoodGI (feqI _ _) env e g = ttG2
substGoodGI (fimpI a b) env e f =
  \ x -> substGoodGI b env e
    (\ c -> f c (unsubstGoodGI a env e c x))
  where
  unsubstGoodGI : (A : FormulaI) -> (env : CEnvG) -> (e : CExpI) ->
    (c : Code) ->
    GoodGI env (substFormulaICode0 e A) -> GoodGI (extendCEnvG env c) A
  unsubstGoodGI fbotI env e c g = g
  unsubstGoodGI (feqI _ _) env e c g = ttG2
  unsubstGoodGI (fimpI a b) env e c g =
    \ x -> unsubstGoodGI b env e c (g (substGoodGI a env e (\ _ -> x)))
  unsubstGoodGI (fallI _) env e c g = ttG2
  unsubstGoodGI (fcodeI _) env e c g = ttG2
  unsubstGoodGI (fceqI _ _) env e c g = ttG2
  unsubstGoodGI (fcAllI a) env e c g =
    \ c' -> unsubstGoodGI a (extendCEnvG env c') (liftCExpI e) c (g c')
substGoodGI (fallI _) env e g = ttG2
substGoodGI (fcodeI _) env e g = ttG2
substGoodGI (fceqI _ _) env e g = ttG2
substGoodGI (fcAllI a) env e g =
  \ c -> substGoodGI a (extendCEnvG env c) (liftCExpI e) (\ c' -> g c' c)

------------------------------------------------------------------------
-- Soundness of tree induction under GoodGI
------------------------------------------------------------------------

-- The key lemma: structural induction on Code gives GoodGI for fcAllI P
-- from the atom and node premises.
treeIndSound : {P : FormulaI} ->
  (env : CEnvG) ->
  -- Atom premise: for every k, GoodGI at catom k
  ((k : Nat) -> GoodGI env (substFormulaICode0 (clitI (catom k)) P)) ->
  -- Node premise: for all c, if c is a node, P(left c) -> P(right c) -> P(c)
  ((c : Code) -> GoodGI (extendCEnvG env c)
    (fimpI (fceqI (cisNode (cvarI cvz)) (clitI (catom zero)))
           (fimpI (substFormulaICode0 (cleft (cvarI cvz))
                    (liftFormulaI P))
                  (fimpI (substFormulaICode0 (cright (cvarI cvz))
                           (liftFormulaI P))
                         P)))) ->
  -- Conclusion
  (c : Code) -> GoodGI (extendCEnvG env c) P
treeIndSound {P} env atomCase nodeCase (catom k) =
  -- For atoms, use atomCase. We need:
  --   GoodGI (extendCEnvG env (catom k)) P
  -- from: GoodGI env (substFormulaICode0 (clitI (catom k)) P)
  -- These are related by the substitution/environment correspondence.
  unsubstGI P env (catom k) (atomCase k)
  where
  -- Helper: unsubstitute for GoodGI
  unsubstGI : (A : FormulaI) -> (env : CEnvG) -> (c : Code) ->
    GoodGI env (substFormulaICode0 (clitI c) A) ->
    GoodGI (extendCEnvG env c) A
  unsubstGI fbotI env c g = g
  unsubstGI (feqI _ _) env c g = ttG2
  unsubstGI (fimpI a b) env c g =
    \ x -> unsubstGI b env c (g (substGI a env c x))
    where
    substGI : (A : FormulaI) -> (env : CEnvG) -> (c : Code) ->
      GoodGI (extendCEnvG env c) A ->
      GoodGI env (substFormulaICode0 (clitI c) A)
    substGI fbotI env c g = g
    substGI (feqI _ _) env c g = ttG2
    substGI (fimpI a b) env c g =
      \ x -> substGI b env c (g (unsubstGI a env c x))
    substGI (fallI _) env c g = ttG2
    substGI (fcodeI _) env c g = ttG2
    substGI (fceqI _ _) env c g = ttG2
    substGI (fcAllI a) env c g =
      \ c' -> substGI a (extendCEnvG env c') c (g c')
  unsubstGI (fallI _) env c g = ttG2
  unsubstGI (fcodeI _) env c g = ttG2
  unsubstGI (fceqI _ _) env c g = ttG2
  unsubstGI (fcAllI a) env c g =
    \ c' -> unsubstGI a (extendCEnvG env c') c (g c')
treeIndSound {P} env atomCase nodeCase (cnode a b) =
  -- For nodes, nodeCase gives us:
  --   GoodGI (extendCEnvG env (cnode a b))
  --     (fimpI (fceqI ...) (fimpI P(left) (fimpI P(right) P)))
  -- which is a function chain. fceqI is UnitG2, so the first
  -- implication is trivially satisfiable.
  let
    step = nodeCase (cnode a b)
    -- step : UnitG2 -> GoodGI ... (fimpI P(left) (fimpI P(right) P))
    step2 = step ttG2
    -- step2 : GoodGI ... (substFormulaICode0 (cleft (cvarI cvz)) (liftFormulaI P))
    --       -> GoodGI ... (fimpI (substFormulaICode0 (cright ...) ...) P)
    -- We need P(a) and P(b) as GoodGI under the right environments.
    -- By induction (Agda structural recursion):
    ihA = treeIndSound {P} env atomCase nodeCase a
    ihB = treeIndSound {P} env atomCase nodeCase b
    -- ihA : GoodGI (extendCEnvG env a) P
    -- ihB : GoodGI (extendCEnvG env b) P
    -- We need to convert these to the substituted forms that step2 expects.
    -- step2 expects GoodGI (extendCEnvG env (cnode a b))
    --   (substFormulaICode0 (cleft (cvarI cvz)) (liftFormulaI P))
    -- Under env' = extendCEnvG env (cnode a b):
    --   cleft (cvarI cvz) evaluates to left child of env'(cvz) = a
    --   So substFormulaICode0 (cleft (cvarI cvz)) (liftFormulaI P)
    --   should be semantically equivalent to P[clitI a / cvz] under env
    --   which is equivalent to GoodGI (extendCEnvG env a) P.
    --
    -- Since GoodGI maps fceqI to UnitG2 (ignoring evaluation details),
    -- the substituted formula's GoodGI value depends only on the
    -- structure of P, not on which CExpI appears in the substitution.
    -- For fimpI, fcAllI etc., the structure is preserved.
    -- So we need: GoodGI (extendCEnvG env (cnode a b))
    --               (substFormulaICode0 (cleft (cvarI cvz)) (liftFormulaI P))
    -- which by the valuation is the same as
    --   GoodGI (extendCEnvG env a) P
    -- because the GoodGI valuation ignores the CExpI arguments in fceqI,
    -- and for structural connectives, substitution commutes with GoodGI.
    --
    -- We prove this via a lemma.
    liftedA = goodGI-lift-env P env a (cnode a b) ihA
    liftedB = goodGI-lift-env P env b (cnode a b) ihB
    allA = \ c -> goodGI-env-irrel (liftFormulaI P)
                    (extendCEnvG env (cnode a b)) a c liftedA
    allB = \ c -> goodGI-env-irrel (liftFormulaI P)
                    (extendCEnvG env (cnode a b)) b c liftedB
    leftIH  = substGoodGI-any (liftFormulaI P) (extendCEnvG env (cnode a b))
                               (cleft (cvarI cvz)) allA
    rightIH = substGoodGI-any (liftFormulaI P) (extendCEnvG env (cnode a b))
                               (cright (cvarI cvz)) allB
  in step2 leftIH rightIH
  where
  -- Lemma: GoodGI is invariant under CExpI substitution for the same
  -- formula structure. Since GoodGI maps fceqI to UnitG2 regardless,
  -- substFormulaICode0 e A has the same GoodGI as substFormulaICode0 e' A
  -- for any e, e'.
  --
  -- More precisely: GoodGI env (substFormulaICode0 e A) depends on A's
  -- structure and the fcAllI bindings, not on the specific CExpI e.

  -- Lemma: GoodGI under extended env with different code has same shape
  -- when P doesn't actually depend on the code variable's value
  -- (because GoodGI makes fceqI trivially true).
  --
  -- Key insight: for the GoodGI valuation, what matters is the
  -- FORMULA STRUCTURE, not the specific code values. So
  -- GoodGI (extendCEnvG env a) P = GoodGI (extendCEnvG env b) P
  -- for any a, b.

  goodGI-env-irrel : (A : FormulaI) -> (env : CEnvG) -> (c1 c2 : Code) ->
    GoodGI (extendCEnvG env c1) A -> GoodGI (extendCEnvG env c2) A
  goodGI-env-irrel fbotI env c1 c2 g = g
  goodGI-env-irrel (feqI _ _) env c1 c2 g = ttG2
  goodGI-env-irrel (fimpI a b) env c1 c2 g =
    \ x -> goodGI-env-irrel b env c1 c2
             (g (goodGI-env-irrel a env c2 c1 x))
  goodGI-env-irrel (fallI _) env c1 c2 g = ttG2
  goodGI-env-irrel (fcodeI _) env c1 c2 g = ttG2
  goodGI-env-irrel (fceqI _ _) env c1 c2 g = ttG2
  goodGI-env-irrel (fcAllI a) env c1 c2 g =
    \ c -> goodGI-env-irrel a (extendCEnvG env c) c1 c2 (g c)

  -- Wait, that's wrong. extendCEnvG env c1 maps cvz -> c1,
  -- and extendCEnvG env c2 maps cvz -> c2. For fcAllI a,
  -- GoodGI (extendCEnvG env c1) (fcAllI a)
  -- = (c : Code) -> GoodGI (extendCEnvG (extendCEnvG env c1) c) a
  -- The inner env has cvz -> c, cvs cvz -> c1, ...
  -- vs for c2: cvz -> c, cvs cvz -> c2, ...
  -- These differ at cvs cvz. But if a has fceqI that references
  -- cvarI (cvs cvz), GoodGI still gives UnitG2.
  -- Actually, GoodGI NEVER looks at the environment at all!
  -- GoodGI is purely structural on the formula.
  -- Let me verify: GoodGI env fbotI = EmptyG2 (no env use)
  -- GoodGI env (fimpI a b) = GoodGI env a -> GoodGI env b (env passed through)
  -- GoodGI env (fcAllI a) = (c : Code) -> GoodGI (extendCEnvG env c) a
  -- The env is only used in fcAllI to extend. But the VALUES in env
  -- never affect the TYPE GoodGI computes, because none of the base
  -- cases (fbotI, feqI, fceqI, fcodeI, fallI) use env.
  -- So goodGI-env-irrel should work but the fcAllI case needs care.

  -- Actually, let me just prove the simpler fact we need:
  -- GoodGI (extendCEnvG env a) P -> GoodGI under substituted form

  -- For the node case, we need to convert
  --   GoodGI (extendCEnvG env a) P
  -- into
  --   GoodGI (extendCEnvG env (cnode a b))
  --          (substFormulaICode0 (cleft (cvarI cvz)) (liftFormulaI P))

  -- Since GoodGI doesn't look at env values for base cases,
  -- and substFormulaICode0/liftFormulaI preserve formula structure
  -- (only changing CExpI arguments in fceqI, which map to UnitG2),
  -- we can prove this by structural induction on P.

  goodGI-lift-env : (A : FormulaI) -> (env : CEnvG) ->
    (c1 c2 : Code) ->
    GoodGI (extendCEnvG env c1) A ->
    GoodGI (extendCEnvG (extendCEnvG env c2) c1) (liftFormulaI A)
  goodGI-lift-env fbotI env c1 c2 g = g
  goodGI-lift-env (feqI _ _) env c1 c2 g = ttG2
  goodGI-lift-env (fimpI a b) env c1 c2 g =
    \ x -> goodGI-lift-env b env c1 c2
             (g (goodGI-unlift-env a env c1 c2 x))
    where
    goodGI-unlift-env : (A : FormulaI) -> (env : CEnvG) ->
      (c1 c2 : Code) ->
      GoodGI (extendCEnvG (extendCEnvG env c2) c1) (liftFormulaI A) ->
      GoodGI (extendCEnvG env c1) A
    goodGI-unlift-env fbotI env c1 c2 g = g
    goodGI-unlift-env (feqI _ _) env c1 c2 g = ttG2
    goodGI-unlift-env (fimpI a b) env c1 c2 g =
      \ x -> goodGI-unlift-env b env c1 c2
               (g (goodGI-lift-env a env c1 c2 x))
    goodGI-unlift-env (fallI _) env c1 c2 g = ttG2
    goodGI-unlift-env (fcodeI _) env c1 c2 g = ttG2
    goodGI-unlift-env (fceqI _ _) env c1 c2 g = ttG2
    goodGI-unlift-env (fcAllI a) env c1 c2 g =
      \ c -> goodGI-unlift-env a (extendCEnvG env c) c1 c2 (g c)
  goodGI-lift-env (fallI _) env c1 c2 g = ttG2
  goodGI-lift-env (fcodeI _) env c1 c2 g = ttG2
  goodGI-lift-env (fceqI _ _) env c1 c2 g = ttG2
  goodGI-lift-env (fcAllI a) env c1 c2 g =
    \ c -> goodGI-lift-env a (extendCEnvG env c) c1 c2 (g c)

  -- Now we need: from GoodGI (extendCEnvG env' c1) (liftFormulaI P)
  -- to GoodGI env' (substFormulaICode0 e (liftFormulaI P))
  -- where env' = extendCEnvG env (cnode a b) and e = cleft (cvarI cvz)
  -- This is just the substitution lemma substGoodGI specialized.
  substGoodGI-any : (A : FormulaI) -> (env : CEnvG) -> (e : CExpI) ->
    ((c : Code) -> GoodGI (extendCEnvG env c) A) ->
    GoodGI env (substFormulaICode0 e A)
  substGoodGI-any = substGoodGI

------------------------------------------------------------------------
-- Soundness of ProofTI under GoodGI
------------------------------------------------------------------------

soundGoodTI : {n : Nat} {A : FormulaI} -> ProofTI n A ->
  (env : CEnvG) -> GoodGI env A
soundGoodTI (liftTI pf) env = goodGI-pToIF env _ (soundGoodTP pf env)
soundGoodTI (mpTI pf1 pf2) env =
  soundGoodTI pf1 env (soundGoodTI pf2 env)
soundGoodTI (cgenTI pf) env =
  \ c -> soundGoodTI pf (extendCEnvG env c)
soundGoodTI (cinstTI {A} pf e) env =
  substGoodGI A env e (soundGoodTI pf env)
soundGoodTI (axKI A B) env = \ x _ -> x
soundGoodTI (axSI A B C) env = \ f g a -> f a (g a)
soundGoodTI axSdExpI env = \ _ -> ttG2
soundGoodTI (axTreeInd {P} atomPf nodePf) env =
  treeIndSound {P} env
    (\ k -> soundGoodTI (atomPf k) env)
    (soundGoodTI nodePf env)

------------------------------------------------------------------------
-- ConGI and GoedelSentenceI in FormulaI
------------------------------------------------------------------------

ConGI : FormulaI
ConGI = fcAllI (fimpI (fceqI (ccheckI (cvarI cvz))
                              (clitI (encFormula fbot)))
                       fbotI)

GoedelBodyGI : FormulaI
GoedelBodyGI =
  fimpI (fceqI (ccheckI (cvarI cvz))
               (pToI (oldToNew (csub (clit phiCode) (clit phiCode)))))
        fbotI

GoedelSentenceI : FormulaI
GoedelSentenceI = fcAllI GoedelBodyGI

------------------------------------------------------------------------
-- Goedel II in ProofTI: ConGI is unprovable
------------------------------------------------------------------------

goedel2-BTA : {n : Nat} -> ProofTI n ConGI -> EmptyG2
goedel2-BTA {n} con =
  soundGoodTI (cgenTI (bodyProof con)) emptyCEnvG (catom zero) ttG2
  where
  compose-impI : {A B C : FormulaI} ->
    ProofTI n (fimpI A B) -> ProofTI n (fimpI B C) ->
    ProofTI n (fimpI A C)
  compose-impI {A} {B} {C} f g =
    mpTI (mpTI (axSI A B C)
               (mpTI (axKI (fimpI B C) A) g))
         f

  bodyProof : ProofTI n ConGI -> ProofTI n GoedelBodyGI
  bodyProof conP =
    compose-impI axSdExpI
                 (cinstTI conP (pToI (sdExp (cvarP cvz))))

------------------------------------------------------------------------
-- STATUS
------------------------------------------------------------------------

-- BTA.agda provides:
--
-- 1. CExpI: CExpP extended with cleft, cright, cisNode destructors
-- 2. evalGI: extended evaluator with destructor semantics
-- 3. FormulaI: formula type using CExpI
-- 4. ProofTI: proof system with tree induction rule (axTreeInd)
-- 5. GoodGI soundness: tree induction is sound under GoodGI valuation
-- 6. goedel2-BTA: Goedel II reproved in this extended system
--
-- The tree induction rule (axTreeInd) has two premises:
--   - Atom case: a meta-level function giving proofs for each catom k
--   - Node case: an object-level proof that P is preserved under cnode
--     (given P for the left and right children)
--
-- Soundness is proved by Agda's structural recursion on Code,
-- using the fact that GoodGI maps fceqI to UnitG2 (trivially true),
-- so the node-is-a-node premise is vacuously satisfiable.
--
-- Next steps (Stage 2): use axTreeInd to derive representability
-- lemmas and ultimately derive axSdExp from more primitive principles.
