{-# OPTIONS --without-K --exact-split #-}

-- Extended CExp with cpair (code-level node constructor).
-- Parallel to the stable core; does NOT modify ChwistekSyntax.

module CExpPair where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekSoundness
open import ChwistekGodel2Genuine

------------------------------------------------------------------------
-- CExpP: CExp extended with cpair
------------------------------------------------------------------------

data CExpP : Set where
  cvarP   : CVar -> CExpP
  clitP   : Code -> CExpP
  ccheckP : CExpP -> CExpP
  csubP   : CExpP -> CExpP -> CExpP
  cpair   : CExpP -> CExpP -> CExpP    -- NEW: evaluates to cnode

------------------------------------------------------------------------
-- Embedding from old CExp
------------------------------------------------------------------------

oldToNew : CExp -> CExpP
oldToNew (cvar v)     = cvarP v
oldToNew (clit c)     = clitP c
oldToNew (ccheck e)   = ccheckP (oldToNew e)
oldToNew (csub e1 e2) = csubP (oldToNew e1) (oldToNew e2)

------------------------------------------------------------------------
-- Lifting and substitution for CExpP
------------------------------------------------------------------------

liftCExpP : CExpP -> CExpP
liftCExpP (cvarP v)     = cvarP (cvs v)
liftCExpP (clitP c)     = clitP c
liftCExpP (ccheckP e)   = ccheckP (liftCExpP e)
liftCExpP (csubP e1 e2) = csubP (liftCExpP e1) (liftCExpP e2)
liftCExpP (cpair e1 e2) = cpair (liftCExpP e1) (liftCExpP e2)

substCExpP0 : CExpP -> CExpP -> CExpP
substCExpP0 s (cvarP cvz)     = s
substCExpP0 s (cvarP (cvs v)) = cvarP v
substCExpP0 s (clitP c)       = clitP c
substCExpP0 s (ccheckP e)     = ccheckP (substCExpP0 s e)
substCExpP0 s (csubP e1 e2)   = csubP (substCExpP0 s e1) (substCExpP0 s e2)
substCExpP0 s (cpair e1 e2)   = cpair (substCExpP0 s e1) (substCExpP0 s e2)

------------------------------------------------------------------------
-- Extended evaluator (mutual recursion with checkG from the core)
------------------------------------------------------------------------

-- evalGP reuses checkG from ChwistekGodel2Genuine for ccheckP.
-- cpair evaluates both sub-expressions and builds cnode.

evalGP : Nat -> CExpP -> Maybe Code
evalGP zero _ = nothing
evalGP (suc n) (cvarP _) = nothing
evalGP (suc n) (clitP c) = just c
evalGP (suc n) (ccheckP e) =
  maybeBind (evalGP n e) (\ p ->
  maybeBind (checkG n p) (\ a ->
  just (encFormula a)))
evalGP (suc n) (csubP e1 e2) =
  maybeBind (evalGP n e1) (\ c1 ->
  maybeBind (evalGP n e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))
evalGP (suc n) (cpair e1 e2) =
  maybeBind (evalGP n e1) (\ c1 ->
  maybeBind (evalGP n e2) (\ c2 ->
  just (cnode c1 c2)))

------------------------------------------------------------------------
-- evalGP agrees with evalG on old CExps
------------------------------------------------------------------------

evalGP-old : (n : Nat) -> (e : CExp) ->
  Eq (evalGP n (oldToNew e)) (evalG n e)
evalGP-old zero e = refl
evalGP-old (suc n) (cvar _) = refl
evalGP-old (suc n) (clit c) = refl
evalGP-old (suc n) (ccheck e) =
  eqCong (\ r -> maybeBind r (\ p -> maybeBind (checkG n p)
            (\ a -> just (encFormula a))))
         (evalGP-old n e)
evalGP-old (suc n) (csub e1 e2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ c1 ->
              maybeBind (evalGP n (oldToNew e2)) (\ c2 ->
              maybeBind (decFormula c1) (\ a ->
              just (encFormula (substFormulaCode0 (clit c2) a))))))
            (evalGP-old n e1))
    (eqCong (\ r -> maybeBind (evalG n e1) (\ c1 ->
              maybeBind r (\ c2 ->
              maybeBind (decFormula c1) (\ a ->
              just (encFormula (substFormulaCode0 (clit c2) a))))))
            (evalGP-old n e2))

------------------------------------------------------------------------
-- cpair evaluation lemma
------------------------------------------------------------------------

evalGP-cpair : (n : Nat) -> (e1 e2 : CExpP) -> (c1 c2 : Code) ->
  Eq (evalGP n e1) (just c1) ->
  Eq (evalGP n e2) (just c2) ->
  Eq (evalGP (suc n) (cpair e1 e2)) (just (cnode c1 c2))
evalGP-cpair n e1 e2 c1 c2 h1 h2 =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ x1 ->
              maybeBind (evalGP n e2) (\ x2 -> just (cnode x1 x2))))
            h1)
    (eqCong (\ r -> maybeBind r (\ x2 -> just (cnode c1 x2)))
            h2)

------------------------------------------------------------------------
-- clitP evaluation
------------------------------------------------------------------------

evalGP-clitP : (n : Nat) -> (c : Code) ->
  Eq (evalGP (suc n) (clitP c)) (just c)
evalGP-clitP n c = refl
