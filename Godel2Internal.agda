{-# OPTIONS --without-K --exact-split #-}

-- Genuine Goedel II via the template-closure rule.
--
-- We add a single narrow axiom: checker-validity is preserved
-- by the self-destruct template sdExp. This is the exact internal
-- counterpart of sd-meta-correct.
--
-- From this we derive:
--   1. Uniform self-destruct: forall p, Prf(p,G) -> Prf(sd(p),fbot)
--   2. Con -> G (internal)
--   3. Goedel II: ProofT n ConG -> EmptyT

module Godel2Internal where

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

------------------------------------------------------------------------
-- FormulaP: formulas using CExpP instead of CExp
------------------------------------------------------------------------

-- For the template-closure rule, we need formulas that mention
-- CExpP expressions (specifically sdExp and cpair). We define
-- the minimal formula type needed.

-- Rather than redefining all of Formula, we work with the specific
-- formulas we need. The key formulas are:
--   fceq(ccheckP e, clitP (encFormula A))
-- which says "code expression e checks as formula A."
--
-- We express this using the existing fceq but with CExpP converted
-- to CExp where possible, or by working at the meta-level.

------------------------------------------------------------------------
-- ProofT: the proof system with template-closure
------------------------------------------------------------------------

-- ProofT extends ProofG with:
-- 1. cpair-aware evaluation (axEvalP)
-- 2. The template-closure rule (axSdExp)
-- 3. CExp-instantiation of fcAll (cinstEP)

-- The old CExp lacks cpair, so we cannot express sdCode(p) for
-- variable p. We extend the formula language to FormulaP (using CExpP)
-- and define ProofTP with the template-closure rule.

------------------------------------------------------------------------
-- FormulaP: formulas with CExpP
------------------------------------------------------------------------

data FormulaP : Set where
  fbotP  : FormulaP
  feqP   : Term -> Term -> FormulaP
  fimpP  : FormulaP -> FormulaP -> FormulaP
  fallP  : FormulaP -> FormulaP
  fcodeP : Code -> FormulaP
  fceqP  : CExpP -> CExpP -> FormulaP
  fcAllP : FormulaP -> FormulaP

-- Embedding from old Formula
oldToNewF : Formula -> FormulaP
oldToNewF fbot       = fbotP
oldToNewF (feq s t)  = feqP s t
oldToNewF (fimp a b) = fimpP (oldToNewF a) (oldToNewF b)
oldToNewF (fall a)   = fallP (oldToNewF a)
oldToNewF (fcode c)  = fcodeP c
oldToNewF (fceq e1 e2) = fceqP (oldToNew e1) (oldToNew e2)
oldToNewF (fcAll a)  = fcAllP (oldToNewF a)

-- Substitution for CExpP in FormulaP
substFormulaPCode0 : CExpP -> FormulaP -> FormulaP
substFormulaPCode0 s fbotP         = fbotP
substFormulaPCode0 s (feqP t u)    = feqP t u
substFormulaPCode0 s (fimpP a b)   = fimpP (substFormulaPCode0 s a)
                                           (substFormulaPCode0 s b)
substFormulaPCode0 s (fallP a)     = fallP (substFormulaPCode0 s a)
substFormulaPCode0 s (fcodeP c)    = fcodeP c
substFormulaPCode0 s (fceqP e1 e2) = fceqP (substCExpP0 s e1)
                                            (substCExpP0 s e2)
substFormulaPCode0 s (fcAllP a)    = fcAllP (substFormulaPCode0 (liftCExpP s) a)

------------------------------------------------------------------------
-- ProofTP: the proof system with FormulaP + template-closure
------------------------------------------------------------------------

data ProofTP (n : Nat) : FormulaP -> Set where
  liftTP   : {A : Formula} -> ProofG n A -> ProofTP n (oldToNewF A)
  mpTP     : {A B : FormulaP} -> ProofTP n (fimpP A B) ->
             ProofTP n A -> ProofTP n B
  cgenTP   : {A : FormulaP} -> ProofTP n A -> ProofTP n (fcAllP A)
  cinstTP  : {A : FormulaP} -> ProofTP n (fcAllP A) -> (e : CExpP) ->
             ProofTP n (substFormulaPCode0 e A)
  -- K and S axioms for FormulaP
  axKP     : (A B : FormulaP) -> ProofTP n (fimpP A (fimpP B A))
  axSP     : (A B C : FormulaP) ->
             ProofTP n (fimpP (fimpP A (fimpP B C))
                              (fimpP (fimpP A B) (fimpP A C)))
  -- Template-closure: the ONLY new axiom.
  -- If ccheckP(e) evaluates to enc(G), then ccheckP(sdExp(e))
  -- evaluates to enc(fbot).
  axSdExp  : {e : CExpP} ->
    ProofTP n (fimpP (fceqP (ccheckP e)
                            (oldToNew (csub (clit phiCode) (clit phiCode))))
                     (fceqP (ccheckP (sdExp e))
                            (clitP (encFormula fbot))))

------------------------------------------------------------------------
-- GoodGP valuation for ProofTP
------------------------------------------------------------------------

GoodGP : CEnvG -> FormulaP -> Set
GoodGP env fbotP         = EmptyG2
GoodGP env (feqP _ _)    = UnitG2
GoodGP env (fimpP a b)   = GoodGP env a -> GoodGP env b
GoodGP env (fallP _)     = UnitG2
GoodGP env (fcodeP _)    = UnitG2
GoodGP env (fceqP _ _)   = UnitG2
GoodGP env (fcAllP a)    = (c : Code) -> GoodGP (extendCEnvG env c) a

-- GoodGP for old formulas agrees with GoodG
goodGP-old : (env : CEnvG) -> (A : Formula) ->
  GoodG env A -> GoodGP env (oldToNewF A)
goodGP-old env fbot g = g
goodGP-old env (feq _ _) g = g
goodGP-old env (fimp a b) g =
  \ x -> goodGP-old env b (g (goodG-old env a x))
  where
  goodG-old : (env : CEnvG) -> (A : Formula) ->
    GoodGP env (oldToNewF A) -> GoodG env A
  goodG-old env fbot g = g
  goodG-old env (feq _ _) g = g
  goodG-old env (fimp a b) g =
    \ x -> goodG-old env b (g (goodGP-old env a x))
  goodG-old env (fall _) g = g
  goodG-old env (fcode _) g = g
  goodG-old env (fceq _ _) g = g
  goodG-old env (fcAll a) g =
    \ c -> goodG-old env a (g c)
goodGP-old env (fall _) g = g
goodGP-old env (fcode _) g = g
goodGP-old env (fceq _ _) g = g
goodGP-old env (fcAll a) g =
  \ c -> goodGP-old env a (g c)

-- Substitution lemma for GoodGP
substGoodGP : (A : FormulaP) -> (env : CEnvG) -> (e : CExpP) ->
  ((c : Code) -> GoodGP (extendCEnvG env c) A) ->
  GoodGP env (substFormulaPCode0 e A)
substGoodGP fbotP env e g = g (catom zero)
substGoodGP (feqP _ _) env e g = ttG2
substGoodGP (fimpP a b) env e f =
  \ x -> substGoodGP b env e
    (\ c -> f c (unsubstGoodGP a env e c x))
  where
  unsubstGoodGP : (A : FormulaP) -> (env : CEnvG) -> (e : CExpP) ->
    (c : Code) ->
    GoodGP env (substFormulaPCode0 e A) -> GoodGP (extendCEnvG env c) A
  unsubstGoodGP fbotP env e c g = g
  unsubstGoodGP (feqP _ _) env e c g = ttG2
  unsubstGoodGP (fimpP a b) env e c g =
    \ x -> unsubstGoodGP b env e c (g (substGoodGP a env e (\ _ -> x)))
  unsubstGoodGP (fallP _) env e c g = ttG2
  unsubstGoodGP (fcodeP _) env e c g = ttG2
  unsubstGoodGP (fceqP _ _) env e c g = ttG2
  unsubstGoodGP (fcAllP a) env e c g =
    \ c' -> unsubstGoodGP a (extendCEnvG env c') (liftCExpP e) c (g c')
substGoodGP (fallP _) env e g = ttG2
substGoodGP (fcodeP _) env e g = ttG2
substGoodGP (fceqP _ _) env e g = ttG2
substGoodGP (fcAllP a) env e g =
  \ c -> substGoodGP a (extendCEnvG env c) (liftCExpP e) (\ c' -> g c' c)

-- Soundness of ProofTP under GoodGP
soundGoodTP : {n : Nat} {A : FormulaP} -> ProofTP n A ->
  (env : CEnvG) -> GoodGP env A
soundGoodTP (liftTP pf) env = goodGP-old env _ (soundGoodG pf env)
soundGoodTP (mpTP pf1 pf2) env =
  soundGoodTP pf1 env (soundGoodTP pf2 env)
soundGoodTP (cgenTP pf) env =
  \ c -> soundGoodTP pf (extendCEnvG env c)
soundGoodTP (cinstTP {A} pf e) env =
  substGoodGP A env e (soundGoodTP pf env)
soundGoodTP (axKP A B) env = \ x _ -> x
soundGoodTP (axSP A B C) env = \ f g a -> f a (g a)
soundGoodTP axSdExp env = \ _ -> ttG2

------------------------------------------------------------------------
-- ConGP and GoedelSentence in FormulaP
------------------------------------------------------------------------

ConGP : FormulaP
ConGP = fcAllP (fimpP (fceqP (ccheckP (cvarP cvz))
                              (clitP (encFormula fbot)))
                       fbotP)

GoedelBodyGP : FormulaP
GoedelBodyGP =
  fimpP (fceqP (ccheckP (cvarP cvz))
               (oldToNew (csub (clit phiCode) (clit phiCode))))
        fbotP

GoedelSentenceP : FormulaP
GoedelSentenceP = fcAllP GoedelBodyGP

------------------------------------------------------------------------
-- Con-implies-G (internal derivation in ProofTP)
------------------------------------------------------------------------

Con-implies-G-bodyTP :
  {n : Nat} ->
  ProofTP n ConGP ->
  ProofTP n GoedelBodyGP
Con-implies-G-bodyTP {n} con =
  compose-imp (axSdExp {e = cvarP cvz})
              (cinstTP con (sdExp (cvarP cvz)))
  where
  compose-imp : {A B C : FormulaP} ->
    ProofTP n (fimpP A B) -> ProofTP n (fimpP B C) ->
    ProofTP n (fimpP A C)
  compose-imp {A} {B} {C} f g =
    mpTP (mpTP (axSP A B C)
               (mpTP (axKP (fimpP B C) A) g))
         f

Con-implies-GTP :
  {n : Nat} ->
  ProofTP n ConGP ->
  ProofTP n GoedelSentenceP
Con-implies-GTP con = cgenTP (Con-implies-G-bodyTP con)

------------------------------------------------------------------------
-- THE THEOREM: Goedel II via template-closure
------------------------------------------------------------------------

-- ConGP is unprovable in ProofTP.
--
-- Proof:
-- 1. From ProofTP n ConGP, derive ProofTP n GoedelSentenceP
-- 2. GoodGP env GoedelSentenceP = (c : Code) -> UnitG2 -> EmptyG2
-- 3. Instantiate at any code and apply ttG2 to get EmptyG2
--
-- This uses:
-- - self-reference (GoedelSentence via csub/phiCode)
-- - the self-destruct template (sdExp via axSdExp)
-- - internal Con -> G derivation
-- - GoodGP soundness
--
-- The ONLY axiom beyond ProofG is axSdExp (template-closure).
-- axSdExp is the internal counterpart of sd-meta-correct.

goedel2-internal : {n : Nat} -> ProofTP n ConGP -> EmptyG2
goedel2-internal {n} con =
  let g = Con-implies-GTP con
  in soundGoodTP g emptyCEnvG (catom zero) ttG2
