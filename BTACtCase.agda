{-# OPTIONS --without-K --exact-split #-}

-- BTACtCase.agda -- Experiment: adding ctCase to CodeTerm
--
-- FINDING: ctCase (one-level tag dispatch on atom vs node) is
-- NECESSARY for expressing conditional code transformations on
-- variable codes, but INSUFFICIENT to derive the 7 checker axioms
-- without recursion (ctFold). The checker axioms are therefore
-- retained, and Goedel II goes through as before.
--
-- ctCase enables: "if this code is an atom, do X; if a node, do Y"
-- ctCase does NOT enable: defining the recursive proof checker,
-- because checkG calls itself on sub-proofs.
--
-- Conclusion: ctCase + ctFold (primitive recursion on Code trees)
-- would allow DEFINING checkG as a CodeTermC, making the 7
-- checker axioms DERIVABLE from computation rules alone.
-- ctCase alone is a stepping stone, not the full solution.

module BTACtCase where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekGodel2Genuine
open import SelfDestruct

------------------------------------------------------------------------
-- 1. CodeTermC: CodeTerm extended with ctCase
------------------------------------------------------------------------

data CodeTermC : Set where
  ctVarC  : CVar -> CodeTermC
  ctLitC  : Code -> CodeTermC
  ctNodeC : CodeTermC -> CodeTermC -> CodeTermC
  -- Case analysis on Code shape:
  --   ctCaseC target atomBranch nodeBranch
  --   catom k   -> atomBranch with (catom k) bound at index 0
  --   cnode a b -> nodeBranch with b at index 0, a at index 1
  ctCaseC : CodeTermC -> CodeTermC -> CodeTermC -> CodeTermC

------------------------------------------------------------------------
-- 2. Lift and substitution for CodeTermC
------------------------------------------------------------------------

liftCTC : CodeTermC -> CodeTermC
liftCTC (ctVarC v)        = ctVarC (cvs v)
liftCTC (ctLitC c)        = ctLitC c
liftCTC (ctNodeC t1 t2)   = ctNodeC (liftCTC t1) (liftCTC t2)
liftCTC (ctCaseC t ab nb) = ctCaseC (liftCTC t)
                                     (liftCTC ab)
                                     (liftCTC nb)

substCTC0 : CodeTermC -> CodeTermC -> CodeTermC
substCTC0 s (ctVarC cvz)       = s
substCTC0 s (ctVarC (cvs v))   = ctVarC v
substCTC0 s (ctLitC c)         = ctLitC c
substCTC0 s (ctNodeC t1 t2)    = ctNodeC (substCTC0 s t1) (substCTC0 s t2)
substCTC0 s (ctCaseC t ab nb)  = ctCaseC (substCTC0 s t)
                                          (substCTC0 (liftCTC s) ab)
                                          (substCTC0 (liftCTC (liftCTC s)) nb)

------------------------------------------------------------------------
-- 3. FormulaBTAC: formulas with proof predicate (CodeTermC version)
------------------------------------------------------------------------

data FormulaBTAC : Set where
  fbotC  : FormulaBTAC
  fimpC  : FormulaBTAC -> FormulaBTAC -> FormulaBTAC
  fcAllC : FormulaBTAC -> FormulaBTAC
  fPrfC  : CodeTermC -> CodeTermC -> FormulaBTAC

-- Code-expression equality in the CodeTermC world
fceqCC : CodeTermC -> CodeTermC -> FormulaBTAC
fceqCC a b = fPrfC (ctLitC (catom zero)) (ctNodeC (ctLitC (catom n8)) (ctNodeC a b))

substFC0 : CodeTermC -> FormulaBTAC -> FormulaBTAC
substFC0 s fbotC        = fbotC
substFC0 s (fimpC a b)  = fimpC (substFC0 s a) (substFC0 s b)
substFC0 s (fcAllC a)   = fcAllC (substFC0 (liftCTC s) a)
substFC0 s (fPrfC p c)  = fPrfC (substCTC0 s p) (substCTC0 s c)

------------------------------------------------------------------------
-- 4. Helper CodeTermC builders (same as BinaryTreeArith but for C)
------------------------------------------------------------------------

private
  n5 : Nat
  n5 = suc (suc (suc (suc (suc zero))))

  encBotC : Code
  encBotC = encFormula fbot

  encGC : Code
  encGC = encFormula GoedelSentence

  encCSubPhiValC : Code
  encCSubPhiValC = encCSubPhi

  encFceqCTC : CodeTermC -> CodeTermC -> CodeTermC
  encFceqCTC a b = ctNodeC (ctLitC (catom n8)) (ctNodeC a b)

  encCCheckLitCTC : CodeTermC -> CodeTermC
  encCCheckLitCTC p = ctNodeC (ctLitC (catom n18)) (ctNodeC (ctLitC (catom n17)) p)

  axEvalCodeCTC : CodeTermC -> CodeTermC -> CodeTermC
  axEvalCodeCTC encCE encResult =
    ctNodeC (ctLitC (catom n36g)) (ctNodeC encCE encResult)

  encSubstCExpCTC : CodeTermC -> CExp -> CodeTermC
  encSubstCExpCTC c (cvar cvz)     = ctNodeC (ctLitC (catom n17)) c
  encSubstCExpCTC c (cvar (cvs v)) = ctLitC (encCExp (cvar v))
  encSubstCExpCTC c (clit k)       = ctLitC (encCExp (clit k))
  encSubstCExpCTC c (ccheck e)     = ctNodeC (ctLitC (catom n18)) (encSubstCExpCTC c e)
  encSubstCExpCTC c (csub e1 e2)   =
    ctNodeC (ctLitC (catom n19)) (ctNodeC (encSubstCExpCTC c e1) (encSubstCExpCTC c e2))

  encSubstFormulaCTC : CodeTermC -> Formula -> CodeTermC
  encSubstFormulaCTC c fbot       = ctLitC (encFormula fbot)
  encSubstFormulaCTC c (feq s t)  = ctLitC (encFormula (feq s t))
  encSubstFormulaCTC c (fimp a b) =
    ctNodeC (ctLitC (catom n5)) (ctNodeC (encSubstFormulaCTC c a) (encSubstFormulaCTC c b))
  encSubstFormulaCTC c (fall a)   =
    ctNodeC (ctLitC (catom (suc (suc (suc (suc (suc (suc zero))))))))
            (encSubstFormulaCTC c a)
  encSubstFormulaCTC c (fcode k)  = ctLitC (encFormula (fcode k))
  encSubstFormulaCTC c (fceq e1 e2) =
    ctNodeC (ctLitC (catom n8)) (ctNodeC (encSubstCExpCTC c e1) (encSubstCExpCTC c e2))
  encSubstFormulaCTC c (fcAll a)  =
    ctNodeC (ctLitC (catom n9)) (encSubstFormulaCTC c a)

  encGoedelBodyCTC : CodeTermC -> CodeTermC
  encGoedelBodyCTC p =
    ctNodeC (ctLitC (catom n5))
            (ctNodeC (encFceqCTC (encCCheckLitCTC p) (ctLitC encCSubPhiValC))
                     (ctLitC encBotC))

  sdCTC : CodeTermC -> CodeTermC
  sdCTC p =
    let
      step1 = ctNodeC (ctLitC (catom n37g)) (ctNodeC p p)
      step2 = axEvalCodeCTC (encCCheckLitCTC p) (ctLitC encGC)
      step3 = axEvalCodeCTC (ctLitC encCSubPhiValC) (ctLitC encGC)
      step4 = ctNodeC (ctLitC (catom n39g)) step3
      step5 = ctNodeC (ctLitC (catom n38g)) (ctNodeC step2 step4)
    in ctNodeC (ctLitC (catom n33)) (ctNodeC step1 step5)

  selfRefCodeC : CodeTermC
  selfRefCodeC = axEvalCodeCTC (ctLitC encCSubPhiValC) (ctLitC encGC)

  encGCTC : CodeTermC
  encGCTC = ctLitC encGC

  encBotCTC : CodeTermC
  encBotCTC = ctLitC encBotC

------------------------------------------------------------------------
-- 5. ProofCC: proof system with ctCase computation + checker axioms
------------------------------------------------------------------------

-- GoedelBodyF for cinst axiom
private
  GoedelBodyFC : Formula
  GoedelBodyFC = fimp (fceq (ccheck (cvar cvz))
                            (csub (clit phiCode) (clit phiCode)))
                      fbot

data ProofCC : FormulaBTAC -> Set where
  -- Hilbert
  axKC : (A B : FormulaBTAC) -> ProofCC (fimpC A (fimpC B A))
  axSC : (A B C : FormulaBTAC) ->
         ProofCC (fimpC (fimpC A (fimpC B C))
                         (fimpC (fimpC A B)
                                (fimpC A C)))
  mpCC : {A B : FormulaBTAC} -> ProofCC (fimpC A B) -> ProofCC A -> ProofCC B
  cgenCC : {A : FormulaBTAC} -> ProofCC A -> ProofCC (fcAllC A)
  cinstCC : {A : FormulaBTAC} -> ProofCC (fcAllC A) -> (t : CodeTermC) ->
            ProofCC (substFC0 t A)

  -- ctCase computation (beta rules)
  -- These are the NEW axioms that ctCase introduces.
  -- They express: ctCase on a known-shape target reduces.
  axCaseAtomC : {k : Nat} {ab nb : CodeTermC} ->
    ProofCC (fceqCC (ctCaseC (ctLitC (catom k)) ab nb)
                    (substCTC0 (ctLitC (catom k)) ab))
  axCaseNodeC : {a b : Code} {ab nb : CodeTermC} ->
    ProofCC (fceqCC (ctCaseC (ctNodeC (ctLitC a) (ctLitC b)) ab nb)
                    (substCTC0 (ctLitC b) (substCTC0 (liftCTC (ctLitC a)) nb)))

  -- Code equality
  fceqTrCC : {p c1 c2 : CodeTermC} ->
             ProofCC (fimpC (fceqCC p c1) (fceqCC p c2))
  fceqSyCC : {a b : CodeTermC} ->
             ProofCC (fimpC (fceqCC a b) (fceqCC b a))
  axCongNodeCC : {a1 a2 b1 b2 : CodeTermC} ->
                 ProofCC (fimpC (fceqCC a1 a2)
                                (fimpC (fceqCC b1 b2)
                                       (fceqCC (ctNodeC a1 b1) (ctNodeC a2 b2))))

  -- fPrf congruence
  axPrfCongCC : {p c1 c2 : CodeTermC} ->
                ProofCC (fimpC (fPrfC p c1) (fPrfC p c2))

  -- The 7 checker axioms: STILL NEEDED (ctCase alone cannot derive them)
  --
  -- WHY: These axioms connect the ABSTRACT proof predicate fPrfC to
  -- the structure of proof codes. ctCase can inspect code structure,
  -- but fPrfC is not DEFINED in terms of ctCase -- it is abstract.
  -- To derive these axioms, we would need:
  --   (a) A primitive recursion operator ctFold on Code trees, AND
  --   (b) fPrfC DEFINED as "ctFold-based checker returns success"
  -- ctCase alone gives one-level dispatch, not recursion.

  axChkMPctC : {p1 p2 encA encB : CodeTermC} ->
               ProofCC (fimpC (fPrfC p1 (ctNodeC (ctLitC (catom n5)) (ctNodeC encA encB)))
                               (fimpC (fPrfC p2 encA)
                                      (fPrfC (ctNodeC (ctLitC (catom n33)) (ctNodeC p1 p2))
                                             encB)))

  axChkCinstC : (A : Formula) -> {p c : CodeTermC} ->
                ProofCC (fimpC (fPrfC p (ctLitC (encFormula (fcAll A))))
                                (fPrfC (ctNodeC (ctLitC (catom n37g)) (ctNodeC p c))
                                       (encSubstFormulaCTC c A)))

  axChkEvalC : (A : Formula) -> {p : CodeTermC} ->
               ProofCC (fimpC (fPrfC p (ctLitC (encFormula A)))
                               (fPrfC (axEvalCodeCTC (encCCheckLitCTC p) (ctLitC (encFormula A)))
                                      (encFceqCTC (encCCheckLitCTC p) (ctLitC (encFormula A)))))

  axChkSyC : {p : CodeTermC} -> {a b : CodeTermC} ->
             ProofCC (fimpC (fPrfC p (encFceqCTC a b))
                             (fPrfC (ctNodeC (ctLitC (catom n39g)) p) (encFceqCTC b a)))

  axChkTrC : {p1 p2 : CodeTermC} -> {a b c : CodeTermC} ->
             ProofCC (fimpC (fPrfC p1 (encFceqCTC a b))
                             (fimpC (fPrfC p2 (encFceqCTC b c))
                                    (fPrfC (ctNodeC (ctLitC (catom n38g)) (ctNodeC p1 p2))
                                           (encFceqCTC a c))))

  axSelfRefC : ProofCC (fPrfC selfRefCodeC
                               (encFceqCTC (ctLitC encCSubPhiValC) encGCTC))

------------------------------------------------------------------------
-- 6. GoodCC valuation (soundness model)
------------------------------------------------------------------------

private
  GoodCC : CEnvG -> FormulaBTAC -> Set
  GoodCC env fbotC        = EmptyG2
  GoodCC env (fimpC a b)  = GoodCC env a -> GoodCC env b
  GoodCC env (fcAllC a)   = (c : Code) -> GoodCC (extendCEnvG env c) a
  GoodCC env (fPrfC _ _)  = UnitG2

------------------------------------------------------------------------
-- 7. Soundness
------------------------------------------------------------------------

private
  substGoodCC : (A : FormulaBTAC) -> (env : CEnvG) -> (t : CodeTermC) ->
    ((c : Code) -> GoodCC (extendCEnvG env c) A) ->
    GoodCC env (substFC0 t A)
  unsubstGoodCC : (A : FormulaBTAC) -> (env : CEnvG) -> (t : CodeTermC) ->
    (c : Code) ->
    GoodCC env (substFC0 t A) -> GoodCC (extendCEnvG env c) A

  substGoodCC fbotC env t g = g (catom zero)
  substGoodCC (fimpC a b) env t f =
    \ x -> substGoodCC b env t
      (\ c -> f c (unsubstGoodCC a env t c x))
  substGoodCC (fcAllC a) env t g =
    \ c -> substGoodCC a (extendCEnvG env c) (liftCTC t) (\ c' -> g c' c)
  substGoodCC (fPrfC _ _) env t g = ttG2

  unsubstGoodCC fbotC env t c g = g
  unsubstGoodCC (fimpC a b) env t c g =
    \ x -> unsubstGoodCC b env t c
      (g (substGoodCC a env t (\ _ -> x)))
  unsubstGoodCC (fcAllC a) env t c g =
    \ c' -> unsubstGoodCC a (extendCEnvG env c') (liftCTC t) c (g c')
  unsubstGoodCC (fPrfC _ _) env t c g = ttG2

  soundCC : {A : FormulaBTAC} -> ProofCC A -> (env : CEnvG) -> GoodCC env A
  soundCC (axKC A B) env = \ x _ -> x
  soundCC (axSC A B C) env = \ f g a -> f a (g a)
  soundCC (mpCC pf1 pf2) env = soundCC pf1 env (soundCC pf2 env)
  soundCC (cgenCC pf) env = \ c -> soundCC pf (extendCEnvG env c)
  soundCC (cinstCC {A} pf t) env =
    substGoodCC A env t (soundCC pf env)
  soundCC axCaseAtomC env = ttG2
  soundCC axCaseNodeC env = ttG2
  soundCC fceqTrCC env = \ _ -> ttG2
  soundCC fceqSyCC env = \ _ -> ttG2
  soundCC axCongNodeCC env = \ _ _ -> ttG2
  soundCC axPrfCongCC env = \ _ -> ttG2
  soundCC axChkMPctC env = \ _ _ -> ttG2
  soundCC (axChkCinstC A) env = \ _ -> ttG2
  soundCC (axChkEvalC A) env = \ _ -> ttG2
  soundCC axChkSyC env = \ _ -> ttG2
  soundCC axChkTrC env = \ _ _ -> ttG2
  soundCC axSelfRefC env = ttG2

------------------------------------------------------------------------
-- 8. Key formulas
------------------------------------------------------------------------

private
  GoedelBodyCC : FormulaBTAC
  GoedelBodyCC = fimpC (fPrfC (ctVarC cvz) encGCTC) fbotC

  GoedelSentenceCC : FormulaBTAC
  GoedelSentenceCC = fcAllC GoedelBodyCC

  ConCC : FormulaBTAC
  ConCC = fcAllC (fimpC (fPrfC (ctVarC cvz) encBotCTC) fbotC)

------------------------------------------------------------------------
-- 9. sdDerivedImpCC: the key derivation (same structure as BTA)
------------------------------------------------------------------------

private
  p0C : CodeTermC
  p0C = ctVarC cvz

  HTypeC : FormulaBTAC
  HTypeC = fPrfC p0C encGCTC

  S1typeC : FormulaBTAC
  S1typeC = fPrfC (ctNodeC (ctLitC (catom n37g)) (ctNodeC p0C p0C))
                  (encGoedelBodyCTC p0C)

  S2typeC : FormulaBTAC
  S2typeC = fPrfC (axEvalCodeCTC (encCCheckLitCTC p0C) encGCTC)
                  (encFceqCTC (encCCheckLitCTC p0C) encGCTC)

  S3typeC : FormulaBTAC
  S3typeC = fPrfC selfRefCodeC (encFceqCTC (ctLitC encCSubPhiValC) encGCTC)

  S4typeC : FormulaBTAC
  S4typeC = fPrfC (ctNodeC (ctLitC (catom n39g)) selfRefCodeC)
                  (encFceqCTC encGCTC (ctLitC encCSubPhiValC))

  S5typeC : FormulaBTAC
  S5typeC = fPrfC (ctNodeC (ctLitC (catom n38g))
                           (ctNodeC (axEvalCodeCTC (encCCheckLitCTC p0C) encGCTC)
                                    (ctNodeC (ctLitC (catom n39g)) selfRefCodeC)))
                  (encFceqCTC (encCCheckLitCTC p0C) (ctLitC encCSubPhiValC))

  ResultTypeC : FormulaBTAC
  ResultTypeC = fPrfC (sdCTC p0C) encBotCTC

  -- Hilbert helpers
  composeImpC : {A B C : FormulaBTAC} ->
    ProofCC (fimpC A B) -> ProofCC (fimpC B C) -> ProofCC (fimpC A C)
  composeImpC {A} {B} {C} f g =
    mpCC (mpCC (axSC A B C)
               (mpCC (axKC (fimpC B C) A) g))
         f

  constImpC : {A B : FormulaBTAC} -> ProofCC B -> ProofCC (fimpC A B)
  constImpC {A} {B} pb = mpCC (axKC B A) pb

  hilbertSC : {A B C : FormulaBTAC} ->
    ProofCC (fimpC A (fimpC B C)) -> ProofCC (fimpC A B) ->
    ProofCC (fimpC A C)
  hilbertSC {A} {B} {C} f g = mpCC (mpCC (axSC A B C) f) g

  step4proofC : ProofCC S4typeC
  step4proofC = mpCC axChkSyC axSelfRefC

  impH-S1-rawC : ProofCC (fimpC HTypeC
                    (fPrfC (ctNodeC (ctLitC (catom n37g)) (ctNodeC p0C p0C))
                           (encSubstFormulaCTC p0C GoedelBodyFC)))
  impH-S1-rawC = axChkCinstC GoedelBodyFC

  impH-S1C : ProofCC (fimpC HTypeC S1typeC)
  impH-S1C = composeImpC impH-S1-rawC axPrfCongCC

  impH-S2C : ProofCC (fimpC HTypeC S2typeC)
  impH-S2C = axChkEvalC GoedelSentence

  trAxiomC : ProofCC (fimpC S2typeC (fimpC S4typeC S5typeC))
  trAxiomC = axChkTrC

  impH-impS4S5C : ProofCC (fimpC HTypeC (fimpC S4typeC S5typeC))
  impH-impS4S5C = composeImpC impH-S2C trAxiomC

  impH-S4C : ProofCC (fimpC HTypeC S4typeC)
  impH-S4C = constImpC step4proofC

  impH-S5C : ProofCC (fimpC HTypeC S5typeC)
  impH-S5C = hilbertSC impH-impS4S5C impH-S4C

  mpAxiomC : ProofCC (fimpC S1typeC (fimpC S5typeC ResultTypeC))
  mpAxiomC = axChkMPctC

  impH-impS5RC : ProofCC (fimpC HTypeC (fimpC S5typeC ResultTypeC))
  impH-impS5RC = composeImpC impH-S1C mpAxiomC

  sdDerivedImpCC : ProofCC (fimpC HTypeC ResultTypeC)
  sdDerivedImpCC = hilbertSC impH-impS5RC impH-S5C

------------------------------------------------------------------------
-- 10. bodyProof and goedel2-ctCase
------------------------------------------------------------------------

private
  bodyProofCC : ProofCC ConCC -> ProofCC (fimpC HTypeC fbotC)
  bodyProofCC con =
    composeImpC sdDerivedImpCC (cinstCC con (sdCTC p0C))

goedel2-ctCase : ProofCC ConCC -> EmptyG2
goedel2-ctCase con =
  let
    body : ProofCC (fimpC HTypeC fbotC)
    body = bodyProofCC con

    gs : ProofCC GoedelSentenceCC
    gs = cgenCC body
  in soundCC gs emptyCEnvG (catom zero) ttG2

------------------------------------------------------------------------
-- 11. What ctCase DOES enable (documentation)
------------------------------------------------------------------------

-- ctCase enables expressing conditional code operations on VARIABLE
-- codes. For example, a "isNode" test:
--
--   isNodeCTC : CodeTermC -> CodeTermC
--   isNodeCTC t = ctCaseC t
--     (ctLitC (catom zero))       -- atom -> return 0 (false)
--     (ctLitC (catom (suc zero))) -- node -> return 1 (true)
--
-- Or extracting the left child of a node (returning a default for atoms):
--
--   leftChildCTC : CodeTermC -> CodeTermC -> CodeTermC
--   leftChildCTC t default = ctCaseC t
--     default                     -- atom -> default
--     (ctVarC (cvs cvz))          -- node -> left child (bound at depth 1)
--
-- These are genuinely new: without ctCase, CodeTerm can only BUILD
-- codes (ctNode, ctLit), never INSPECT them.
--
-- However, for Goedel II, what matters is fPrfC, and fPrfC is abstract.
-- ctCase can inspect code shapes, but cannot tell us what fPrfC holds
-- for those shapes. That requires the checker axioms (or a defined
-- checker via ctFold + ctCase).
--
-- ROADMAP to eliminating checker axioms:
--   1. Add ctFold : CodeTermC -> CodeTermC -> CodeTermC -> CodeTermC
--      (primitive recursion on Code trees)
--   2. Define checkCTC using ctCase + ctFold (recursive tag dispatch)
--   3. Define fPrfC p c = fceqCC (checkCTC p) c
--   4. The 7 checker axioms become DERIVABLE from ctCase/ctFold
--      computation rules
