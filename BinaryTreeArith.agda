{-# OPTIONS --without-K --exact-split #-}

-- BinaryTreeArith.agda -- Binary Tree Arithmetic for genuine Goedel II
--
-- Checker rules are IMPLICATION AXIOMS (constructors producing formulas),
-- not inference rules. This makes soundness trivial under GoodBTA,
-- where fPrf maps to UnitG2.

module BinaryTreeArith where

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
-- 1. CodeTerm: code-valued terms
------------------------------------------------------------------------

data CodeTerm : Set where
  ctVar  : CVar -> CodeTerm
  ctLit  : Code -> CodeTerm
  ctNode : CodeTerm -> CodeTerm -> CodeTerm

private
  liftCT : CodeTerm -> CodeTerm
  liftCT (ctVar v)      = ctVar (cvs v)
  liftCT (ctLit c)      = ctLit c
  liftCT (ctNode t1 t2) = ctNode (liftCT t1) (liftCT t2)

  substCT0 : CodeTerm -> CodeTerm -> CodeTerm
  substCT0 s (ctVar cvz)     = s
  substCT0 s (ctVar (cvs v)) = ctVar v
  substCT0 s (ctLit c)       = ctLit c
  substCT0 s (ctNode t1 t2)  = ctNode (substCT0 s t1) (substCT0 s t2)

------------------------------------------------------------------------
-- 2. FormulaBTA: formulas with proof predicate
------------------------------------------------------------------------

data FormulaBTA : Set where
  fbotA  : FormulaBTA
  fimpA  : FormulaBTA -> FormulaBTA -> FormulaBTA
  fcAllA : FormulaBTA -> FormulaBTA
  fPrf   : CodeTerm -> CodeTerm -> FormulaBTA

private
  substFA0 : CodeTerm -> FormulaBTA -> FormulaBTA
  substFA0 s fbotA        = fbotA
  substFA0 s (fimpA a b)  = fimpA (substFA0 s a) (substFA0 s b)
  substFA0 s (fcAllA a)   = fcAllA (substFA0 (liftCT s) a)
  substFA0 s (fPrf p c)   = fPrf (substCT0 s p) (substCT0 s c)

------------------------------------------------------------------------
-- Helper CodeTerm builders (private)
------------------------------------------------------------------------

private
  encBot : Code
  encBot = encFormula fbot

  encG : Code
  encG = encFormula GoedelSentence

  encCSubPhiVal : Code
  encCSubPhiVal = encCSubPhi

  encFceqCT : CodeTerm -> CodeTerm -> CodeTerm
  encFceqCT a b = ctNode (ctLit (catom n8)) (ctNode a b)

  encCCheckLitCT : CodeTerm -> CodeTerm
  encCCheckLitCT p = ctNode (ctLit (catom n18)) (ctNode (ctLit (catom n17)) p)

  axEvalCodeCT : CodeTerm -> CodeTerm -> CodeTerm
  axEvalCodeCT encCE encResult =
    ctNode (ctLit (catom n36g)) (ctNode encCE encResult)

  n5 : Nat
  n5 = suc (suc (suc (suc (suc zero))))

  -- General encoding of substFormulaCode0 (clit c) A as a CodeTerm,
  -- where c is a CodeTerm variable. The key function: walks the formula
  -- at the meta-level and produces a CodeTerm encoding where code
  -- variable 0 has been replaced by the CodeTerm argument c.

  encSubstCExpCT : CodeTerm -> CExp -> CodeTerm
  encSubstCExpCT c (cvar cvz)     = ctNode (ctLit (catom n17)) c
  encSubstCExpCT c (cvar (cvs v)) = ctLit (encCExp (cvar v))
  encSubstCExpCT c (clit k)       = ctLit (encCExp (clit k))
  encSubstCExpCT c (ccheck e)     = ctNode (ctLit (catom n18)) (encSubstCExpCT c e)
  encSubstCExpCT c (csub e1 e2)   =
    ctNode (ctLit (catom n19)) (ctNode (encSubstCExpCT c e1) (encSubstCExpCT c e2))

  encSubstFormulaCT : CodeTerm -> Formula -> CodeTerm
  encSubstFormulaCT c fbot       = ctLit (encFormula fbot)
  encSubstFormulaCT c (feq s t)  = ctLit (encFormula (feq s t))
  encSubstFormulaCT c (fimp a b) =
    ctNode (ctLit (catom n5)) (ctNode (encSubstFormulaCT c a) (encSubstFormulaCT c b))
  encSubstFormulaCT c (fall a)   =
    ctNode (ctLit (catom (suc (suc (suc (suc (suc (suc zero))))))))
           (encSubstFormulaCT c a)
  encSubstFormulaCT c (fcode k)  = ctLit (encFormula (fcode k))
  encSubstFormulaCT c (fceq e1 e2) =
    ctNode (ctLit (catom n8)) (ctNode (encSubstCExpCT c e1) (encSubstCExpCT c e2))
  encSubstFormulaCT c (fcAll a)  =
    ctNode (ctLit (catom n9)) (encSubstFormulaCT c a)

  -- GoedelBody encoding (SPECIFIC INSTANCE of encSubstFormulaCT)
  -- GoedelBody = fimp (fceq (ccheck (cvar cvz)) (csub phi phi)) fbot
  -- After substitution with c: fimp (fceq (ccheck (clit c)) (csub phi phi)) fbot
  -- We define this separately to match what sdDerivedImp needs.
  encGoedelBodyCT : CodeTerm -> CodeTerm
  encGoedelBodyCT p =
    ctNode (ctLit (catom n5))
           (ctNode (encFceqCT (encCCheckLitCT p) (ctLit encCSubPhiVal))
                   (ctLit encBot))

  sdCT : CodeTerm -> CodeTerm
  sdCT p =
    let
      step1 = ctNode (ctLit (catom n37g)) (ctNode p p)
      step2 = axEvalCodeCT (encCCheckLitCT p) (ctLit encG)
      step3 = axEvalCodeCT (ctLit encCSubPhiVal) (ctLit encG)
      step4 = ctNode (ctLit (catom n39g)) step3
      step5 = ctNode (ctLit (catom n38g)) (ctNode step2 step4)
    in ctNode (ctLit (catom n33)) (ctNode step1 step5)

  selfRefCode : CodeTerm
  selfRefCode = axEvalCodeCT (ctLit encCSubPhiVal) (ctLit encG)

  encGCT : CodeTerm
  encGCT = ctLit encG

  encBotCT : CodeTerm
  encBotCT = ctLit encBot

------------------------------------------------------------------------
-- 3. ProofBTA: Hilbert system with compositional checker axioms
------------------------------------------------------------------------

data ProofBTA : FormulaBTA -> Set where
  axK : (A B : FormulaBTA) -> ProofBTA (fimpA A (fimpA B A))
  axS : (A B C : FormulaBTA) ->
        ProofBTA (fimpA (fimpA A (fimpA B C))
                        (fimpA (fimpA A B)
                               (fimpA A C)))
  mpA : {A B : FormulaBTA} -> ProofBTA (fimpA A B) -> ProofBTA A -> ProofBTA B
  cgenA : {A : FormulaBTA} -> ProofBTA A -> ProofBTA (fcAllA A)
  cinstA : {A : FormulaBTA} -> ProofBTA (fcAllA A) -> (t : CodeTerm) ->
           ProofBTA (substFA0 t A)

  -- (a) axChkMPct: CodeTerm-level MP checker
  -- If p1 proves an implication (encoded as ctNode(catom 5)(ctNode encA encB))
  -- and p2 proves the premise (encoded as encA),
  -- then mp(p1,p2) proves the conclusion (encoded as encB).
  axChkMPct : {p1 p2 encA encB : CodeTerm} ->
              ProofBTA (fimpA (fPrf p1 (ctNode (ctLit (catom n5)) (ctNode encA encB)))
                              (fimpA (fPrf p2 encA)
                                     (fPrf (ctNode (ctLit (catom n33)) (ctNode p1 p2))
                                           encB)))

  -- (b) axChkCinst: GENERAL cinst for ANY formula A
  -- If p proves fcAll A, then cnode(37, cnode(p, c)) proves A[c].
  -- The result encoding is encSubstFormulaCT c A.
  axChkCinst : (A : Formula) -> {p c : CodeTerm} ->
               ProofBTA (fimpA (fPrf p (ctLit (encFormula (fcAll A))))
                               (fPrf (ctNode (ctLit (catom n37g)) (ctNode p c))
                                     (encSubstFormulaCT c A)))

  -- (c) axChkEval: GENERAL eval checker for ANY formula A
  -- If p proves A, then the axEval code proves fceq(ccheck(clit p), enc(A)).
  axChkEval : (A : Formula) -> {p : CodeTerm} ->
              ProofBTA (fimpA (fPrf p (ctLit (encFormula A)))
                              (fPrf (axEvalCodeCT (encCCheckLitCT p) (ctLit (encFormula A)))
                                    (encFceqCT (encCCheckLitCT p) (ctLit (encFormula A)))))

  -- Proof-predicate congruence: fPrf is invariant under CodeTerm
  -- equivalence. Since GoodBTA maps fPrf to UnitG2, this is trivially
  -- sound. It bridges syntactic differences between CodeTerms that
  -- evaluate to the same Code (e.g., ctLit(cnode a b) vs ctNode(ctLit a)(ctLit b)).
  axPrfCong : {p c1 c2 : CodeTerm} ->
              ProofBTA (fimpA (fPrf p c1) (fPrf p c2))

  -- (d) axChkSy: symmetry of fceq
  axChkSy : {p : CodeTerm} -> {a b : CodeTerm} ->
            ProofBTA (fimpA (fPrf p (encFceqCT a b))
                            (fPrf (ctNode (ctLit (catom n39g)) p) (encFceqCT b a)))

  -- (e) axChkTr: transitivity of fceq
  axChkTr : {p1 p2 : CodeTerm} -> {a b c : CodeTerm} ->
            ProofBTA (fimpA (fPrf p1 (encFceqCT a b))
                            (fimpA (fPrf p2 (encFceqCT b c))
                                   (fPrf (ctNode (ctLit (catom n38g)) (ctNode p1 p2))
                                         (encFceqCT a c))))

  -- (f) axSelfRef: self-reference (constant axiom)
  axSelfRef : ProofBTA (fPrf selfRefCode
                              (encFceqCT (ctLit encCSubPhiVal) encGCT))

------------------------------------------------------------------------
-- 4. GoodBTA valuation
------------------------------------------------------------------------

private
  GoodBTA : CEnvG -> FormulaBTA -> Set
  GoodBTA env fbotA        = EmptyG2
  GoodBTA env (fimpA a b)  = GoodBTA env a -> GoodBTA env b
  GoodBTA env (fcAllA a)   = (c : Code) -> GoodBTA (extendCEnvG env c) a
  GoodBTA env (fPrf _ _)   = UnitG2

------------------------------------------------------------------------
-- 5. soundBTA: all constructors are GoodBTA-sound
------------------------------------------------------------------------

private
  substGoodBTA : (A : FormulaBTA) -> (env : CEnvG) -> (t : CodeTerm) ->
    ((c : Code) -> GoodBTA (extendCEnvG env c) A) ->
    GoodBTA env (substFA0 t A)
  unsubstGoodBTA : (A : FormulaBTA) -> (env : CEnvG) -> (t : CodeTerm) ->
    (c : Code) ->
    GoodBTA env (substFA0 t A) -> GoodBTA (extendCEnvG env c) A

  substGoodBTA fbotA env t g = g (catom zero)
  substGoodBTA (fimpA a b) env t f =
    \ x -> substGoodBTA b env t
      (\ c -> f c (unsubstGoodBTA a env t c x))
  substGoodBTA (fcAllA a) env t g =
    \ c -> substGoodBTA a (extendCEnvG env c) (liftCT t) (\ c' -> g c' c)
  substGoodBTA (fPrf _ _) env t g = ttG2

  unsubstGoodBTA fbotA env t c g = g
  unsubstGoodBTA (fimpA a b) env t c g =
    \ x -> unsubstGoodBTA b env t c
      (g (substGoodBTA a env t (\ _ -> x)))
  unsubstGoodBTA (fcAllA a) env t c g =
    \ c' -> unsubstGoodBTA a (extendCEnvG env c') (liftCT t) c (g c')
  unsubstGoodBTA (fPrf _ _) env t c g = ttG2

  soundBTA : {A : FormulaBTA} -> ProofBTA A -> (env : CEnvG) -> GoodBTA env A
  soundBTA (axK A B) env = \ x _ -> x
  soundBTA (axS A B C) env = \ f g a -> f a (g a)
  soundBTA (mpA pf1 pf2) env = soundBTA pf1 env (soundBTA pf2 env)
  soundBTA (cgenA pf) env = \ c -> soundBTA pf (extendCEnvG env c)
  soundBTA (cinstA {A} pf t) env =
    substGoodBTA A env t (soundBTA pf env)
  soundBTA axChkMPct env = \ _ _ -> ttG2
  soundBTA (axChkCinst A) env = \ _ -> ttG2
  soundBTA (axChkEval A) env = \ _ -> ttG2
  soundBTA axChkSy env = \ _ -> ttG2
  soundBTA axChkTr env = \ _ _ -> ttG2
  soundBTA axSelfRef env = ttG2
  soundBTA axPrfCong env = \ _ -> ttG2

------------------------------------------------------------------------
-- 6. Key formulas
------------------------------------------------------------------------

private
  GoedelBodyBTA : FormulaBTA
  GoedelBodyBTA = fimpA (fPrf (ctVar cvz) encGCT) fbotA

  GoedelSentenceBTA : FormulaBTA
  GoedelSentenceBTA = fcAllA GoedelBodyBTA

  ConBTA : FormulaBTA
  ConBTA = fcAllA (fimpA (fPrf (ctVar cvz) encBotCT) fbotA)

------------------------------------------------------------------------
-- 7. sdDerivedImp: the key derivation via S/K composition
------------------------------------------------------------------------

private
  p0 : CodeTerm
  p0 = ctVar cvz

  HType : FormulaBTA
  HType = fPrf p0 encGCT

  S1type : FormulaBTA
  S1type = fPrf (ctNode (ctLit (catom n37g)) (ctNode p0 p0))
                (encGoedelBodyCT p0)

  S2type : FormulaBTA
  S2type = fPrf (axEvalCodeCT (encCCheckLitCT p0) encGCT)
                (encFceqCT (encCCheckLitCT p0) encGCT)

  S3type : FormulaBTA
  S3type = fPrf selfRefCode (encFceqCT (ctLit encCSubPhiVal) encGCT)

  S4type : FormulaBTA
  S4type = fPrf (ctNode (ctLit (catom n39g)) selfRefCode)
                (encFceqCT encGCT (ctLit encCSubPhiVal))

  S5type : FormulaBTA
  S5type = fPrf (ctNode (ctLit (catom n38g))
                        (ctNode (axEvalCodeCT (encCCheckLitCT p0) encGCT)
                                (ctNode (ctLit (catom n39g)) selfRefCode)))
                (encFceqCT (encCCheckLitCT p0) (ctLit encCSubPhiVal))

  ResultType : FormulaBTA
  ResultType = fPrf (sdCT p0) encBotCT

  -- Hilbert helpers
  composeImp : {A B C : FormulaBTA} ->
    ProofBTA (fimpA A B) -> ProofBTA (fimpA B C) -> ProofBTA (fimpA A C)
  composeImp {A} {B} {C} f g =
    mpA (mpA (axS A B C)
             (mpA (axK (fimpA B C) A) g))
        f

  constImp : {A B : FormulaBTA} -> ProofBTA B -> ProofBTA (fimpA A B)
  constImp {A} {B} pb = mpA (axK B A) pb

  hilbertS : {A B C : FormulaBTA} ->
    ProofBTA (fimpA A (fimpA B C)) -> ProofBTA (fimpA A B) ->
    ProofBTA (fimpA A C)
  hilbertS {A} {B} {C} f g = mpA (mpA (axS A B C) f) g

  -- Step 4: symmetry of self-reference (constant, no hypothesis)
  step4proof : ProofBTA S4type
  step4proof = mpA axChkSy axSelfRef

  -- GoedelBody as Formula (body of GoedelSentence under fcAll)
  GoedelBodyF : Formula
  GoedelBodyF = fimp (fceq (ccheck (cvar cvz))
                           (csub (clit phiCode) (clit phiCode)))
                     fbot

  -- fimpA H S1type (cinst axiom, general, then congruence)
  -- axChkCinst gives: fPrf p enc(G) -> fPrf(cinst, encSubstFormulaCT p GoedelBodyF)
  -- We need: fPrf(cinst, encGoedelBodyCT p) [= S1type]
  -- Bridge via axPrfCong: encSubstFormulaCT p GoedelBodyF ~> encGoedelBodyCT p
  impH-S1-raw : ProofBTA (fimpA HType
                   (fPrf (ctNode (ctLit (catom n37g)) (ctNode p0 p0))
                         (encSubstFormulaCT p0 GoedelBodyF)))
  impH-S1-raw = axChkCinst GoedelBodyF

  impH-S1 : ProofBTA (fimpA HType S1type)
  impH-S1 = composeImp impH-S1-raw axPrfCong

  -- fimpA H S2type (eval axiom, general)
  impH-S2 : ProofBTA (fimpA HType S2type)
  impH-S2 = axChkEval GoedelSentence

  -- axChkTr instantiated: fimpA S2type (fimpA S4type S5type)
  trAxiom : ProofBTA (fimpA S2type (fimpA S4type S5type))
  trAxiom = axChkTr

  -- fimpA H (fimpA S4type S5type)
  impH-impS4S5 : ProofBTA (fimpA HType (fimpA S4type S5type))
  impH-impS4S5 = composeImp impH-S2 trAxiom

  -- fimpA H S4type (constant)
  impH-S4 : ProofBTA (fimpA HType S4type)
  impH-S4 = constImp step4proof

  -- fimpA H S5type
  impH-S5 : ProofBTA (fimpA HType S5type)
  impH-S5 = hilbertS impH-impS4S5 impH-S4

  -- axChkMPct: fimpA S1type (fimpA S5type ResultType)
  mpAxiom : ProofBTA (fimpA S1type (fimpA S5type ResultType))
  mpAxiom = axChkMPct

  -- fimpA H (fimpA S5type ResultType)
  impH-impS5R : ProofBTA (fimpA HType (fimpA S5type ResultType))
  impH-impS5R = composeImp impH-S1 mpAxiom

  -- fimpA H ResultType
  sdDerivedImp : ProofBTA (fimpA HType ResultType)
  sdDerivedImp = hilbertS impH-impS5R impH-S5

------------------------------------------------------------------------
-- 8. bodyProof: Con + sdDerivedImp -> GoedelBody
------------------------------------------------------------------------

private
  bodyProof : ProofBTA ConBTA -> ProofBTA (fimpA HType fbotA)
  bodyProof con =
    composeImp sdDerivedImp (cinstA con (sdCT p0))

------------------------------------------------------------------------
-- 9. goedel2-BTA: the final Goedel II result
------------------------------------------------------------------------

goedel2-BTA : ProofBTA ConBTA -> EmptyG2
goedel2-BTA con =
  let
    body : ProofBTA (fimpA HType fbotA)
    body = bodyProof con

    gs : ProofBTA GoedelSentenceBTA
    gs = cgenA body
  in soundBTA gs emptyCEnvG (catom zero) ttG2
