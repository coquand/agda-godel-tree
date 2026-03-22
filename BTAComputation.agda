{-# OPTIONS --without-K --exact-split #-}

-- BTAComputation.agda -- Binary Tree Arithmetic with computation primitives
--
-- Extends BinaryTreeArith with ctCase + ctEqTag on CodeTerms, plus
-- fceqF for internal code equality.  The 7 checker axioms are RETAINED
-- (not derived) but supplemented with computation axioms that express
-- beta-reduction of ctCase and ctEqTag on known-shape targets.
--
-- The computation axioms make the system strictly stronger than
-- BinaryTreeArith: internal code analysis is now expressible.
--
-- Also provides Nelson chain infrastructure (isActiveRedex, reduceCode,
-- normalCode) at the meta level, ready for the next experiment.

module BTAComputation where

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
-- 1. CodeTermF: CodeTerm with ctCase + ctEqTag
------------------------------------------------------------------------

data CodeTermF : Set where
  ctVarF  : CVar -> CodeTermF
  ctLitF  : Code -> CodeTermF
  ctNodeF : CodeTermF -> CodeTermF -> CodeTermF
  -- Case analysis on Code shape:
  --   ctCaseF target atomBranch nodeBranch
  --   catom k   -> atomBranch with (catom k) bound at index 0
  --   cnode a b -> nodeBranch with b at index 0, a at index 1
  ctCaseF : CodeTermF -> CodeTermF -> CodeTermF -> CodeTermF
  -- Tag equality test on atoms:
  --   ctEqTagF t1 t2 thenBranch elseBranch
  --   if t1 = catom k1 and t2 = catom k2 and k1 = k2: thenBranch
  --   otherwise: elseBranch
  ctEqTagF : CodeTermF -> CodeTermF -> CodeTermF -> CodeTermF -> CodeTermF

------------------------------------------------------------------------
-- 2. Lift and substitution for CodeTermF
------------------------------------------------------------------------

liftCTF : CodeTermF -> CodeTermF
liftCTF (ctVarF v)           = ctVarF (cvs v)
liftCTF (ctLitF c)           = ctLitF c
liftCTF (ctNodeF t1 t2)      = ctNodeF (liftCTF t1) (liftCTF t2)
liftCTF (ctCaseF t ab nb)    = ctCaseF (liftCTF t)
                                        (liftCTF ab)
                                        (liftCTF nb)
liftCTF (ctEqTagF t1 t2 b e) = ctEqTagF (liftCTF t1) (liftCTF t2)
                                          (liftCTF b) (liftCTF e)

substCTF0 : CodeTermF -> CodeTermF -> CodeTermF
substCTF0 s (ctVarF cvz)          = s
substCTF0 s (ctVarF (cvs v))      = ctVarF v
substCTF0 s (ctLitF c)            = ctLitF c
substCTF0 s (ctNodeF t1 t2)       = ctNodeF (substCTF0 s t1) (substCTF0 s t2)
substCTF0 s (ctCaseF t ab nb)     = ctCaseF (substCTF0 s t)
                                             (substCTF0 (liftCTF s) ab)
                                             (substCTF0 (liftCTF (liftCTF s)) nb)
substCTF0 s (ctEqTagF t1 t2 b e)  = ctEqTagF (substCTF0 s t1) (substCTF0 s t2)
                                               (substCTF0 s b) (substCTF0 s e)

------------------------------------------------------------------------
-- 3. FormulaBTAF: formulas with fPrf + fceqF
------------------------------------------------------------------------

data FormulaBTAF : Set where
  fbotF  : FormulaBTAF
  fimpF  : FormulaBTAF -> FormulaBTAF -> FormulaBTAF
  fcAllF : FormulaBTAF -> FormulaBTAF
  fPrfF  : CodeTermF -> CodeTermF -> FormulaBTAF
  fceqF  : CodeTermF -> CodeTermF -> FormulaBTAF   -- internal code equality

private
  substFAF0 : CodeTermF -> FormulaBTAF -> FormulaBTAF
  substFAF0 s fbotF        = fbotF
  substFAF0 s (fimpF a b)  = fimpF (substFAF0 s a) (substFAF0 s b)
  substFAF0 s (fcAllF a)   = fcAllF (substFAF0 (liftCTF s) a)
  substFAF0 s (fPrfF p c)  = fPrfF (substCTF0 s p) (substCTF0 s c)
  substFAF0 s (fceqF a b)  = fceqF (substCTF0 s a) (substCTF0 s b)

------------------------------------------------------------------------
-- 4. Helper CodeTermF builders
------------------------------------------------------------------------

private
  n5F : Nat
  n5F = suc (suc (suc (suc (suc zero))))

  encBotF : Code
  encBotF = encFormula fbot

  encGF : Code
  encGF = encFormula GoedelSentence

  encCSubPhiValF : Code
  encCSubPhiValF = encCSubPhi

  encFceqCTF : CodeTermF -> CodeTermF -> CodeTermF
  encFceqCTF a b = ctNodeF (ctLitF (catom n8)) (ctNodeF a b)

  encCCheckLitCTF : CodeTermF -> CodeTermF
  encCCheckLitCTF p = ctNodeF (ctLitF (catom n18)) (ctNodeF (ctLitF (catom n17)) p)

  axEvalCodeCTF : CodeTermF -> CodeTermF -> CodeTermF
  axEvalCodeCTF encCE encResult =
    ctNodeF (ctLitF (catom n36g)) (ctNodeF encCE encResult)

  encSubstCExpCTF : CodeTermF -> CExp -> CodeTermF
  encSubstCExpCTF c (cvar cvz)     = ctNodeF (ctLitF (catom n17)) c
  encSubstCExpCTF c (cvar (cvs v)) = ctLitF (encCExp (cvar v))
  encSubstCExpCTF c (clit k)       = ctLitF (encCExp (clit k))
  encSubstCExpCTF c (ccheck e)     = ctNodeF (ctLitF (catom n18)) (encSubstCExpCTF c e)
  encSubstCExpCTF c (csub e1 e2)   =
    ctNodeF (ctLitF (catom n19)) (ctNodeF (encSubstCExpCTF c e1) (encSubstCExpCTF c e2))

  encSubstFormulaCTF : CodeTermF -> Formula -> CodeTermF
  encSubstFormulaCTF c fbot       = ctLitF (encFormula fbot)
  encSubstFormulaCTF c (feq s t)  = ctLitF (encFormula (feq s t))
  encSubstFormulaCTF c (fimp a b) =
    ctNodeF (ctLitF (catom n5F)) (ctNodeF (encSubstFormulaCTF c a) (encSubstFormulaCTF c b))
  encSubstFormulaCTF c (fall a)   =
    ctNodeF (ctLitF (catom (suc (suc (suc (suc (suc (suc zero))))))))
            (encSubstFormulaCTF c a)
  encSubstFormulaCTF c (fcode k)  = ctLitF (encFormula (fcode k))
  encSubstFormulaCTF c (fceq e1 e2) =
    ctNodeF (ctLitF (catom n8)) (ctNodeF (encSubstCExpCTF c e1) (encSubstCExpCTF c e2))
  encSubstFormulaCTF c (fcAll a)  =
    ctNodeF (ctLitF (catom n9)) (encSubstFormulaCTF c a)

  encGoedelBodyCTF : CodeTermF -> CodeTermF
  encGoedelBodyCTF p =
    ctNodeF (ctLitF (catom n5F))
            (ctNodeF (encFceqCTF (encCCheckLitCTF p) (ctLitF encCSubPhiValF))
                     (ctLitF encBotF))

  sdCTF : CodeTermF -> CodeTermF
  sdCTF p =
    let
      step1 = ctNodeF (ctLitF (catom n37g)) (ctNodeF p p)
      step2 = axEvalCodeCTF (encCCheckLitCTF p) (ctLitF encGF)
      step3 = axEvalCodeCTF (ctLitF encCSubPhiValF) (ctLitF encGF)
      step4 = ctNodeF (ctLitF (catom n39g)) step3
      step5 = ctNodeF (ctLitF (catom n38g)) (ctNodeF step2 step4)
    in ctNodeF (ctLitF (catom n33)) (ctNodeF step1 step5)

  selfRefCodeF : CodeTermF
  selfRefCodeF = axEvalCodeCTF (ctLitF encCSubPhiValF) (ctLitF encGF)

  encGCTF : CodeTermF
  encGCTF = ctLitF encGF

  encBotCTF : CodeTermF
  encBotCTF = ctLitF encBotF

------------------------------------------------------------------------
-- 5. ProofBTAF: Hilbert + checker axioms + computation axioms
------------------------------------------------------------------------

private
  GoedelBodyFF : Formula
  GoedelBodyFF = fimp (fceq (ccheck (cvar cvz))
                            (csub (clit phiCode) (clit phiCode)))
                      fbot

data ProofBTAF : FormulaBTAF -> Set where
  -- Hilbert core
  axKF : (A B : FormulaBTAF) -> ProofBTAF (fimpF A (fimpF B A))
  axSF : (A B C : FormulaBTAF) ->
         ProofBTAF (fimpF (fimpF A (fimpF B C))
                          (fimpF (fimpF A B)
                                 (fimpF A C)))
  mpF : {A B : FormulaBTAF} -> ProofBTAF (fimpF A B) -> ProofBTAF A -> ProofBTAF B
  cgenF : {A : FormulaBTAF} -> ProofBTAF A -> ProofBTAF (fcAllF A)
  cinstF : {A : FormulaBTAF} -> ProofBTAF (fcAllF A) -> (t : CodeTermF) ->
           ProofBTAF (substFAF0 t A)

  -- (I) 7 checker axioms (same as BinaryTreeArith, for CodeTermF)
  axChkMPctF : {p1 p2 encA encB : CodeTermF} ->
               ProofBTAF (fimpF (fPrfF p1 (ctNodeF (ctLitF (catom n5F)) (ctNodeF encA encB)))
                                (fimpF (fPrfF p2 encA)
                                       (fPrfF (ctNodeF (ctLitF (catom n33)) (ctNodeF p1 p2))
                                              encB)))

  axChkCinstF : (A : Formula) -> {p c : CodeTermF} ->
                ProofBTAF (fimpF (fPrfF p (ctLitF (encFormula (fcAll A))))
                                 (fPrfF (ctNodeF (ctLitF (catom n37g)) (ctNodeF p c))
                                        (encSubstFormulaCTF c A)))

  axChkEvalF : (A : Formula) -> {p : CodeTermF} ->
               ProofBTAF (fimpF (fPrfF p (ctLitF (encFormula A)))
                                (fPrfF (axEvalCodeCTF (encCCheckLitCTF p) (ctLitF (encFormula A)))
                                       (encFceqCTF (encCCheckLitCTF p) (ctLitF (encFormula A)))))

  axPrfCongF : {p c1 c2 : CodeTermF} ->
               ProofBTAF (fimpF (fPrfF p c1) (fPrfF p c2))

  axChkSyF : {p : CodeTermF} -> {a b : CodeTermF} ->
             ProofBTAF (fimpF (fPrfF p (encFceqCTF a b))
                              (fPrfF (ctNodeF (ctLitF (catom n39g)) p) (encFceqCTF b a)))

  axChkTrF : {p1 p2 : CodeTermF} -> {a b c : CodeTermF} ->
             ProofBTAF (fimpF (fPrfF p1 (encFceqCTF a b))
                              (fimpF (fPrfF p2 (encFceqCTF b c))
                                     (fPrfF (ctNodeF (ctLitF (catom n38g)) (ctNodeF p1 p2))
                                            (encFceqCTF a c))))

  axSelfRefF : ProofBTAF (fPrfF selfRefCodeF
                                 (encFceqCTF (ctLitF encCSubPhiValF) encGCTF))

  -- (II) Computation axioms for ctCase
  axCaseAtomF : (k : Nat) -> (ab nb : CodeTermF) ->
    ProofBTAF (fceqF (ctCaseF (ctLitF (catom k)) ab nb)
                     (substCTF0 (ctLitF (catom k)) ab))

  axCaseNodeF : (a b : Code) -> (ab nb : CodeTermF) ->
    ProofBTAF (fceqF (ctCaseF (ctNodeF (ctLitF a) (ctLitF b)) ab nb)
                     (substCTF0 (ctLitF b) (substCTF0 (liftCTF (ctLitF a)) nb)))

  -- (III) Computation axioms for ctEqTag
  axEqTagTrueF : (k : Nat) -> (tb eb : CodeTermF) ->
    ProofBTAF (fceqF (ctEqTagF (ctLitF (catom k)) (ctLitF (catom k)) tb eb)
                     tb)

  -- Note: for the false case we need the tag values to be SYNTACTICALLY
  -- different Nat literals, so we parameterize by a witness of inequality.
  -- But Nat inequality is hard to express without decidability.
  -- Instead: give a concrete version for each pair (k1, k2) where
  -- eqNat k1 k2 = false.  We express this as: if eqNat returns false,
  -- the else branch is taken.
  axEqTagFalseF : (k1 k2 : Nat) -> (tb eb : CodeTermF) ->
    Eq (eqNat k1 k2) false ->
    ProofBTAF (fceqF (ctEqTagF (ctLitF (catom k1)) (ctLitF (catom k2)) tb eb)
                     eb)

  -- (IV) Code equality reasoning for fceqF
  axCeqReflF : (t : CodeTermF) ->
    ProofBTAF (fceqF t t)

  axCeqSymF : {a b : CodeTermF} ->
    ProofBTAF (fimpF (fceqF a b) (fceqF b a))

  axCeqTransF : {a b c : CodeTermF} ->
    ProofBTAF (fimpF (fceqF a b) (fimpF (fceqF b c) (fceqF a c)))

  axCongNodeF : {a1 a2 b1 b2 : CodeTermF} ->
    ProofBTAF (fimpF (fceqF a1 a2)
                     (fimpF (fceqF b1 b2)
                            (fceqF (ctNodeF a1 b1) (ctNodeF a2 b2))))

  axCongCaseF : {t1 t2 ab1 ab2 nb1 nb2 : CodeTermF} ->
    ProofBTAF (fimpF (fceqF t1 t2)
                     (fimpF (fceqF ab1 ab2)
                            (fimpF (fceqF nb1 nb2)
                                   (fceqF (ctCaseF t1 ab1 nb1)
                                          (ctCaseF t2 ab2 nb2)))))

------------------------------------------------------------------------
-- 6. GoodBTAF valuation
------------------------------------------------------------------------

private
  GoodBTAF : CEnvG -> FormulaBTAF -> Set
  GoodBTAF env fbotF        = EmptyG2
  GoodBTAF env (fimpF a b)  = GoodBTAF env a -> GoodBTAF env b
  GoodBTAF env (fcAllF a)   = (c : Code) -> GoodBTAF (extendCEnvG env c) a
  GoodBTAF env (fPrfF _ _)  = UnitG2
  GoodBTAF env (fceqF _ _)  = UnitG2

------------------------------------------------------------------------
-- 7. soundBTAF: all constructors are GoodBTAF-sound
------------------------------------------------------------------------

private
  substGoodBTAF : (A : FormulaBTAF) -> (env : CEnvG) -> (t : CodeTermF) ->
    ((c : Code) -> GoodBTAF (extendCEnvG env c) A) ->
    GoodBTAF env (substFAF0 t A)
  unsubstGoodBTAF : (A : FormulaBTAF) -> (env : CEnvG) -> (t : CodeTermF) ->
    (c : Code) ->
    GoodBTAF env (substFAF0 t A) -> GoodBTAF (extendCEnvG env c) A

  substGoodBTAF fbotF env t g = g (catom zero)
  substGoodBTAF (fimpF a b) env t f =
    \ x -> substGoodBTAF b env t
      (\ c -> f c (unsubstGoodBTAF a env t c x))
  substGoodBTAF (fcAllF a) env t g =
    \ c -> substGoodBTAF a (extendCEnvG env c) (liftCTF t) (\ c' -> g c' c)
  substGoodBTAF (fPrfF _ _) env t g = ttG2
  substGoodBTAF (fceqF _ _) env t g = ttG2

  unsubstGoodBTAF fbotF env t c g = g
  unsubstGoodBTAF (fimpF a b) env t c g =
    \ x -> unsubstGoodBTAF b env t c
      (g (substGoodBTAF a env t (\ _ -> x)))
  unsubstGoodBTAF (fcAllF a) env t c g =
    \ c' -> unsubstGoodBTAF a (extendCEnvG env c') (liftCTF t) c (g c')
  unsubstGoodBTAF (fPrfF _ _) env t c g = ttG2
  unsubstGoodBTAF (fceqF _ _) env t c g = ttG2

  soundBTAF : {A : FormulaBTAF} -> ProofBTAF A -> (env : CEnvG) -> GoodBTAF env A
  soundBTAF (axKF A B) env = \ x _ -> x
  soundBTAF (axSF A B C) env = \ f g a -> f a (g a)
  soundBTAF (mpF pf1 pf2) env = soundBTAF pf1 env (soundBTAF pf2 env)
  soundBTAF (cgenF pf) env = \ c -> soundBTAF pf (extendCEnvG env c)
  soundBTAF (cinstF {A} pf t) env =
    substGoodBTAF A env t (soundBTAF pf env)
  -- Checker axioms: trivially sound (fPrfF = UnitG2)
  soundBTAF axChkMPctF env = \ _ _ -> ttG2
  soundBTAF (axChkCinstF A) env = \ _ -> ttG2
  soundBTAF (axChkEvalF A) env = \ _ -> ttG2
  soundBTAF axPrfCongF env = \ _ -> ttG2
  soundBTAF axChkSyF env = \ _ -> ttG2
  soundBTAF axChkTrF env = \ _ _ -> ttG2
  soundBTAF axSelfRefF env = ttG2
  -- Computation axioms: trivially sound (fceqF = UnitG2)
  soundBTAF (axCaseAtomF k ab nb) env = ttG2
  soundBTAF (axCaseNodeF a b ab nb) env = ttG2
  soundBTAF (axEqTagTrueF k tb eb) env = ttG2
  soundBTAF (axEqTagFalseF k1 k2 tb eb _) env = ttG2
  -- Equality reasoning: trivially sound (fceqF = UnitG2)
  soundBTAF (axCeqReflF t) env = ttG2
  soundBTAF axCeqSymF env = \ _ -> ttG2
  soundBTAF axCeqTransF env = \ _ _ -> ttG2
  soundBTAF axCongNodeF env = \ _ _ -> ttG2
  soundBTAF axCongCaseF env = \ _ _ _ -> ttG2

------------------------------------------------------------------------
-- 8. Key formulas
------------------------------------------------------------------------

private
  GoedelBodyBTAF : FormulaBTAF
  GoedelBodyBTAF = fimpF (fPrfF (ctVarF cvz) encGCTF) fbotF

  GoedelSentenceBTAF : FormulaBTAF
  GoedelSentenceBTAF = fcAllF GoedelBodyBTAF

  ConBTAF : FormulaBTAF
  ConBTAF = fcAllF (fimpF (fPrfF (ctVarF cvz) encBotCTF) fbotF)

------------------------------------------------------------------------
-- 9. sdDerivedImpF: the key derivation via S/K composition
------------------------------------------------------------------------

private
  p0F : CodeTermF
  p0F = ctVarF cvz

  HTypeF : FormulaBTAF
  HTypeF = fPrfF p0F encGCTF

  S1typeF : FormulaBTAF
  S1typeF = fPrfF (ctNodeF (ctLitF (catom n37g)) (ctNodeF p0F p0F))
                  (encGoedelBodyCTF p0F)

  S2typeF : FormulaBTAF
  S2typeF = fPrfF (axEvalCodeCTF (encCCheckLitCTF p0F) encGCTF)
                  (encFceqCTF (encCCheckLitCTF p0F) encGCTF)

  S4typeF : FormulaBTAF
  S4typeF = fPrfF (ctNodeF (ctLitF (catom n39g)) selfRefCodeF)
                  (encFceqCTF encGCTF (ctLitF encCSubPhiValF))

  S5typeF : FormulaBTAF
  S5typeF = fPrfF (ctNodeF (ctLitF (catom n38g))
                           (ctNodeF (axEvalCodeCTF (encCCheckLitCTF p0F) encGCTF)
                                    (ctNodeF (ctLitF (catom n39g)) selfRefCodeF)))
                  (encFceqCTF (encCCheckLitCTF p0F) (ctLitF encCSubPhiValF))

  ResultTypeF : FormulaBTAF
  ResultTypeF = fPrfF (sdCTF p0F) encBotCTF

  -- Hilbert helpers
  composeImpF : {A B C : FormulaBTAF} ->
    ProofBTAF (fimpF A B) -> ProofBTAF (fimpF B C) -> ProofBTAF (fimpF A C)
  composeImpF {A} {B} {C} f g =
    mpF (mpF (axSF A B C)
             (mpF (axKF (fimpF B C) A) g))
        f

  constImpF : {A B : FormulaBTAF} -> ProofBTAF B -> ProofBTAF (fimpF A B)
  constImpF {A} {B} pb = mpF (axKF B A) pb

  hilbertSF : {A B C : FormulaBTAF} ->
    ProofBTAF (fimpF A (fimpF B C)) -> ProofBTAF (fimpF A B) ->
    ProofBTAF (fimpF A C)
  hilbertSF {A} {B} {C} f g = mpF (mpF (axSF A B C) f) g

  step4proofF : ProofBTAF S4typeF
  step4proofF = mpF axChkSyF axSelfRefF

  impH-S1-rawF : ProofBTAF (fimpF HTypeF
                    (fPrfF (ctNodeF (ctLitF (catom n37g)) (ctNodeF p0F p0F))
                           (encSubstFormulaCTF p0F GoedelBodyFF)))
  impH-S1-rawF = axChkCinstF GoedelBodyFF

  impH-S1F : ProofBTAF (fimpF HTypeF S1typeF)
  impH-S1F = composeImpF impH-S1-rawF axPrfCongF

  impH-S2F : ProofBTAF (fimpF HTypeF S2typeF)
  impH-S2F = axChkEvalF GoedelSentence

  trAxiomF : ProofBTAF (fimpF S2typeF (fimpF S4typeF S5typeF))
  trAxiomF = axChkTrF

  impH-impS4S5F : ProofBTAF (fimpF HTypeF (fimpF S4typeF S5typeF))
  impH-impS4S5F = composeImpF impH-S2F trAxiomF

  impH-S4F : ProofBTAF (fimpF HTypeF S4typeF)
  impH-S4F = constImpF step4proofF

  impH-S5F : ProofBTAF (fimpF HTypeF S5typeF)
  impH-S5F = hilbertSF impH-impS4S5F impH-S4F

  mpAxiomF : ProofBTAF (fimpF S1typeF (fimpF S5typeF ResultTypeF))
  mpAxiomF = axChkMPctF

  impH-impS5RF : ProofBTAF (fimpF HTypeF (fimpF S5typeF ResultTypeF))
  impH-impS5RF = composeImpF impH-S1F mpAxiomF

  sdDerivedImpF : ProofBTAF (fimpF HTypeF ResultTypeF)
  sdDerivedImpF = hilbertSF impH-impS5RF impH-S5F

------------------------------------------------------------------------
-- 10. bodyProof and goedel2-BTAF
------------------------------------------------------------------------

private
  bodyProofF : ProofBTAF ConBTAF -> ProofBTAF (fimpF HTypeF fbotF)
  bodyProofF con =
    composeImpF sdDerivedImpF (cinstF con (sdCTF p0F))

goedel2-BTAF : ProofBTAF ConBTAF -> EmptyG2
goedel2-BTAF con =
  let
    body : ProofBTAF (fimpF HTypeF fbotF)
    body = bodyProofF con

    gs : ProofBTAF GoedelSentenceBTAF
    gs = cgenF body
  in soundBTAF gs emptyCEnvG (catom zero) ttG2

------------------------------------------------------------------------
-- 11. Nelson chain infrastructure (meta-level Code operations)
------------------------------------------------------------------------

-- Tag constants for readability
private
  tagMP : Nat
  tagMP = n33

  tagGen : Nat
  tagGen = n34

  tagCGen : Nat
  tagCGen = n35

  tagEval : Nat
  tagEval = n36g

  tagCinst : Nat
  tagCinst = n37g

  tagTr : Nat
  tagTr = n38g

  tagSy : Nat
  tagSy = n39g

-- isActiveRedex: does the top-level tag admit a cut-commuting reduction?
-- An "active redex" is a proof code cnode(catom tag, payload) where
-- tag is one of the inference tags (33, 37, 38, 39) and the payload
-- has the right shape for the tag to fire.
isActiveRedex : Code -> Bool
isActiveRedex (cnode (catom tag) (cnode _ _)) = h (eqNat tag n33) tag
  where
  h : Bool -> Nat -> Bool
  h true  _ = true
  h false t = h2 (eqNat t n37g) t
    where
    h2 : Bool -> Nat -> Bool
    h2 true  _ = true
    h2 false t2 = h3 (eqNat t2 n38g) t2
      where
      h3 : Bool -> Nat -> Bool
      h3 true  _ = true
      h3 false t3 = eqNat t3 n39g
isActiveRedex (cnode (catom _) (catom _)) = false
isActiveRedex (catom _) = false
isActiveRedex (cnode (cnode _ _) _) = false

-- normalCode: no active redexes anywhere in the tree
normalCode : Code -> Bool
normalCode (catom _) = true
normalCode (cnode a b) = hTop (isActiveRedex (cnode a b)) (normalCode a) (normalCode b)
  where
  hTop : Bool -> Bool -> Bool -> Bool
  hTop true  _  _  = false
  hTop false na nb = and na nb

-- reduceCode: one step of cut-commuting reduction at the root
-- If the code is not an active redex, returns it unchanged.
-- For tag 33 (mp): cnode(33, cnode(p, q)) is already "normal" as mp
--   unless we want to reduce sub-proofs. Here we just mark it.
-- This is a STUB for the Nelson chain experiment; the actual
-- reduction strategy will depend on the specific chain analysis.
reduceCode : Code -> Code
reduceCode (cnode (catom tag) (cnode p q)) = hR (eqNat tag n39g) tag p q
  where
  -- tag 39 (symmetry): reduce by swapping
  hR : Bool -> Nat -> Code -> Code -> Code
  hR true  _ p _ = p   -- sym(p) reduces to p (forgetting structure)
  hR false _ p q = cnode (catom tag) (cnode p q)
reduceCode (cnode (catom tag) (catom k)) = cnode (catom tag) (catom k)
reduceCode (catom k) = catom k
reduceCode (cnode (cnode a b) c) = cnode (cnode a b) c

-- reduceOnce: reduce the leftmost active redex (depth-first)
reduceOnce : Code -> Code
reduceOnce (catom k) = catom k
reduceOnce (cnode a b) = hNode (isActiveRedex (cnode a b)) a b
  where
  hNode : Bool -> Code -> Code -> Code
  hNode true  a b = reduceCode (cnode a b)
  hNode false a b = cnode (reduceOnce a) (reduceOnce b)

------------------------------------------------------------------------
-- 12. CodeTermF examples: expressible operations via ctCase + ctEqTag
------------------------------------------------------------------------

-- isNodeCTF: test whether a code is a node (returns catom 1 for node,
-- catom 0 for atom)
isNodeCTF : CodeTermF -> CodeTermF
isNodeCTF t = ctCaseF t
  (ctLitF (catom zero))
  (ctLitF (catom (suc zero)))

-- leftChildCTF: extract left child (default for atoms)
leftChildCTF : CodeTermF -> CodeTermF -> CodeTermF
leftChildCTF t dflt = ctCaseF t
  dflt
  (ctVarF (cvs cvz))

-- rightChildCTF: extract right child (default for atoms)
rightChildCTF : CodeTermF -> CodeTermF -> CodeTermF
rightChildCTF t dflt = ctCaseF t
  dflt
  (ctVarF cvz)

-- tagTestCTF: test if a code has a specific atom tag
-- Returns thenBranch if code = catom k, elseBranch otherwise
tagTestCTF : CodeTermF -> Nat -> CodeTermF -> CodeTermF -> CodeTermF
tagTestCTF t k tb eb = ctCaseF t
  (ctEqTagF (ctVarF cvz) (ctLitF (catom k))
            (substCTF0 (ctVarF cvz) (liftCTF tb))
            (substCTF0 (ctVarF cvz) (liftCTF eb)))
  (substCTF0 (ctVarF cvz)
    (substCTF0 (ctVarF (cvs cvz))
      (liftCTF (liftCTF eb))))
