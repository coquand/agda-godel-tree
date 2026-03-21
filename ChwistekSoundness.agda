{-# OPTIONS --without-K --exact-split #-}

module ChwistekSoundness where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof

------------------------------------------------------------------------
-- A. Eq helpers
------------------------------------------------------------------------

eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
eqSym refl = refl

eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px

------------------------------------------------------------------------
-- B. Environments
------------------------------------------------------------------------

TEnv : Set
TEnv = Var -> Term

CEnv : Set
CEnv = CVar -> Code

emptyTEnv : TEnv
emptyTEnv v = tvar v

emptyCEnv : CEnv
emptyCEnv _ = catom zero

extendTEnv : TEnv -> Term -> TEnv
extendTEnv env t vz     = t
extendTEnv env t (vs v) = env v

extendCEnv : CEnv -> Code -> CEnv
extendCEnv env c cvz     = c
extendCEnv env c (cvs v) = env v

------------------------------------------------------------------------
-- C. Term evaluation
------------------------------------------------------------------------

evalTerm : TEnv -> Term -> Term
evalTerm env (tvar v)  = env v
evalTerm env tzero     = tzero
evalTerm env (tsucc t) = tsucc (evalTerm env t)

------------------------------------------------------------------------
-- D. Code expression evaluation under environment
------------------------------------------------------------------------

evalCExpEnv : CEnv -> CExp -> Maybe Code
evalCExpEnv env (cvar v)     = just (env v)
evalCExpEnv env (clit c)     = just c
evalCExpEnv env (ccheck e)   =
  maybeBind (evalCExpEnv env e) (\ p ->
  maybeBind (checkProof p) (\ a ->
  just (encFormula a)))
evalCExpEnv env (csub e1 e2) =
  maybeBind (evalCExpEnv env e1) (\ c1 ->
  maybeBind (evalCExpEnv env e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))

------------------------------------------------------------------------
-- E. Environment-based truth predicate
------------------------------------------------------------------------

TrueCodeEqEnv : CEnv -> CExp -> CExp -> Set
TrueCodeEqEnv cenv e1 e2 =
  Sigma Code (\ c -> Prod (Eq (evalCExpEnv cenv e1) (just c))
                          (Eq (evalCExpEnv cenv e2) (just c)))

TrueF : TEnv -> CEnv -> Formula -> Set
TrueF tenv cenv fbot         = Empty
TrueF tenv cenv (feq s t)    = Eq (evalTerm tenv s) (evalTerm tenv t)
TrueF tenv cenv (fimp a b)   = TrueF tenv cenv a -> TrueF tenv cenv b
TrueF tenv cenv (fall a)     = (t : Term) -> TrueF (extendTEnv tenv t) cenv a
TrueF tenv cenv (fcode c)    = Eq c c
TrueF tenv cenv (fceq e1 e2) = TrueCodeEqEnv cenv e1 e2
TrueF tenv cenv (fcAll a)    = (c : Code) -> TrueF tenv (extendCEnv cenv c) a

TrueFormula : Formula -> Set
TrueFormula A = (tenv : TEnv) -> (cenv : CEnv) -> TrueF tenv cenv A

------------------------------------------------------------------------
-- F. Soundness for the inductive Proof type
------------------------------------------------------------------------

soundProof : {A : Formula} -> Proof A -> TrueFormula A
soundProof (ax-refl t) tenv cenv = refl
soundProof (ax-k A B) tenv cenv = \ ta -> \ _ -> ta
soundProof (ax-s A B C) tenv cenv = \ f -> \ g -> \ a -> f a (g a)
soundProof (mp pf1 pf2) tenv cenv = soundProof pf1 tenv cenv (soundProof pf2 tenv cenv)
soundProof (gen pf) tenv cenv = \ t -> soundProof pf (extendTEnv tenv t) cenv
soundProof (cgen pf) tenv cenv = \ c -> soundProof pf tenv (extendCEnv cenv c)

------------------------------------------------------------------------
-- G. Encode Proof as a proof code
------------------------------------------------------------------------

encodeProof : {A : Formula} -> Proof A -> Code
encodeProof (ax-refl t)  = cnode (catom n30) (encTerm t)
encodeProof (ax-k A B)   = cnode (catom n31) (cnode (encFormula A) (encFormula B))
encodeProof (ax-s A B C) = cnode (catom n32)
  (cnode (encFormula A) (cnode (encFormula B) (encFormula C)))
encodeProof (mp pf1 pf2) = cnode (catom n33)
  (cnode (encodeProof pf1) (encodeProof pf2))
encodeProof (gen pf)     = cnode (catom n34) (encodeProof pf)
encodeProof (cgen pf)    = cnode (catom n35) (encodeProof pf)

------------------------------------------------------------------------
-- H. Boolean equality reflexivity chain
------------------------------------------------------------------------

-- eqNat-refl is already in ChwistekProvability

eqVar-refl : (v : Var) -> Eq (eqVar v v) true
eqVar-refl vz     = refl
eqVar-refl (vs v) = eqVar-refl v

eqCVar-refl : (v : CVar) -> Eq (eqCVar v v) true
eqCVar-refl cvz     = refl
eqCVar-refl (cvs v) = eqCVar-refl v

and-true-both : (a b : Bool) -> Eq a true -> Eq b true -> Eq (and a b) true
and-true-both true  true  refl refl = refl
and-true-both true  false refl ()
and-true-both false true  ()   _
and-true-both false false ()   _

eqCode-refl : (c : Code) -> Eq (eqCode c c) true
eqCode-refl (catom n)   = eqNat-refl n
eqCode-refl (cnode a b) = and-true-both (eqCode a a) (eqCode b b)
                            (eqCode-refl a) (eqCode-refl b)

eqCExp-refl : (e : CExp) -> Eq (eqCExp e e) true
eqCExp-refl (cvar v)     = eqCVar-refl v
eqCExp-refl (clit c)     = eqCode-refl c
eqCExp-refl (ccheck e)   = eqCExp-refl e
eqCExp-refl (csub e1 e2) = and-true-both (eqCExp e1 e1) (eqCExp e2 e2)
                             (eqCExp-refl e1) (eqCExp-refl e2)

eqTerm-refl : (t : Term) -> Eq (eqTerm t t) true
eqTerm-refl (tvar v)  = eqVar-refl v
eqTerm-refl tzero     = refl
eqTerm-refl (tsucc t) = eqTerm-refl t

eqFormula-refl : (A : Formula) -> Eq (eqFormula A A) true
eqFormula-refl fbot       = refl
eqFormula-refl (feq s t)  = and-true-both (eqTerm s s) (eqTerm t t)
                              (eqTerm-refl s) (eqTerm-refl t)
eqFormula-refl (fimp a b) = and-true-both (eqFormula a a) (eqFormula b b)
                              (eqFormula-refl a) (eqFormula-refl b)
eqFormula-refl (fall a)    = eqFormula-refl a
eqFormula-refl (fcode c)   = eqCode-refl c
eqFormula-refl (fceq e1 e2) = and-true-both (eqCExp e1 e1) (eqCExp e2 e2)
                                (eqCExp-refl e1) (eqCExp-refl e2)
eqFormula-refl (fcAll a)   = eqFormula-refl a

------------------------------------------------------------------------
-- I. guardEq self-application
------------------------------------------------------------------------

guardEq-self : (A : Formula) (B : Formula) ->
  Eq (guardEq A A (just B)) (just B)
guardEq-self A B =
  eqSubst (\ b -> Eq (boolGuard b (just B)) (just B))
          (eqSym (eqFormula-refl A))
          refl

------------------------------------------------------------------------
-- J. encodeProof correctness
------------------------------------------------------------------------

encodeProof-correct :
  {A : Formula} ->
  (prf : Proof A) ->
  Eq (checkProof (encodeProof prf)) (just A)

encodeProof-correct (ax-refl t) =
  refl-provable-lemma t

encodeProof-correct (ax-k A B) =
  helper (decFormula (encFormula A)) (decFormula-encFormula A)
  where
  helper : (r : Maybe Formula) -> Eq r (just A) ->
    Eq (maybeBind r (\ a ->
        maybeBind (decFormula (encFormula B)) (\ b ->
        just (fimp a (fimp b a)))))
       (just (fimp A (fimp B A)))
  helper (just _) refl =
    helper2 (decFormula (encFormula B)) (decFormula-encFormula B)
    where
    helper2 : (r : Maybe Formula) -> Eq r (just B) ->
      Eq (maybeBind r (\ b -> just (fimp A (fimp b A))))
         (just (fimp A (fimp B A)))
    helper2 (just _) refl = refl
    helper2 nothing ()
  helper nothing ()

encodeProof-correct (ax-s A B C) =
  helper (decFormula (encFormula A)) (decFormula-encFormula A)
  where
  helper : (r : Maybe Formula) -> Eq r (just A) ->
    Eq (maybeBind r (\ a ->
        maybeBind (decFormula (encFormula B)) (\ b ->
        maybeBind (decFormula (encFormula C)) (\ c ->
        just (fimp (fimp a (fimp b c))
                   (fimp (fimp a b) (fimp a c)))))))
       (just (fimp (fimp A (fimp B C))
                   (fimp (fimp A B) (fimp A C))))
  helper (just _) refl =
    helper2 (decFormula (encFormula B)) (decFormula-encFormula B)
    where
    helper2 : (r : Maybe Formula) -> Eq r (just B) ->
      Eq (maybeBind r (\ b ->
          maybeBind (decFormula (encFormula C)) (\ c ->
          just (fimp (fimp A (fimp b c))
                     (fimp (fimp A b) (fimp A c))))))
         (just (fimp (fimp A (fimp B C))
                     (fimp (fimp A B) (fimp A C))))
    helper2 (just _) refl =
      helper3 (decFormula (encFormula C)) (decFormula-encFormula C)
      where
      helper3 : (r : Maybe Formula) -> Eq r (just C) ->
        Eq (maybeBind r (\ c ->
            just (fimp (fimp A (fimp B c))
                       (fimp (fimp A B) (fimp A c)))))
           (just (fimp (fimp A (fimp B C))
                       (fimp (fimp A B) (fimp A C))))
      helper3 (just _) refl = refl
      helper3 nothing ()
    helper2 nothing ()
  helper nothing ()

encodeProof-correct (mp {A} {B} pf1 pf2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ pf ->
              maybeBind (checkProof (encodeProof pf2)) (\ qf ->
              matchMP pf qf)))
            (encodeProof-correct pf1))
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
              (encodeProof-correct pf2))
      (guardEq-self A B))

encodeProof-correct (gen pf) =
  eqCong (maybeMap fall) (encodeProof-correct pf)

encodeProof-correct (cgen pf) =
  eqCong (maybeMap fcAll) (encodeProof-correct pf)

------------------------------------------------------------------------
-- K. Final Goedel I theorem (no assumptions)
------------------------------------------------------------------------

-- The body of GoedelSentence under the fcAll binder
GoedelBody : Formula
GoedelBody =
  fimp (fceq (ccheck (cvar cvz))
             (csub (clit phiCode) (clit phiCode)))
       fbot

goedel1-final : MetaNot (Proof GoedelSentence)
goedel1-final prf =
  let
    -- Step 1: soundness gives truth of GoedelSentence
    trueG : TrueF emptyTEnv emptyCEnv GoedelSentence
    trueG = soundProof prf emptyTEnv emptyCEnv

    -- Step 2: encode the proof as a code
    p : Code
    p = encodeProof prf

    -- Step 3: GoedelSentence = fcAll GoedelBody, so
    -- trueG : (c : Code) -> TrueF emptyTEnv (extendCEnv emptyCEnv c) GoedelBody
    -- Instantiate at c = p
    trueInst : TrueF emptyTEnv (extendCEnv emptyCEnv p) GoedelBody
    trueInst = trueG p

    -- Step 4: GoedelBody = fimp (fceq (ccheck (cvar cvz)) (csub ...)) fbot
    -- So trueInst : TrueCodeEqEnv (extendCEnv emptyCEnv p) (ccheck (cvar cvz)) (csub ...) -> Empty

    -- Step 5: construct the code equality witness
    -- evalCExpEnv (extendCEnv emptyCEnv p) (ccheck (cvar cvz))
    --   = maybeBind (just p) (\ q -> maybeBind (checkProof q) (\ a -> just (encFormula a)))
    --   = maybeBind (checkProof p) (\ a -> just (encFormula a))
    side1 : Eq (evalCExpEnv (extendCEnv emptyCEnv p) (ccheck (cvar cvz)))
               (just (encFormula GoedelSentence))
    side1 = eqCong (\ r -> maybeBind r (\ a -> just (encFormula a)))
                   (encodeProof-correct prf)

    -- evalCExpEnv (extendCEnv emptyCEnv p) (csub (clit phiCode) (clit phiCode))
    -- reduces identically to evalCExp (csub (clit phiCode) (clit phiCode))
    -- because clit has no free code variables
    side2 : Eq (evalCExpEnv (extendCEnv emptyCEnv p)
                 (csub (clit phiCode) (clit phiCode)))
               (just (encFormula GoedelSentence))
    side2 = GoedelSentence-self-ref

    codeEq : TrueCodeEqEnv (extendCEnv emptyCEnv p)
               (ccheck (cvar cvz))
               (csub (clit phiCode) (clit phiCode))
    codeEq = mkSigma (encFormula GoedelSentence) (mkProd side1 side2)
  in
    trueInst codeEq

------------------------------------------------------------------------
-- L. Comments
------------------------------------------------------------------------

-- RESULT: goedel1-final : MetaNot (Proof GoedelSentence)
--
-- This is the first incompleteness theorem for the tree-code framework.
-- It says: there is no Proof of GoedelSentence.
--
-- NO ASSUMPTIONS. No consistency hypothesis, no soundness postulate.
-- The proof derives a contradiction from the existence of any Proof
-- of GoedelSentence.
--
-- How it works:
--
--   1. soundProof gives: if Proof A exists, then A is true in all
--      environments. This is a general soundness theorem for the
--      inductive Proof type.
--
--   2. encodeProof encodes a Proof tree as a proof Code.
--      encodeProof-correct shows checkProof accepts this code.
--
--   3. GoedelSentence says: for all codes p,
--      checkProof(p) != encFormula(GoedelSentence).
--      (Via the quine trick: csub(phiCode, phiCode) evaluates to
--      encFormula(GoedelSentence) by GoedelSentence-self-ref.)
--
--   4. From a hypothetical Proof GoedelSentence:
--      - soundProof gives TrueF GoedelSentence
--      - encodeProof gives a code p
--      - encodeProof-correct gives checkProof(p) = just GoedelSentence
--      - Instantiating TrueF at p: checkProof(p) should differ from
--        encFormula(GoedelSentence)
--      - But checkProof(p) = just GoedelSentence, so
--        encFormula(result) = encFormula(GoedelSentence)
--      - Contradiction.
--
-- Where GoedelSentence-self-ref is used:
--
--   To show that evalCExpEnv env (csub (clit phiCode) (clit phiCode))
--   = just (encFormula GoedelSentence). This is the fixed-point
--   property that makes GoedelSentence genuinely self-referential.
--
-- Soundness was proved for ALL formulas (not just a fragment):
--   soundProof handles all constructors of Proof.
--   TrueF is defined for all constructors of Formula.
--   The cgen rule correctly matches fcAll semantics.
--
-- This completes the first incompleteness theorem in the
-- Chwistek-inspired tree-code framework.
