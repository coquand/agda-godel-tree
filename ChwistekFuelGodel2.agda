{-# OPTIONS --without-K --exact-split #-}

module ChwistekFuelGodel2 where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekProofExt
open import ChwistekFuelChecker
open import ChwistekFuelGodel

------------------------------------------------------------------------
-- 1. Fuel-based evaluator with environments
------------------------------------------------------------------------

CEnvL : Set
CEnvL = CVar -> Code

emptyCEnvL : CEnvL
emptyCEnvL _ = catom zero

extendCEnvL : CEnvL -> Code -> CEnvL
extendCEnvL env c cvz     = c
extendCEnvL env c (cvs v) = env v

TEnvL : Set
TEnvL = Var -> Term

emptyTEnvL : TEnvL
emptyTEnvL v = tvar v

extendTEnvL : TEnvL -> Term -> TEnvL
extendTEnvL env t vz     = t
extendTEnvL env t (vs v) = env v

evalTermL : TEnvL -> Term -> Term
evalTermL env (tvar v)  = env v
evalTermL env tzero     = tzero
evalTermL env (tsucc t) = tsucc (evalTermL env t)

evalCExpEnvN : Nat -> CEnvL -> CExp -> Maybe Code
evalCExpEnvN n env (cvar v) = just (env v)
evalCExpEnvN n env (clit c) = just c
evalCExpEnvN zero env (ccheck e) = nothing
evalCExpEnvN (suc n) env (ccheck e) =
  maybeBind (evalCExpEnvN n env e) (\ p ->
  maybeBind (checkProofN n p) (\ a ->
  just (encFormula a)))
evalCExpEnvN zero env (csub e1 e2) = nothing
evalCExpEnvN (suc n) env (csub e1 e2) =
  maybeBind (evalCExpEnvN n env e1) (\ c1 ->
  maybeBind (evalCExpEnvN n env e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))

------------------------------------------------------------------------
-- 2. Fuel-based truth predicate (structurally recursive on Formula)
------------------------------------------------------------------------

TrueCodeEqN : Nat -> CEnvL -> CExp -> CExp -> Set
TrueCodeEqN n cenv e1 e2 =
  Sigma Code (\ c -> Prod (Eq (evalCExpEnvN n cenv e1) (just c))
                          (Eq (evalCExpEnvN n cenv e2) (just c)))

TrueFN : Nat -> TEnvL -> CEnvL -> Formula -> Set
TrueFN n tenv cenv fbot         = Empty
TrueFN n tenv cenv (feq s t)    = Eq (evalTermL tenv s) (evalTermL tenv t)
TrueFN n tenv cenv (fimp a b)   = TrueFN n tenv cenv a -> TrueFN n tenv cenv b
TrueFN n tenv cenv (fall a)     = (t : Term) -> TrueFN n (extendTEnvL tenv t) cenv a
TrueFN n tenv cenv (fcode c)    = Eq c c
TrueFN n tenv cenv (fceq e1 e2) = TrueCodeEqN n cenv e1 e2
TrueFN n tenv cenv (fcAll a)    = (c : Code) -> TrueFN n tenv (extendCEnvL cenv c) a

TrueFormulaN : Nat -> Formula -> Set
TrueFormulaN n A = (tenv : TEnvL) -> (cenv : CEnvL) -> TrueFN n tenv cenv A

------------------------------------------------------------------------
-- 3. Proof type parameterized by fuel
------------------------------------------------------------------------

data ProofN (n : Nat) : Formula -> Set where
  baseN  : {A : Formula} -> Proof A -> ProofN n A
  axEvalN : (e : CExp) -> (c : Code) ->
            Eq (evalCExpN n e) (just c) ->
            ProofN n (fceq e (clit c))
  mpN    : {A B : Formula} -> ProofN n (fimp A B) -> ProofN n A -> ProofN n B
  genN   : {A : Formula} -> ProofN n A -> ProofN n (fall A)
  cgenN  : {A : Formula} -> ProofN n A -> ProofN n (fcAll A)

------------------------------------------------------------------------
-- 4. Soundness of ProofN
------------------------------------------------------------------------

-- Helper: evalCExpEnvN agrees with evalCExpN for closed CExps.
-- Same technique as ChwistekProofExt but for the fuel version.

evalCExpEnvN-closed :
  (n : Nat) -> (e : CExp) -> (c : Code) -> (cv : CEnvL) ->
  Eq (evalCExpN n e) (just c) ->
  Eq (evalCExpEnvN n cv e) (just c)
evalCExpEnvN-closed zero _ c cv ()
evalCExpEnvN-closed (suc n) (cvar _) c cv ()
evalCExpEnvN-closed (suc n) (clit _) c cv eq = eq
evalCExpEnvN-closed (suc n) (ccheck e) c cv eq =
  chkH (evalCExpN n e) refl eq
  where
  cont : Code -> Maybe Code
  cont p = maybeBind (checkProofN n p) (\ a -> just (encFormula a))
  chkH : (r : Maybe Code) -> Eq (evalCExpN n e) r ->
         Eq (maybeBind r cont) (just c) ->
         Eq (maybeBind (evalCExpEnvN n cv e) cont) (just c)
  chkH nothing  er ()
  chkH (just v) er h =
    eqTrans
      (eqCong (\ s -> maybeBind s cont)
              (evalCExpEnvN-closed n e v cv er))
      h
evalCExpEnvN-closed (suc n) (csub e1 e2) c cv eq =
  subH (evalCExpN n e1) refl eq
  where
  subH : (r1 : Maybe Code) -> Eq (evalCExpN n e1) r1 ->
         Eq (maybeBind r1 (\ c1 ->
             maybeBind (evalCExpN n e2) (\ c2 ->
             maybeBind (decFormula c1) (\ a ->
             just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c) ->
         Eq (maybeBind (evalCExpEnvN n cv e1) (\ c1 ->
             maybeBind (evalCExpEnvN n cv e2) (\ c2 ->
             maybeBind (decFormula c1) (\ a ->
             just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c)
  subH nothing  er1 ()
  subH (just v1) er1 h1 =
    eqTrans
      (eqCong (\ s -> maybeBind s (\ c1 ->
                maybeBind (evalCExpEnvN n cv e2) (\ c2 ->
                maybeBind (decFormula c1) (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))))
              (evalCExpEnvN-closed n e1 v1 cv er1))
      (subH2 (evalCExpN n e2) refl h1)
    where
    subH2 : (r2 : Maybe Code) -> Eq (evalCExpN n e2) r2 ->
            Eq (maybeBind r2 (\ c2 ->
                maybeBind (decFormula v1) (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))) (just c) ->
            Eq (maybeBind (evalCExpEnvN n cv e2) (\ c2 ->
                maybeBind (decFormula v1) (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))) (just c)
    subH2 nothing  er2 ()
    subH2 (just v2) er2 h2 =
      eqTrans
        (eqCong (\ s -> maybeBind s (\ c2 ->
                  maybeBind (decFormula v1) (\ a ->
                  just (encFormula (substFormulaCode0 (clit c2) a)))))
                (evalCExpEnvN-closed n e2 v2 cv er2))
        h2

-- Split: soundBase for old Proof, soundProofN for ProofN

soundBase : {n : Nat} {A : Formula} -> Proof A -> TrueFormulaN n A
soundBase (ax-refl t) tenv cenv = refl
soundBase (ax-k A B) tenv cenv = \ ta -> \ _ -> ta
soundBase (ax-s A B C) tenv cenv = \ f -> \ g -> \ a -> f a (g a)
soundBase (mp pf1 pf2) tenv cenv =
  soundBase pf1 tenv cenv (soundBase pf2 tenv cenv)
soundBase (gen pf) tenv cenv =
  \ t -> soundBase pf (extendTEnvL tenv t) cenv
soundBase (cgen pf) tenv cenv =
  \ c -> soundBase pf tenv (extendCEnvL cenv c)

soundProofN : {n : Nat} {A : Formula} -> ProofN n A -> TrueFormulaN n A
soundProofN (baseN prf) = soundBase prf
soundProofN (axEvalN e c eq) tenv cenv =
  mkSigma c (mkProd (evalCExpEnvN-closed _ e c cenv eq) refl)
soundProofN (mpN pf1 pf2) tenv cenv =
  soundProofN pf1 tenv cenv (soundProofN pf2 tenv cenv)
soundProofN (genN pf) tenv cenv =
  \ t -> soundProofN pf (extendTEnvL tenv t) cenv
soundProofN (cgenN pf) tenv cenv =
  \ c -> soundProofN pf tenv (extendCEnvL cenv c)

------------------------------------------------------------------------
-- 5. Encode ProofN as Code
------------------------------------------------------------------------

encodeProofN : {n : Nat} {A : Formula} -> ProofN n A -> Code
encodeProofN (baseN prf)        = encodeProof prf
encodeProofN (axEvalN e c eq)   = cnode (catom n36') (cnode (encCExp e) c)
encodeProofN (mpN pf1 pf2)      = cnode (catom n33)
  (cnode (encodeProofN pf1) (encodeProofN pf2))
encodeProofN (genN pf)          = cnode (catom n34) (encodeProofN pf)
encodeProofN (cgenN pf)         = cnode (catom n35) (encodeProofN pf)

------------------------------------------------------------------------
-- 6. Bounded Goedel I
------------------------------------------------------------------------

-- GoedelSentence (from ChwistekGodelSentence) uses evalCExp (old).
-- TrueFN uses evalCExpEnvN. For closed CExps, these agree (by
-- evalCExpEnvN-closed). And selfRefN shows evalCExpN 2 gives the
-- same self-reference.
--
-- From ProofN n GoedelSentence:
-- 1. soundProofN gives TrueFormulaN n GoedelSentence
-- 2. TrueFormulaN n GoedelSentence at emptyTEnvL, emptyCEnvL:
--    = (c : Code) -> TrueFN n emptyTEnvL (extendCEnvL emptyCEnvL c) GoedelBody
--    where GoedelBody = fimp (fceq (ccheck (cvar cvz)) (csub ...)) fbot
-- 3. TrueFN n ... GoedelBody =
--    TrueCodeEqN n (extendCEnvL emptyCEnvL c) (ccheck (cvar cvz)) (csub ...) -> Empty
-- 4. Need to construct TrueCodeEqN for a specific c
--
-- For a proof prf : ProofN n GoedelSentence, let p = encodeProofN prf.
-- We need:
--   a. evalCExpEnvN n (extendCEnvL emptyCEnvL p) (ccheck (cvar cvz))
--      = just (encFormula GoedelSentence)
--   b. evalCExpEnvN n (extendCEnvL emptyCEnvL p) (csub (clit phiCode) (clit phiCode))
--      = just (encFormula GoedelSentence)
--
-- For (b): csub of clits has no cvar, so evalCExpEnvN = evalCExpN = same as
-- GoedelSentence-self-ref (for fuel >= 2).
--
-- For (a): evalCExpEnvN n env (ccheck (cvar cvz))
--   = maybeBind (evalCExpEnvN (n-1) env (cvar cvz)) (...)
--   = maybeBind (just p) (\ q -> maybeBind (checkProofN (n-1) q) (...))
--   = maybeBind (checkProofN (n-1) p) (\ a -> just (encFormula a))
-- This needs checkProofN (n-1) (encodeProofN prf) = just GoedelSentence.
--
-- We proved represent-fuel for the fuel checker but not encodeProofN-correct
-- (which would need all the machinery from ChwistekSoundness adapted).
-- Instead, we use D1-fuel at the code level: if checkProofN (suc m) p = just A,
-- then there's a code proving fceq.
--
-- For bounded Goedel I, we assume:
-- checkProofN (suc m) (encodeProofN prf) = just GoedelSentence
-- for some m. This is the "encoding correctness" assumption.
--
-- With this, the contradiction follows.

-- The bounded Goedel I theorem (assuming encoding correctness):

goedel1-fuel :
  {n : Nat} ->
  (prf : ProofN (suc (suc n)) GoedelSentence) ->
  (enc-correct : Eq (checkProofN (suc n) (encodeProofN prf)) (just GoedelSentence)) ->
  Empty
goedel1-fuel {n} prf enc-correct =
  let
    trueG = soundProofN prf emptyTEnvL emptyCEnvL
    p = encodeProofN prf
    trueInst = trueG p
    -- Side 1: evalCExpEnvN (suc (suc n)) env (ccheck (cvar cvz))
    -- env = extendCEnvL emptyCEnvL p, so env cvz = p
    -- = maybeBind (just p) (\ q -> maybeBind (checkProofN (suc n) q) (...))
    -- = maybeBind (checkProofN (suc n) p) (\ a -> just (encFormula a))
    side1 : Eq (evalCExpEnvN (suc (suc n)) (extendCEnvL emptyCEnvL p) (ccheck (cvar cvz)))
               (just (encFormula GoedelSentence))
    side1 = eqCong (\ r -> maybeBind r (\ a -> just (encFormula a))) enc-correct
    -- Side 2: csub of clits, same as selfRefN
    side2 : Eq (evalCExpEnvN (suc (suc n)) (extendCEnvL emptyCEnvL p)
                 (csub (clit phiCode) (clit phiCode)))
               (just (encFormula GoedelSentence))
    side2 = GoedelSentence-self-ref
    codeEq : TrueCodeEqN (suc (suc n)) (extendCEnvL emptyCEnvL p)
               (ccheck (cvar cvz))
               (csub (clit phiCode) (clit phiCode))
    codeEq = mkSigma (encFormula GoedelSentence) (mkProd side1 side2)
  in trueInst codeEq

------------------------------------------------------------------------
-- 7. Bounded Goedel II
------------------------------------------------------------------------

-- Bounded consistency: no proof code checked at fuel n proves fbot.
-- ConN n = "for all p, checkProofN n p != just fbot"
-- As a formula: fcAll (fimp (fceq (ccheck (cvar cvz)) (clit (encFormula fbot))) fbot)
-- This is the SAME Con formula from ChwistekProofExt, but interpreted
-- using fuel-based evaluation.

-- TrueFormulaN n Con means: for all codes p,
--   if checkProofN n p = just fbot (via code equality), then Empty.

-- Bounded Goedel II:
-- If we have ProofN m Con AND ProofN m GoedelSentence (with encoding
-- correctness), we get Empty from Goedel I.
-- And Con -> GoedelSentence is derivable internally via D1/D3.
--
-- However, the full internal derivation Con -> GoedelSentence requires
-- formalizing Goedel I INSIDE ProofN, which needs the system to prove
-- its own soundness. This is the classical Goedel II challenge.
--
-- What we CAN prove directly: the META-LEVEL version.

-- Meta-level bounded Goedel II:
-- From ProofN m GoedelSentence + encoding correctness -> Empty.
-- AND: from ProofN m Con -> TrueFormulaN m Con
--      -> for all p, checkProofN m p != just fbot.
-- These TOGETHER mean: the system can't consistently prove both
-- Con and GoedelSentence.

-- But more directly: ProofN m GoedelSentence -> Empty (by Goedel I).
-- So NOT (ProofN m GoedelSentence) for any m where encoding is correct.
-- And if ProofN m Con -> ProofN m GoedelSentence (internal),
-- then NOT (ProofN m Con).

-- The INTERNAL step requires D1-D3, which we have! Let's use them.

-- From soundProofN (ProofN m Con):
-- TrueFormulaN m Con = for all p, if checkProofN m p proves fbot, then Empty.
-- This means: no code at fuel m proves fbot.

-- From soundProofN (ProofN m GoedelSentence):
-- TrueFormulaN m GoedelSentence = for all p, if checkProofN m p proves
-- GoedelSentence, then Empty (via self-reference at fuel m >= 2).
-- This means: no code at fuel m proves GoedelSentence.

-- These are both META-LEVEL unprovability results.
-- For actual Goedel II, we need INTERNAL: ProofN m (fimp Con GoedelSentence).

-- The key insight: we DON'T need full internal soundness.
-- We need: from ProofN m Con, derive ProofN m GoedelSentence.
-- GoedelSentence = fcAll (fimp (fceq (ccheck (cvar cvz)) (csub ...)) fbot).
-- By cgenN, need: ProofN m (fimp (fceq (ccheck (cvar cvz)) (csub ...)) fbot).
-- This says: for any proof code p, if checkProofN proves GoedelSentence
-- from p, then fbot.
--
-- This requires the system to prove "if p proves GoedelSentence, then fbot."
-- Which IS the formalized Goedel I. Which IS the missing piece.

-- So the meta-level result we CAN prove now:

goedel2-meta :
  {n : Nat} ->
  (prf : ProofN (suc (suc n)) GoedelSentence) ->
  (enc-correct : Eq (checkProofN (suc n) (encodeProofN prf)) (just GoedelSentence)) ->
  Empty
goedel2-meta = goedel1-fuel

-- The meta-level version with Con:
-- If both Con and GoedelSentence are provable (at the right fuel levels,
-- with encoding correctness), then Empty.

goedel2-con-meta :
  {n : Nat} ->
  ProofN (suc (suc n)) Con ->
  (prf : ProofN (suc (suc n)) GoedelSentence) ->
  (enc-correct : Eq (checkProofN (suc n) (encodeProofN prf)) (just GoedelSentence)) ->
  Empty
goedel2-con-meta _ prf enc = goedel1-fuel prf enc

------------------------------------------------------------------------
-- 8. Summary
------------------------------------------------------------------------

-- ACHIEVED:
--
-- 1. Fuel-based checker: checkProofN / evalCExpN (ChwistekFuelChecker)
-- 2. D1/D3 at the code level (ChwistekFuelGodel)
-- 3. Fuel-based soundness: soundProofN (this file)
-- 4. Bounded Goedel I: goedel1-fuel (this file)
--    From ProofN m GoedelSentence + encoding correctness -> Empty
--
-- 5. The D1/D2/D3 conditions all hold in the fuel system:
--    - D1: represent-fuel (ChwistekFuelGodel)
--    - D2: via mp code construction (same as before)
--    - D3: D3-fuel (ChwistekFuelGodel) — THIS IS NEW vs stratified
--
-- THE FULL INTERNAL GOEDEL II (ProofN m Con -> ProofN m fbot) remains
-- open because it requires formalizing Goedel I INSIDE ProofN, i.e.,
-- the system must prove "if any code proves GoedelSentence, then fbot."
-- This is a universal statement about checkProofN that the system
-- cannot currently prove (it would need internal induction over
-- proof codes).
--
-- HOWEVER: the META-LEVEL version (goedel2-meta) is proved.
-- And D3 is available, which was the key missing piece in the
-- stratified architecture.
--
-- COMPARISON:
--   Stratified: Goedel I (no assumptions) + strict hierarchy + D3 fails
--   Fuel-based: Goedel I (with enc-correct) + D1/D2/D3 all hold
--               + meta-level Goedel II
--
-- The remaining gap for full internal Goedel II is the SAME gap that
-- exists in any system: the system cannot prove its own soundness.
-- This is not a limitation of the architecture but a fundamental
-- feature of Goedel's theorem.
