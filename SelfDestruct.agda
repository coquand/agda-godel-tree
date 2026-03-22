{-# OPTIONS --without-K --exact-split #-}

-- The self-destruct code builder and its meta-correctness theorem.
--
-- sdCode : Code -> Code takes a proof code p and wraps it in the
-- 6-step constructive Goedel I derivation template:
--
--   step1 = cinstG(p, p)        -- instantiate G at p
--   step2 = axEvalG(ccheck(clit p), enc(G))  -- checker fact
--   step3 = axEvalG(csub(phi,phi), enc(G))   -- self-reference fact
--   step4 = fceqSyG(step3)      -- swap
--   step5 = fceqTrG(step2, step4) -- chain
--   step6 = mpG(step1, step5)   -- modus ponens -> fbot
--
-- sdCode is NOT recursive in p. It is a fixed-depth template wrapper.
--
-- sd-meta-correct proves: if checkG accepts p as proving G,
-- then checkG accepts sdCode(p) as proving fbot (at sufficient fuel).

module SelfDestruct where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekGodel2Genuine

------------------------------------------------------------------------
-- The self-destruct code builder
------------------------------------------------------------------------

-- Tag reminders from ChwistekGodel2Genuine:
--   n33 = mp, n36g = axEval, n37g = cinst, n38g = fceqTr, n39g = fceqSy

-- The CExp (ccheck (clit p)) encoded as Code
encCCheckLit : Code -> Code
encCCheckLit p = cnode (catom n18) (cnode (catom n17) p)

-- The CExp (csub (clit phiCode) (clit phiCode)) encoded as Code
encCSubPhi : Code
encCSubPhi = encCExp (csub (clit phiCode) (clit phiCode))

sdCode : Code -> Code
sdCode p =
  let
    -- step1: cinstG(p, p) -- tag 37, instantiate proof p at code p
    step1 = cnode (catom n37g) (cnode p p)

    -- step2: axEvalG(ccheck(clit p), encFormula G) -- tag 36
    step2 = cnode (catom n36g) (cnode (encCCheckLit p)
                                      (encFormula GoedelSentence))

    -- step3: axEvalG(csub(phi,phi), encFormula G) -- tag 36
    step3 = cnode (catom n36g) (cnode encCSubPhi
                                      (encFormula GoedelSentence))

    -- step4: fceqSyG(step3) -- tag 39
    step4 = cnode (catom n39g) step3

    -- step5: fceqTrG(step2, step4) -- tag 38
    step5 = cnode (catom n38g) (cnode step2 step4)

    -- step6: mpG(step1, step5) -- tag 33
  in cnode (catom n33) (cnode step1 step5)

------------------------------------------------------------------------
-- Meta-correctness: if checkG accepts p as proving G,
-- then checkG accepts sdCode(p) as proving fbot
------------------------------------------------------------------------

-- Helper: evalG for ccheck(clit p) when checkG(p) = just A
-- evalG (suc (suc n)) (ccheck (clit p)) reduces definitionally:
--   = maybeBind (evalG (suc n) (clit p)) (\ q -> maybeBind (checkG (suc n) q) ...)
--   = maybeBind (just p) (...)                    [evalG (suc n) (clit p) = just p]
--   = maybeBind (checkG (suc n) p) (\ a -> just (encFormula a))
evalG-ccheck-lit :
  (n : Nat) -> (p : Code) -> (A : Formula) ->
  Eq (checkG (suc n) p) (just A) ->
  Eq (evalG (suc (suc n)) (ccheck (clit p))) (just (encFormula A))
evalG-ccheck-lit n p A hyp =
  eqCong (\ r -> maybeBind r (\ a -> just (encFormula a))) hyp

-- Helper: evalG for csub(clit phiCode, clit phiCode) at fuel >= 2
-- This is just the self-reference property
evalG-csub-phi :
  (n : Nat) ->
  Eq (evalG (suc (suc n)) (csub (clit phiCode) (clit phiCode)))
     (just (encFormula GoedelSentence))
evalG-csub-phi n = GoedelSentence-self-ref

-- Fuel for the self-destruct verification:
-- Root (mp) needs 1 + max(step1-fuel, step5-fuel)
-- step1 (cinst) needs 1 + checkG on p: needs suc n -> total 2+n from root
-- step5 (fceqTr) needs 1 + max(step2-fuel, step4-fuel)
-- step2 (axEval) needs 1 + evalG(ccheck(clit p)):
--   evalG needs 1 + evalG(clit p) [=1] + checkG(p) [needs suc n] -> 3+n from step2, 5+n from root
-- step4 (fceqSy) -> step3 (axEval) for csub self-ref:
--   needs evalG >= 2 for csub: 3 from step3, 5 from step4, 6 from root
-- Total: max(2+n, 5+n, 6) from root = 5+n for n >= 1
sdFuel : Nat -> Nat
sdFuel n = suc (suc (suc (suc (suc n))))

-- The main meta-correctness theorem
sd-meta-correct :
  (n : Nat) -> (p : Code) ->
  Eq (checkG (suc n) p) (just GoedelSentence) ->
  Eq (checkG (suc (sdFuel n)) (sdCode p)) (just fbot)
sd-meta-correct n p hyp =
  let
    -- Abbreviations
    encG : Code
    encG = encFormula GoedelSentence

    phi' : CExp
    phi' = csub (clit phiCode) (clit phiCode)

    -- The instantiation of GoedelSentence at p:
    --   substFormulaCode0 (clit p) GoedelBodyG
    --   = fimp (fceq (ccheck (clit p)) (csub (clit phiCode) (clit phiCode))) fbot
    GoedelBodyInst : Formula
    GoedelBodyInst = fimp (fceq (ccheck (clit p)) phi') fbot

    -- Lift hypothesis to sufficient fuel levels
    hyp2 : Eq (checkG (suc (suc n)) p) (just GoedelSentence)
    hyp2 = checkG-mono (suc n) p GoedelSentence hyp

    hyp4 : Eq (checkG (suc (suc (suc (suc n)))) p) (just GoedelSentence)
    hyp4 = checkG-mono-plus (suc (suc (suc zero))) (suc n) p GoedelSentence hyp

    ----------------------------------------------------------------
    -- evalG results for the two axEval steps
    ----------------------------------------------------------------

    -- evalG (suc(suc(suc n))) (ccheck (clit p)) = just encG
    eval-ccheck : Eq (evalG (suc (suc (suc n))) (ccheck (clit p))) (just encG)
    eval-ccheck = evalG-ccheck-lit (suc n) p GoedelSentence hyp2

    -- evalG (suc(suc n)) (csub (clit phiCode) (clit phiCode)) = just encG
    eval-csub : Eq (evalG (suc (suc n)) phi') (just encG)
    eval-csub = evalG-csub-phi n

    ----------------------------------------------------------------
    -- boolGuard steps for axEval (eqMaybeCodeG after evalG)
    ----------------------------------------------------------------

    -- For step2: boolGuard (eqMaybeCodeG (evalG ... (ccheck (clit p))) encG) ...
    guard-ccheck : Eq (boolGuard (eqMaybeCodeG (evalG (suc (suc (suc n)))
                                   (ccheck (clit p))) encG)
                                 (just (fceq (ccheck (clit p)) (clit encG))))
                      (just (fceq (ccheck (clit p)) (clit encG)))
    guard-ccheck =
      eqSubst (\ r -> Eq (boolGuard (eqMaybeCodeG r encG)
                            (just (fceq (ccheck (clit p)) (clit encG))))
                         (just (fceq (ccheck (clit p)) (clit encG))))
              (eqSym eval-ccheck)
              (eqSubst (\ b -> Eq (boolGuard b
                                    (just (fceq (ccheck (clit p)) (clit encG))))
                                  (just (fceq (ccheck (clit p)) (clit encG))))
                       (eqSym (eqCode-refl encG))
                       refl)

    -- For step3: boolGuard (eqMaybeCodeG (evalG ... phi') encG) ...
    guard-csub : Eq (boolGuard (eqMaybeCodeG (evalG (suc (suc n)) phi') encG)
                               (just (fceq phi' (clit encG))))
                    (just (fceq phi' (clit encG)))
    guard-csub =
      eqSubst (\ r -> Eq (boolGuard (eqMaybeCodeG r encG)
                            (just (fceq phi' (clit encG))))
                         (just (fceq phi' (clit encG))))
              (eqSym eval-csub)
              (eqSubst (\ b -> Eq (boolGuard b (just (fceq phi' (clit encG))))
                                  (just (fceq phi' (clit encG))))
                       (eqSym (eqCode-refl encG))
                       refl)

    ----------------------------------------------------------------
    -- Code abbreviations for inner steps
    ----------------------------------------------------------------

    step2Code : Code
    step2Code = cnode (catom n36g)
                  (cnode (encCCheckLit p) (encFormula GoedelSentence))

    step3Code : Code
    step3Code = cnode (catom n36g)
                  (cnode encCSubPhi (encFormula GoedelSentence))

    step5Code : Code
    step5Code = cnode (catom n38g)
                  (cnode step2Code (cnode (catom n39g) step3Code))

    ----------------------------------------------------------------
    -- Step 2: checkG for axEval(ccheck(clit p), encG)
    -- Tag n36g dispatches to decCExp + evalG + boolGuard
    ----------------------------------------------------------------

    step2-eq : Eq (checkG (suc (suc (suc (suc n)))) step2Code)
                  (just (fceq (ccheck (clit p)) (clit encG)))
    step2-eq =
      eqTrans
        (eqCong (\ r -> maybeBind r (\ e ->
                   boolGuard (eqMaybeCodeG (evalG (suc (suc (suc n))) e) encG)
                             (just (fceq e (clit encG)))))
                (decCExp-encCExp (ccheck (clit p))))
        guard-ccheck

    ----------------------------------------------------------------
    -- Step 3: checkG for axEval(csub(phi,phi), encG)
    ----------------------------------------------------------------

    step3-eq : Eq (checkG (suc (suc (suc n))) step3Code)
                  (just (fceq phi' (clit encG)))
    step3-eq =
      eqTrans
        (eqCong (\ r -> maybeBind r (\ e ->
                   boolGuard (eqMaybeCodeG (evalG (suc (suc n)) e) encG)
                             (just (fceq e (clit encG)))))
                (decCExp-encCExp (csub (clit phiCode) (clit phiCode))))
        guard-csub

    ----------------------------------------------------------------
    -- Step 4: checkG for fceqSy(step3) -- swaps the fceq
    -- Tag n39g dispatches to checkG + matchFceqSy
    ----------------------------------------------------------------

    step4-eq : Eq (checkG (suc (suc (suc (suc n))))
                          (cnode (catom n39g) step3Code))
                  (just (fceq (clit encG) phi'))
    step4-eq = eqCong (\ r -> maybeBind r matchFceqSy) step3-eq

    ----------------------------------------------------------------
    -- matchFceqTr guard: eqCExp (clit encG) (clit encG) = true
    ----------------------------------------------------------------

    fceqTr-guard : Eq (boolGuard (eqCExp (clit encG) (clit encG))
                                 (just (fceq (ccheck (clit p)) phi')))
                      (just (fceq (ccheck (clit p)) phi'))
    fceqTr-guard =
      eqSubst (\ b -> Eq (boolGuard b (just (fceq (ccheck (clit p)) phi')))
                         (just (fceq (ccheck (clit p)) phi')))
              (eqSym (eqCExp-refl (clit encG)))
              refl

    ----------------------------------------------------------------
    -- Step 5: checkG for fceqTr(step2, step4)
    -- Tag n38g dispatches to checkG on both children + matchFceqTr
    ----------------------------------------------------------------

    step5-eq : Eq (checkG (sdFuel n) step5Code)
                  (just (fceq (ccheck (clit p)) phi'))
    step5-eq =
      eqTrans
        (eqCong (\ r -> maybeBind r (\ f1 ->
                   maybeBind (checkG (suc (suc (suc (suc n))))
                                     (cnode (catom n39g) step3Code))
                             (\ f2 -> matchFceqTr f1 f2)))
                step2-eq)
        (eqTrans
          (eqCong (\ r -> maybeBind r
                     (\ f2 -> matchFceqTr
                                (fceq (ccheck (clit p)) (clit encG)) f2))
                  step4-eq)
          fceqTr-guard)

    ----------------------------------------------------------------
    -- Step 1: checkG for cinst(p, p)
    -- Tag n37g dispatches to checkG on p + matchCinst
    -- matchCinst (fcAll body) p = just (substFormulaCode0 (clit p) body)
    ----------------------------------------------------------------

    step1-eq : Eq (checkG (sdFuel n) (cnode (catom n37g) (cnode p p)))
                  (just GoedelBodyInst)
    step1-eq = eqCong (\ r -> maybeBind r (\ pf -> matchCinst pf p)) hyp4

    ----------------------------------------------------------------
    -- Final: matchMP GoedelBodyInst (fceq ...) = just fbot
    ----------------------------------------------------------------

    mp-result : Eq (matchMP GoedelBodyInst (fceq (ccheck (clit p)) phi'))
                   (just fbot)
    mp-result = guardEq-self (fceq (ccheck (clit p)) phi') fbot

  in eqTrans
       (eqCong (\ r -> maybeBind r (\ pf ->
                  maybeBind (checkG (sdFuel n) step5Code)
                            (\ qf -> matchMP pf qf)))
               step1-eq)
       (eqTrans
         (eqCong (\ r -> maybeBind r
                    (\ qf -> matchMP GoedelBodyInst qf))
                 step5-eq)
         mp-result)

------------------------------------------------------------------------
-- STATUS
------------------------------------------------------------------------

-- sdCode is defined and the meta-correctness theorem is stated.
--
-- The proof of sd-meta-correct is a FINITE CASE ANALYSIS on the
-- known structure of sdCode(p). It does NOT require induction on p.
-- It requires:
--   1. checkG-mono to lift the hypothesis to sufficient fuel
--   2. decCExp roundtrip lemmas for the encoded CExps
--   3. self-reference (GoedelSentence-self-ref)
--   4. eqCExp-refl for the boolGuard comparisons
--   5. guardEq-self for the matchMP step
--
-- The detailed unfolding through checkG's nested dispatch is
-- mechanical but verbose (~100 lines of eqTrans/eqCong chains).
--
-- Once sd-meta-correct is proved, it validates axSDruleG as
-- metatheoretically conservative: the axiom only asserts what
-- the checker can already verify.
