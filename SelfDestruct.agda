{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

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
  -- checkG processes sdCode(p) = cnode (catom n33) (cnode step1 step5)
  -- Tag 33 = mp: checkG on step1 and step5, then matchMP
  --
  -- We need to show:
  -- (a) checkG step1 = just (fimp (fceq (ccheck(clit p)) (csub phi phi)) fbot)
  -- (b) checkG step5 = just (fceq (ccheck(clit p)) (csub phi phi))
  -- (c) matchMP (a) (b) = just fbot
  --
  -- For (a): step1 = cnode (catom n37g) (cnode p p), tag 37 = cinst
  --   checkG on p gives GoedelSentence = fcAll GoedelBodyG
  --   matchCinst (fcAll GoedelBodyG) p = just (substFormulaCode0 (clit p) GoedelBodyG)
  --     = just (fimp (fceq (ccheck (clit p)) (csub phi phi)) fbot)
  --
  -- For (b): step5 = cnode (catom n38g) (cnode step2 step4), tag 38 = fceqTr
  --   checkG on step2 gives fceq (ccheck(clit p)) (clit enc(G))
  --   checkG on step4 gives fceq (clit enc(G)) (csub phi phi)
  --   matchFceqTr chains them: fceq (ccheck(clit p)) (csub phi phi)
  --
  -- The key fact: step2 (tag 36 = axEvalG) requires
  --   evalG (ccheck(clit p)) = just (encFormula G)
  -- which follows from checkG(p) = just G (our hypothesis)
  --
  -- step3 (tag 36) requires
  --   evalG (csub phi phi) = just (encFormula G)
  -- which is the self-reference property

  -- For now we state this and leave the detailed verification
  -- as a structured proof. The proof is finite case analysis
  -- on the known structure of sdCode(p), NOT induction on p.

  {!!}
  -- The proof is finite case analysis on the known structure of
  -- sdCode(p). It requires unfolding checkG through 4 dispatch
  -- levels using:
  --   checkG-mono to lift the hypothesis to sufficient fuel
  --   decCExp-encCExp for the axEvalG tag decode step
  --   evalG-ccheck-lit for the conditional evaluation fact
  --   evalG-csub-phi (= GoedelSentence-self-ref) for self-reference
  --   eqCExp-refl for the boolGuard comparisons in axEvalG
  --   eqCode-refl for the eqMaybeCodeG comparisons
  --   guardEq-self for the matchMP step
  --
  -- Estimated: ~100 lines of eqTrans/eqCong chains.
  -- NOT induction on p — purely structural on the fixed template.

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
