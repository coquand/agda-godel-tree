{-# OPTIONS --without-K --exact-split #-}

module ChwistekFuelChecker where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant

------------------------------------------------------------------------
-- Fuel-based mutual checker and evaluator
------------------------------------------------------------------------

-- checkProofN and evalCExpN are mutually recursive, with Nat fuel
-- decreasing at each call. This avoids the stratification that
-- blocked D3 in the previous architecture.

checkProofN : Nat -> Code -> Maybe Formula
evalCExpN   : Nat -> CExp -> Maybe Code

-- Evaluator
evalCExpN zero _ = nothing
evalCExpN (suc n) (cvar _)     = nothing
evalCExpN (suc n) (clit c)     = just c
evalCExpN (suc n) (ccheck e)   =
  maybeBind (evalCExpN n e) (\ p ->
  maybeBind (checkProofN n p) (\ a ->
  just (encFormula a)))
evalCExpN (suc n) (csub e1 e2) =
  maybeBind (evalCExpN n e1) (\ c1 ->
  maybeBind (evalCExpN n e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))

-- Helper for tag 36
eqMaybeCode : Maybe Code -> Code -> Bool
eqMaybeCode nothing  _ = false
eqMaybeCode (just x) y = eqCode x y

-- Checker: same tags 30-35 as checkProof, plus tag 36 (ax-eval)
checkProofN zero _ = nothing
checkProofN (suc n) (cnode (catom tag) tc) = chk30 (eqNat tag n30) tag tc
  where
  chk30 : Bool -> Nat -> Code -> Maybe Formula
  chk30 true _ tc =
    maybeBind (decTerm tc) (\ t -> just (feq t t))
  chk30 false tag tc = chk31 (eqNat tag n31) tag tc
    where
    chk31 : Bool -> Nat -> Code -> Maybe Formula
    chk31 true _ (cnode ac bc) =
      maybeBind (decFormula ac) (\ a ->
      maybeBind (decFormula bc) (\ b ->
      just (fimp a (fimp b a))))
    chk31 true _ _ = nothing
    chk31 false tag tc = chk32 (eqNat tag n32) tag tc
      where
      chk32 : Bool -> Nat -> Code -> Maybe Formula
      chk32 true _ (cnode ac (cnode bc cc)) =
        maybeBind (decFormula ac) (\ a ->
        maybeBind (decFormula bc) (\ b ->
        maybeBind (decFormula cc) (\ c ->
        just (fimp (fimp a (fimp b c))
                   (fimp (fimp a b)
                         (fimp a c))))))
      chk32 true _ _ = nothing
      chk32 false tag tc = chk33 (eqNat tag n33) tag tc
        where
        chk33 : Bool -> Nat -> Code -> Maybe Formula
        chk33 true _ (cnode p q) =
          maybeBind (checkProofN n p) (\ pf ->
          maybeBind (checkProofN n q) (\ qf ->
          matchMP pf qf))
        chk33 true _ _ = nothing
        chk33 false tag tc = chk34 (eqNat tag n34) tag tc
          where
          chk34 : Bool -> Nat -> Code -> Maybe Formula
          chk34 true _ p = maybeMap fall (checkProofN n p)
          chk34 false tag tc = chk35 (eqNat tag n35) tag tc
            where
            chk35 : Bool -> Nat -> Code -> Maybe Formula
            chk35 true _ p = maybeMap fcAll (checkProofN n p)
            chk35 false tag tc = chk36 (eqNat tag n36) tc
              where
              n36 : Nat
              n36 = suc n35
              chk36 : Bool -> Code -> Maybe Formula
              chk36 true (cnode ec c) =
                maybeBind (decCExp ec) (\ e ->
                boolGuard (eqMaybeCode (evalCExpN n e) c)
                  (just (fceq e (clit c))))
              chk36 true (catom _) = nothing
              chk36 false (catom _) = nothing
              chk36 false (cnode _ _) = nothing
checkProofN (suc n) (catom _) = nothing
checkProofN (suc n) (cnode (cnode _ _) _) = nothing

------------------------------------------------------------------------
-- Self-reference for the fuel system
------------------------------------------------------------------------

-- The Goedel sentence (from ChwistekGodelSentence) uses evalCExp (old).
-- For the fuel system, we need evalCExpN to give the same self-reference.
--
-- Key fact: for closed CExps (no cvar), evalCExpN (suc (suc n)) agrees
-- with evalCExp for clit and csub of clits, because the computation
-- doesn't depend on the checker for those expressions.
--
-- Specifically:
--   evalCExpN 2 (csub (clit phiCode) (clit phiCode))
--   = maybeBind (just phiCode) (\ c1 ->
--     maybeBind (just phiCode) (\ c2 ->
--     maybeBind (decFormula phiCode) (\ a ->
--     just (encFormula (substFormulaCode0 (clit phiCode) a)))))
--   = evalCExp (csub (clit phiCode) (clit phiCode))
--   = just (encFormula GoedelSentence)

-- We import GoedelSentence to state this

open import ChwistekGodelSentence

selfRefN : Eq (evalCExpN (suc (suc zero)) (csub (clit phiCode) (clit phiCode)))
              (just (encFormula GoedelSentence))
selfRefN = GoedelSentence-self-ref

------------------------------------------------------------------------
-- Comments
------------------------------------------------------------------------

-- checkProofN and evalCExpN form a unified fuel-based system.
-- Tag 36 (ax-eval) is handled by checkProofN using evalCExpN,
-- and evalCExpN's ccheck case calls checkProofN.
-- Both decrease fuel at each mutual call, ensuring termination.
--
-- Key difference from the stratified architecture:
-- The old evalCExp called checkProof (old, no tag 36).
-- evalCExpN calls checkProofN (new, handles tag 36).
-- So the evaluator can SEE reflected proofs.
-- This breaks the reflection hierarchy.
--
-- selfRefN shows that for fuel >= 2, the csub self-reference
-- property holds — it equals evalCExp's result because csub
-- of clits doesn't involve checkProofN at all.
--
-- Next: prove monotonicity, encoding correctness, soundness,
-- and D1/D2/D3 for this system.
