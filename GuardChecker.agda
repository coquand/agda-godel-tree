{-# OPTIONS --without-K --exact-split #-}

-- GuardChecker.agda
-- Self-encoding CodeTm fold: encLiftCodeTm computes encCodeTm(liftCode(c)).
-- This is the representability of the encoding function needed for
-- genuine proof checking (Guard's Theorem 12 ingredient).
-- 0 postulates, 0 holes.

module GuardChecker where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import TreeArith
  using (EmptyTA; SigmaTA; mkSigmaTA; UnitTA; n95)
open import TreeArithTrack1
  using (CodeTm; ctVar; ctAtom; ctNode;
         Env3; emptyEnv3; extendEnv3;
         evalCT; foldCT;
         liftCode)
open import TreeArithBootstrap
  using (addB)

------------------------------------------------------------------------
-- Encoding tags (local copies of TreeArithGodel2 privates)
------------------------------------------------------------------------

private
  n100t : Nat
  n100t = suc (suc (suc (suc (suc n95))))

  ctAtomTag : Nat
  ctAtomTag = suc n100t

  ctNodeTag : Nat
  ctNodeTag = suc (suc n100t)

  n3 : Nat
  n3 = suc (suc (suc zero))

  eqTr : {X : Set} {a b c : X} -> Eq a b -> Eq b c -> Eq a c
  eqTr refl q = q

  eqSy : {X : Set} {a b : X} -> Eq a b -> Eq b a
  eqSy refl = refl

  eqSub : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
  eqSub P refl px = px

  addB-assoc : (a b c : Nat) -> Eq (addB (addB a b) c) (addB a (addB b c))
  addB-assoc zero    b c = refl
  addB-assoc (suc a) b c = eqCong suc (addB-assoc a b c)

  addB-suc-r : (x y : Nat) -> Eq (addB x (suc y)) (suc (addB x y))
  addB-suc-r zero    y = refl
  addB-suc-r (suc x) y = eqCong suc (addB-suc-r x y)

  addB-zero-r : (a : Nat) -> Eq (addB a zero) a
  addB-zero-r zero    = refl
  addB-zero-r (suc a) = eqCong suc (addB-zero-r a)

  addB-comm : (a b : Nat) -> Eq (addB a b) (addB b a)
  addB-comm zero    b = eqSy (addB-zero-r b)
  addB-comm (suc a) b = eqTr (eqCong suc (addB-comm a b)) (eqSy (addB-suc-r b a))

  addB-comm-assoc : (f1 f2 g : Nat) ->
    Eq (addB (addB f1 f2) g) (addB f2 (addB f1 g))
  addB-comm-assoc f1 f2 g =
    eqTr (eqCong (\ x -> addB x g) (addB-comm f1 f2)) (addB-assoc f2 f1 g)

  foldCT-fuel-eq : (f1 f2 : Nat) -> Eq f1 f2 ->
    (env : Env3) -> (c : Code) -> (ac nc : CodeTm) ->
    Eq (foldCT f1 env c ac nc) (foldCT f2 env c ac nc)
  foldCT-fuel-eq f .f refl env c ac nc = refl

------------------------------------------------------------------------
-- encLiftCodeTm: fold that computes encCodeTm(liftCode(c))
------------------------------------------------------------------------

acEnc : CodeTm
acEnc = ctNode (ctAtom ctAtomTag) (ctVar zero)

ncEnc : CodeTm
ncEnc = ctNode (ctAtom ctNodeTag) (ctNode (ctVar (suc (suc zero))) (ctVar (suc (suc (suc zero)))))

encLiftExpected : Code -> Code
encLiftExpected (catom n)   = cnode (catom ctAtomTag) (catom n)
encLiftExpected (cnode a b) = cnode (catom ctNodeTag)
  (cnode (encLiftExpected a) (encLiftExpected b))

-- Fuel: addB n3 (addB extra k) where extra is the code recursion depth.
encLiftExtra : Code -> Nat
encLiftExtra (catom _)   = zero
encLiftExtra (cnode a b) = suc (addB (encLiftExtra a) (encLiftExtra b))

-- Correctness at fuel addB n3 (addB (encLiftExtra c) k).
-- For catom: fuel = suc(suc(suc k)). Handler needs 3 steps. ✓
-- For cnode: fuel = suc(suc(suc(addB (addB ea eb) k))).
--   Sub-folds use same fuel minus the outer suc.
--   IH on a at k' = addB eb k; IH on b at k' = addB ea k.
encLiftCorrect : (c : Code) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB n3 (addB (encLiftExtra c) k)) env c acEnc ncEnc)
     (encLiftExpected c)
encLiftCorrect (catom n) env k = refl
encLiftCorrect (cnode a b) env k =
  eqTr
    -- Step 1: substitute fold(b) with encLiftExpected(b) via IH
    (eqCong (\ fb -> evalCT f2 (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb)
      (foldCT f2 env a acEnc ncEnc)) b) a) ncEnc)
      ihB)
    (eqTr
      -- Step 2: substitute fold(a) with encLiftExpected(a) via IH
      (eqCong (\ fa -> evalCT f2 (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env
        (encLiftExpected b)) fa) b) a) ncEnc)
        ihA)
      -- Step 3: final computation is refl (ncEnc at 3 suc's of fuel)
      refl)
  where
  ea : Nat
  ea = encLiftExtra a
  eb : Nat
  eb = encLiftExtra b

  -- f2 = the inner fuel (outer fuel minus one foldCT suc)
  -- outer = suc(suc(suc(suc(addB (addB ea eb) k))))
  -- f2 = suc(suc(suc(addB (addB ea eb) k))) = addB n3 (addB (addB ea eb) k)
  f2 : Nat
  f2 = suc (suc (suc (addB (addB ea eb) k)))

  -- IH on b: at fuel addB n3 (addB eb (addB ea k)) = f2
  -- Need: f2 = addB n3 (addB eb (addB ea k))
  -- f2 = suc(suc(addB (addB ea eb) k))
  --     = suc(suc(addB eb (addB ea k)))  [by comm-assoc ea eb k]
  --     = addB n3 (addB eb (addB ea k))... wait
  -- n3 = suc(suc(suc zero)). addB n3 X = suc(suc(suc X)).
  -- f2 = suc(suc(addB (addB ea eb) k)). This is suc(suc(Y)) where Y = addB (addB ea eb) k.
  -- addB n3 (addB eb (addB ea k)) = suc(suc(suc(addB eb (addB ea k))))
  --   = suc(suc(suc(addB (addB ea eb) k))) [by comm-assoc]
  --   = suc(suc(suc Y))
  -- But f2 = suc(suc Y). So f2 ≠ addB n3 (...). Off by one suc!

  -- CORRECTION: the outer fuel for cnode is addB n3 (addB (suc (addB ea eb)) k)
  --   = suc(suc(suc(addB (suc (addB ea eb)) k)))
  --   = suc(suc(suc(suc(addB (addB ea eb) k))))
  -- foldCT suc peels one: f2 = suc(suc(suc(addB (addB ea eb) k))) = addB n3 (addB (addB ea eb) k).
  -- IH on a at k' = addB eb k: addB n3 (addB ea (addB eb k))
  --   = suc(suc(suc(addB ea (addB eb k)))) = suc(suc(suc(addB (addB ea eb) k))) [assoc]
  --   = addB n3 (addB (addB ea eb) k) = f2. ✓
  -- IH on b at k' = addB ea k: addB n3 (addB eb (addB ea k))
  --   = suc(suc(suc(addB eb (addB ea k)))) = suc(suc(suc(addB (addB ea eb) k))) [comm-assoc]
  --   = f2. ✓

  -- Wait, I need to recompute. The outer fuel is:
  -- addB n3 (addB (encLiftExtra (cnode a b)) k)
  -- = addB n3 (addB (suc (addB ea eb)) k)
  -- = addB (suc (suc (suc zero))) (suc (addB (addB ea eb) k))
  -- = suc (suc (suc (suc (addB (addB ea eb) k))))
  -- So foldCT at this fuel: foldCT (suc (suc (suc (suc (addB (addB ea eb) k))))) ...
  -- foldCT suc gives: evalCT (suc (suc (suc (addB (addB ea eb) k)))) ...
  -- f2 = suc (suc (suc (addB (addB ea eb) k))) = addB n3 (addB (addB ea eb) k)

  -- So f2 IS addB n3 (addB (addB ea eb) k). And:
  -- IH on a: addB n3 (addB ea (addB eb k)) = addB n3 (addB (addB ea eb) k) [by assoc] = f2. ✓
  -- IH on b: addB n3 (addB eb (addB ea k)) = addB n3 (addB (addB ea eb) k) [by comm-assoc] = f2. ✓

  -- f2 = addB n3 (addB (addB ea eb) k)
  -- IH on b needs: f2 = addB n3 (addB eb (addB ea k))
  -- Proof: addB (addB ea eb) k = addB eb (addB ea k) by comm-assoc
  ihB : Eq (foldCT f2 env b acEnc ncEnc) (encLiftExpected b)
  ihB = eqTr
    (foldCT-fuel-eq f2 (addB n3 (addB eb (addB ea k)))
      (eqCong (addB n3) (addB-comm-assoc ea eb k))
      env b acEnc ncEnc)
    (encLiftCorrect b env (addB ea k))

  ihA : Eq (foldCT f2 env a acEnc ncEnc) (encLiftExpected a)
  ihA = eqTr
    (foldCT-fuel-eq f2 (addB n3 (addB ea (addB eb k)))
      (eqCong (addB n3) (addB-assoc ea eb k))
      env a acEnc ncEnc)
    (encLiftCorrect a env (addB eb k))
