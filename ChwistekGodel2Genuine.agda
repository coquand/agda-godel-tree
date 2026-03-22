{-# OPTIONS --without-K --exact-split #-}

module ChwistekGodel2Genuine where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness

------------------------------------------------------------------------
-- Unified self-referential checker with tags 30-39
------------------------------------------------------------------------

n36g : Nat
n36g = suc n35

n37g : Nat
n37g = suc n36g

n38g : Nat
n38g = suc n37g

n39g : Nat
n39g = suc n38g

matchCinst : Formula -> Code -> Maybe Formula
matchCinst (fcAll a) c = just (substFormulaCode0 (clit c) a)
matchCinst fbot        _ = nothing
matchCinst (feq _ _)   _ = nothing
matchCinst (fimp _ _)  _ = nothing
matchCinst (fall _)    _ = nothing
matchCinst (fcode _)   _ = nothing
matchCinst (fceq _ _)  _ = nothing

matchFceqTr : Formula -> Formula -> Maybe Formula
matchFceqTr (fceq e1 e2) (fceq e3 e4) =
  boolGuard (eqCExp e2 e3) (just (fceq e1 e4))
matchFceqTr _ _ = nothing

matchFceqSy : Formula -> Maybe Formula
matchFceqSy (fceq e1 e2) = just (fceq e2 e1)
matchFceqSy fbot        = nothing
matchFceqSy (feq _ _)   = nothing
matchFceqSy (fimp _ _)  = nothing
matchFceqSy (fall _)    = nothing
matchFceqSy (fcode _)   = nothing
matchFceqSy (fcAll _)   = nothing

eqMaybeCodeG : Maybe Code -> Code -> Bool
eqMaybeCodeG nothing  _ = false
eqMaybeCodeG (just x) y = eqCode x y

checkG : Nat -> Code -> Maybe Formula
evalG  : Nat -> CExp -> Maybe Code

evalG zero _ = nothing
evalG (suc n) (cvar _) = nothing
evalG (suc n) (clit c) = just c
evalG (suc n) (ccheck e) =
  maybeBind (evalG n e) (\ p ->
  maybeBind (checkG n p) (\ a ->
  just (encFormula a)))
evalG (suc n) (csub e1 e2) =
  maybeBind (evalG n e1) (\ c1 ->
  maybeBind (evalG n e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))

checkG zero _ = nothing
checkG (suc n) (cnode (catom tag) tc) = dispatch tag tc n
  where
  dispatch : Nat -> Code -> Nat -> Maybe Formula
  dispatch tag tc n = d30 (eqNat tag n30) tag tc n
    where
    d30 : Bool -> Nat -> Code -> Nat -> Maybe Formula
    d30 true _ tc _ = maybeBind (decTerm tc) (\ t -> just (feq t t))
    d30 false tag tc n = d31 (eqNat tag n31) tag tc n
      where
      d31 : Bool -> Nat -> Code -> Nat -> Maybe Formula
      d31 true _ (cnode ac bc) _ =
        maybeBind (decFormula ac) (\ a ->
        maybeBind (decFormula bc) (\ b ->
        just (fimp a (fimp b a))))
      d31 true _ _ _ = nothing
      d31 false tag tc n = d32 (eqNat tag n32) tag tc n
        where
        d32 : Bool -> Nat -> Code -> Nat -> Maybe Formula
        d32 true _ (cnode ac (cnode bc cc)) _ =
          maybeBind (decFormula ac) (\ a ->
          maybeBind (decFormula bc) (\ b ->
          maybeBind (decFormula cc) (\ c ->
          just (fimp (fimp a (fimp b c))
                     (fimp (fimp a b) (fimp a c))))))
        d32 true _ _ _ = nothing
        d32 false tag tc n = d33 (eqNat tag n33) tag tc n
          where
          d33 : Bool -> Nat -> Code -> Nat -> Maybe Formula
          d33 true _ (cnode p q) n =
            maybeBind (checkG n p) (\ pf ->
            maybeBind (checkG n q) (\ qf ->
            matchMP pf qf))
          d33 true _ _ _ = nothing
          d33 false tag tc n = d34 (eqNat tag n34) tag tc n
            where
            d34 : Bool -> Nat -> Code -> Nat -> Maybe Formula
            d34 true _ p n = maybeMap fall (checkG n p)
            d34 false tag tc n = d35 (eqNat tag n35) tag tc n
              where
              d35 : Bool -> Nat -> Code -> Nat -> Maybe Formula
              d35 true _ p n = maybeMap fcAll (checkG n p)
              d35 false tag tc n = d36 (eqNat tag n36g) tag tc n
                where
                d36 : Bool -> Nat -> Code -> Nat -> Maybe Formula
                d36 true _ (cnode ec c) n =
                  maybeBind (decCExp ec) (\ e ->
                  boolGuard (eqMaybeCodeG (evalG n e) c)
                    (just (fceq e (clit c))))
                d36 true _ (catom _) _ = nothing
                d36 false tag tc n = d37 (eqNat tag n37g) tag tc n
                  where
                  d37 : Bool -> Nat -> Code -> Nat -> Maybe Formula
                  d37 true _ (cnode p c) n =
                    maybeBind (checkG n p) (\ pf -> matchCinst pf c)
                  d37 true _ (catom _) _ = nothing
                  d37 false tag tc n = d38 (eqNat tag n38g) tag tc n
                    where
                    d38 : Bool -> Nat -> Code -> Nat -> Maybe Formula
                    d38 true _ (cnode p1 p2) n =
                      maybeBind (checkG n p1) (\ f1 ->
                      maybeBind (checkG n p2) (\ f2 ->
                      matchFceqTr f1 f2))
                    d38 true _ (catom _) _ = nothing
                    d38 false tag tc n = d39 (eqNat tag n39g) tc n
                      where
                      d39 : Bool -> Code -> Nat -> Maybe Formula
                      d39 true p n = maybeBind (checkG n p) matchFceqSy
                      d39 false (catom _)  _ = nothing
                      d39 false (cnode _ _) _ = nothing
checkG (suc n) (catom _) = nothing
checkG (suc n) (cnode (cnode _ _) _) = nothing

------------------------------------------------------------------------
-- Self-reference
------------------------------------------------------------------------

selfRefG : (n : Nat) ->
  Eq (evalG (suc (suc n)) (csub (clit phiCode) (clit phiCode)))
     (just (encFormula GoedelSentence))
selfRefG n = GoedelSentence-self-ref

------------------------------------------------------------------------
-- ProofG
------------------------------------------------------------------------

data ProofG (n : Nat) : Formula -> Set where
  baseG   : {A : Formula} -> Proof A -> ProofG n A
  axEvalG : (e : CExp) -> (c : Code) ->
            Eq (evalG n e) (just c) -> ProofG n (fceq e (clit c))
  mpG     : {A B : Formula} -> ProofG n (fimp A B) -> ProofG n A -> ProofG n B
  genG    : {A : Formula} -> ProofG n A -> ProofG n (fall A)
  cgenG   : {A : Formula} -> ProofG n A -> ProofG n (fcAll A)
  cinstG  : {A : Formula} -> ProofG n (fcAll A) -> (c : Code) ->
            ProofG n (substFormulaCode0 (clit c) A)
  fceqTrG : {e1 e2 e3 : CExp} ->
            ProofG n (fceq e1 e2) -> ProofG n (fceq e2 e3) ->
            ProofG n (fceq e1 e3)
  fceqSyG : {e1 e2 : CExp} ->
            ProofG n (fceq e1 e2) -> ProofG n (fceq e2 e1)

------------------------------------------------------------------------
-- Encode ProofG
------------------------------------------------------------------------

encodeProofG : {n : Nat} {A : Formula} -> ProofG n A -> Code
encodeProofG (baseG prf) = encodeProof prf
encodeProofG (axEvalG e c eq) = cnode (catom n36g) (cnode (encCExp e) c)
encodeProofG (mpG pf1 pf2) = cnode (catom n33)
  (cnode (encodeProofG pf1) (encodeProofG pf2))
encodeProofG (genG pf) = cnode (catom n34) (encodeProofG pf)
encodeProofG (cgenG pf) = cnode (catom n35) (encodeProofG pf)
encodeProofG (cinstG pf c) = cnode (catom n37g) (cnode (encodeProofG pf) c)
encodeProofG (fceqTrG pf1 pf2) = cnode (catom n38g)
  (cnode (encodeProofG pf1) (encodeProofG pf2))
encodeProofG (fceqSyG pf) = cnode (catom n39g) (encodeProofG pf)

------------------------------------------------------------------------
-- Fuel monotonicity for checkG / evalG
------------------------------------------------------------------------

-- Forward declarations (mutually recursive)
evalG-mono : (n : Nat) -> (e : CExp) -> (c : Code) ->
  Eq (evalG n e) (just c) -> Eq (evalG (suc n) e) (just c)
checkG-mono : (n : Nat) -> (p : Code) -> (A : Formula) ->
  Eq (checkG n p) (just A) -> Eq (checkG (suc n) p) (just A)

-- evalG monotonicity
evalG-mono zero _ _ ()
evalG-mono (suc n) (cvar _) _ ()
evalG-mono (suc n) (clit _) _ h = h
evalG-mono (suc n) (ccheck e) c h =
  ckH (evalG n e) refl h
  where
  ckH : (r : Maybe Code) -> Eq (evalG n e) r ->
    Eq (maybeBind r (\ p -> maybeBind (checkG n p)
        (\ a -> just (encFormula a)))) (just c) ->
    Eq (maybeBind (evalG (suc n) e) (\ p -> maybeBind (checkG (suc n) p)
        (\ a -> just (encFormula a)))) (just c)
  ckH nothing eq ()
  ckH (just p) eq h2 =
    eqTrans
      (eqCong (\ s -> maybeBind s (\ p2 -> maybeBind (checkG (suc n) p2)
                (\ a -> just (encFormula a))))
              (evalG-mono n e p eq))
      (ckH2 (checkG n p) refl h2)
    where
    ckH2 : (r2 : Maybe Formula) -> Eq (checkG n p) r2 ->
      Eq (maybeBind r2 (\ a -> just (encFormula a))) (just c) ->
      Eq (maybeBind (checkG (suc n) p) (\ a -> just (encFormula a))) (just c)
    ckH2 nothing eq2 ()
    ckH2 (just a) eq2 h3 =
      eqTrans (eqCong (\ s -> maybeBind s (\ a2 -> just (encFormula a2)))
                      (checkG-mono n p a eq2)) h3
evalG-mono (suc n) (csub e1 e2) c h =
  sH (evalG n e1) refl h
  where
  sH : (r1 : Maybe Code) -> Eq (evalG n e1) r1 ->
    Eq (maybeBind r1 (\ c1 -> maybeBind (evalG n e2) (\ c2 ->
        maybeBind (decFormula c1) (\ a ->
        just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c) ->
    Eq (maybeBind (evalG (suc n) e1) (\ c1 -> maybeBind (evalG (suc n) e2) (\ c2 ->
        maybeBind (decFormula c1) (\ a ->
        just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c)
  sH nothing eq ()
  sH (just c1) eq h2 =
    eqTrans
      (eqCong (\ s -> maybeBind s (\ c1' -> maybeBind (evalG (suc n) e2) (\ c2 ->
                maybeBind (decFormula c1') (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))))
              (evalG-mono n e1 c1 eq))
      (sH2 (evalG n e2) refl h2)
    where
    sH2 : (r2 : Maybe Code) -> Eq (evalG n e2) r2 ->
      Eq (maybeBind r2 (\ c2 -> maybeBind (decFormula c1) (\ a ->
          just (encFormula (substFormulaCode0 (clit c2) a))))) (just c) ->
      Eq (maybeBind (evalG (suc n) e2) (\ c2 -> maybeBind (decFormula c1) (\ a ->
          just (encFormula (substFormulaCode0 (clit c2) a))))) (just c)
    sH2 nothing eq2 ()
    sH2 (just c2) eq2 h3 =
      eqTrans (eqCong (\ s -> maybeBind s (\ c2' -> maybeBind (decFormula c1) (\ a ->
                        just (encFormula (substFormulaCode0 (clit c2') a)))))
                      (evalG-mono n e2 c2 eq2)) h3

-- Reusable mono helpers (forward-reference checkG-mono at fuel n)
liftCkBind : (n : Nat) -> (p : Code) -> (f : Formula -> Maybe Formula) ->
  (A : Formula) ->
  Eq (maybeBind (checkG n p) f) (just A) ->
  Eq (maybeBind (checkG (suc n) p) f) (just A)
liftCkBind n p f A hh = go (checkG n p) refl hh
  where
  go : (r : Maybe Formula) -> Eq (checkG n p) r ->
    Eq (maybeBind r f) (just A) -> Eq (maybeBind (checkG (suc n) p) f) (just A)
  go nothing eq ()
  go (just x) eq h2 =
    eqTrans (eqCong (\ s -> maybeBind s f) (checkG-mono n p x eq)) h2

liftCkMap : (n : Nat) -> (p : Code) -> (f : Formula -> Formula) ->
  (A : Formula) ->
  Eq (maybeMap f (checkG n p)) (just A) ->
  Eq (maybeMap f (checkG (suc n) p)) (just A)
liftCkMap n p f A hh = go (checkG n p) refl hh
  where
  go : (r : Maybe Formula) -> Eq (checkG n p) r ->
    Eq (maybeMap f r) (just A) -> Eq (maybeMap f (checkG (suc n) p)) (just A)
  go nothing eq ()
  go (just x) eq h2 =
    eqTrans (eqCong (maybeMap f) (checkG-mono n p x eq)) h2

liftCk2Bind : (n : Nat) -> (p q : Code) ->
  (g : Formula -> Formula -> Maybe Formula) -> (A : Formula) ->
  Eq (maybeBind (checkG n p) (\ f1 ->
      maybeBind (checkG n q) (\ f2 -> g f1 f2))) (just A) ->
  Eq (maybeBind (checkG (suc n) p) (\ f1 ->
      maybeBind (checkG (suc n) q) (\ f2 -> g f1 f2))) (just A)
liftCk2Bind n p q g A hh = go1 (checkG n p) refl hh
  where
  go1 : (r1 : Maybe Formula) -> Eq (checkG n p) r1 ->
    Eq (maybeBind r1 (\ f1 -> maybeBind (checkG n q) (\ f2 ->
        g f1 f2))) (just A) ->
    Eq (maybeBind (checkG (suc n) p) (\ f1 ->
        maybeBind (checkG (suc n) q) (\ f2 -> g f1 f2))) (just A)
  go1 nothing eq ()
  go1 (just f1) eq h2 =
    eqTrans
      (eqCong (\ s -> maybeBind s (\ f1' ->
                maybeBind (checkG (suc n) q) (\ f2 -> g f1' f2)))
              (checkG-mono n p f1 eq))
      (go2 (checkG n q) refl h2)
    where
    go2 : (r2 : Maybe Formula) -> Eq (checkG n q) r2 ->
      Eq (maybeBind r2 (\ f2 -> g f1 f2)) (just A) ->
      Eq (maybeBind (checkG (suc n) q) (\ f2 -> g f1 f2)) (just A)
    go2 nothing eq2 ()
    go2 (just f2) eq2 h3 =
      eqTrans (eqCong (\ s -> maybeBind s (\ f2' -> g f1 f2'))
                      (checkG-mono n q f2 eq2)) h3

liftEvGuard : (n : Nat) -> (ec cv : Code) -> (A : Formula) ->
  Eq (maybeBind (decCExp ec) (\ e ->
      boolGuard (eqMaybeCodeG (evalG n e) cv)
        (just (fceq e (clit cv))))) (just A) ->
  Eq (maybeBind (decCExp ec) (\ e ->
      boolGuard (eqMaybeCodeG (evalG (suc n) e) cv)
        (just (fceq e (clit cv))))) (just A)
liftEvGuard n ec cv A hh = goD (decCExp ec) refl hh
  where
  goD : (r : Maybe CExp) -> Eq (decCExp ec) r ->
    Eq (maybeBind r (\ e ->
        boolGuard (eqMaybeCodeG (evalG n e) cv)
          (just (fceq e (clit cv))))) (just A) ->
    Eq (maybeBind r (\ e ->
        boolGuard (eqMaybeCodeG (evalG (suc n) e) cv)
          (just (fceq e (clit cv))))) (just A)
  goD nothing eq ()
  goD (just e) eq h2 = goV (evalG n e) refl h2
    where
    goV : (rv : Maybe Code) -> Eq (evalG n e) rv ->
      Eq (boolGuard (eqMaybeCodeG rv cv)
            (just (fceq e (clit cv)))) (just A) ->
      Eq (boolGuard (eqMaybeCodeG (evalG (suc n) e) cv)
            (just (fceq e (clit cv)))) (just A)
    goV nothing eq2 ()
    goV (just v) eq2 h3 =
      eqSubst (\ s -> Eq (boolGuard (eqMaybeCodeG s cv)
                (just (fceq e (clit cv)))) (just A))
              (eqSym (evalG-mono n e v eq2)) h3

-- checkG monotonicity (explicit LHS patterns for with-clause scoping)
checkG-mono zero _ _ ()
checkG-mono (suc n) (catom _) _ ()
checkG-mono (suc n) (cnode (cnode _ _) _) _ ()
checkG-mono (suc n) (cnode (catom tag) tc) A h with eqNat tag n30
checkG-mono (suc n) (cnode (catom tag) tc) A h | true = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false with eqNat tag n31
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | true with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | true | cnode _ _ = h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | true | catom _ = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false with eqNat tag n32
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | true with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | true | cnode _ (cnode _ _) = h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | true | cnode _ (catom _) = h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | true | catom _ = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false with eqNat tag n33
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | true with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | true | cnode p q =
  liftCk2Bind n p q matchMP A h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | true | catom _ = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false with eqNat tag n34
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | true =
  liftCkMap n tc fall A h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false with eqNat tag n35
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | true =
  liftCkMap n tc fcAll A h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false with eqNat tag n36g
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | true with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | true | cnode ec cv =
  liftEvGuard n ec cv A h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | true | catom _ = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false with eqNat tag n37g
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false | true with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | false | true | cnode p cv =
  liftCkBind n p (\ pf -> matchCinst pf cv) A h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | false | true | catom _ = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false | false with eqNat tag n38g
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false | false | true with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | false | false | true | cnode p1 p2 =
  liftCk2Bind n p1 p2 matchFceqTr A h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | false | false | true | catom _ = h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false | false | false with eqNat tag n39g
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false | false | false | true =
  liftCkBind n tc matchFceqSy A h
checkG-mono (suc n) (cnode (catom tag) tc) A h | false | false | false | false | false | false | false | false | false | false with tc
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | false | false | false | false | catom _ = h
checkG-mono (suc n) (cnode (catom tag) _) A h | false | false | false | false | false | false | false | false | false | false | cnode _ _ = h

-- Addition
addN : Nat -> Nat -> Nat
addN zero m = m
addN (suc n) m = suc (addN n m)

-- Iterated monotonicity
checkG-mono-plus : (k n : Nat) -> (p : Code) -> (A : Formula) ->
  Eq (checkG n p) (just A) -> Eq (checkG (addN k n) p) (just A)
checkG-mono-plus zero n p A h = h
checkG-mono-plus (suc k) n p A h =
  checkG-mono (addN k n) p A (checkG-mono-plus k n p A h)

evalG-mono-plus : (k n : Nat) -> (e : CExp) -> (c : Code) ->
  Eq (evalG n e) (just c) -> Eq (evalG (addN k n) e) (just c)
evalG-mono-plus zero n e c h = h
evalG-mono-plus (suc k) n e c h =
  evalG-mono (addN k n) e c (evalG-mono-plus k n e c h)

------------------------------------------------------------------------
-- Encoding correctness (existential fuel)
------------------------------------------------------------------------

natMax : Nat -> Nat -> Nat
natMax zero m = m
natMax (suc n) zero = suc n
natMax (suc n) (suc m) = suc (natMax n m)

-- natMax is an upper bound
sigFstG : {A : Set} {B : A -> Set} -> Sigma A B -> A
sigFstG (mkSigma x _) = x

sigSndG : {A : Set} {B : A -> Set} -> (s : Sigma A B) -> B (sigFstG s)
sigSndG (mkSigma _ y) = y

addN-zero-right : (n : Nat) -> Eq (addN n zero) n
addN-zero-right zero = refl
addN-zero-right (suc n) = eqCong suc (addN-zero-right n)

addN-suc-right : (k n : Nat) -> Eq (addN k (suc n)) (suc (addN k n))
addN-suc-right zero n = refl
addN-suc-right (suc k) n = eqCong suc (addN-suc-right k n)

natMax-add-left : (n m : Nat) ->
  Sigma Nat (\ k -> Eq (natMax n m) (addN k n))
natMax-add-left zero m = mkSigma m (eqSym (addN-zero-right m))
natMax-add-left (suc n) zero = mkSigma zero refl
natMax-add-left (suc n) (suc m) = helper (natMax-add-left n m)
  where
  helper : Sigma Nat (\ k -> Eq (natMax n m) (addN k n)) ->
           Sigma Nat (\ k -> Eq (suc (natMax n m)) (addN k (suc n)))
  helper (mkSigma k eq) =
    mkSigma k (eqTrans (eqCong suc eq) (eqSym (addN-suc-right k n)))

natMax-add-right : (n m : Nat) ->
  Sigma Nat (\ k -> Eq (natMax n m) (addN k m))
natMax-add-right zero m = mkSigma zero refl
natMax-add-right (suc n) zero =
  mkSigma (suc n) (eqSym (addN-zero-right (suc n)))
natMax-add-right (suc n) (suc m) = helper (natMax-add-right n m)
  where
  helper : Sigma Nat (\ k -> Eq (natMax n m) (addN k m)) ->
           Sigma Nat (\ k -> Eq (suc (natMax n m)) (addN k (suc m)))
  helper (mkSigma k eq) =
    mkSigma k (eqTrans (eqCong suc eq) (eqSym (addN-suc-right k m)))

-- Lift checkG to natMax fuel
checkG-lift-left : (k1 k2 : Nat) -> (p : Code) -> (A : Formula) ->
  Eq (checkG k1 p) (just A) -> Eq (checkG (natMax k1 k2) p) (just A)
checkG-lift-left k1 k2 p A h = helper (natMax-add-left k1 k2)
  where
  helper : Sigma Nat (\ k -> Eq (natMax k1 k2) (addN k k1)) ->
           Eq (checkG (natMax k1 k2) p) (just A)
  helper (mkSigma k eq) =
    eqSubst (\ m -> Eq (checkG m p) (just A))
            (eqSym eq)
            (checkG-mono-plus k k1 p A h)

checkG-lift-right : (k1 k2 : Nat) -> (p : Code) -> (A : Formula) ->
  Eq (checkG k2 p) (just A) -> Eq (checkG (natMax k1 k2) p) (just A)
checkG-lift-right k1 k2 p A h = helper (natMax-add-right k1 k2)
  where
  helper : Sigma Nat (\ k -> Eq (natMax k1 k2) (addN k k2)) ->
           Eq (checkG (natMax k1 k2) p) (just A)
  helper (mkSigma k eq) =
    eqSubst (\ m -> Eq (checkG m p) (just A))
            (eqSym eq)
            (checkG-mono-plus k k2 p A h)

-- Encoding correctness: there exists fuel at which checkG accepts
encodeBaseG-fuel :
  {A : Formula} -> (prf : Proof A) ->
  Sigma Nat (\ k -> Eq (checkG k (encodeProof prf)) (just A))

encodeBaseG-fuel (ax-refl t) =
  mkSigma (suc zero) (refl-provable-lemma t)

encodeBaseG-fuel (ax-k A B) =
  mkSigma (suc zero)
    (eqTrans
      (eqCong (\ r -> maybeBind r
                (\ a -> maybeBind (decFormula (encFormula B))
                (\ b -> just (fimp a (fimp b a)))))
              (decFormula-encFormula A))
      (eqCong (\ r -> maybeBind r (\ b -> just (fimp A (fimp b A))))
              (decFormula-encFormula B)))

encodeBaseG-fuel (ax-s A B C) =
  mkSigma (suc zero)
    (eqTrans
      (eqCong (\ r -> maybeBind r
                (\ a -> maybeBind (decFormula (encFormula B))
                (\ b -> maybeBind (decFormula (encFormula C))
                (\ c -> just (fimp (fimp a (fimp b c))
                                   (fimp (fimp a b) (fimp a c)))))))
              (decFormula-encFormula A))
      (eqTrans
        (eqCong (\ r -> maybeBind r
                  (\ b -> maybeBind (decFormula (encFormula C))
                  (\ c -> just (fimp (fimp A (fimp b c))
                                     (fimp (fimp A b) (fimp A c))))))
                (decFormula-encFormula B))
        (eqCong (\ r -> maybeBind r
                  (\ c -> just (fimp (fimp A (fimp B c))
                                     (fimp (fimp A B) (fimp A c)))))
                (decFormula-encFormula C))))

encodeBaseG-fuel (mp {A} {B} pf1 pf2) =
  mpHelper (encodeBaseG-fuel pf1) (encodeBaseG-fuel pf2)
  where
  mpHelper :
    Sigma Nat (\ k -> Eq (checkG k (encodeProof pf1)) (just (fimp A B))) ->
    Sigma Nat (\ k -> Eq (checkG k (encodeProof pf2)) (just A)) ->
    Sigma Nat (\ k -> Eq (checkG k (encodeProof (mp pf1 pf2))) (just B))
  mpHelper (mkSigma k1 h1) (mkSigma k2 h2) =
    let km = natMax k1 k2
        h1' = checkG-lift-left k1 k2 (encodeProof pf1) (fimp A B) h1
        h2' = checkG-lift-right k1 k2 (encodeProof pf2) A h2
    in mkSigma (suc km)
       (eqTrans
         (eqCong (\ r -> maybeBind r (\ pf ->
                   maybeBind (checkG km (encodeProof pf2)) (\ qf ->
                   matchMP pf qf)))
                 h1')
         (eqTrans
           (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
                   h2')
           (guardEq-self A B)))

encodeBaseG-fuel (gen pf) = genHelper (encodeBaseG-fuel pf)
  where
  genHelper : Sigma Nat (\ k -> Eq (checkG k (encodeProof pf)) (just _)) ->
              Sigma Nat (\ k -> Eq (checkG k (encodeProof (gen pf))) (just _))
  genHelper (mkSigma k h) = mkSigma (suc k) (eqCong (maybeMap fall) h)

encodeBaseG-fuel (cgen pf) = cgenHelper (encodeBaseG-fuel pf)
  where
  cgenHelper : Sigma Nat (\ k -> Eq (checkG k (encodeProof pf)) (just _)) ->
               Sigma Nat (\ k -> Eq (checkG k (encodeProof (cgen pf))) (just _))
  cgenHelper (mkSigma k h) = mkSigma (suc k) (eqCong (maybeMap fcAll) h)

------------------------------------------------------------------------
-- Types shared with GoodG valuation
------------------------------------------------------------------------

data EmptyG2 : Set where
data UnitG2 : Set where
  ttG2 : UnitG2

CEnvG : Set
CEnvG = CVar -> Code

emptyCEnvG : CEnvG
emptyCEnvG _ = catom zero

extendCEnvG : CEnvG -> Code -> CEnvG
extendCEnvG env c cvz     = c
extendCEnvG env c (cvs v) = env v

------------------------------------------------------------------------
-- GoodG valuation (simplified semantics for Goedel II)
------------------------------------------------------------------------

GoodG : CEnvG -> Formula -> Set
GoodG env fbot         = EmptyG2
GoodG env (feq _ _)    = UnitG2
GoodG env (fimp a b)   = GoodG env a -> GoodG env b
GoodG env (fall _)     = UnitG2
GoodG env (fcode _)    = UnitG2
GoodG env (fceq _ _)   = UnitG2
GoodG env (fcAll a)    = (c : Code) -> GoodG (extendCEnvG env c) a

soundGoodBaseG : {A : Formula} -> Proof A -> (env : CEnvG) -> GoodG env A
soundGoodBaseG (ax-refl t) env = ttG2
soundGoodBaseG (ax-k A B) env = \ x _ -> x
soundGoodBaseG (ax-s A B C) env = \ f g a -> f a (g a)
soundGoodBaseG (mp pf1 pf2) env =
  soundGoodBaseG pf1 env (soundGoodBaseG pf2 env)
soundGoodBaseG (gen pf) env = ttG2
soundGoodBaseG (cgen pf) env =
  \ c -> soundGoodBaseG pf (extendCEnvG env c)

substGoodG : (A : Formula) -> (env : CEnvG) -> (c : Code) ->
  GoodG (extendCEnvG env c) A -> GoodG env (substFormulaCode0 (clit c) A)
unsubstGoodG : (A : Formula) -> (env : CEnvG) -> (c : Code) ->
  GoodG env (substFormulaCode0 (clit c) A) -> GoodG (extendCEnvG env c) A
substGoodG fbot env c g = g
substGoodG (feq _ _) env c g = ttG2
substGoodG (fimp a b) env c g =
  \ x -> substGoodG b env c (g (unsubstGoodG a env c x))
substGoodG (fall _) env c g = ttG2
substGoodG (fcode _) env c g = ttG2
substGoodG (fceq _ _) env c g = ttG2
substGoodG (fcAll a) env c g =
  \ c' -> substGoodG a (extendCEnvG env c') c (g c')
unsubstGoodG fbot env c g = g
unsubstGoodG (feq _ _) env c g = ttG2
unsubstGoodG (fimp a b) env c g =
  \ x -> unsubstGoodG b env c (g (substGoodG a env c x))
unsubstGoodG (fall _) env c g = ttG2
unsubstGoodG (fcode _) env c g = ttG2
unsubstGoodG (fceq _ _) env c g = ttG2
unsubstGoodG (fcAll a) env c g =
  \ c' -> unsubstGoodG a (extendCEnvG env c') c (g c')

soundGoodG : {n : Nat} {A : Formula} -> ProofG n A ->
  (env : CEnvG) -> GoodG env A
soundGoodG (baseG pf) env = soundGoodBaseG pf env
soundGoodG (axEvalG e c eq) env = ttG2
soundGoodG (mpG pf1 pf2) env =
  soundGoodG pf1 env (soundGoodG pf2 env)
soundGoodG (genG pf) env = ttG2
soundGoodG (cgenG pf) env =
  \ c -> soundGoodG pf (extendCEnvG env c)
soundGoodG (cinstG {A} pf c) env =
  substGoodG A env c (soundGoodG pf env c)
soundGoodG (fceqTrG pf1 pf2) env = ttG2
soundGoodG (fceqSyG pf) env = ttG2

------------------------------------------------------------------------
-- ProofG2: extended with cinstE and axSDrule for Goedel II
------------------------------------------------------------------------

data ProofG2 (n : Nat) : Formula -> Set where
  liftG    : {A : Formula} -> ProofG n A -> ProofG2 n A
  mpG2     : {A B : Formula} -> ProofG2 n (fimp A B) ->
             ProofG2 n A -> ProofG2 n B
  cgenG2   : {A : Formula} -> ProofG2 n A -> ProofG2 n (fcAll A)
  cinstEG  : {A : Formula} -> ProofG2 n (fcAll A) -> (e : CExp) ->
             ProofG2 n (substFormulaCode0 e A)
  axSDruleG : {e : CExp} ->
    ProofG2 n (fimp (fceq (ccheck e)
                          (csub (clit phiCode) (clit phiCode)))
                    (fceq (ccheck (csub (clit phiCode) e))
                          (clit (encFormula fbot))))

-- GoodG soundness for ProofG2

substGoodEG : (A : Formula) -> (env : CEnvG) -> (e : CExp) ->
  ((c : Code) -> GoodG (extendCEnvG env c) A) ->
  GoodG env (substFormulaCode0 e A)
unsubstGoodEG : (A : Formula) -> (env : CEnvG) -> (e : CExp) ->
  (c : Code) ->
  GoodG env (substFormulaCode0 e A) -> GoodG (extendCEnvG env c) A
substGoodEG fbot env e g = g (catom zero)
substGoodEG (feq _ _) env e g = ttG2
substGoodEG (fimp a b) env e f =
  \ x -> substGoodEG b env e
    (\ c -> f c (unsubstGoodEG a env e c x))
substGoodEG (fall _) env e g = ttG2
substGoodEG (fcode _) env e g = ttG2
substGoodEG (fceq _ _) env e g = ttG2
substGoodEG (fcAll a) env e g =
  \ c -> substGoodEG a (extendCEnvG env c) (liftCExp e) (\ c' -> g c' c)
unsubstGoodEG fbot env e c g = g
unsubstGoodEG (feq _ _) env e c g = ttG2
unsubstGoodEG (fimp a b) env e c g =
  \ x -> unsubstGoodEG b env e c
    (g (substGoodEG a env e (\ _ -> x)))
unsubstGoodEG (fall _) env e c g = ttG2
unsubstGoodEG (fcode _) env e c g = ttG2
unsubstGoodEG (fceq _ _) env e c g = ttG2
unsubstGoodEG (fcAll a) env e c g =
  \ c' -> unsubstGoodEG a (extendCEnvG env c') (liftCExp e) c (g c')

soundGoodG2 : {n : Nat} {A : Formula} -> ProofG2 n A ->
  (env : CEnvG) -> GoodG env A
soundGoodG2 (liftG pf) env = soundGoodG pf env
soundGoodG2 (mpG2 pf1 pf2) env =
  soundGoodG2 pf1 env (soundGoodG2 pf2 env)
soundGoodG2 (cgenG2 pf) env =
  \ c -> soundGoodG2 pf (extendCEnvG env c)
soundGoodG2 (cinstEG {A} pf e) env =
  substGoodEG A env e (soundGoodG2 pf env)
soundGoodG2 axSDruleG env = \ _ -> ttG2

------------------------------------------------------------------------
-- Goedel II: Con -> GoedelSentence -> EmptyG2
------------------------------------------------------------------------

-- Consistency formula
ConG : Formula
ConG = fcAll (fimp (fceq (ccheck (cvar cvz))
                         (clit (encFormula fbot)))
                   fbot)

-- GoedelSentence body (under fcAll)
GoedelBodyG : Formula
GoedelBodyG =
  fimp (fceq (ccheck (cvar cvz))
             (csub (clit phiCode) (clit phiCode)))
       fbot

-- Con implies GoedelSentence (internal derivation in ProofG2)

Con-implies-G-body :
  {n : Nat} ->
  ProofG2 n ConG ->
  ProofG2 n GoedelBodyG
Con-implies-G-body {n} con =
  compose-imp (axSDruleG {e = cvar cvz})
              (cinstEG con (csub (clit phiCode) (cvar cvz)))
  where
  compose-imp : {A B C : Formula} ->
    ProofG2 n (fimp A B) -> ProofG2 n (fimp B C) ->
    ProofG2 n (fimp A C)
  compose-imp {A} {B} {C} f g =
    mpG2 (mpG2 (liftG (baseG (ax-s A B C)))
               (mpG2 (liftG (baseG (ax-k (fimp B C) A))) g))
         f

Con-implies-G :
  {n : Nat} ->
  ProofG2 n ConG ->
  ProofG2 n GoedelSentence
Con-implies-G con = cgenG2 (Con-implies-G-body con)

------------------------------------------------------------------------
-- THE THEOREM: Goedel II for the genuine system
------------------------------------------------------------------------

-- goedel2-genuine: ConG is not provable in ProofG2.
--
-- Proof:
-- 1. From ProofG2 n ConG, derive ProofG2 n GoedelSentence via Con-implies-G
-- 2. GoedelSentence = fcAll GoedelBodyG = fcAll (fimp (fceq ...) fbot)
-- 3. GoodG env GoedelSentence = (c : Code) -> UnitG2 -> EmptyG2
-- 4. Instantiate at any code and apply ttG2 to get EmptyG2

goedel2-genuine : {n : Nat} -> ProofG2 n ConG -> EmptyG2
goedel2-genuine {n} con =
  let g = Con-implies-G con
  in soundGoodG2 g emptyCEnvG (catom zero) ttG2
