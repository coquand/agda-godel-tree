{-# OPTIONS --without-K --exact-split #-}

module TreeArithB where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import ChwistekProvability
  using (Bool; true; false; and; Maybe; nothing; just;
         maybeBind; maybeMap; eqNat; eqCode; eqNat-refl)
open import TreeArith

private
  eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
  eqSym refl = refl
  eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
  eqTrans refl q = q
  eqSubstB : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
  eqSubstB P refl px = px
  mb-cong1 : {X Y : Set} (f : X -> Maybe Y) (r1 r2 : Maybe X) ->
    Eq r1 r2 -> Eq (maybeBind r1 f) (maybeBind r2 f)
  mb-cong1 f r1 r2 refl = refl
  and-true-both : (a b : Bool) -> Eq a true -> Eq b true -> Eq (and a b) true
  and-true-both true  true  refl refl = refl
  and-true-both true  false refl ()
  and-true-both false _     ()
  eqCode-refl : (c : Code) -> Eq (eqCode c c) true
  eqCode-refl (catom n)   = eqNat-refl n
  eqCode-refl (cnode a b) = and-true-both (eqCode a a) (eqCode b b)
                               (eqCode-refl a) (eqCode-refl b)
  eqFormTA-refl : (f : FormTA) -> Eq (eqFormTA f f) true
  eqFormTA-refl fbotTA        = refl
  eqFormTA-refl (fatomTA n)   = eqNat-refl n
  eqFormTA-refl (fimpTA a b)  = and-true-both (eqFormTA a a) (eqFormTA b b)
                                  (eqFormTA-refl a) (eqFormTA-refl b)
  eqFormTA-refl (fallTA a)    = eqFormTA-refl a
  eqFormTA-refl (feqTA c1 c2) = and-true-both (eqCode c1 c1) (eqCode c2 c2)
                                  (eqCode-refl c1) (eqCode-refl c2)
  eqNat-sound : (n m : Nat) -> Eq (eqNat n m) true -> Eq n m
  eqNat-sound zero    zero    refl = refl
  eqNat-sound zero    (suc _) ()
  eqNat-sound (suc _) zero    ()
  eqNat-sound (suc n) (suc m) h = eqCong suc (eqNat-sound n m h)
  and-true-split : (a b : Bool) -> Eq (and a b) true ->
    SigmaTA (Eq a true) (\ _ -> Eq b true)
  and-true-split true  true  refl = mkSigmaTA refl refl
  and-true-split true  false ()
  and-true-split false _     ()
  eqCode-sound : (c d : Code) -> Eq (eqCode c d) true -> Eq c d
  eqCode-sound (catom n)   (catom m)   h = eqCong catom (eqNat-sound n m h)
  eqCode-sound (catom _)   (cnode _ _) ()
  eqCode-sound (cnode _ _) (catom _)   ()
  eqCode-sound (cnode a b) (cnode c d) h = lem (and-true-split (eqCode a c) (eqCode b d) h)
    where
    lem : SigmaTA (Eq (eqCode a c) true) (\ _ -> Eq (eqCode b d) true) ->
          Eq (cnode a b) (cnode c d)
    lem (mkSigmaTA ha hb) = lem2 (eqCode-sound a c ha) (eqCode-sound b d hb)
      where
      lem2 : Eq a c -> Eq b d -> Eq (cnode a b) (cnode c d)
      lem2 refl refl = refl
  eqFormTA-sound : (f g : FormTA) -> Eq (eqFormTA f g) true -> Eq f g
  eqFormTA-sound fbotTA        fbotTA        refl = refl
  eqFormTA-sound fbotTA        (fatomTA _)   ()
  eqFormTA-sound fbotTA        (fimpTA _ _)  ()
  eqFormTA-sound fbotTA        (fallTA _)    ()
  eqFormTA-sound fbotTA        (feqTA _ _)   ()
  eqFormTA-sound (fatomTA _)   fbotTA        ()
  eqFormTA-sound (fatomTA n)   (fatomTA m)   h = eqCong fatomTA (eqNat-sound n m h)
  eqFormTA-sound (fatomTA _)   (fimpTA _ _)  ()
  eqFormTA-sound (fatomTA _)   (fallTA _)    ()
  eqFormTA-sound (fatomTA _)   (feqTA _ _)   ()
  eqFormTA-sound (fimpTA _ _)  fbotTA        ()
  eqFormTA-sound (fimpTA _ _)  (fatomTA _)   ()
  eqFormTA-sound (fimpTA a b)  (fimpTA c d)  h = lem (and-true-split (eqFormTA a c) (eqFormTA b d) h)
    where
    lem : SigmaTA (Eq (eqFormTA a c) true) (\ _ -> Eq (eqFormTA b d) true) ->
          Eq (fimpTA a b) (fimpTA c d)
    lem (mkSigmaTA ha hb) = lem2 (eqFormTA-sound a c ha) (eqFormTA-sound b d hb)
      where
      lem2 : Eq a c -> Eq b d -> Eq (fimpTA a b) (fimpTA c d)
      lem2 refl refl = refl
  eqFormTA-sound (fimpTA _ _)  (fallTA _)    ()
  eqFormTA-sound (fimpTA _ _)  (feqTA _ _)   ()
  eqFormTA-sound (fallTA _)    fbotTA        ()
  eqFormTA-sound (fallTA _)    (fatomTA _)   ()
  eqFormTA-sound (fallTA _)    (fimpTA _ _)  ()
  eqFormTA-sound (fallTA a)    (fallTA b)    h = eqCong fallTA (eqFormTA-sound a b h)
  eqFormTA-sound (fallTA _)    (feqTA _ _)   ()
  eqFormTA-sound (feqTA _ _)   fbotTA        ()
  eqFormTA-sound (feqTA _ _)   (fatomTA _)   ()
  eqFormTA-sound (feqTA _ _)   (fimpTA _ _)  ()
  eqFormTA-sound (feqTA _ _)   (fallTA _)    ()
  eqFormTA-sound (feqTA a b)   (feqTA c d)   h = lem (and-true-split (eqCode a c) (eqCode b d) h)
    where
    lem : SigmaTA (Eq (eqCode a c) true) (\ _ -> Eq (eqCode b d) true) ->
          Eq (feqTA a b) (feqTA c d)
    lem (mkSigmaTA ha hb) = lem2 (eqCode-sound a c ha) (eqCode-sound b d hb)
      where
      lem2 : Eq a c -> Eq b d -> Eq (feqTA a b) (feqTA c d)
      lem2 refl refl = refl
  -- matchMPTA-self via eqSubstB (matchMPTA now uses boolGuardTA)
  matchMPTA-self : (A B : FormTA) ->
    Eq (matchMPTA (fimpTA A B) A) (just B)
  matchMPTA-self A B =
    eqSubstB (\ b -> Eq (boolGuardTA b (just B)) (just B))
             (eqSym (eqFormTA-refl A))
             refl
  boolGuardTA-self : (A : FormTA) (r : Maybe FormTA) ->
    Eq (boolGuardTA (eqFormTA A A) r) r
  boolGuardTA-self A r =
    eqSubstB (\ b -> Eq (boolGuardTA b r) r)
             (eqSym (eqFormTA-refl A))
             refl
  addN : Nat -> Nat -> Nat
  addN zero    m = m
  addN (suc n) m = suc (addN n m)
  natMax : Nat -> Nat -> Nat
  natMax zero    m       = m
  natMax (suc n) zero    = suc n
  natMax (suc n) (suc m) = suc (natMax n m)
  justInj : {X : Set} {x y : X} -> Eq (just x) (just y) -> Eq x y
  justInj refl = refl
  boolGuardTA-just : (bo : Bool) (r : Maybe FormTA) (B : FormTA) ->
    Eq (boolGuardTA bo r) (just B) -> Eq bo true
  boolGuardTA-just true  r B h = refl
  boolGuardTA-just false r B ()

------------------------------------------------------------------------
-- 1. Consistency definitions
------------------------------------------------------------------------

ConExt : Set
ConExt = ProofTA fbotTA -> EmptyTA

conExt-proof : ConExt
conExt-proof = consistencyTA

ConInt : Set
ConInt = (n : Nat) -> (c : Code) -> Eq (checkTA n c) (just fbotTA) -> EmptyTA

------------------------------------------------------------------------
-- 2. Fuel monotonicity
------------------------------------------------------------------------

private
  hInst-fuel-eq : (f1 f2 : Nat) -> (fp a : FormTA) -> (c : Code) ->
    Eq (checkTA-hInst f1 fp a c) (checkTA-hInst f2 fp a c)
  hInst-fuel-eq f1 f2 fbotTA       a c = refl
  hInst-fuel-eq f1 f2 (fatomTA _)  a c = refl
  hInst-fuel-eq f1 f2 (fimpTA _ _) a c = refl
  hInst-fuel-eq f1 f2 (feqTA _ _)  a c = refl
  hInst-fuel-eq f1 f2 (fallTA _)   a c = refl

  checkTA-mono : (n : Nat) -> (p : Code) -> (A : FormTA) ->
    Eq (checkTA n p) (just A) -> Eq (checkTA (suc n) p) (just A)
  checkTA-mono-d90 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) ->
          Eq (checkTA fuel p) (just A) -> Eq (checkTA (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d90 fuel b tag payload) (just A) ->
    Eq (checkTA-d90 (suc fuel) b tag payload) (just A)
  checkTA-mono-d91 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) ->
          Eq (checkTA fuel p) (just A) -> Eq (checkTA (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d91 fuel b tag payload) (just A) ->
    Eq (checkTA-d91 (suc fuel) b tag payload) (just A)
  checkTA-mono-d92 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) ->
          Eq (checkTA fuel p) (just A) -> Eq (checkTA (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d92 fuel b tag payload) (just A) ->
    Eq (checkTA-d92 (suc fuel) b tag payload) (just A)
  checkTA-mono-d93 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) ->
          Eq (checkTA fuel p) (just A) -> Eq (checkTA (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d93 fuel b tag payload) (just A) ->
    Eq (checkTA-d93 (suc fuel) b tag payload) (just A)
  checkTA-mono-d94 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) ->
          Eq (checkTA fuel p) (just A) -> Eq (checkTA (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d94 fuel b tag payload) (just A) ->
    Eq (checkTA-d94 (suc fuel) b tag payload) (just A)
  checkTA-mono-d95 : (fuel : Nat) ->
    (b : Bool) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d95 fuel b payload) (just A) ->
    Eq (checkTA-d95 (suc fuel) b payload) (just A)

  checkTA-mono-d95 fuel true  c A h = h
  checkTA-mono-d95 fuel false _ A ()

  checkTA-mono-d94 fuel IH true tag (cnode p (cnode ac c)) A h =
    lem1 (checkTA fuel p) (checkTA (suc fuel) p) (\ fp -> IH p fp) h
    where
    lem1 : (r1 r2 : Maybe FormTA) ->
      ((X : FormTA) -> Eq r1 (just X) -> Eq r2 (just X)) ->
      Eq (maybeBind r1 (\ fp -> maybeBind (decFormTA ac) (\ a ->
          checkTA-hInst fuel fp a c))) (just A) ->
      Eq (maybeBind r2 (\ fp -> maybeBind (decFormTA ac) (\ a ->
          checkTA-hInst (suc fuel) fp a c))) (just A)
    lem1 nothing  _  _  ()
    lem1 (just x) r2 mono h2 =
      eqTrans
        (mb-cong1 (\ fp -> maybeBind (decFormTA ac) (\ a -> checkTA-hInst (suc fuel) fp a c))
                  r2 (just x) (mono x refl))
        (lem2 (decFormTA ac) h2)
      where
      lem2 : (rd : Maybe FormTA) ->
        Eq (maybeBind rd (\ a -> checkTA-hInst fuel x a c)) (just A) ->
        Eq (maybeBind rd (\ a -> checkTA-hInst (suc fuel) x a c)) (just A)
      lem2 nothing  ()
      lem2 (just a) h3 = eqTrans (eqSym (hInst-fuel-eq fuel (suc fuel) x a c)) h3
  checkTA-mono-d94 fuel IH true tag (cnode p (catom _)) A ()
  checkTA-mono-d94 fuel IH true tag (catom _) A ()
  checkTA-mono-d94 fuel IH false tag payload A h =
    checkTA-mono-d95 fuel (eqNat tag n95) payload A h

  checkTA-mono-d93 fuel IH true tag p A h =
    lem1 (checkTA fuel p) (checkTA (suc fuel) p) (\ fp -> IH p fp) h
    where
    lem1 : (r1 r2 : Maybe FormTA) ->
      ((X : FormTA) -> Eq r1 (just X) -> Eq r2 (just X)) ->
      Eq (maybeMap fallTA r1) (just A) -> Eq (maybeMap fallTA r2) (just A)
    lem1 nothing  _  _  ()
    lem1 (just x) r2 mono h2 = eqTrans (eqCong (maybeMap fallTA) (mono x refl)) h2
  checkTA-mono-d93 fuel IH false tag payload A h =
    checkTA-mono-d94 fuel IH (eqNat tag n94) tag payload A h

  checkTA-mono-d92 fuel IH true tag (cnode p1 p2) A h =
    lem1 (checkTA fuel p1) (checkTA (suc fuel) p1)
         (checkTA fuel p2) (checkTA (suc fuel) p2)
         (\ fp -> IH p1 fp) (\ fp -> IH p2 fp) h
    where
    lem1 : (r1 s1 r2 s2 : Maybe FormTA) ->
      ((X : FormTA) -> Eq r1 (just X) -> Eq s1 (just X)) ->
      ((X : FormTA) -> Eq r2 (just X) -> Eq s2 (just X)) ->
      Eq (maybeBind r1 (\ f1 -> maybeBind r2 (\ f2 -> matchMPTA f1 f2))) (just A) ->
      Eq (maybeBind s1 (\ f1 -> maybeBind s2 (\ f2 -> matchMPTA f1 f2))) (just A)
    lem1 nothing  _  _  _  _  _  ()
    lem1 (just x) s1 nothing  _  m1 _  ()
    lem1 (just x) s1 (just y) s2 m1 m2 h2 =
      eqTrans (mb-cong1 (\ f1 -> maybeBind s2 (\ f2 -> matchMPTA f1 f2))
                        s1 (just x) (m1 x refl))
      (eqTrans (eqCong (\ r -> maybeBind r (\ f2 -> matchMPTA x f2)) (m2 y refl)) h2)
  checkTA-mono-d92 fuel IH true  tag (catom _) A ()
  checkTA-mono-d92 fuel IH false tag payload A h =
    checkTA-mono-d93 fuel IH (eqNat tag n93) tag payload A h

  checkTA-mono-d91 fuel IH true  tag (cnode ac (cnode bc cc)) A h = h
  checkTA-mono-d91 fuel IH true  tag (cnode _ (catom _)) A h = h
  checkTA-mono-d91 fuel IH true  tag (catom _) A h = h
  checkTA-mono-d91 fuel IH false tag payload A h =
    checkTA-mono-d92 fuel IH (eqNat tag n92) tag payload A h

  checkTA-mono-d90 fuel IH true  tag (cnode ac bc) A h = h
  checkTA-mono-d90 fuel IH true  tag (catom _) A ()
  checkTA-mono-d90 fuel IH false tag payload A h =
    checkTA-mono-d91 fuel IH (eqNat tag n91) tag payload A h

  checkTA-mono zero p A ()
  checkTA-mono (suc n) (catom _) A ()
  checkTA-mono (suc n) (cnode (cnode _ _) _) A ()
  checkTA-mono (suc n) (cnode (catom tag) payload) A h =
    checkTA-mono-d90 n (\ p2 a2 -> checkTA-mono n p2 a2)
                     (eqNat tag n90) tag payload A h

------------------------------------------------------------------------
-- 3. Lifting to natMax
------------------------------------------------------------------------

private
  checkTA-mono-plus : (k n : Nat) -> (p : Code) -> (A : FormTA) ->
    Eq (checkTA n p) (just A) -> Eq (checkTA (addN k n) p) (just A)
  checkTA-mono-plus zero    n p A h = h
  checkTA-mono-plus (suc k) n p A h =
    checkTA-mono (addN k n) p A (checkTA-mono-plus k n p A h)
  addN-zero-right : (n : Nat) -> Eq (addN n zero) n
  addN-zero-right zero    = refl
  addN-zero-right (suc n) = eqCong suc (addN-zero-right n)
  addN-suc-right : (k n : Nat) -> Eq (addN k (suc n)) (suc (addN k n))
  addN-suc-right zero    n = refl
  addN-suc-right (suc k) n = eqCong suc (addN-suc-right k n)
  natMax-add-left : (n m : Nat) -> SigmaTA Nat (\ k -> Eq (natMax n m) (addN k n))
  natMax-add-left zero    m = mkSigmaTA m (eqSym (addN-zero-right m))
  natMax-add-left (suc n) zero    = mkSigmaTA zero refl
  natMax-add-left (suc n) (suc m) = helper (natMax-add-left n m)
    where
    helper : SigmaTA Nat (\ k -> Eq (natMax n m) (addN k n)) ->
             SigmaTA Nat (\ k -> Eq (suc (natMax n m)) (addN k (suc n)))
    helper (mkSigmaTA k eq) =
      mkSigmaTA k (eqTrans (eqCong suc eq) (eqSym (addN-suc-right k n)))
  natMax-add-right : (n m : Nat) -> SigmaTA Nat (\ k -> Eq (natMax n m) (addN k m))
  natMax-add-right zero    m = mkSigmaTA zero refl
  natMax-add-right (suc n) zero    = mkSigmaTA (suc n) (eqSym (addN-zero-right (suc n)))
  natMax-add-right (suc n) (suc m) = helper (natMax-add-right n m)
    where
    helper : SigmaTA Nat (\ k -> Eq (natMax n m) (addN k m)) ->
             SigmaTA Nat (\ k -> Eq (suc (natMax n m)) (addN k (suc m)))
    helper (mkSigmaTA k eq) =
      mkSigmaTA k (eqTrans (eqCong suc eq) (eqSym (addN-suc-right k m)))
  checkTA-lift-left : (k1 k2 : Nat) -> (p : Code) -> (A : FormTA) ->
    Eq (checkTA k1 p) (just A) -> Eq (checkTA (natMax k1 k2) p) (just A)
  checkTA-lift-left k1 k2 p A h = helper (natMax-add-left k1 k2)
    where
    helper : SigmaTA Nat (\ k -> Eq (natMax k1 k2) (addN k k1)) ->
             Eq (checkTA (natMax k1 k2) p) (just A)
    helper (mkSigmaTA k eq) =
      eqSubstB (\ m -> Eq (checkTA m p) (just A)) (eqSym eq) (checkTA-mono-plus k k1 p A h)
  checkTA-lift-right : (k1 k2 : Nat) -> (p : Code) -> (A : FormTA) ->
    Eq (checkTA k2 p) (just A) -> Eq (checkTA (natMax k1 k2) p) (just A)
  checkTA-lift-right k1 k2 p A h = helper (natMax-add-right k1 k2)
    where
    helper : SigmaTA Nat (\ k -> Eq (natMax k1 k2) (addN k k2)) ->
             Eq (checkTA (natMax k1 k2) p) (just A)
    helper (mkSigmaTA k eq) =
      eqSubstB (\ m -> Eq (checkTA m p) (just A)) (eqSym eq) (checkTA-mono-plus k k2 p A h)

------------------------------------------------------------------------
-- 4. Full encoding correctness (D1)
------------------------------------------------------------------------

encodeTA-correct :
  {A : FormTA} -> (prf : ProofTA A) ->
  SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA prf)) (just A))
encodeTA-correct (axReflTA c) = mkSigmaTA n1 (encodeTA-axRefl c)
encodeTA-correct (axKTA a b) = mkSigmaTA n1 (encodeTA-axK a b)
encodeTA-correct (axSTA a b c) = mkSigmaTA n1 (encodeTA-axS a b c)
encodeTA-correct (genTA {A} pf) = helper (encodeTA-correct pf)
  where
  helper : SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA pf)) (just A)) ->
           SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA (genTA pf))) (just (fallTA A)))
  helper (mkSigmaTA k h) =
    mkSigmaTA (suc k) (mm-just fallTA A (checkTA k (encProofTA pf)) h)
encodeTA-correct (mpTA {A} {B} pf1 pf2) =
  mpHelper (encodeTA-correct pf1) (encodeTA-correct pf2)
  where
  mpHelper :
    SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA pf1)) (just (fimpTA A B))) ->
    SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA pf2)) (just A)) ->
    SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA (mpTA pf1 pf2))) (just B))
  mpHelper (mkSigmaTA k1 h1) (mkSigmaTA k2 h2) =
    mkSigmaTA (suc km)
      (eqTrans
        (eqCong (\ r -> maybeBind r (\ f1 ->
                  maybeBind (checkTA km (encProofTA pf2)) (\ f2 -> matchMPTA f1 f2)))
                h1')
        (eqTrans
          (eqCong (\ r -> maybeBind r (\ f2 -> matchMPTA (fimpTA A B) f2)) h2')
          (matchMPTA-self A B)))
    where
    km : Nat
    km = natMax k1 k2
    h1' : Eq (checkTA km (encProofTA pf1)) (just (fimpTA A B))
    h1' = checkTA-lift-left k1 k2 (encProofTA pf1) (fimpTA A B) h1
    h2' : Eq (checkTA km (encProofTA pf2)) (just A)
    h2' = checkTA-lift-right k1 k2 (encProofTA pf2) A h2
encodeTA-correct (instTA A c pf) = instHelper (encodeTA-correct pf)
  where
  instHelper :
    SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA pf)) (just (fallTA A))) ->
    SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA (instTA A c pf))) (just (substFormTA c A)))
  instHelper (mkSigmaTA k h) =
    mkSigmaTA (suc k)
      (eqTrans
        (eqCong (\ r -> maybeBind r (\ fp ->
                  maybeBind (decFormTA (encFormTA A)) (\ a -> checkTA-hInst k fp a c)))
                h)
        (eqTrans
          (eqCong (\ r -> maybeBind r (\ a -> checkTA-hInst k (fallTA A) a c))
                  (decFormTA-encFormTA A))
          (boolGuardTA-self A (just (substFormTA c A)))))

------------------------------------------------------------------------
-- 5. ConInt -> ConExt
------------------------------------------------------------------------

conInt-to-conExt : ConInt -> ConExt
conInt-to-conExt conI prf = extractBot (encodeTA-correct prf)
  where
  extractBot : SigmaTA Nat (\ k -> Eq (checkTA k (encProofTA prf)) (just fbotTA)) -> EmptyTA
  extractBot (mkSigmaTA k eq) = conI k (encProofTA prf) eq

------------------------------------------------------------------------
-- 6. Checker soundness
------------------------------------------------------------------------

private
  -- matchMPTA now uses boolGuardTA (transparent). We can use
  -- boolGuardTA-just to derive eqFormTA a f2 = true, then
  -- eqFormTA-sound to get a = f2, then transport.
  matchMPTA-good : (f1 f2 : FormTA) -> (B : FormTA) ->
    GoodTA f1 -> GoodTA f2 ->
    Eq (matchMPTA f1 f2) (just B) -> GoodTA B
  matchMPTA-good fbotTA       f2 B g1 g2 ()
  matchMPTA-good (fatomTA _)  f2 B g1 g2 ()
  matchMPTA-good (fallTA _)   f2 B g1 g2 ()
  matchMPTA-good (feqTA _ _)  f2 B g1 g2 ()
  matchMPTA-good (fimpTA a b) f2 B g1 g2 h =
    -- h : Eq (boolGuardTA (eqFormTA a f2) (just b)) (just B)
    -- boolGuardTA-just gives: eqFormTA a f2 = true
    -- eqFormTA-sound gives: a = f2
    -- After substituting a for f2: h becomes Eq (boolGuardTA (eqFormTA a a) (just b)) (just B)
    -- = Eq (just b) (just B), so B = b
    -- g1 : GoodTA a -> GoodTA b, g2 : GoodTA f2 = GoodTA a (after subst)
    matchMPTA-good-h (eqFormTA-sound a f2 (boolGuardTA-just (eqFormTA a f2) (just b) B h)) g1 g2 h
    where
    matchMPTA-good-h : Eq a f2 ->
      (GoodTA a -> GoodTA b) -> GoodTA f2 ->
      Eq (boolGuardTA (eqFormTA a f2) (just b)) (just B) -> GoodTA B
    matchMPTA-good-h refl gab gf2' h' =
      -- Now f2 = a, so eqFormTA a a = true, boolGuardTA true (just b) = just b
      -- h' : Eq (just b) (just B) (after eqFormTA a a reduces to true)
      -- But eqFormTA a a does NOT reduce for variable a.
      -- Use eqSubstB instead:
      eqSubstB GoodTA (justInj (eqTrans (eqSym (boolGuardTA-self a (just b))) h')) (gab gf2')

  hInst-good : (fuel : Nat) -> (fp a : FormTA) -> (c : Code) -> (B : FormTA) ->
    GoodTA fp ->
    Eq (checkTA-hInst fuel fp a c) (just B) -> GoodTA B
  hInst-good fuel fbotTA       a c B _  ()
  hInst-good fuel (fatomTA _)  a c B _  ()
  hInst-good fuel (fimpTA _ _) a c B _  ()
  hInst-good fuel (feqTA _ _)  a c B _  ()
  hInst-good fuel (fallTA body) a c B gf h =
    -- h : Eq (boolGuardTA (eqFormTA body a) (just (substFormTA c a))) (just B)
    hInst-good-h (eqFormTA-sound body a (boolGuardTA-just (eqFormTA body a) (just (substFormTA c a)) B h)) gf h
    where
    hInst-good-h : Eq body a ->
      GoodTA (fallTA body) ->
      Eq (boolGuardTA (eqFormTA body a) (just (substFormTA c a))) (just B) -> GoodTA B
    hInst-good-h refl gf' h' =
      eqSubstB GoodTA
        (justInj (eqTrans (eqSym (boolGuardTA-self a (just (substFormTA c a)))) h'))
        (eqSubstB GoodTA (eqSym (substFormTA-id c a)) (gf' c))

  checkTA-sound : (n : Nat) -> (c : Code) -> (A : FormTA) ->
    Eq (checkTA n c) (just A) -> GoodTA A
  checkTA-sound-d90 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) -> Eq (checkTA fuel p) (just A) -> GoodTA A) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d90 fuel b tag payload) (just A) -> GoodTA A
  checkTA-sound-d91 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) -> Eq (checkTA fuel p) (just A) -> GoodTA A) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d91 fuel b tag payload) (just A) -> GoodTA A
  checkTA-sound-d92 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) -> Eq (checkTA fuel p) (just A) -> GoodTA A) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d92 fuel b tag payload) (just A) -> GoodTA A
  checkTA-sound-d93 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) -> Eq (checkTA fuel p) (just A) -> GoodTA A) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d93 fuel b tag payload) (just A) -> GoodTA A
  checkTA-sound-d94 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA) -> Eq (checkTA fuel p) (just A) -> GoodTA A) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d94 fuel b tag payload) (just A) -> GoodTA A
  checkTA-sound-d95 : (fuel : Nat) ->
    (b : Bool) -> (payload : Code) -> (A : FormTA) ->
    Eq (checkTA-d95 fuel b payload) (just A) -> GoodTA A

  checkTA-sound-d95 fuel true  c .(feqTA c c) refl = refl
  checkTA-sound-d95 fuel false _ A ()

  checkTA-sound-d94 fuel IH true tag (cnode p (cnode ac c)) A h =
    lem (checkTA fuel p) (IH p) h
    where
    lem : (r : Maybe FormTA) ->
      ((X : FormTA) -> Eq r (just X) -> GoodTA X) ->
      Eq (maybeBind r (\ fp -> maybeBind (decFormTA ac) (\ a ->
          checkTA-hInst fuel fp a c))) (just A) -> GoodTA A
    lem nothing  _  ()
    lem (just x) gx h2 = lem2 (decFormTA ac) h2
      where
      lem2 : (r2 : Maybe FormTA) ->
        Eq (maybeBind r2 (\ a -> checkTA-hInst fuel x a c)) (just A) -> GoodTA A
      lem2 nothing  ()
      lem2 (just a) h3 = hInst-good fuel x a c A (gx x refl) h3
  checkTA-sound-d94 fuel IH true tag (cnode p (catom _)) A ()
  checkTA-sound-d94 fuel IH true tag (catom _) A ()
  checkTA-sound-d94 fuel IH false tag payload A h =
    checkTA-sound-d95 fuel (eqNat tag n95) payload A h

  checkTA-sound-d93 fuel IH true tag p A h =
    lem (checkTA fuel p) (IH p) h
    where
    lem : (r : Maybe FormTA) ->
      ((X : FormTA) -> Eq r (just X) -> GoodTA X) ->
      Eq (maybeMap fallTA r) (just A) -> GoodTA A
    lem nothing  _  ()
    lem (just x) gx refl = \ c -> gx x refl
  checkTA-sound-d93 fuel IH false tag payload A h =
    checkTA-sound-d94 fuel IH (eqNat tag n94) tag payload A h

  checkTA-sound-d92 fuel IH true tag (cnode p1 p2) A h =
    lem (checkTA fuel p1) (checkTA fuel p2) (IH p1) (IH p2) h
    where
    lem : (r1 r2 : Maybe FormTA) ->
      ((X : FormTA) -> Eq r1 (just X) -> GoodTA X) ->
      ((X : FormTA) -> Eq r2 (just X) -> GoodTA X) ->
      Eq (maybeBind r1 (\ f1 -> maybeBind r2 (\ f2 -> matchMPTA f1 f2))) (just A) -> GoodTA A
    lem nothing  _  _  _  ()
    lem (just x) nothing  _  _  ()
    lem (just x) (just y) gx gy h2 = matchMPTA-good x y A (gx x refl) (gy y refl) h2
  checkTA-sound-d92 fuel IH true  tag (catom _) A ()
  checkTA-sound-d92 fuel IH false tag payload A h =
    checkTA-sound-d93 fuel IH (eqNat tag n93) tag payload A h

  checkTA-sound-d91 fuel IH true tag (cnode ac (cnode bc cc)) A h =
    lem (decFormTA ac) (decFormTA bc) (decFormTA cc) h
    where
    lem : (r1 r2 r3 : Maybe FormTA) ->
      Eq (maybeBind r1 (\ a -> maybeBind r2 (\ b -> maybeBind r3 (\ c ->
          just (fimpTA (fimpTA a (fimpTA b c))
                       (fimpTA (fimpTA a b) (fimpTA a c))))))) (just A) -> GoodTA A
    lem nothing  _        _        ()
    lem (just _) nothing  _        ()
    lem (just _) (just _) nothing  ()
    lem (just a) (just b) (just c) refl = \ gABC -> \ gAB -> \ gA -> gABC gA (gAB gA)
  checkTA-sound-d91 fuel IH true  tag (cnode _ (catom _)) A ()
  checkTA-sound-d91 fuel IH true  tag (catom _) A ()
  checkTA-sound-d91 fuel IH false tag payload A h =
    checkTA-sound-d92 fuel IH (eqNat tag n92) tag payload A h

  checkTA-sound-d90 fuel IH true tag (cnode ac bc) A h =
    lem (decFormTA ac) (decFormTA bc) h
    where
    lem : (r1 r2 : Maybe FormTA) ->
      Eq (maybeBind r1 (\ a -> maybeBind r2 (\ b -> just (fimpTA a (fimpTA b a))))) (just A) ->
      GoodTA A
    lem nothing  _        ()
    lem (just _) nothing  ()
    lem (just a) (just b) refl = \ ga -> \ _ -> ga
  checkTA-sound-d90 fuel IH true  tag (catom _) A ()
  checkTA-sound-d90 fuel IH false tag payload A h =
    checkTA-sound-d91 fuel IH (eqNat tag n91) tag payload A h

  checkTA-sound zero    c A ()
  checkTA-sound (suc n) (catom _) A ()
  checkTA-sound (suc n) (cnode (cnode _ _) _) A ()
  checkTA-sound (suc n) (cnode (catom tag) payload) A h =
    checkTA-sound-d90 n (\ p a -> checkTA-sound n p a) (eqNat tag n90) tag payload A h

------------------------------------------------------------------------
-- 7. ConExt -> ConInt
------------------------------------------------------------------------

conExt-to-conInt : ConExt -> ConInt
conExt-to-conInt _ n c h = checkTA-sound n c fbotTA h

conInt-proof : ConInt
conInt-proof n c h = checkTA-sound n c fbotTA h

------------------------------------------------------------------------
-- 8. R3 = ConExt in Hilbert-style systems
------------------------------------------------------------------------

normalTA : {A : FormTA} -> ProofTA A -> UnitTA
normalTA _ = ttTA

R3 : Set
R3 = (prf : ProofTA fbotTA) -> Eq (normalTA prf) ttTA -> EmptyTA

r3-to-conExt : R3 -> ConExt
r3-to-conExt r3 prf = r3 prf refl

conExt-to-r3 : ConExt -> R3
conExt-to-r3 con prf _ = con prf

r3-proof : R3
r3-proof prf _ = consistencyTA prf
