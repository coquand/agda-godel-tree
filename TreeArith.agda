{-# OPTIONS --without-K --exact-split #-}

module TreeArith where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import ChwistekProvability
  using (Bool; true; false; and; Maybe; nothing; just;
         maybeBind; maybeMap; eqNat; eqCode; eqNat-refl)

------------------------------------------------------------------------
-- Local infrastructure
------------------------------------------------------------------------

data EmptyTA : Set where

record UnitTA : Set where
  constructor ttTA

data SigmaTA (A : Set) (B : A -> Set) : Set where
  mkSigmaTA : (x : A) -> B x -> SigmaTA A B

------------------------------------------------------------------------
-- Tag constants
------------------------------------------------------------------------

n80 : Nat
n80 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

n81 : Nat
n81 = suc n80

n82 : Nat
n82 = suc n81

n83 : Nat
n83 = suc n82

n84 : Nat
n84 = suc n83

n90 : Nat
n90 = suc (suc (suc (suc (suc n84))))

n91 : Nat
n91 = suc n90

n92 : Nat
n92 = suc n91

n93 : Nat
n93 = suc n92

n94 : Nat
n94 = suc n93

n95 : Nat
n95 = suc n94

------------------------------------------------------------------------
-- Formulas
------------------------------------------------------------------------

data FormTA : Set where
  fbotTA  : FormTA
  fatomTA : Nat -> FormTA
  fimpTA  : FormTA -> FormTA -> FormTA
  fallTA  : FormTA -> FormTA
  feqTA   : Code -> Code -> FormTA

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

substFormTA : Code -> FormTA -> FormTA
substFormTA c fbotTA        = fbotTA
substFormTA c (fatomTA n)   = fatomTA n
substFormTA c (fimpTA a b)  = fimpTA (substFormTA c a) (substFormTA c b)
substFormTA c (fallTA a)    = fallTA a
substFormTA c (feqTA x y)   = feqTA x y

------------------------------------------------------------------------
-- Formula equality
------------------------------------------------------------------------

eqFormTA : FormTA -> FormTA -> Bool
eqFormTA fbotTA        fbotTA        = true
eqFormTA fbotTA        (fatomTA _)   = false
eqFormTA fbotTA        (fimpTA _ _)  = false
eqFormTA fbotTA        (fallTA _)    = false
eqFormTA fbotTA        (feqTA _ _)   = false
eqFormTA (fatomTA _)   fbotTA        = false
eqFormTA (fatomTA n)   (fatomTA m)   = eqNat n m
eqFormTA (fatomTA _)   (fimpTA _ _)  = false
eqFormTA (fatomTA _)   (fallTA _)    = false
eqFormTA (fatomTA _)   (feqTA _ _)   = false
eqFormTA (fimpTA _ _)  fbotTA        = false
eqFormTA (fimpTA _ _)  (fatomTA _)   = false
eqFormTA (fimpTA a b)  (fimpTA c d)  = and (eqFormTA a c) (eqFormTA b d)
eqFormTA (fimpTA _ _)  (fallTA _)    = false
eqFormTA (fimpTA _ _)  (feqTA _ _)   = false
eqFormTA (fallTA _)    fbotTA        = false
eqFormTA (fallTA _)    (fatomTA _)   = false
eqFormTA (fallTA _)    (fimpTA _ _)  = false
eqFormTA (fallTA a)    (fallTA b)    = eqFormTA a b
eqFormTA (fallTA _)    (feqTA _ _)   = false
eqFormTA (feqTA _ _)   fbotTA        = false
eqFormTA (feqTA _ _)   (fatomTA _)   = false
eqFormTA (feqTA _ _)   (fimpTA _ _)  = false
eqFormTA (feqTA _ _)   (fallTA _)    = false
eqFormTA (feqTA a b)   (feqTA c d)   = and (eqCode a c) (eqCode b d)

------------------------------------------------------------------------
-- Encoding
------------------------------------------------------------------------

encFormTA : FormTA -> Code
encFormTA fbotTA        = catom n80
encFormTA (fatomTA n)   = cnode (catom n81) (catom n)
encFormTA (fimpTA a b)  = cnode (catom n82) (cnode (encFormTA a) (encFormTA b))
encFormTA (fallTA a)    = cnode (catom n83) (encFormTA a)
encFormTA (feqTA c1 c2) = cnode (catom n84) (cnode c1 c2)

------------------------------------------------------------------------
-- Decoding (chain of top-level Bool dispatchers)
------------------------------------------------------------------------

decFormTA : Code -> Maybe FormTA

-- Level 1: is it fbot?
decFormTA-d80 : Bool -> Nat -> Code -> Maybe FormTA
-- Level 2: is tag n81 (fatom)?
decFormTA-d81 : Bool -> Nat -> Code -> Maybe FormTA
-- Level 3: is tag n82 (fimp)?
decFormTA-d82 : Bool -> Nat -> Code -> Maybe FormTA
-- Level 4: is tag n83 (fall)?
decFormTA-d83 : Bool -> Nat -> Code -> Maybe FormTA
-- Level 5: is tag n84 (feq)?
decFormTA-d84 : Bool -> Code -> Maybe FormTA

decFormTA (catom n)              = decFormTA-d80 (eqNat n n80) n (catom n)
decFormTA (cnode (catom t) p)    = decFormTA-d81 (eqNat t n81) t p
decFormTA (cnode (cnode _ _) _)  = nothing

decFormTA-d80 true  _ _ = just fbotTA
decFormTA-d80 false _ _ = nothing

decFormTA-d81 true  _ (catom n)    = just (fatomTA n)
decFormTA-d81 true  _ (cnode _ _)  = nothing
decFormTA-d81 false t p            = decFormTA-d82 (eqNat t n82) t p

decFormTA-d82 true _ (cnode ac bc) =
  maybeBind (decFormTA ac) (\ a ->
  maybeBind (decFormTA bc) (\ b ->
  just (fimpTA a b)))
decFormTA-d82 true  _ (catom _)    = nothing
decFormTA-d82 false t p            = decFormTA-d83 (eqNat t n83) t p

decFormTA-d83 true  _ p = maybeMap fallTA (decFormTA p)
decFormTA-d83 false t p = decFormTA-d84 (eqNat t n84) p

decFormTA-d84 true  (cnode c1 c2)  = just (feqTA c1 c2)
decFormTA-d84 true  (catom _)      = nothing
decFormTA-d84 false _              = nothing

------------------------------------------------------------------------
-- Proof system
------------------------------------------------------------------------

data ProofTA : FormTA -> Set where
  axKTA    : (A B : FormTA) -> ProofTA (fimpTA A (fimpTA B A))
  axSTA    : (A B C : FormTA) ->
              ProofTA (fimpTA (fimpTA A (fimpTA B C))
                              (fimpTA (fimpTA A B) (fimpTA A C)))
  mpTA     : {A B : FormTA} -> ProofTA (fimpTA A B) -> ProofTA A -> ProofTA B
  genTA    : {A : FormTA} -> ProofTA A -> ProofTA (fallTA A)
  instTA   : (A : FormTA) -> (c : Code) -> ProofTA (fallTA A) ->
              ProofTA (substFormTA c A)
  axReflTA : (c : Code) -> ProofTA (feqTA c c)

------------------------------------------------------------------------
-- Proof encoding
------------------------------------------------------------------------

encProofTA : {A : FormTA} -> ProofTA A -> Code
encProofTA (axKTA a b) =
  cnode (catom n90) (cnode (encFormTA a) (encFormTA b))
encProofTA (axSTA a b c) =
  cnode (catom n91) (cnode (encFormTA a) (cnode (encFormTA b) (encFormTA c)))
encProofTA (mpTA p q) =
  cnode (catom n92) (cnode (encProofTA p) (encProofTA q))
encProofTA (genTA p) =
  cnode (catom n93) (encProofTA p)
encProofTA (instTA a c p) =
  cnode (catom n94) (cnode (encProofTA p) (cnode (encFormTA a) c))
encProofTA (axReflTA c) =
  cnode (catom n95) c

------------------------------------------------------------------------
-- Bool guard
------------------------------------------------------------------------

boolGuardTA : Bool -> Maybe FormTA -> Maybe FormTA
boolGuardTA true  r = r
boolGuardTA false _ = nothing

------------------------------------------------------------------------
-- Modus ponens matcher
------------------------------------------------------------------------

matchMPTA : FormTA -> FormTA -> Maybe FormTA
matchMPTA (fimpTA a b) q = boolGuardTA (eqFormTA a q) (just b)
matchMPTA fbotTA       _ = nothing
matchMPTA (fatomTA _)  _ = nothing
matchMPTA (fallTA _)   _ = nothing
matchMPTA (feqTA _ _)  _ = nothing

------------------------------------------------------------------------
-- Checker (fuel-based)
------------------------------------------------------------------------

checkTA : Nat -> Code -> Maybe FormTA

-- Top-level dispatch chain for checker
checkTA-d90 : Nat -> Bool -> Nat -> Code -> Maybe FormTA
checkTA-d91 : Nat -> Bool -> Nat -> Code -> Maybe FormTA
checkTA-d92 : Nat -> Bool -> Nat -> Code -> Maybe FormTA
checkTA-d93 : Nat -> Bool -> Nat -> Code -> Maybe FormTA
checkTA-d94 : Nat -> Bool -> Nat -> Code -> Maybe FormTA
checkTA-d95 : Nat -> Bool -> Code -> Maybe FormTA
checkTA-hInst : Nat -> FormTA -> FormTA -> Code -> Maybe FormTA

checkTA zero _ = nothing
checkTA (suc n) (catom _) = nothing
checkTA (suc n) (cnode (cnode _ _) _) = nothing
checkTA (suc n) (cnode (catom tag) payload) =
  checkTA-d90 n (eqNat tag n90) tag payload

checkTA-d90 fuel true _ (cnode ac bc) =
  maybeBind (decFormTA ac) (\ a ->
  maybeBind (decFormTA bc) (\ b ->
  just (fimpTA a (fimpTA b a))))
checkTA-d90 fuel true _ (catom _) = nothing
checkTA-d90 fuel false tag payload =
  checkTA-d91 fuel (eqNat tag n91) tag payload

checkTA-d91 fuel true _ (cnode ac (cnode bc cc)) =
  maybeBind (decFormTA ac) (\ a ->
  maybeBind (decFormTA bc) (\ b ->
  maybeBind (decFormTA cc) (\ c ->
  just (fimpTA (fimpTA a (fimpTA b c))
               (fimpTA (fimpTA a b) (fimpTA a c))))))
checkTA-d91 fuel true  _ _ = nothing
checkTA-d91 fuel false tag payload =
  checkTA-d92 fuel (eqNat tag n92) tag payload

checkTA-d92 fuel true _ (cnode p1 p2) =
  maybeBind (checkTA fuel p1) (\ f1 ->
  maybeBind (checkTA fuel p2) (\ f2 ->
  matchMPTA f1 f2))
checkTA-d92 fuel true  _ (catom _) = nothing
checkTA-d92 fuel false tag payload =
  checkTA-d93 fuel (eqNat tag n93) tag payload

checkTA-d93 fuel true _ p = maybeMap fallTA (checkTA fuel p)
checkTA-d93 fuel false tag payload =
  checkTA-d94 fuel (eqNat tag n94) tag payload

checkTA-d94 fuel true _ (cnode p (cnode ac c)) =
  maybeBind (checkTA fuel p) (\ fp ->
  maybeBind (decFormTA ac) (\ a ->
  checkTA-hInst fuel fp a c))
checkTA-d94 fuel true  _ _ = nothing
checkTA-d94 fuel false tag payload =
  checkTA-d95 fuel (eqNat tag n95) payload

checkTA-d95 fuel true  c = just (feqTA c c)
checkTA-d95 fuel false _ = nothing

checkTA-hInst fuel (fallTA body) a c =
  boolGuardTA (eqFormTA body a) (just (substFormTA c a))
checkTA-hInst fuel fbotTA       _ _ = nothing
checkTA-hInst fuel (fatomTA _)  _ _ = nothing
checkTA-hInst fuel (fimpTA _ _) _ _ = nothing
checkTA-hInst fuel (feqTA _ _)  _ _ = nothing

------------------------------------------------------------------------
-- Negation, consistency
------------------------------------------------------------------------

FNotTA : FormTA -> FormTA
FNotTA a = fimpTA a fbotTA

ConTA : Set
ConTA = ProofTA fbotTA -> EmptyTA

------------------------------------------------------------------------
-- Soundness model
------------------------------------------------------------------------

-- substFormTA is the identity (no formula-level variables exist)
substFormTA-id : (c : Code) -> (f : FormTA) -> Eq (substFormTA c f) f
substFormTA-id c fbotTA        = refl
substFormTA-id c (fatomTA n)   = refl
substFormTA-id c (fimpTA a b)  = lemImp (substFormTA c a) (substFormTA c b)
                                        (substFormTA-id c a) (substFormTA-id c b)
  where
  lemImp : (x : FormTA) -> (y : FormTA) -> Eq x a -> Eq y b ->
           Eq (fimpTA x y) (fimpTA a b)
  lemImp .a .b refl refl = refl
substFormTA-id c (fallTA a)    = refl
substFormTA-id c (feqTA x y)   = refl

-- Transport for GoodTA
eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px

GoodTA : FormTA -> Set
GoodTA fbotTA        = EmptyTA
GoodTA (fatomTA _)   = UnitTA
GoodTA (fimpTA a b)  = GoodTA a -> GoodTA b
GoodTA (fallTA a)    = (c : Code) -> GoodTA a
GoodTA (feqTA c1 c2) = Eq c1 c2

soundTA : {A : FormTA} -> ProofTA A -> GoodTA A
soundTA (axKTA A B) = \ ga -> \ _ -> ga
soundTA (axSTA A B C) = \ gABC -> \ gAB -> \ gA -> gABC gA (gAB gA)
soundTA (mpTA pAB pA) = (soundTA pAB) (soundTA pA)
soundTA (genTA pA) = \ c -> soundTA pA
soundTA (instTA A c pAll) =
  eqSubst GoodTA (eqSym (substFormTA-id c A)) ((soundTA pAll) c)
  where
  eqSym : {X : Set} {a b : X} -> Eq a b -> Eq b a
  eqSym refl = refl
soundTA (axReflTA c) = refl

consistencyTA : ConTA
consistencyTA p = soundTA p

------------------------------------------------------------------------
-- Roundtrip lemma helpers
------------------------------------------------------------------------

-- maybeBind-just lemma
mb-just : {A B : Set} (a : A) (f : A -> Maybe B) (r : Maybe A) ->
  Eq r (just a) -> Eq (maybeBind r f) (f a)
mb-just a f (just x) refl = refl
mb-just a f nothing  ()

-- maybeMap-just lemma
mm-just : {A B : Set} (g : A -> B) (a : A) (r : Maybe A) ->
  Eq r (just a) -> Eq (maybeMap g r) (just (g a))
mm-just g a (just x) refl = refl
mm-just g a nothing  ()

------------------------------------------------------------------------
-- Decoding roundtrip
------------------------------------------------------------------------

decFormTA-encFormTA : (f : FormTA) -> Eq (decFormTA (encFormTA f)) (just f)

-- fbot: decFormTA (catom n80) = decFormTA-d80 (eqNat n80 n80) n80 (catom n80)
--     = decFormTA-d80 true n80 (catom n80) = just fbotTA
-- This should be refl because eqNat n80 n80 reduces to true.
decFormTA-encFormTA fbotTA = refl

-- fatom: decFormTA (cnode (catom n81) (catom n))
--      = decFormTA-d81 (eqNat n81 n81) n81 (catom n)
--      = decFormTA-d81 true n81 (catom n)
--      = just (fatomTA n)
decFormTA-encFormTA (fatomTA n) = refl

-- fimp: decFormTA (cnode (catom n82) (cnode ea eb))
--     = decFormTA-d81 (eqNat n82 n81) n82 (cnode ea eb)
--     = decFormTA-d81 false n82 (cnode ea eb)     [since n82 /= n81]
--     = decFormTA-d82 (eqNat n82 n82) n82 (cnode ea eb)
--     = decFormTA-d82 true n82 (cnode ea eb)
--     = maybeBind (decFormTA ea) (\ a -> maybeBind (decFormTA eb) (\ b -> just (fimpTA a b)))
-- Need IH on a and b.
decFormTA-encFormTA (fimpTA a b) =
  lem (decFormTA (encFormTA a)) (decFormTA (encFormTA b))
      (decFormTA-encFormTA a) (decFormTA-encFormTA b)
  where
  lem : (r1 : Maybe FormTA) -> (r2 : Maybe FormTA) ->
    Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (fimpTA da db))))
       (just (fimpTA a b))
  lem (just _)  (just _)  refl refl = refl
  lem (just _)  nothing   _    ()
  lem nothing   _         ()

-- fall: decFormTA (cnode (catom n83) ea)
--     = decFormTA-d81 (eqNat n83 n81) n83 ea
--     = decFormTA-d81 false n83 ea
--     = decFormTA-d82 (eqNat n83 n82) n83 ea
--     = decFormTA-d82 false n83 ea    -- but wait, ea is encFormTA a, could be catom or cnode
--     -- Hmm, decFormTA-d82 false t p = decFormTA-d83 (eqNat t n83) t p
--     = decFormTA-d83 (eqNat n83 n83) n83 ea
--     = decFormTA-d83 true n83 ea
--     = maybeMap fallTA (decFormTA ea)
decFormTA-encFormTA (fallTA a) =
  mm-just fallTA a (decFormTA (encFormTA a)) (decFormTA-encFormTA a)

-- feq: decFormTA (cnode (catom n84) (cnode c1 c2))
--    = decFormTA-d81 false n84 (cnode c1 c2)
--    = decFormTA-d82 false n84 (cnode c1 c2)
--    = decFormTA-d83 false n84 (cnode c1 c2)
--    = decFormTA-d84 (eqNat n84 n84) (cnode c1 c2)
--    = decFormTA-d84 true (cnode c1 c2)
--    = just (feqTA c1 c2)
decFormTA-encFormTA (feqTA c1 c2) = refl

------------------------------------------------------------------------
-- Encoding correctness (D1): proofs encode to checkable codes
------------------------------------------------------------------------

-- Proof size (for fuel)
proofSize : {A : FormTA} -> ProofTA A -> Nat
proofSize (axKTA _ _)     = suc zero
proofSize (axSTA _ _ _)   = suc zero
proofSize (mpTA p q)      = suc (natAdd (proofSize p) (proofSize q))
  where
  natAdd : Nat -> Nat -> Nat
  natAdd zero    m = m
  natAdd (suc n) m = suc (natAdd n m)
proofSize (genTA p)       = suc (proofSize p)
proofSize (instTA _ _ p)  = suc (proofSize p)
proofSize (axReflTA _)    = suc zero

-- For the encoding correctness proof, we prove it for axReflTA and axKTA
-- as representative cases.

-- axRefl correctness:
-- checkTA 1 (cnode (catom n95) c)
-- = checkTA-d90 0 (eqNat n95 n90) n95 c
-- = checkTA-d90 0 false n95 c
-- = checkTA-d91 0 (eqNat n95 n91) n95 c
-- = checkTA-d91 0 false n95 c
-- = checkTA-d92 0 (eqNat n95 n92) n95 c
-- = checkTA-d92 0 false n95 c
-- = checkTA-d93 0 (eqNat n95 n93) n95 c
-- = checkTA-d93 0 false n95 c
-- = checkTA-d94 0 (eqNat n95 n94) n95 c
-- = checkTA-d94 0 false n95 c
-- = checkTA-d95 0 (eqNat n95 n95) c
-- = checkTA-d95 0 true c
-- = just (feqTA c c)

n1 : Nat
n1 = suc zero

encodeTA-axRefl : (c : Code) ->
  Eq (checkTA n1 (encProofTA (axReflTA c))) (just (feqTA c c))
encodeTA-axRefl c = refl

-- axK correctness:
-- checkTA 1 (cnode (catom n90) (cnode ea eb))
-- = checkTA-d90 0 (eqNat n90 n90) n90 (cnode ea eb)
-- = checkTA-d90 0 true n90 (cnode ea eb)
-- = maybeBind (decFormTA ea) (\ a -> maybeBind (decFormTA eb) (\ b -> just (fimpTA a (fimpTA b a))))

encodeTA-axK : (A B : FormTA) ->
  Eq (checkTA n1 (encProofTA (axKTA A B))) (just (fimpTA A (fimpTA B A)))
encodeTA-axK a b =
  lem (decFormTA (encFormTA a)) (decFormTA (encFormTA b))
      (decFormTA-encFormTA a) (decFormTA-encFormTA b)
  where
  lem : (r1 : Maybe FormTA) -> (r2 : Maybe FormTA) ->
    Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (fimpTA da (fimpTA db da)))))
       (just (fimpTA a (fimpTA b a)))
  lem (just _) (just _) refl refl = refl
  lem (just _) nothing  _    ()
  lem nothing  _        ()

-- axS correctness:
encodeTA-axS : (A B C : FormTA) ->
  Eq (checkTA n1 (encProofTA (axSTA A B C)))
     (just (fimpTA (fimpTA A (fimpTA B C)) (fimpTA (fimpTA A B) (fimpTA A C))))
encodeTA-axS a b c =
  lem (decFormTA (encFormTA a)) (decFormTA (encFormTA b)) (decFormTA (encFormTA c))
      (decFormTA-encFormTA a) (decFormTA-encFormTA b) (decFormTA-encFormTA c)
  where
  lem : (r1 r2 r3 : Maybe FormTA) ->
    Eq r1 (just a) -> Eq r2 (just b) -> Eq r3 (just c) ->
    Eq (maybeBind r1 (\ da ->
        maybeBind r2 (\ db ->
        maybeBind r3 (\ dc ->
        just (fimpTA (fimpTA da (fimpTA db dc))
                     (fimpTA (fimpTA da db) (fimpTA da dc)))))))
       (just (fimpTA (fimpTA a (fimpTA b c)) (fimpTA (fimpTA a b) (fimpTA a c))))
  lem (just _) (just _) (just _) refl refl refl = refl
  lem (just _) (just _) nothing  _    _    ()
  lem (just _) nothing  _        _    ()
  lem nothing  _        _        ()

------------------------------------------------------------------------
-- Internal provability predicate
------------------------------------------------------------------------

ProvableTA : FormTA -> Set
ProvableTA A = SigmaTA Nat (\ k ->
               SigmaTA Code (\ p -> Eq (checkTA k p) (just A)))

-- Witness: axRefl is provable
axRefl-provableTA : (c : Code) -> ProvableTA (feqTA c c)
axRefl-provableTA c =
  mkSigmaTA n1 (mkSigmaTA (encProofTA (axReflTA c)) (encodeTA-axRefl c))

-- Witness: axK is provable
axK-provableTA : (A B : FormTA) -> ProvableTA (fimpTA A (fimpTA B A))
axK-provableTA a b =
  mkSigmaTA n1 (mkSigmaTA (encProofTA (axKTA a b)) (encodeTA-axK a b))
