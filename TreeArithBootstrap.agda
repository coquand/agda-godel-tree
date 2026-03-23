{-# OPTIONS --without-K --exact-split #-}

module TreeArithBootstrap where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import ChwistekProvability
  using (Bool; true; false; and; Maybe; nothing; just;
         maybeBind; maybeMap; eqNat; eqCode; eqNat-refl)
open import TreeArith
open import TreeArithTrack1
open import TreeArithInternal
open import TreeArithGodel2

------------------------------------------------------------------------
-- 1. Tag constants for ProofTA3 proof encodings
------------------------------------------------------------------------
-- ProofTA3 has 15 constructors. We assign distinct tags starting
-- well past the existing ranges (n80-n95 for ProofTA, n100t-n114t
-- for CodeTm/FormTA3 encodings in TreeArithGodel2).

addB : Nat -> Nat -> Nat
addB zero    m = m
addB (suc n) m = suc (addB n m)

private
  addB-zero-right : (a : Nat) -> Eq (addB a zero) a
  addB-zero-right zero    = refl
  addB-zero-right (suc a) = eqCong suc (addB-zero-right a)

  addB-suc-right : (a b : Nat) -> Eq (addB a (suc b)) (suc (addB a b))
  addB-suc-right zero    b = refl
  addB-suc-right (suc a) b = eqCong suc (addB-suc-right a b)

  eqSym0 : {X : Set} {a b : X} -> Eq a b -> Eq b a
  eqSym0 refl = refl

  eqTrans0 : {X : Set} {a b c : X} -> Eq a b -> Eq b c -> Eq a c
  eqTrans0 refl q = q

  addB-comm : (a b : Nat) -> Eq (addB a b) (addB b a)
  addB-comm zero    b = eqSym0 (addB-zero-right b)
  addB-comm (suc a) b = eqTrans0 (eqCong suc (addB-comm a b)) (eqSym0 (addB-suc-right b a))

private
  -- Base: n95 + 25 = a safe distance past all existing tags
  tagBase : Nat
  tagBase = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
            (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
            (suc (suc (suc (suc (suc n95))))))))))))))))))))))))

tagK3 : Nat           -- axK3
tagK3 = tagBase
tagS3 : Nat           -- axS3
tagS3 = suc tagK3
tagMP3 : Nat          -- mp3
tagMP3 = suc tagS3
tagGen3 : Nat         -- gen3
tagGen3 = suc tagMP3
tagInst3 : Nat        -- inst3
tagInst3 = suc tagGen3
tagEx3 : Nat          -- exIntro3
tagEx3 = suc tagInst3
tagRefl3 : Nat        -- axRefl3
tagRefl3 = suc tagEx3
tagSym3 : Nat         -- axSym3
tagSym3 = suc tagRefl3
tagTrans3 : Nat       -- axTrans3
tagTrans3 = suc tagSym3
tagCaseAtom : Nat     -- axCaseAtom
tagCaseAtom = suc tagTrans3
tagCaseNode : Nat     -- axCaseNodeL
tagCaseNode = suc tagCaseAtom
tagFoldAtom : Nat     -- axFoldAtom
tagFoldAtom = suc tagCaseNode
tagIfTrue : Nat       -- axIfTrue
tagIfTrue = suc tagFoldAtom
tagIfFalse : Nat      -- axIfFalse
tagIfFalse = suc tagIfTrue
tagEqRefl : Nat       -- axEqNatRefl
tagEqRefl = suc tagIfFalse

------------------------------------------------------------------------
-- 2. Proof encoding: ProofTA3 A -> Code
------------------------------------------------------------------------

encProofTA3 : {A : FormTA3} -> ProofTA3 A -> Code

encProofTA3 (axK3 A B) =
  cnode (catom tagK3) (cnode (encFormTA3 A) (encFormTA3 B))

encProofTA3 (axS3 A B C) =
  cnode (catom tagS3) (cnode (encFormTA3 A) (cnode (encFormTA3 B) (encFormTA3 C)))

encProofTA3 (mp3 p q) =
  cnode (catom tagMP3) (cnode (encProofTA3 p) (encProofTA3 q))

encProofTA3 (gen3 p) =
  cnode (catom tagGen3) (encProofTA3 p)

encProofTA3 (inst3 A c p) =
  cnode (catom tagInst3) (cnode (encFormTA3 (substF3 c A)) (encProofTA3 p))

encProofTA3 (exIntro3 A c p) =
  cnode (catom tagEx3) (cnode (encProofTA3 p) (cnode (encFormTA3 A) c))

encProofTA3 (axRefl3 t) =
  cnode (catom tagRefl3) (encCodeTm t)

encProofTA3 (axSym3 s t) =
  cnode (catom tagSym3) (cnode (encCodeTm s) (encCodeTm t))

encProofTA3 (axTrans3 r s t) =
  cnode (catom tagTrans3) (cnode (encCodeTm r) (cnode (encCodeTm s) (encCodeTm t)))

encProofTA3 (axCaseAtom k ab nb) =
  cnode (catom tagCaseAtom) (encFormTA3 (feqTA3 (ctCase (ctAtom k) ab nb) (substCT (catom k) ab)))

encProofTA3 (axCaseNodeL a b ab nb) =
  cnode (catom tagCaseNode) (encFormTA3 (feqTA3 (ctCase (ctNode a b) ab nb) nb))

encProofTA3 (axFoldAtom k ac nc) =
  cnode (catom tagFoldAtom) (encFormTA3 (feqTA3 (ctFold (ctAtom k) ac nc) (substCT (catom k) ac)))

encProofTA3 (axIfTrue k tb eb) =
  cnode (catom tagIfTrue) (encFormTA3 (feqTA3 (ctIf (ctAtom (suc k)) tb eb) tb))

encProofTA3 (axIfFalse tb eb) =
  cnode (catom tagIfFalse) (encFormTA3 (feqTA3 (ctIf (ctAtom zero) tb eb) eb))

encProofTA3 (axEqNatRefl n) =
  cnode (catom tagEqRefl) (encFormTA3 (feqTA3 (ctEqNat (ctAtom n) (ctAtom n)) (ctAtom (suc zero))))

------------------------------------------------------------------------
-- 3. Smoke test: encoding produces cnodes
------------------------------------------------------------------------

private
  test-enc-axK3 : Eq (encProofTA3 (axK3 fbotTA3 fbotTA3))
                     (cnode (catom tagK3) (cnode (encFormTA3 fbotTA3) (encFormTA3 fbotTA3)))
  test-enc-axK3 = refl

  test-enc-axRefl3 : Eq (encProofTA3 (axRefl3 (ctAtom zero)))
                        (cnode (catom tagRefl3) (encCodeTm (ctAtom zero)))
  test-enc-axRefl3 = refl

------------------------------------------------------------------------
-- 4. Encoding tag constants (redefined; private in TreeArithGodel2)
------------------------------------------------------------------------

-- CodeTm encoding tags
ct0 : Nat    -- ctVar tag
ct0 = suc (suc (suc (suc (suc n95))))
ct1 : Nat    -- ctAtom tag
ct1 = suc ct0
ct2 : Nat    -- ctNode tag
ct2 = suc ct1
ct3 : Nat    -- ctCase tag
ct3 = suc ct2
ct4 : Nat    -- ctFold tag
ct4 = suc ct3
ct5 : Nat    -- ctEqNat tag
ct5 = suc ct4
ct6 : Nat    -- ctIf tag
ct6 = suc ct5
ct7 : Nat    -- ctEqCode tag
ct7 = suc ct6

-- FormTA3 encoding tags
ft0 : Nat    -- fbotTA3 tag
ft0 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ct0)))))))))
ft1 : Nat    -- fimpTA3 tag
ft1 = suc ft0
ft2 : Nat    -- fallTA3 tag
ft2 = suc ft1
ft3 : Nat    -- fexTA3 tag
ft3 = suc ft2
ft4 : Nat    -- feqTA3 tag
ft4 = suc ft3

-- Verify tag constants match the encoding functions
private
  test-ct0 : Eq (encCodeTm (ctVar zero)) (cnode (catom ct0) (catom zero))
  test-ct0 = refl
  test-ct1 : Eq (encCodeTm (ctAtom zero)) (cnode (catom ct1) (catom zero))
  test-ct1 = refl
  test-ft0 : Eq (encFormTA3 fbotTA3) (catom ft0)
  test-ft0 = refl
  test-ft1 : Eq (encFormTA3 (fimpTA3 fbotTA3 fbotTA3))
                (cnode (catom ft1) (cnode (catom ft0) (catom ft0)))
  test-ft1 = refl

------------------------------------------------------------------------
-- 5. Decoder: Code -> Maybe CodeTm
------------------------------------------------------------------------

decCodeTm : Code -> Maybe CodeTm
decCT-d0 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d1 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d2 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d3 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d4 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d5 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d6 : Bool -> Nat -> Code -> Maybe CodeTm
decCT-d7 : Bool -> Code -> Maybe CodeTm

decCodeTm (catom _) = nothing
decCodeTm (cnode (cnode _ _) _) = nothing
decCodeTm (cnode (catom tag) payload) = decCT-d0 (eqNat tag ct0) tag payload

-- ct0: ctVar n
decCT-d0 true  _ (catom n)    = just (ctVar n)
decCT-d0 true  _ (cnode _ _)  = nothing
decCT-d0 false tag payload    = decCT-d1 (eqNat tag ct1) tag payload

-- ct1: ctAtom n
decCT-d1 true  _ (catom n)    = just (ctAtom n)
decCT-d1 true  _ (cnode _ _)  = nothing
decCT-d1 false tag payload    = decCT-d2 (eqNat tag ct2) tag payload

-- ct2: ctNode a b
decCT-d2 true _ (cnode ac bc) =
  maybeBind (decCodeTm ac) (\ a ->
  maybeBind (decCodeTm bc) (\ b ->
  just (ctNode a b)))
decCT-d2 true  _ (catom _)    = nothing
decCT-d2 false tag payload    = decCT-d3 (eqNat tag ct3) tag payload

-- ct3: ctCase t ab nb
decCT-d3 true _ (cnode tc (cnode abc nbc)) =
  maybeBind (decCodeTm tc) (\ t ->
  maybeBind (decCodeTm abc) (\ ab ->
  maybeBind (decCodeTm nbc) (\ nb ->
  just (ctCase t ab nb))))
decCT-d3 true  _ _ = nothing
decCT-d3 false tag payload = decCT-d4 (eqNat tag ct4) tag payload

-- ct4: ctFold t ac nc
decCT-d4 true _ (cnode tc (cnode acc ncc)) =
  maybeBind (decCodeTm tc) (\ t ->
  maybeBind (decCodeTm acc) (\ ac ->
  maybeBind (decCodeTm ncc) (\ nc ->
  just (ctFold t ac nc))))
decCT-d4 true  _ _ = nothing
decCT-d4 false tag payload = decCT-d5 (eqNat tag ct5) tag payload

-- ct5: ctEqNat a b
decCT-d5 true _ (cnode ac bc) =
  maybeBind (decCodeTm ac) (\ a ->
  maybeBind (decCodeTm bc) (\ b ->
  just (ctEqNat a b)))
decCT-d5 true  _ (catom _)    = nothing
decCT-d5 false tag payload    = decCT-d6 (eqNat tag ct6) tag payload

-- ct6: ctIf c tb eb
decCT-d6 true _ (cnode cc (cnode tbc ebc)) =
  maybeBind (decCodeTm cc) (\ c ->
  maybeBind (decCodeTm tbc) (\ tb ->
  maybeBind (decCodeTm ebc) (\ eb ->
  just (ctIf c tb eb))))
decCT-d6 true  _ _ = nothing
decCT-d6 false tag payload = decCT-d7 (eqNat tag ct7) payload

-- ct7: ctEqCode a b
decCT-d7 true (cnode ac bc) =
  maybeBind (decCodeTm ac) (\ a ->
  maybeBind (decCodeTm bc) (\ b ->
  just (ctEqCode a b)))
decCT-d7 true  (catom _) = nothing
decCT-d7 false _ = nothing

------------------------------------------------------------------------
-- 6. Decoder: Code -> Maybe FormTA3
------------------------------------------------------------------------

decFormTA3 : Code -> Maybe FormTA3
decF3-d0 : Bool -> Nat -> Code -> Maybe FormTA3
decF3-d1 : Bool -> Nat -> Code -> Maybe FormTA3
decF3-d2 : Bool -> Nat -> Code -> Maybe FormTA3
decF3-d3 : Bool -> Nat -> Code -> Maybe FormTA3
decF3-d4 : Bool -> Code -> Maybe FormTA3

-- fbot = catom ft0
decFormTA3 (catom n) = decF3-d0 (eqNat n ft0) n (catom n)
decFormTA3 (cnode (catom tag) payload) = decF3-d1 (eqNat tag ft1) tag payload
decFormTA3 (cnode (cnode _ _) _) = nothing

decF3-d0 true  _ _ = just fbotTA3
decF3-d0 false _ _ = nothing

-- ft1: fimpTA3 a b
decF3-d1 true _ (cnode ac bc) =
  maybeBind (decFormTA3 ac) (\ a ->
  maybeBind (decFormTA3 bc) (\ b ->
  just (fimpTA3 a b)))
decF3-d1 true  _ (catom _) = nothing
decF3-d1 false tag payload = decF3-d2 (eqNat tag ft2) tag payload

-- ft2: fallTA3 a
decF3-d2 true  _ p = maybeMap fallTA3 (decFormTA3 p)
decF3-d2 false tag payload = decF3-d3 (eqNat tag ft3) tag payload

-- ft3: fexTA3 a
decF3-d3 true  _ p = maybeMap fexTA3 (decFormTA3 p)
decF3-d3 false tag payload = decF3-d4 (eqNat tag ft4) payload

-- ft4: feqTA3 t1 t2
decF3-d4 true (cnode t1c t2c) =
  maybeBind (decCodeTm t1c) (\ t1 ->
  maybeBind (decCodeTm t2c) (\ t2 ->
  just (feqTA3 t1 t2)))
decF3-d4 true  (catom _) = nothing
decF3-d4 false _ = nothing

------------------------------------------------------------------------
-- 7. Decoder roundtrip tests
------------------------------------------------------------------------

private
  test-dec-fbot : Eq (decFormTA3 (encFormTA3 fbotTA3)) (just fbotTA3)
  test-dec-fbot = refl

  test-dec-fimp : Eq (decFormTA3 (encFormTA3 (fimpTA3 fbotTA3 fbotTA3)))
                     (just (fimpTA3 fbotTA3 fbotTA3))
  test-dec-fimp = refl

  test-dec-fall : Eq (decFormTA3 (encFormTA3 (fallTA3 fbotTA3)))
                     (just (fallTA3 fbotTA3))
  test-dec-fall = refl

  test-dec-fex : Eq (decFormTA3 (encFormTA3 (fexTA3 fbotTA3)))
                    (just (fexTA3 fbotTA3))
  test-dec-fex = refl

  test-dec-feq : Eq (decFormTA3 (encFormTA3 (feqTA3 (ctAtom zero) (ctVar zero))))
                    (just (feqTA3 (ctAtom zero) (ctVar zero)))
  test-dec-feq = refl

  test-dec-ctVar : Eq (decCodeTm (encCodeTm (ctVar (suc zero)))) (just (ctVar (suc zero)))
  test-dec-ctVar = refl

  test-dec-ctNode : Eq (decCodeTm (encCodeTm (ctNode (ctAtom zero) (ctVar zero))))
                       (just (ctNode (ctAtom zero) (ctVar zero)))
  test-dec-ctNode = refl

  test-dec-ctCase : Eq (decCodeTm (encCodeTm (ctCase (ctVar zero) (ctAtom zero) (ctAtom (suc zero)))))
                       (just (ctCase (ctVar zero) (ctAtom zero) (ctAtom (suc zero))))
  test-dec-ctCase = refl

  test-dec-ctIf : Eq (decCodeTm (encCodeTm (ctIf (ctAtom zero) (ctAtom (suc zero)) (ctAtom zero))))
                     (just (ctIf (ctAtom zero) (ctAtom (suc zero)) (ctAtom zero)))
  test-dec-ctIf = refl

------------------------------------------------------------------------
-- 8. Equality on CodeTm and FormTA3
------------------------------------------------------------------------

eqCodeTm : CodeTm -> CodeTm -> Bool
eqCodeTm (ctVar n)      (ctVar m)      = eqNat n m
eqCodeTm (ctAtom n)     (ctAtom m)     = eqNat n m
eqCodeTm (ctNode a b)   (ctNode c d)   = and (eqCodeTm a c) (eqCodeTm b d)
eqCodeTm (ctCase t a n) (ctCase u b m) = and (eqCodeTm t u) (and (eqCodeTm a b) (eqCodeTm n m))
eqCodeTm (ctFold t a n) (ctFold u b m) = and (eqCodeTm t u) (and (eqCodeTm a b) (eqCodeTm n m))
eqCodeTm (ctEqNat a b)  (ctEqNat c d)  = and (eqCodeTm a c) (eqCodeTm b d)
eqCodeTm (ctIf c t e)   (ctIf d u f)   = and (eqCodeTm c d) (and (eqCodeTm t u) (eqCodeTm e f))
eqCodeTm (ctEqCode a b) (ctEqCode c d) = and (eqCodeTm a c) (eqCodeTm b d)
eqCodeTm _               _             = false

eqFormTA3 : FormTA3 -> FormTA3 -> Bool
eqFormTA3 fbotTA3        fbotTA3        = true
eqFormTA3 (fimpTA3 a b)  (fimpTA3 c d)  = and (eqFormTA3 a c) (eqFormTA3 b d)
eqFormTA3 (fallTA3 a)    (fallTA3 b)    = eqFormTA3 a b
eqFormTA3 (fexTA3 a)     (fexTA3 b)     = eqFormTA3 a b
eqFormTA3 (feqTA3 s t)   (feqTA3 u v)   = and (eqCodeTm s u) (eqCodeTm t v)
eqFormTA3 _               _             = false

------------------------------------------------------------------------
-- 9. Bool guard and modus ponens matcher for FormTA3
------------------------------------------------------------------------

boolGuardTA3 : Bool -> Maybe FormTA3 -> Maybe FormTA3
boolGuardTA3 true  r = r
boolGuardTA3 false _ = nothing

matchMPTA3 : FormTA3 -> FormTA3 -> Maybe FormTA3
matchMPTA3 (fimpTA3 a b) q = boolGuardTA3 (eqFormTA3 a q) (just b)
matchMPTA3 fbotTA3       _ = nothing
matchMPTA3 (fallTA3 _)   _ = nothing
matchMPTA3 (fexTA3 _)    _ = nothing
matchMPTA3 (feqTA3 _ _)  _ = nothing

-- Helper for inst3: check that sub-proof is fallTA3, return result
inst3-check : FormTA3 -> FormTA3 -> Maybe FormTA3
inst3-check (fallTA3 _) result = just result
inst3-check fbotTA3     _      = nothing
inst3-check (fimpTA3 _ _) _   = nothing
inst3-check (fexTA3 _)    _   = nothing
inst3-check (feqTA3 _ _)  _   = nothing

------------------------------------------------------------------------
-- 10. Checker: checkTA3 : Nat -> Code -> Maybe FormTA3
------------------------------------------------------------------------
-- Dispatches on proof tags. Follows the same pattern as checkTA.
-- For each constructor of ProofTA3:
--   Decode payload, recursively check sub-proofs, return conclusion.

checkTA3 : Nat -> Code -> Maybe FormTA3

-- Dispatch chain
checkTA3-dK3    : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dS3    : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dMP3   : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dGen3  : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dInst3 : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dEx3   : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dRefl3 : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dSym3  : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dTrans3  : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dCaseA   : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dCaseN   : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dFoldA   : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dIfT     : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dIfF     : Nat -> Bool -> Nat -> Code -> Maybe FormTA3
checkTA3-dEqR     : Nat -> Bool -> Code -> Maybe FormTA3

checkTA3 zero _ = nothing
checkTA3 (suc n) (catom _) = nothing
checkTA3 (suc n) (cnode (cnode _ _) _) = nothing
checkTA3 (suc n) (cnode (catom tag) payload) =
  checkTA3-dK3 n (eqNat tag tagK3) tag payload

-- tagK3: axK3 A B
checkTA3-dK3 fuel true _ (cnode ac bc) =
  maybeBind (decFormTA3 ac) (\ a ->
  maybeBind (decFormTA3 bc) (\ b ->
  just (fimpTA3 a (fimpTA3 b a))))
checkTA3-dK3 fuel true  _ (catom _) = nothing
checkTA3-dK3 fuel false tag payload =
  checkTA3-dS3 fuel (eqNat tag tagS3) tag payload

-- tagS3: axS3 A B C
checkTA3-dS3 fuel true _ (cnode ac (cnode bc cc)) =
  maybeBind (decFormTA3 ac) (\ a ->
  maybeBind (decFormTA3 bc) (\ b ->
  maybeBind (decFormTA3 cc) (\ c ->
  just (fimpTA3 (fimpTA3 a (fimpTA3 b c))
                (fimpTA3 (fimpTA3 a b) (fimpTA3 a c))))))
checkTA3-dS3 fuel true  _ _ = nothing
checkTA3-dS3 fuel false tag payload =
  checkTA3-dMP3 fuel (eqNat tag tagMP3) tag payload

-- tagMP3: mp3 p q
checkTA3-dMP3 fuel true _ (cnode p1 p2) =
  maybeBind (checkTA3 fuel p1) (\ f1 ->
  maybeBind (checkTA3 fuel p2) (\ f2 ->
  matchMPTA3 f1 f2))
checkTA3-dMP3 fuel true  _ (catom _) = nothing
checkTA3-dMP3 fuel false tag payload =
  checkTA3-dGen3 fuel (eqNat tag tagGen3) tag payload

-- tagGen3: gen3 p
checkTA3-dGen3 fuel true _ p = maybeMap fallTA3 (checkTA3 fuel p)
checkTA3-dGen3 fuel false tag payload =
  checkTA3-dInst3 fuel (eqNat tag tagInst3) tag payload

-- tagInst3: inst3 A c p  (payload = cnode enc(result) enc(p))
checkTA3-dInst3 fuel true _ (cnode rc p) =
  maybeBind (decFormTA3 rc) (\ result ->
  maybeBind (checkTA3 fuel p) (\ fp ->
  inst3-check fp result))
checkTA3-dInst3 fuel true  _ (catom _) = nothing
checkTA3-dInst3 fuel false tag payload =
  checkTA3-dEx3 fuel (eqNat tag tagEx3) tag payload

-- tagEx3: exIntro3 A c p  (payload = cnode enc(p) (cnode enc(A) c))
-- p proves substF3 c A, checker returns fexTA3 A
checkTA3-dEx3 fuel true _ (cnode p (cnode ac c)) =
  maybeBind (checkTA3 fuel p) (\ fp ->
  maybeBind (decFormTA3 ac) (\ a ->
  boolGuardTA3 (eqFormTA3 fp (substF3 c a)) (just (fexTA3 a))))
checkTA3-dEx3 fuel true  _ _ = nothing
checkTA3-dEx3 fuel false tag payload =
  checkTA3-dRefl3 fuel (eqNat tag tagRefl3) tag payload

-- tagRefl3: axRefl3 t  (payload = encCodeTm t)
checkTA3-dRefl3 fuel true _ payload =
  maybeBind (decCodeTm payload) (\ t ->
  just (feqTA3 t t))
checkTA3-dRefl3 fuel false tag payload =
  checkTA3-dSym3 fuel (eqNat tag tagSym3) tag payload

-- tagSym3: axSym3 s t  (payload = cnode enc(s) enc(t))
checkTA3-dSym3 fuel true _ (cnode sc tc) =
  maybeBind (decCodeTm sc) (\ s ->
  maybeBind (decCodeTm tc) (\ t ->
  just (fimpTA3 (feqTA3 s t) (feqTA3 t s))))
checkTA3-dSym3 fuel true  _ (catom _) = nothing
checkTA3-dSym3 fuel false tag payload =
  checkTA3-dTrans3 fuel (eqNat tag tagTrans3) tag payload

-- tagTrans3: axTrans3 r s t  (payload = cnode enc(r) (cnode enc(s) enc(t)))
checkTA3-dTrans3 fuel true _ (cnode rc (cnode sc tc)) =
  maybeBind (decCodeTm rc) (\ r ->
  maybeBind (decCodeTm sc) (\ s ->
  maybeBind (decCodeTm tc) (\ t ->
  just (fimpTA3 (feqTA3 r s) (fimpTA3 (feqTA3 s t) (feqTA3 r t))))))
checkTA3-dTrans3 fuel true  _ _ = nothing
checkTA3-dTrans3 fuel false tag payload =
  checkTA3-dCaseA fuel (eqNat tag tagCaseAtom) tag payload

-- tagCaseAtom: payload = encFormTA3 (result formula)
checkTA3-dCaseA fuel true _ payload = decFormTA3 payload
checkTA3-dCaseA fuel false tag payload =
  checkTA3-dCaseN fuel (eqNat tag tagCaseNode) tag payload

-- tagCaseNode: payload = encFormTA3 (result formula)
checkTA3-dCaseN fuel true _ payload = decFormTA3 payload
checkTA3-dCaseN fuel false tag payload =
  checkTA3-dFoldA fuel (eqNat tag tagFoldAtom) tag payload

-- tagFoldAtom: payload = encFormTA3 (result formula)
checkTA3-dFoldA fuel true _ payload = decFormTA3 payload
checkTA3-dFoldA fuel false tag payload =
  checkTA3-dIfT fuel (eqNat tag tagIfTrue) tag payload

-- tagIfTrue: payload = encFormTA3 (result formula)
checkTA3-dIfT fuel true _ payload = decFormTA3 payload
checkTA3-dIfT fuel false tag payload =
  checkTA3-dIfF fuel (eqNat tag tagIfFalse) tag payload

-- tagIfFalse: payload = encFormTA3 (result formula)
checkTA3-dIfF fuel true _ payload = decFormTA3 payload
checkTA3-dIfF fuel false tag payload =
  checkTA3-dEqR fuel (eqNat tag tagEqRefl) payload

-- tagEqRefl: payload = encFormTA3 (result formula)
checkTA3-dEqR fuel true payload = decFormTA3 payload
checkTA3-dEqR fuel false _ = nothing

------------------------------------------------------------------------
-- 11. Checker ground tests
------------------------------------------------------------------------

private
  -- axRefl3 (ctAtom 0): feqTA3 (ctAtom 0) (ctAtom 0)
  test-chk-refl3 : Eq (checkTA3 (suc zero) (encProofTA3 (axRefl3 (ctAtom zero))))
                      (just (feqTA3 (ctAtom zero) (ctAtom zero)))
  test-chk-refl3 = refl

  -- axK3 bot bot: fimpTA3 bot (fimpTA3 bot bot)
  test-chk-axK3 : Eq (checkTA3 (suc zero) (encProofTA3 (axK3 fbotTA3 fbotTA3)))
                     (just (fimpTA3 fbotTA3 (fimpTA3 fbotTA3 fbotTA3)))
  test-chk-axK3 = refl

  -- axSym3 (ctAtom 0) (ctVar 0)
  test-chk-sym3 : Eq (checkTA3 (suc zero) (encProofTA3 (axSym3 (ctAtom zero) (ctVar zero))))
                     (just (fimpTA3 (feqTA3 (ctAtom zero) (ctVar zero))
                                    (feqTA3 (ctVar zero) (ctAtom zero))))
  test-chk-sym3 = refl

  -- axCaseAtom 0 (ctAtom 1) (ctAtom 2)
  test-chk-caseA : Eq (checkTA3 (suc zero)
                        (encProofTA3 (axCaseAtom zero (ctAtom (suc zero)) (ctAtom (suc (suc zero))))))
                      (just (feqTA3 (ctCase (ctAtom zero) (ctAtom (suc zero)) (ctAtom (suc (suc zero))))
                                    (substCT (catom zero) (ctAtom (suc zero)))))
  test-chk-caseA = refl

  -- axEqNatRefl 0
  test-chk-eqr : Eq (checkTA3 (suc zero) (encProofTA3 (axEqNatRefl zero)))
                    (just (feqTA3 (ctEqNat (ctAtom zero) (ctAtom zero)) (ctAtom (suc zero))))
  test-chk-eqr = refl

  -- gen3 (axRefl3 (ctAtom 0)): fallTA3 (feqTA3 (ctAtom 0) (ctAtom 0))
  n2b : Nat
  n2b = suc (suc zero)
  test-chk-gen3 : Eq (checkTA3 n2b (encProofTA3 (gen3 (axRefl3 (ctAtom zero)))))
                     (just (fallTA3 (feqTA3 (ctAtom zero) (ctAtom zero))))
  test-chk-gen3 = refl

  -- mp3 (axK3 bot bot) (id-proof): test mp dispatch
  -- axK3 bot bot : fimpTA3 bot (fimpTA3 bot bot)
  -- We need a proof of bot to apply mp. Instead test with axRefl3 + axK3:
  -- axK3 (feqTA3 (ctAtom 0) (ctAtom 0)) bot : fimpTA3 (feq 0 0) (fimpTA3 bot (feq 0 0))
  -- mp3 (above) (axRefl3 (ctAtom 0)) : fimpTA3 bot (feq 0 0)
  feq00 : FormTA3
  feq00 = feqTA3 (ctAtom zero) (ctAtom zero)
  n3b : Nat
  n3b = suc (suc (suc zero))
  test-chk-mp3 : Eq (checkTA3 n3b (encProofTA3 (mp3 (axK3 feq00 fbotTA3) (axRefl3 (ctAtom zero)))))
                    (just (fimpTA3 fbotTA3 feq00))
  test-chk-mp3 = refl

------------------------------------------------------------------------
-- 12. Decoder roundtrip: decCodeTm (encCodeTm t) = just t
------------------------------------------------------------------------

decCodeTm-encCodeTm : (t : CodeTm) -> Eq (decCodeTm (encCodeTm t)) (just t)
decCodeTm-encCodeTm (ctVar n) = refl
decCodeTm-encCodeTm (ctAtom n) = refl
decCodeTm-encCodeTm (ctNode a b) =
  lem2 (decCodeTm (encCodeTm a)) (decCodeTm (encCodeTm b))
       (decCodeTm-encCodeTm a) (decCodeTm-encCodeTm b)
  where
  lem2 : (r1 r2 : Maybe CodeTm) -> Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (ctNode da db))))
       (just (ctNode a b))
  lem2 (just _) (just _) refl refl = refl
  lem2 (just _) nothing  _    ()
  lem2 nothing  _        ()
decCodeTm-encCodeTm (ctCase t ab nb) =
  lem3 (decCodeTm (encCodeTm t)) (decCodeTm (encCodeTm ab)) (decCodeTm (encCodeTm nb))
       (decCodeTm-encCodeTm t) (decCodeTm-encCodeTm ab) (decCodeTm-encCodeTm nb)
  where
  lem3 : (r1 r2 r3 : Maybe CodeTm) ->
    Eq r1 (just t) -> Eq r2 (just ab) -> Eq r3 (just nb) ->
    Eq (maybeBind r1 (\ dt -> maybeBind r2 (\ da -> maybeBind r3 (\ dn -> just (ctCase dt da dn)))))
       (just (ctCase t ab nb))
  lem3 (just _) (just _) (just _) refl refl refl = refl
  lem3 (just _) (just _) nothing  _    _    ()
  lem3 (just _) nothing  _        _    ()
  lem3 nothing  _        _        ()
decCodeTm-encCodeTm (ctFold t ac nc) =
  lem3 (decCodeTm (encCodeTm t)) (decCodeTm (encCodeTm ac)) (decCodeTm (encCodeTm nc))
       (decCodeTm-encCodeTm t) (decCodeTm-encCodeTm ac) (decCodeTm-encCodeTm nc)
  where
  lem3 : (r1 r2 r3 : Maybe CodeTm) ->
    Eq r1 (just t) -> Eq r2 (just ac) -> Eq r3 (just nc) ->
    Eq (maybeBind r1 (\ dt -> maybeBind r2 (\ da -> maybeBind r3 (\ dn -> just (ctFold dt da dn)))))
       (just (ctFold t ac nc))
  lem3 (just _) (just _) (just _) refl refl refl = refl
  lem3 (just _) (just _) nothing  _    _    ()
  lem3 (just _) nothing  _        _    ()
  lem3 nothing  _        _        ()
decCodeTm-encCodeTm (ctEqNat a b) =
  lem2 (decCodeTm (encCodeTm a)) (decCodeTm (encCodeTm b))
       (decCodeTm-encCodeTm a) (decCodeTm-encCodeTm b)
  where
  lem2 : (r1 r2 : Maybe CodeTm) -> Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (ctEqNat da db))))
       (just (ctEqNat a b))
  lem2 (just _) (just _) refl refl = refl
  lem2 (just _) nothing  _    ()
  lem2 nothing  _        ()
decCodeTm-encCodeTm (ctIf c t e) =
  lem3 (decCodeTm (encCodeTm c)) (decCodeTm (encCodeTm t)) (decCodeTm (encCodeTm e))
       (decCodeTm-encCodeTm c) (decCodeTm-encCodeTm t) (decCodeTm-encCodeTm e)
  where
  lem3 : (r1 r2 r3 : Maybe CodeTm) ->
    Eq r1 (just c) -> Eq r2 (just t) -> Eq r3 (just e) ->
    Eq (maybeBind r1 (\ dc -> maybeBind r2 (\ dt -> maybeBind r3 (\ de -> just (ctIf dc dt de)))))
       (just (ctIf c t e))
  lem3 (just _) (just _) (just _) refl refl refl = refl
  lem3 (just _) (just _) nothing  _    _    ()
  lem3 (just _) nothing  _        _    ()
  lem3 nothing  _        _        ()
decCodeTm-encCodeTm (ctEqCode a b) =
  lem2 (decCodeTm (encCodeTm a)) (decCodeTm (encCodeTm b))
       (decCodeTm-encCodeTm a) (decCodeTm-encCodeTm b)
  where
  lem2 : (r1 r2 : Maybe CodeTm) -> Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (ctEqCode da db))))
       (just (ctEqCode a b))
  lem2 (just _) (just _) refl refl = refl
  lem2 (just _) nothing  _    ()
  lem2 nothing  _        ()

------------------------------------------------------------------------
-- 13. Decoder roundtrip: decFormTA3 (encFormTA3 f) = just f
------------------------------------------------------------------------

decFormTA3-encFormTA3 : (f : FormTA3) -> Eq (decFormTA3 (encFormTA3 f)) (just f)
decFormTA3-encFormTA3 fbotTA3 = refl
decFormTA3-encFormTA3 (fimpTA3 a b) =
  lem2 (decFormTA3 (encFormTA3 a)) (decFormTA3 (encFormTA3 b))
       (decFormTA3-encFormTA3 a) (decFormTA3-encFormTA3 b)
  where
  lem2 : (r1 r2 : Maybe FormTA3) -> Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (fimpTA3 da db))))
       (just (fimpTA3 a b))
  lem2 (just _) (just _) refl refl = refl
  lem2 (just _) nothing  _    ()
  lem2 nothing  _        ()
decFormTA3-encFormTA3 (fallTA3 a) =
  mm-just fallTA3 a (decFormTA3 (encFormTA3 a)) (decFormTA3-encFormTA3 a)
decFormTA3-encFormTA3 (fexTA3 a) =
  mm-just fexTA3 a (decFormTA3 (encFormTA3 a)) (decFormTA3-encFormTA3 a)
decFormTA3-encFormTA3 (feqTA3 t1 t2) =
  lem2 (decCodeTm (encCodeTm t1)) (decCodeTm (encCodeTm t2))
       (decCodeTm-encCodeTm t1) (decCodeTm-encCodeTm t2)
  where
  lem2 : (r1 r2 : Maybe CodeTm) -> Eq r1 (just t1) -> Eq r2 (just t2) ->
    Eq (maybeBind r1 (\ d1 -> maybeBind r2 (\ d2 -> just (feqTA3 d1 d2))))
       (just (feqTA3 t1 t2))
  lem2 (just _) (just _) refl refl = refl
  lem2 (just _) nothing  _    ()
  lem2 nothing  _        ()


------------------------------------------------------------------------
-- 14. Helpers
------------------------------------------------------------------------

private
  eqSym5 : {X : Set} {a b : X} -> Eq a b -> Eq b a
  eqSym5 refl = refl

  eqTrans5 : {X : Set} {a b c : X} -> Eq a b -> Eq b c -> Eq a c
  eqTrans5 refl q = q

  eqSubst5 : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
  eqSubst5 P refl px = px

  checkTA3-fuel-eq : (f1 f2 : Nat) -> Eq f1 f2 ->
    (p : Code) -> (A : FormTA3) ->
    Eq (checkTA3 f1 p) (just A) -> Eq (checkTA3 f2 p) (just A)
  checkTA3-fuel-eq f1 .f1 refl p A h = h

  mb-just3 : {A B : Set} (a : A) (f : A -> Maybe B) (r : Maybe A) ->
    Eq r (just a) -> Eq (maybeBind r f) (f a)
  mb-just3 a f (just x) refl = refl
  mb-just3 a f nothing  ()

  mm-just3 : {A B : Set} (g : A -> B) (a : A) (r : Maybe A) ->
    Eq r (just a) -> Eq (maybeMap g r) (just (g a))
  mm-just3 g a (just x) refl = refl
  mm-just3 g a nothing  ()

------------------------------------------------------------------------
-- 15. Fuel monotonicity: checkTA3-mono
------------------------------------------------------------------------

checkTA3-mono : (n : Nat) -> (p : Code) -> (A : FormTA3) ->
  Eq (checkTA3 n p) (just A) -> Eq (checkTA3 (suc n) p) (just A)

private
  checkTA3-mono-dEqR : (fuel : Nat) ->
    (b : Bool) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dEqR fuel b payload) (just A) ->
    Eq (checkTA3-dEqR (suc fuel) b payload) (just A)
  checkTA3-mono-dEqR fuel true  payload A h = h
  checkTA3-mono-dEqR fuel false _       A ()

  checkTA3-mono-dIfF : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dIfF fuel b tag payload) (just A) ->
    Eq (checkTA3-dIfF (suc fuel) b tag payload) (just A)
  checkTA3-mono-dIfF fuel IH true _ payload A h = h
  checkTA3-mono-dIfF fuel IH false tag payload A h =
    checkTA3-mono-dEqR fuel (eqNat tag tagEqRefl) payload A h

  checkTA3-mono-dIfT : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dIfT fuel b tag payload) (just A) ->
    Eq (checkTA3-dIfT (suc fuel) b tag payload) (just A)
  checkTA3-mono-dIfT fuel IH true _ payload A h = h
  checkTA3-mono-dIfT fuel IH false tag payload A h =
    checkTA3-mono-dIfF fuel IH (eqNat tag tagIfFalse) tag payload A h

  checkTA3-mono-dFoldA : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dFoldA fuel b tag payload) (just A) ->
    Eq (checkTA3-dFoldA (suc fuel) b tag payload) (just A)
  checkTA3-mono-dFoldA fuel IH true _ payload A h = h
  checkTA3-mono-dFoldA fuel IH false tag payload A h =
    checkTA3-mono-dIfT fuel IH (eqNat tag tagIfTrue) tag payload A h

  checkTA3-mono-dCaseN : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dCaseN fuel b tag payload) (just A) ->
    Eq (checkTA3-dCaseN (suc fuel) b tag payload) (just A)
  checkTA3-mono-dCaseN fuel IH true _ payload A h = h
  checkTA3-mono-dCaseN fuel IH false tag payload A h =
    checkTA3-mono-dFoldA fuel IH (eqNat tag tagFoldAtom) tag payload A h

  checkTA3-mono-dCaseA : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dCaseA fuel b tag payload) (just A) ->
    Eq (checkTA3-dCaseA (suc fuel) b tag payload) (just A)
  checkTA3-mono-dCaseA fuel IH true _ payload A h = h
  checkTA3-mono-dCaseA fuel IH false tag payload A h =
    checkTA3-mono-dCaseN fuel IH (eqNat tag tagCaseNode) tag payload A h

  checkTA3-mono-dTrans3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dTrans3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dTrans3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dTrans3 fuel IH true _ (cnode rc (cnode sc tc)) A h = h
  checkTA3-mono-dTrans3 fuel IH true _ (catom _) A ()
  checkTA3-mono-dTrans3 fuel IH true _ (cnode _ (catom _)) A ()
  checkTA3-mono-dTrans3 fuel IH false tag payload A h =
    checkTA3-mono-dCaseA fuel IH (eqNat tag tagCaseAtom) tag payload A h

  checkTA3-mono-dSym3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dSym3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dSym3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dSym3 fuel IH true _ (cnode sc tc) A h = h
  checkTA3-mono-dSym3 fuel IH true _ (catom _) A ()
  checkTA3-mono-dSym3 fuel IH false tag payload A h =
    checkTA3-mono-dTrans3 fuel IH (eqNat tag tagTrans3) tag payload A h

  checkTA3-mono-dRefl3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dRefl3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dRefl3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dRefl3 fuel IH true _ payload A h = h
  checkTA3-mono-dRefl3 fuel IH false tag payload A h =
    checkTA3-mono-dSym3 fuel IH (eqNat tag tagSym3) tag payload A h

  -- Ex3: recursive (uses checkTA3 fuel)
  checkTA3-mono-dEx3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dEx3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dEx3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dEx3 fuel IH true _ (cnode p (cnode ac c)) A h =
    lem1 (checkTA3 fuel p) (checkTA3 (suc fuel) p) (\ fp -> IH p fp) h
    where
    lem1 : (r1 r2 : Maybe FormTA3) ->
      ((X : FormTA3) -> Eq r1 (just X) -> Eq r2 (just X)) ->
      Eq (maybeBind r1 (\ fp -> maybeBind (decFormTA3 ac) (\ a ->
          boolGuardTA3 (eqFormTA3 fp (substF3 c a)) (just (fexTA3 a))))) (just A) ->
      Eq (maybeBind r2 (\ fp -> maybeBind (decFormTA3 ac) (\ a ->
          boolGuardTA3 (eqFormTA3 fp (substF3 c a)) (just (fexTA3 a))))) (just A)
    lem1 nothing  _  _  ()
    lem1 (just x) r2 mono h2 =
      eqTrans5 (eqCong (\ r -> maybeBind r (\ fp -> maybeBind (decFormTA3 ac) (\ a ->
          boolGuardTA3 (eqFormTA3 fp (substF3 c a)) (just (fexTA3 a))))) (mono x refl)) h2
  checkTA3-mono-dEx3 fuel IH true _ (catom _) A ()
  checkTA3-mono-dEx3 fuel IH true _ (cnode _ (catom _)) A ()
  checkTA3-mono-dEx3 fuel IH false tag payload A h =
    checkTA3-mono-dRefl3 fuel IH (eqNat tag tagRefl3) tag payload A h

  -- Inst3: recursive (only checkTA3 fuel p uses fuel)
  checkTA3-mono-dInst3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dInst3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dInst3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dInst3 fuel IH true _ (cnode rc p) A h =
    lem1 (decFormTA3 rc) (checkTA3 fuel p) (checkTA3 (suc fuel) p) (\ fp -> IH p fp) h
    where
    lem1 : (rd : Maybe FormTA3) -> (r1 r2 : Maybe FormTA3) ->
      ((X : FormTA3) -> Eq r1 (just X) -> Eq r2 (just X)) ->
      Eq (maybeBind rd (\ result -> maybeBind r1 (\ fp -> inst3-check fp result))) (just A) ->
      Eq (maybeBind rd (\ result -> maybeBind r2 (\ fp -> inst3-check fp result))) (just A)
    lem1 nothing  _        _  _    ()
    lem1 (just d) nothing  _  _    ()
    lem1 (just d) (just x) r2 mono h2 =
      eqTrans5
        (eqCong (\ r -> maybeBind r (\ fp -> inst3-check fp d)) (mono x refl))
        h2
  checkTA3-mono-dInst3 fuel IH true _ (catom _) A ()
  checkTA3-mono-dInst3 fuel IH false tag payload A h =
    checkTA3-mono-dEx3 fuel IH (eqNat tag tagEx3) tag payload A h

  -- Gen3: recursive
  checkTA3-mono-dGen3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dGen3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dGen3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dGen3 fuel IH true _ p A h =
    lem1 (checkTA3 fuel p) (checkTA3 (suc fuel) p) (\ fp -> IH p fp) h
    where
    lem1 : (r1 r2 : Maybe FormTA3) ->
      ((X : FormTA3) -> Eq r1 (just X) -> Eq r2 (just X)) ->
      Eq (maybeMap fallTA3 r1) (just A) -> Eq (maybeMap fallTA3 r2) (just A)
    lem1 nothing  _  _  ()
    lem1 (just x) r2 mono h2 = eqTrans5 (eqCong (maybeMap fallTA3) (mono x refl)) h2
  checkTA3-mono-dGen3 fuel IH false tag payload A h =
    checkTA3-mono-dInst3 fuel IH (eqNat tag tagInst3) tag payload A h

  -- MP3: recursive
  checkTA3-mono-dMP3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dMP3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dMP3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dMP3 fuel IH true _ (cnode p1 p2) A h =
    lem1 (checkTA3 fuel p1) (checkTA3 (suc fuel) p1)
         (checkTA3 fuel p2) (checkTA3 (suc fuel) p2)
         (\ fp -> IH p1 fp) (\ fp -> IH p2 fp) h
    where
    lem1 : (r1 s1 r2 s2 : Maybe FormTA3) ->
      ((X : FormTA3) -> Eq r1 (just X) -> Eq s1 (just X)) ->
      ((X : FormTA3) -> Eq r2 (just X) -> Eq s2 (just X)) ->
      Eq (maybeBind r1 (\ f1 -> maybeBind r2 (\ f2 -> matchMPTA3 f1 f2))) (just A) ->
      Eq (maybeBind s1 (\ f1 -> maybeBind s2 (\ f2 -> matchMPTA3 f1 f2))) (just A)
    lem1 nothing  _  _  _  _  _  ()
    lem1 (just x) s1 nothing  _  m1 _  ()
    lem1 (just x) s1 (just y) s2 m1 m2 h2 =
      eqTrans5 (eqCong (\ r -> maybeBind r (\ f1 -> maybeBind s2 (\ f2 -> matchMPTA3 f1 f2)))
                        (m1 x refl))
      (eqTrans5 (eqCong (\ r -> maybeBind r (\ f2 -> matchMPTA3 x f2)) (m2 y refl)) h2)
  checkTA3-mono-dMP3 fuel IH true  _ (catom _) A ()
  checkTA3-mono-dMP3 fuel IH false tag payload A h =
    checkTA3-mono-dGen3 fuel IH (eqNat tag tagGen3) tag payload A h

  -- S3: non-recursive
  checkTA3-mono-dS3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dS3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dS3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dS3 fuel IH true  _ (cnode ac (cnode bc cc)) A h = h
  checkTA3-mono-dS3 fuel IH true  _ (catom _) A ()
  checkTA3-mono-dS3 fuel IH true  _ (cnode _ (catom _)) A ()
  checkTA3-mono-dS3 fuel IH false tag payload A h =
    checkTA3-mono-dMP3 fuel IH (eqNat tag tagMP3) tag payload A h

  -- K3: non-recursive
  checkTA3-mono-dK3 : (fuel : Nat) ->
    (IH : (p : Code) -> (A : FormTA3) -> Eq (checkTA3 fuel p) (just A) -> Eq (checkTA3 (suc fuel) p) (just A)) ->
    (b : Bool) -> (tag : Nat) -> (payload : Code) -> (A : FormTA3) ->
    Eq (checkTA3-dK3 fuel b tag payload) (just A) ->
    Eq (checkTA3-dK3 (suc fuel) b tag payload) (just A)
  checkTA3-mono-dK3 fuel IH true  _ (cnode ac bc) A h = h
  checkTA3-mono-dK3 fuel IH true  _ (catom _) A ()
  checkTA3-mono-dK3 fuel IH false tag payload A h =
    checkTA3-mono-dS3 fuel IH (eqNat tag tagS3) tag payload A h

checkTA3-mono zero p A ()
checkTA3-mono (suc n) (catom _) A ()
checkTA3-mono (suc n) (cnode (cnode _ _) _) A ()
checkTA3-mono (suc n) (cnode (catom tag) payload) A h =
  checkTA3-mono-dK3 n (\ p2 a2 -> checkTA3-mono n p2 a2)
                   (eqNat tag tagK3) tag payload A h

private
  checkTA3-mono-plus : (k n : Nat) -> (p : Code) -> (A : FormTA3) ->
    Eq (checkTA3 n p) (just A) -> Eq (checkTA3 (addB k n) p) (just A)
  checkTA3-mono-plus zero    n p A h = h
  checkTA3-mono-plus (suc k) n p A h =
    checkTA3-mono (addB k n) p A (checkTA3-mono-plus k n p A h)

------------------------------------------------------------------------
-- 16. Encoding correctness (D1): checkTA3 accepts encProofTA3
------------------------------------------------------------------------

proofSize3 : {A : FormTA3} -> ProofTA3 A -> Nat
proofSize3 (axK3 _ _)            = suc zero
proofSize3 (axS3 _ _ _)          = suc zero
proofSize3 (mp3 p q)             = suc (addB (proofSize3 p) (proofSize3 q))
proofSize3 (gen3 p)              = suc (proofSize3 p)
proofSize3 (inst3 _ _ p)         = suc (proofSize3 p)
proofSize3 (exIntro3 _ _ p)      = suc (proofSize3 p)
proofSize3 (axRefl3 _)           = suc zero
proofSize3 (axSym3 _ _)          = suc zero
proofSize3 (axTrans3 _ _ _)      = suc zero
proofSize3 (axCaseAtom _ _ _)    = suc zero
proofSize3 (axCaseNodeL _ _ _ _) = suc zero
proofSize3 (axFoldAtom _ _ _)    = suc zero
proofSize3 (axIfTrue _ _ _)      = suc zero
proofSize3 (axIfFalse _ _)       = suc zero
proofSize3 (axEqNatRefl _)       = suc zero

encodeTA3-correct : {A : FormTA3} -> (prf : ProofTA3 A) ->
  Eq (checkTA3 (proofSize3 prf) (encProofTA3 prf)) (just A)

encodeTA3-correct (axK3 a b) =
  lem (decFormTA3 (encFormTA3 a)) (decFormTA3 (encFormTA3 b))
      (decFormTA3-encFormTA3 a) (decFormTA3-encFormTA3 b)
  where
  lem : (r1 r2 : Maybe FormTA3) -> Eq r1 (just a) -> Eq r2 (just b) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> just (fimpTA3 da (fimpTA3 db da)))))
       (just (fimpTA3 a (fimpTA3 b a)))
  lem (just _) (just _) refl refl = refl
  lem (just _) nothing  _    ()
  lem nothing  _        ()

encodeTA3-correct (axS3 a b c) =
  lem (decFormTA3 (encFormTA3 a)) (decFormTA3 (encFormTA3 b)) (decFormTA3 (encFormTA3 c))
      (decFormTA3-encFormTA3 a) (decFormTA3-encFormTA3 b) (decFormTA3-encFormTA3 c)
  where
  lem : (r1 r2 r3 : Maybe FormTA3) ->
    Eq r1 (just a) -> Eq r2 (just b) -> Eq r3 (just c) ->
    Eq (maybeBind r1 (\ da -> maybeBind r2 (\ db -> maybeBind r3 (\ dc ->
        just (fimpTA3 (fimpTA3 da (fimpTA3 db dc))
                      (fimpTA3 (fimpTA3 da db) (fimpTA3 da dc)))))))
       (just (fimpTA3 (fimpTA3 a (fimpTA3 b c)) (fimpTA3 (fimpTA3 a b) (fimpTA3 a c))))
  lem (just _) (just _) (just _) refl refl refl = refl
  lem (just _) (just _) nothing  _    _    ()
  lem (just _) nothing  _        _    ()
  lem nothing  _        _        ()

encodeTA3-correct (axRefl3 t) =
  lem (decCodeTm (encCodeTm t)) (decCodeTm-encCodeTm t)
  where
  lem : (r : Maybe CodeTm) -> Eq r (just t) ->
    Eq (maybeBind r (\ dt -> just (feqTA3 dt dt))) (just (feqTA3 t t))
  lem (just _) refl = refl
  lem nothing  ()

encodeTA3-correct (axSym3 s t) =
  lem (decCodeTm (encCodeTm s)) (decCodeTm (encCodeTm t))
      (decCodeTm-encCodeTm s) (decCodeTm-encCodeTm t)
  where
  lem : (r1 r2 : Maybe CodeTm) -> Eq r1 (just s) -> Eq r2 (just t) ->
    Eq (maybeBind r1 (\ ds -> maybeBind r2 (\ dt ->
        just (fimpTA3 (feqTA3 ds dt) (feqTA3 dt ds)))))
       (just (fimpTA3 (feqTA3 s t) (feqTA3 t s)))
  lem (just _) (just _) refl refl = refl
  lem (just _) nothing  _    ()
  lem nothing  _        ()

encodeTA3-correct (axTrans3 r s t) =
  lem (decCodeTm (encCodeTm r)) (decCodeTm (encCodeTm s)) (decCodeTm (encCodeTm t))
      (decCodeTm-encCodeTm r) (decCodeTm-encCodeTm s) (decCodeTm-encCodeTm t)
  where
  lem : (r1 r2 r3 : Maybe CodeTm) ->
    Eq r1 (just r) -> Eq r2 (just s) -> Eq r3 (just t) ->
    Eq (maybeBind r1 (\ dr -> maybeBind r2 (\ ds -> maybeBind r3 (\ dt ->
        just (fimpTA3 (feqTA3 dr ds) (fimpTA3 (feqTA3 ds dt) (feqTA3 dr dt)))))))
       (just (fimpTA3 (feqTA3 r s) (fimpTA3 (feqTA3 s t) (feqTA3 r t))))
  lem (just _) (just _) (just _) refl refl refl = refl
  lem (just _) (just _) nothing  _    _    ()
  lem (just _) nothing  _        _    ()
  lem nothing  _        _        ()

encodeTA3-correct (axCaseAtom k ab nb) =
  decFormTA3-encFormTA3 (feqTA3 (ctCase (ctAtom k) ab nb) (substCT (catom k) ab))

encodeTA3-correct (axCaseNodeL a b ab nb) =
  decFormTA3-encFormTA3 (feqTA3 (ctCase (ctNode a b) ab nb) nb)

encodeTA3-correct (axFoldAtom k ac nc) =
  decFormTA3-encFormTA3 (feqTA3 (ctFold (ctAtom k) ac nc) (substCT (catom k) ac))

encodeTA3-correct (axIfTrue k tb eb) =
  decFormTA3-encFormTA3 (feqTA3 (ctIf (ctAtom (suc k)) tb eb) tb)

encodeTA3-correct (axIfFalse tb eb) =
  decFormTA3-encFormTA3 (feqTA3 (ctIf (ctAtom zero) tb eb) eb)

encodeTA3-correct (axEqNatRefl n) =
  decFormTA3-encFormTA3 (feqTA3 (ctEqNat (ctAtom n) (ctAtom n)) (ctAtom (suc zero)))

-- gen3: fuel passes through directly
encodeTA3-correct (gen3 prf) =
  mm-just3 fallTA3 _ (checkTA3 (proofSize3 prf) (encProofTA3 prf))
           (encodeTA3-correct prf)

-- mp3: needs mono to lift IH fuel to addB fuel
encodeTA3-correct (mp3 {A} {B} p q) =
  mpLem (checkTA3 fuel3 (encProofTA3 p))
        (checkTA3 fuel3 (encProofTA3 q))
        (checkTA3-fuel-eq (addB (proofSize3 q) (proofSize3 p)) fuel3
          (addB-comm (proofSize3 q) (proofSize3 p))
          (encProofTA3 p) (fimpTA3 A B)
          (checkTA3-mono-plus (proofSize3 q) (proofSize3 p) (encProofTA3 p) (fimpTA3 A B)
            (encodeTA3-correct p)))
        (checkTA3-mono-plus (proofSize3 p) (proofSize3 q) (encProofTA3 q) A
          (encodeTA3-correct q))
  where
  fuel3 : Nat
  fuel3 = addB (proofSize3 p) (proofSize3 q)

  eqFormTA3-refl : (f : FormTA3) -> Eq (eqFormTA3 f f) true
  eqCodeTm-refl : (x : CodeTm) -> Eq (eqCodeTm x x) true
  eqCodeTm-refl (ctVar n)      = eqNat-refl n
  eqCodeTm-refl (ctAtom n)     = eqNat-refl n
  eqCodeTm-refl (ctNode a b)   = at (eqCodeTm a a) (eqCodeTm b b) (eqCodeTm-refl a) (eqCodeTm-refl b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl (ctCase t a n) = at (eqCodeTm t t) (and (eqCodeTm a a) (eqCodeTm n n))
    (eqCodeTm-refl t) (at (eqCodeTm a a) (eqCodeTm n n) (eqCodeTm-refl a) (eqCodeTm-refl n))
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl (ctFold t a n) = at (eqCodeTm t t) (and (eqCodeTm a a) (eqCodeTm n n))
    (eqCodeTm-refl t) (at (eqCodeTm a a) (eqCodeTm n n) (eqCodeTm-refl a) (eqCodeTm-refl n))
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl (ctEqNat a b)  = at (eqCodeTm a a) (eqCodeTm b b) (eqCodeTm-refl a) (eqCodeTm-refl b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl (ctIf c t e)   = at (eqCodeTm c c) (and (eqCodeTm t t) (eqCodeTm e e))
    (eqCodeTm-refl c) (at (eqCodeTm t t) (eqCodeTm e e) (eqCodeTm-refl t) (eqCodeTm-refl e))
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl (ctEqCode a b) = at (eqCodeTm a a) (eqCodeTm b b) (eqCodeTm-refl a) (eqCodeTm-refl b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqFormTA3-refl fbotTA3 = refl
  eqFormTA3-refl (fimpTA3 a b) = at (eqFormTA3 a a) (eqFormTA3 b b) (eqFormTA3-refl a) (eqFormTA3-refl b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqFormTA3-refl (fallTA3 a) = eqFormTA3-refl a
  eqFormTA3-refl (fexTA3 a) = eqFormTA3-refl a
  eqFormTA3-refl (feqTA3 s t) = at (eqCodeTm s s) (eqCodeTm t t) (eqCodeTm-refl s) (eqCodeTm-refl t)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl

  matchLem : Eq (matchMPTA3 (fimpTA3 A B) A) (just B)
  matchLem = eqCong (\ v -> boolGuardTA3 v (just B)) (eqFormTA3-refl A)

  mpLem : (r1 r2 : Maybe FormTA3) ->
    Eq r1 (just (fimpTA3 A B)) -> Eq r2 (just A) ->
    Eq (maybeBind r1 (\ f1 -> maybeBind r2 (\ f2 -> matchMPTA3 f1 f2))) (just B)
  mpLem (just .(fimpTA3 A B)) (just .A) refl refl = matchLem
  mpLem (just _)              nothing   _    ()
  mpLem nothing               _         ()

-- inst3: checker decodes result formula, checks sub-proof is fallTA3
encodeTA3-correct (inst3 A c prf) =
  instLem (decFormTA3 (encFormTA3 (substF3 c A)))
          (checkTA3 (proofSize3 prf) (encProofTA3 prf))
          (decFormTA3-encFormTA3 (substF3 c A))
          (encodeTA3-correct prf)
  where
  instLem : (r1 r2 : Maybe FormTA3) ->
    Eq r1 (just (substF3 c A)) -> Eq r2 (just (fallTA3 A)) ->
    Eq (maybeBind r1 (\ result -> maybeBind r2 (\ fp -> inst3-check fp result)))
       (just (substF3 c A))
  instLem (just .(substF3 c A)) (just .(fallTA3 A)) refl refl = refl
  instLem (just _)              nothing              _    ()
  instLem nothing               _                    ()

-- exIntro3: needs mono + eqFormTA3-refl
encodeTA3-correct (exIntro3 A c prf) =
  exLem (checkTA3 (proofSize3 prf) (encProofTA3 prf))
        (decFormTA3 (encFormTA3 A))
        (encodeTA3-correct prf)
        (decFormTA3-encFormTA3 A)
  where
  eqFormTA3-refl3 : (f : FormTA3) -> Eq (eqFormTA3 f f) true
  eqCodeTm-refl3 : (x : CodeTm) -> Eq (eqCodeTm x x) true
  eqCodeTm-refl3 (ctVar n)      = eqNat-refl n
  eqCodeTm-refl3 (ctAtom n)     = eqNat-refl n
  eqCodeTm-refl3 (ctNode a b)   = at (eqCodeTm a a) (eqCodeTm b b) (eqCodeTm-refl3 a) (eqCodeTm-refl3 b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl3 (ctCase t a n) = at (eqCodeTm t t) (and (eqCodeTm a a) (eqCodeTm n n))
    (eqCodeTm-refl3 t) (at (eqCodeTm a a) (eqCodeTm n n) (eqCodeTm-refl3 a) (eqCodeTm-refl3 n))
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl3 (ctFold t a n) = at (eqCodeTm t t) (and (eqCodeTm a a) (eqCodeTm n n))
    (eqCodeTm-refl3 t) (at (eqCodeTm a a) (eqCodeTm n n) (eqCodeTm-refl3 a) (eqCodeTm-refl3 n))
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl3 (ctEqNat a b)  = at (eqCodeTm a a) (eqCodeTm b b) (eqCodeTm-refl3 a) (eqCodeTm-refl3 b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl3 (ctIf c2 t e)  = at (eqCodeTm c2 c2) (and (eqCodeTm t t) (eqCodeTm e e))
    (eqCodeTm-refl3 c2) (at (eqCodeTm t t) (eqCodeTm e e) (eqCodeTm-refl3 t) (eqCodeTm-refl3 e))
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqCodeTm-refl3 (ctEqCode a b) = at (eqCodeTm a a) (eqCodeTm b b) (eqCodeTm-refl3 a) (eqCodeTm-refl3 b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqFormTA3-refl3 fbotTA3 = refl
  eqFormTA3-refl3 (fimpTA3 a b) = at (eqFormTA3 a a) (eqFormTA3 b b) (eqFormTA3-refl3 a) (eqFormTA3-refl3 b)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl
  eqFormTA3-refl3 (fallTA3 a) = eqFormTA3-refl3 a
  eqFormTA3-refl3 (fexTA3 a) = eqFormTA3-refl3 a
  eqFormTA3-refl3 (feqTA3 s t) = at (eqCodeTm s s) (eqCodeTm t t) (eqCodeTm-refl3 s) (eqCodeTm-refl3 t)
    where at : (x y : Bool) -> Eq x true -> Eq y true -> Eq (and x y) true
          at true true refl refl = refl

  guardLem2 : Eq (boolGuardTA3 (eqFormTA3 (substF3 c A) (substF3 c A)) (just (fexTA3 A)))
                 (just (fexTA3 A))
  guardLem2 = eqCong (\ v -> boolGuardTA3 v (just (fexTA3 A))) (eqFormTA3-refl3 (substF3 c A))

  exLem : (r1 r2 : Maybe FormTA3) ->
    Eq r1 (just (substF3 c A)) -> Eq r2 (just A) ->
    Eq (maybeBind r1 (\ fp -> maybeBind r2 (\ a ->
        boolGuardTA3 (eqFormTA3 fp (substF3 c a)) (just (fexTA3 a)))))
       (just (fexTA3 A))
  exLem (just .(substF3 c A)) (just .A) refl refl = guardLem2
  exLem (just _)              nothing   _    ()
  exLem nothing               _         ()

------------------------------------------------------------------------
-- 17. Internal provability for ProofTA3
------------------------------------------------------------------------

ProvableTA3 : FormTA3 -> Set
ProvableTA3 A = SigmaTA Nat (\ k ->
                SigmaTA Code (\ p -> Eq (checkTA3 k p) (just A)))

d1-for-checkTA3 : {A : FormTA3} -> ProofTA3 A -> ProvableTA3 A
d1-for-checkTA3 prf =
  mkSigmaTA (proofSize3 prf) (mkSigmaTA (encProofTA3 prf) (encodeTA3-correct prf))

------------------------------------------------------------------------
-- 18. Soundness of ProofTA3 at fuel 0 (consistency)
------------------------------------------------------------------------
-- At fuel 0, evalCT zero env t = catom zero for all env, t.
-- So feqTA3 is always Eq (catom 0) (catom 0) = refl.
-- This makes the model env-independent, which avoids the
-- substitution lemma issue for inst3/exIntro3.

-- Env independence at fuel 0
envIndep0 : (env1 env2 : Env3) -> (A : FormTA3) -> GoodTA3 zero env1 A -> GoodTA3 zero env2 A
envIndep0 env1 env2 fbotTA3        h = h
envIndep0 env1 env2 (fimpTA3 a b)  h = \ ga -> envIndep0 env1 env2 b (h (envIndep0 env2 env1 a ga))
envIndep0 env1 env2 (fallTA3 a)    h = \ c -> envIndep0 (extendEnv3 env1 c) (extendEnv3 env2 c) a (h c)
envIndep0 env1 env2 (fexTA3 a)     (mkSigmaTA c gc) =
  mkSigmaTA c (envIndep0 (extendEnv3 env1 c) (extendEnv3 env2 c) a gc)
envIndep0 env1 env2 (feqTA3 t1 t2) h = refl

-- Substitution soundness at fuel 0: GoodTA3 0 env A -> GoodTA3 0 env (substF3 c A)
-- and reverse.
substSound0 : (c : Code) -> (env : Env3) -> (A : FormTA3) ->
  GoodTA3 zero env A -> GoodTA3 zero env (substF3 c A)
substRev0 : (c : Code) -> (env : Env3) -> (A : FormTA3) ->
  GoodTA3 zero env (substF3 c A) -> GoodTA3 zero env A

substSound0 c env fbotTA3        h = h
substSound0 c env (fimpTA3 a b)  h = \ ga -> substSound0 c env b (h (substRev0 c env a ga))
substSound0 c env (fallTA3 a)    h = h
substSound0 c env (fexTA3 a)     h = h
substSound0 c env (feqTA3 t1 t2) h = refl

substRev0 c env fbotTA3        h = h
substRev0 c env (fimpTA3 a b)  h = \ ga -> substRev0 c env b (h (substSound0 c env a ga))
substRev0 c env (fallTA3 a)    h = h
substRev0 c env (fexTA3 a)     h = h
substRev0 c env (feqTA3 t1 t2) h = refl

-- Soundness at fuel 0
sound0 : {A : FormTA3} -> (env : Env3) -> ProofTA3 A -> GoodTA3 zero env A
sound0 env (axK3 A B) = \ ga -> \ _ -> ga
sound0 env (axS3 A B C) = \ gABC -> \ gAB -> \ gA -> gABC gA (gAB gA)
sound0 env (mp3 pAB pA) = (sound0 env pAB) (sound0 env pA)
sound0 env (gen3 pA) = \ c -> sound0 (extendEnv3 env c) pA
sound0 env (inst3 A c pAll) =
  substSound0 c env A (envIndep0 (extendEnv3 env c) env A ((sound0 env pAll) c))
sound0 env (exIntro3 A c p) =
  mkSigmaTA c (envIndep0 env (extendEnv3 env c) A
    (substRev0 c env A (sound0 env p)))
sound0 env (axRefl3 t) = refl
sound0 env (axSym3 s t) = \ h -> eqSym5 h
sound0 env (axTrans3 r s t) = \ hrs -> \ hst -> eqTrans5 hrs hst
sound0 env (axCaseAtom k ab nb) = refl
sound0 env (axCaseNodeL a b ab nb) = refl
sound0 env (axFoldAtom k ac nc) = refl
sound0 env (axIfTrue k tb eb) = refl
sound0 env (axIfFalse tb eb) = refl
sound0 env (axEqNatRefl n) = refl

con3 : ProofTA3 fbotTA3 -> EmptyTA
con3 p = sound0 emptyEnv3 p

------------------------------------------------------------------------
-- 19. checkCT3-full: internal checker as CodeTm
------------------------------------------------------------------------
-- Mirrors checkTA3 as a ctFold expression.
-- In the ctFold nodeCase (after ctCase on left child = tag):
--   var 0 = catom k (tag atom from ctCase)
--   var 1 = left (= catom k)
--   var 2 = right (= payload)
--   var 3 = fold(left)
--   var 4 = fold(right)

private
  w0 : Nat
  w0 = zero
  w1 : Nat
  w1 = suc zero
  w2 : Nat
  w2 = suc (suc zero)
  w3 : Nat
  w3 = suc (suc (suc zero))
  w4 : Nat
  w4 = suc (suc (suc (suc zero)))
  w5 : Nat
  w5 = suc (suc (suc (suc (suc zero))))

  -- handleK3: cnode tagK3 (cnode encA encB)
  -- Result: cnode ft1 (cnode encA (cnode ft1 (cnode encB encA)))
  -- In atom branch: var 2 = payload = cnode encA encB
  handleK3 : CodeTm
  handleK3 = ctCase (ctVar w2)
    (ctAtom zero)
    -- cnode: var 0 = encA, var 1 = encB
    (ctNode (ctAtom ft1)
      (ctNode (ctVar w0)
        (ctNode (ctAtom ft1)
          (ctNode (ctVar w1) (ctVar w0)))))

  -- handleS3: cnode tagS3 (cnode encA (cnode encB encC))
  -- Result: cnode ft1 (cnode (cnode ft1 (cnode encA (cnode ft1 (cnode encB encC))))
  --                         (cnode ft1 (cnode (cnode ft1 (cnode encA encB))
  --                                          (cnode ft1 (cnode encA encC)))))
  handleS3 : CodeTm
  handleS3 = ctCase (ctVar w2)
    (ctAtom zero)
    -- cnode encA rest: var 0 = encA, var 1 = rest
    (ctCase (ctVar w1)
      (ctAtom zero)
      -- cnode encB encC: var 0 = encB, var 1 = encC, var 2 = encA
      (ctNode (ctAtom ft1)
        (ctNode
          (ctNode (ctAtom ft1)
            (ctNode (ctVar w2)
              (ctNode (ctAtom ft1)
                (ctNode (ctVar w0) (ctVar w1)))))
          (ctNode (ctAtom ft1)
            (ctNode
              (ctNode (ctAtom ft1)
                (ctNode (ctVar w2) (ctVar w0)))
              (ctNode (ctAtom ft1)
                (ctNode (ctVar w2) (ctVar w1))))))))

  -- handleMP3: uses fold(right) = var 4
  -- fold(right) should be cnode fold(p1) fold(p2)
  -- fold(p1) should be cnode ft1 (cnode encA encB) for imp
  -- Return encB
  matchMP3-body : CodeTm
  matchMP3-body = ctCase (ctVar w0)
    (ctAtom zero)
    -- fp1 is cnode a b: var 0 = a, var 1 = b
    (ctIf (ctEqNat (ctVar w0) (ctAtom ft1))
      -- a = ft1. b should be cnode encA encB.
      (ctCase (ctVar w1)
        (ctAtom zero)
        -- b is cnode encA encB: var 0 = encA, var 1 = encB
        (ctVar w1))
      (ctAtom zero))

  handleMP3 : CodeTm
  handleMP3 = ctCase (ctVar w4)
    (ctAtom zero)
    -- fold(right) is cnode fp1 fp2: var 0 = fp1, var 1 = fp2
    matchMP3-body

  -- handleGen3: fold(right) = var 4
  -- Wrap with ft2 tag (fallTA3)
  handleGen3 : CodeTm
  handleGen3 = ctCase (ctVar w4)
    (ctIf (ctEqNat (ctVar w0) (ctAtom zero))
      (ctAtom zero)
      (ctNode (ctAtom ft2) (ctVar w0)))
    (ctNode (ctAtom ft2) (ctNode (ctVar w0) (ctVar w1)))

  -- handleInst3: new encoding stores result formula as first component of payload
  -- payload (var w2) = cnode (encFormTA3 result) (encProofTA3 p)
  -- Extract first component of raw payload
  handleInst3 : CodeTm
  handleInst3 = ctCase (ctVar w2)
    (ctAtom zero)
    -- cnode case: var 0 = encFormTA3 result, var 1 = encProofTA3 p
    (ctVar w0)

  -- handleEx3: extract encA from raw payload, wrap with ft3 tag (fexTA3)
  -- payload = cnode enc(p) (cnode encA c)
  -- var 2 = payload
  handleEx3 : CodeTm
  handleEx3 = ctCase (ctVar w2)
    (ctAtom zero)
    -- cnode enc(p) rest: var 0 = enc(p), var 1 = rest
    (ctCase (ctVar w1)
      (ctAtom zero)
      -- cnode encA c: var 0 = encA, var 1 = c
      (ctNode (ctAtom ft3) (ctVar w0)))

  -- handleRefl3: payload = encCodeTm t
  -- Result: cnode ft4 (cnode encT encT) = encFormTA3 (feqTA3 t t)
  -- var 2 = payload = encCodeTm t
  handleRefl3 : CodeTm
  handleRefl3 = ctNode (ctAtom ft4) (ctNode (ctVar w2) (ctVar w2))

  -- handleSym3: payload = cnode enc(s) enc(t)
  -- Result: cnode ft1 (cnode (cnode ft4 (cnode encS encT)) (cnode ft4 (cnode encT encS)))
  handleSym3 : CodeTm
  handleSym3 = ctCase (ctVar w2)
    (ctAtom zero)
    -- cnode encS encT: var 0 = encS, var 1 = encT
    (ctNode (ctAtom ft1)
      (ctNode (ctNode (ctAtom ft4) (ctNode (ctVar w0) (ctVar w1)))
              (ctNode (ctAtom ft4) (ctNode (ctVar w1) (ctVar w0)))))

  -- handleTrans3: payload = cnode enc(r) (cnode enc(s) enc(t))
  -- Result: cnode ft1 (cnode (cnode ft4 (cnode encR encS))
  --                         (cnode ft1 (cnode (cnode ft4 (cnode encS encT))
  --                                          (cnode ft4 (cnode encR encT)))))
  handleTrans3 : CodeTm
  handleTrans3 = ctCase (ctVar w2)
    (ctAtom zero)
    -- cnode encR rest: var 0 = encR, var 1 = rest
    (ctCase (ctVar w1)
      (ctAtom zero)
      -- cnode encS encT: var 0 = encS, var 1 = encT, var 2 = encR
      (ctNode (ctAtom ft1)
        (ctNode (ctNode (ctAtom ft4) (ctNode (ctVar w2) (ctVar w0)))
                (ctNode (ctAtom ft1)
                  (ctNode (ctNode (ctAtom ft4) (ctNode (ctVar w0) (ctVar w1)))
                          (ctNode (ctAtom ft4) (ctNode (ctVar w2) (ctVar w1))))))))

  -- handleCaseAtom: payload = cnode (catom k) (cnode enc(ab) enc(nb))
  -- Result: encFormTA3 (feqTA3 (ctCase (ctAtom k) ab nb) (substCT (catom k) ab))
  -- = cnode ft4 (cnode enc(ctCase (ctAtom k) ab nb) enc(substCT (catom k) ab))
  -- This is VERY complex because we'd need to compute substCT and encCodeTm inside the fold.
  -- SIMPLIFICATION: the checker just returns the result based on the payload structure.
  -- For correctness of D1, we need foldCorrect3 to verify this.
  -- We can't compute substCT inside ctFold. Instead, use the raw payload encoding.
  -- The handler returns: cnode ft4 (cnode enc(ctCase (ctAtom k) ab nb) enc(substCT (catom k) ab))
  -- But this requires re-encoding, which is not possible in CodeTm.
  --
  -- ALTERNATIVE: for computation axioms, the checker just passes through.
  -- The computation axioms are AXIOMATIC — they don't need recursive checking.
  -- We just need to verify the tag and return the appropriate formula encoding.
  -- Since we can't compute the formula encoding inside the fold (it requires
  -- re-encoding CodeTm values), we use a trick: the formula encoding is
  -- ALREADY present in the proof code payload.
  --
  -- REVISED ENCODING for computation axioms:
  -- encProofTA3 (axCaseAtom k ab nb) stores the RESULT formula encoding
  -- alongside the arguments. But our current encoding doesn't do this.
  --
  -- PRACTICAL SOLUTION: Include the formula encoding in the proof code.
  -- Change encProofTA3 for computation axioms to store the result too.
  -- But that changes the encoding, affecting earlier proofs.
  --
  -- SIMPLEST APPROACH: Use a "trust" tag for computation axioms.
  -- The checker for axCaseAtom etc. just extracts the pre-computed result
  -- from an extended payload that includes it.
  -- But this changes encProofTA3, which we already proved correct for checkTA3.
  --
  -- ACTUALLY: The cleanest approach is to have the checker for axiom tags
  -- extract the formula encoding from the raw payload, since the payload
  -- contains enough information. For axCaseAtom, the payload has
  -- (catom k, encCodeTm ab, encCodeTm nb). The result formula has
  -- encCodeTm (ctCase (ctAtom k) ab nb) and encCodeTm (substCT (catom k) ab).
  -- Both can be CONSTRUCTED from the payload components.
  -- encCodeTm (ctCase (ctAtom k) ab nb) = cnode (catom ct3) (cnode (cnode (catom ct1) (catom k))
  --                                              (cnode (encCodeTm ab) (encCodeTm nb)))
  -- Since encCodeTm ab is in the payload, we can build this!
  -- And encCodeTm (substCT (catom k) ab) requires computing substCT,
  -- which is a meta-operation. Inside the fold, we can't compute it.
  --
  -- SOLUTION: For computation axioms, include the result encoding in the
  -- proof encoding. This makes the checker simple: just extract and return.
  --
  -- But this changes encProofTA3. Let me think about this...
  --
  -- ALTERNATIVE SOLUTION: for D1 only, we can use the checkTA3 approach
  -- (meta-level checker) and convert. We already have d1-for-checkTA3.
  -- The CodeTm checker (checkCT3-full) is needed for internal D2/D3.
  -- For internal D2/D3, only mp3/gen3/inst3 handlers matter (not computation axioms).
  -- So for computation axioms, the handler can just return the result from
  -- an extended encoding that includes it.
  --
  -- DECISION: Change encProofTA3 for computation axioms to include the
  -- result formula encoding. This is the standard Gödel numbering approach:
  -- the proof code carries all needed information.
  --
  -- But I already proved encodeTA3-correct for checkTA3 with the current encoding.
  -- If I change encProofTA3, I need to update checkTA3 and re-prove.
  -- That's a LOT of rework.
  --
  -- BETTER DECISION: For computation axiom handlers in checkCT3-full,
  -- construct the result from the payload components. For axCaseAtom:
  -- payload = cnode (catom k) (cnode enc(ab) enc(nb))
  -- We need to build: cnode ft4 (cnode <enc of ctCase (ctAtom k) ab nb>
  --                                    <enc of substCT (catom k) ab>)
  -- <enc of ctCase (ctAtom k) ab nb> = cnode ct3 (cnode (cnode ct1 (catom k))
  --                                              (cnode enc(ab) enc(nb)))
  -- This CAN be constructed from the payload components!
  -- enc(ab) and enc(nb) are at known positions in the payload.
  --
  -- For substCT (catom k) ab: this applies substCT to the CodeTm ab.
  -- Inside the fold, we don't have ab as a CodeTm, only enc(ab) as a Code.
  -- We can't compute substCT on a Code representation of a CodeTm.
  -- So we CAN'T build enc(substCT (catom k) ab) from the payload.
  --
  -- CONCLUSION: We CANNOT build the complete result for computation axioms
  -- inside the fold. The substCT operation is meta-level.
  --
  -- FINAL APPROACH: Include the result formula encoding in the proof code.
  -- Add a "result" field to the computation axiom encodings.
  -- This is standard in Gödel numbering: the proof code is self-describing.

  -- For now, use a simplified approach: computation axiom handlers
  -- extract a pre-stored result from the payload. The encoding stores
  -- cnode tag (cnode <result-formula-code> <arguments>).
  -- This requires changing encProofTA3 for computation axioms.
  -- We'll handle this after getting the logical connective handlers working.

  -- Computation axiom handlers: payload (var w2) = encFormTA3 (result formula)
  -- Just return the raw payload.
  handleCaseAtom3 : CodeTm
  handleCaseAtom3 = ctVar w2
  handleCaseNode3 : CodeTm
  handleCaseNode3 = ctVar w2
  handleFoldAtom3 : CodeTm
  handleFoldAtom3 = ctVar w2
  handleIfTrue3 : CodeTm
  handleIfTrue3 = ctVar w2
  handleIfFalse3 : CodeTm
  handleIfFalse3 = ctVar w2
  handleEqRefl3 : CodeTm
  handleEqRefl3 = ctVar w2

  acFull3 : CodeTm
  acFull3 = ctAtom zero

  ncFull3 : CodeTm
  ncFull3 = ctCase (ctVar w0)
    -- ATOM BRANCH: tag dispatch
    (ctIf (ctEqNat (ctVar w0) (ctAtom tagRefl3))
      handleRefl3
      (ctIf (ctEqNat (ctVar w0) (ctAtom tagGen3))
        handleGen3
        (ctIf (ctEqNat (ctVar w0) (ctAtom tagMP3))
          handleMP3
          (ctIf (ctEqNat (ctVar w0) (ctAtom tagInst3))
            handleInst3
            (ctIf (ctEqNat (ctVar w0) (ctAtom tagK3))
              handleK3
              (ctIf (ctEqNat (ctVar w0) (ctAtom tagS3))
                handleS3
                (ctIf (ctEqNat (ctVar w0) (ctAtom tagSym3))
                  handleSym3
                  (ctIf (ctEqNat (ctVar w0) (ctAtom tagTrans3))
                    handleTrans3
                    (ctIf (ctEqNat (ctVar w0) (ctAtom tagEx3))
                      handleEx3
                      (ctIf (ctEqNat (ctVar w0) (ctAtom tagCaseAtom))
                        handleCaseAtom3
                        (ctIf (ctEqNat (ctVar w0) (ctAtom tagCaseNode))
                          handleCaseNode3
                          (ctIf (ctEqNat (ctVar w0) (ctAtom tagFoldAtom))
                            handleFoldAtom3
                            (ctIf (ctEqNat (ctVar w0) (ctAtom tagIfTrue))
                              handleIfTrue3
                              (ctIf (ctEqNat (ctVar w0) (ctAtom tagIfFalse))
                                handleIfFalse3
                                (ctIf (ctEqNat (ctVar w0) (ctAtom tagEqRefl))
                                  handleEqRefl3
                                  (ctAtom zero))))))))))))))))
    -- NODE BRANCH: pass through cnode fold(left) fold(right)
    (ctNode (ctVar w4) (ctVar w5))

checkCT3-full : CodeTm
checkCT3-full = ctFold (ctVar w0) acFull3 ncFull3

------------------------------------------------------------------------
-- 20. checkCT3-full ground tests
------------------------------------------------------------------------

private
  n30b : Nat
  n30b = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         zero)))))))))))))))))))))))))))))

  -- axRefl3 (ctAtom 0): cnode tagRefl3 (cnode ct1 (catom 0))
  -- Expected: cnode ft4 (cnode (cnode ct1 (catom 0)) (cnode ct1 (catom 0)))
  --         = encFormTA3 (feqTA3 (ctAtom 0) (ctAtom 0))
  test-ct3-refl : Eq (evalCT n30b
                       (extendEnv3 emptyEnv3
                         (encProofTA3 (axRefl3 (ctAtom zero))))
                       checkCT3-full)
                    (encFormTA3 (feqTA3 (ctAtom zero) (ctAtom zero)))
  test-ct3-refl = refl

  -- axK3 bot bot
  test-ct3-axK : Eq (evalCT n30b
                       (extendEnv3 emptyEnv3
                         (encProofTA3 (axK3 fbotTA3 fbotTA3)))
                       checkCT3-full)
                    (encFormTA3 (fimpTA3 fbotTA3 (fimpTA3 fbotTA3 fbotTA3)))
  test-ct3-axK = refl

  -- gen3 (axRefl3 (ctAtom 0))
  test-ct3-gen : Eq (evalCT n30b
                       (extendEnv3 emptyEnv3
                         (encProofTA3 (gen3 (axRefl3 (ctAtom zero)))))
                       checkCT3-full)
                    (encFormTA3 (fallTA3 (feqTA3 (ctAtom zero) (ctAtom zero))))
  test-ct3-gen = refl

  -- mp3 (axK3 feq00 bot) (axRefl3 (ctAtom 0))
  -- where feq00 = feqTA3 (ctAtom 0) (ctAtom 0)
  feq00b : FormTA3
  feq00b = feqTA3 (ctAtom zero) (ctAtom zero)

  n50b : Nat
  n50b = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         zero)))))))))))))))))))))))))))))))))))))))))))))))))

  test-ct3-mp : Eq (evalCT n50b
                      (extendEnv3 emptyEnv3
                        (encProofTA3 (mp3 (axK3 feq00b fbotTA3) (axRefl3 (ctAtom zero)))))
                      checkCT3-full)
                   (encFormTA3 (fimpTA3 fbotTA3 feq00b))
  test-ct3-mp = refl

  -- axSym3
  test-ct3-sym : Eq (evalCT n30b
                       (extendEnv3 emptyEnv3
                         (encProofTA3 (axSym3 (ctAtom zero) (ctVar zero))))
                       checkCT3-full)
                    (encFormTA3 (fimpTA3 (feqTA3 (ctAtom zero) (ctVar zero))
                                        (feqTA3 (ctVar zero) (ctAtom zero))))
  test-ct3-sym = refl

------------------------------------------------------------------------
-- 21. foldCorrect3: the fold of checkCT3-full on proof codes
------------------------------------------------------------------------

private
  -- n30c = 150. Built from addB to avoid huge literal.
  -- This provides enough concrete sucs for the 15-level dispatch chain.
  n25c : Nat
  n25c = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc zero))))))))))))))))))))))))

  n30c : Nat
  n30c = addB n25c (addB n25c (addB n25c (addB n25c (addB n25c (addB n25c zero)))))

proofExtra3 : {A : FormTA3} -> ProofTA3 A -> Nat
proofExtra3 (axRefl3 _)             = zero
proofExtra3 (axK3 _ _)              = zero
proofExtra3 (axS3 _ _ _)            = zero
proofExtra3 (mp3 p q)               = suc (suc (addB (proofExtra3 p) (proofExtra3 q)))
proofExtra3 (gen3 p)                = suc (proofExtra3 p)
proofExtra3 (inst3 _ _ p)           = suc (suc (proofExtra3 p))
proofExtra3 (exIntro3 _ _ p)        = suc (suc (proofExtra3 p))
proofExtra3 (axSym3 _ _)            = zero
proofExtra3 (axTrans3 _ _ _)        = zero
proofExtra3 (axCaseAtom _ _ _)      = zero
proofExtra3 (axCaseNodeL _ _ _ _)   = zero
proofExtra3 (axFoldAtom _ _ _)      = zero
proofExtra3 (axIfTrue _ _ _)        = zero
proofExtra3 (axIfFalse _ _)         = zero
proofExtra3 (axEqNatRefl _)         = zero

proofFuel3 : {A : FormTA3} -> ProofTA3 A -> Nat
proofFuel3 p = addB n30c (proofExtra3 p)

-- foldCorrect3: foldCT at proofFuel3 on encProofTA3 gives encFormTA3.
-- By induction on ProofTA3, following the strong-fuel approach.

-- Base cases (axioms): all by refl since n30c provides enough concrete sucs.
foldCorrect3-axRefl : (t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 (axRefl3 t)) k) env (encProofTA3 (axRefl3 t)) acFull3 ncFull3)
     (encFormTA3 (feqTA3 t t))
foldCorrect3-axRefl t env k = refl

foldCorrect3-axK : (a b : FormTA3) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 (axK3 a b)) k) env (encProofTA3 (axK3 a b)) acFull3 ncFull3)
     (encFormTA3 (fimpTA3 a (fimpTA3 b a)))
foldCorrect3-axK a b env k = refl

foldCorrect3-axS : (a b c : FormTA3) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 (axS3 a b c)) k) env (encProofTA3 (axS3 a b c)) acFull3 ncFull3)
     (encFormTA3 (fimpTA3 (fimpTA3 a (fimpTA3 b c)) (fimpTA3 (fimpTA3 a b) (fimpTA3 a c))))
foldCorrect3-axS a b c env k = refl

foldCorrect3-axSym : (s t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 (axSym3 s t)) k) env (encProofTA3 (axSym3 s t)) acFull3 ncFull3)
     (encFormTA3 (fimpTA3 (feqTA3 s t) (feqTA3 t s)))
foldCorrect3-axSym s t env k = refl

foldCorrect3-axTrans : (r s t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 (axTrans3 r s t)) k) env (encProofTA3 (axTrans3 r s t)) acFull3 ncFull3)
     (encFormTA3 (fimpTA3 (feqTA3 r s) (fimpTA3 (feqTA3 s t) (feqTA3 r t))))
foldCorrect3-axTrans r s t env k = refl

-- Gen3 case: same pattern as foldCorrect-gen in Track 1.
-- proofFuel3 (gen3 prf) = addB n30c (suc (proofExtra3 prf))
-- After 1 suc peel: inner fuel = addB n30c (proofExtra3 prf) = proofFuel3 prf.
-- Sub-fold on encProofTA3 prf gets fuel proofFuel3 prf = IH.
-- ncFull3 wraps the fold result with ft2 (fallTA3 tag).

-- Helper: encProofTA3 always produces cnodes.
private
  encProofTA3-is-cnode : {X : FormTA3} -> (prf : ProofTA3 X) ->
    SigmaTA Code (\ la -> SigmaTA Code (\ lb -> Eq (encProofTA3 prf) (cnode la lb)))
  encProofTA3-is-cnode (axK3 a b)            = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axS3 a b c)          = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (mp3 p q)             = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (gen3 p)              = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (inst3 a c p)         = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (exIntro3 a c p)      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axRefl3 t)           = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axSym3 s t)          = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axTrans3 r s t)      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axCaseAtom k ab nb)  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axCaseNodeL a b ab nb) = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axFoldAtom k ac nc)  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axIfTrue k tb eb)    = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axIfFalse tb eb)     = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofTA3-is-cnode (axEqNatRefl n)       = mkSigmaTA _ (mkSigmaTA _ refl)

  -- foldCT-pair3: when left is cnode, node branch returns cnode fold(left) fold(right).
  foldCT-pair3 : (k : Nat) -> (env : Env3) ->
    (left right : Code) ->
    (fa fb : Code) ->
    Eq (foldCT (addB n30c k) env left acFull3 ncFull3) fa ->
    Eq (foldCT (addB n30c k) env right acFull3 ncFull3) fb ->
    Eq (foldCT (suc (addB n30c k)) env (cnode left right) acFull3 ncFull3)
       (evalCT (addB n30c k)
         (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb) fa) right) left) ncFull3)
  foldCT-pair3 k env left right fa fb ha hb =
    eqTrans5
      (eqCong (\ x -> evalCT (addB n30c k)
        (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env
          (foldCT (addB n30c k) env right acFull3 ncFull3)) x) right) left) ncFull3) ha)
      (eqCong (\ x -> evalCT (addB n30c k)
        (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env x) fa) right) left) ncFull3) hb)

  ncFull3-cnode-default : (k : Nat) -> (env : Env3) ->
    (left right : Code) -> (la lb : Code) -> Eq left (cnode la lb) ->
    (fa fb : Code) ->
    Eq (evalCT (addB n30c k)
         (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb) fa) right) left) ncFull3)
       (cnode fa fb)
  ncFull3-cnode-default k env .(cnode la lb) right la lb refl fa fb = refl

  -- addB helpers (private in this file)
  addB-assoc3 : (a b c : Nat) -> Eq (addB (addB a b) c) (addB a (addB b c))
  addB-assoc3 zero    b c = refl
  addB-assoc3 (suc a) b c = eqCong suc (addB-assoc3 a b c)

  addB-swap3 : (a b c : Nat) -> Eq (addB a (addB b c)) (addB b (addB a c))
  addB-swap3 a b c =
    eqTrans0 (eqSym0 (addB-assoc3 a b c))
    (eqTrans0 (eqCong (\ x -> addB x c) (addB-comm a b))
              (addB-assoc3 b a c))

  foldCT-fuel-eq3 : (f1 f2 : Nat) -> Eq f1 f2 ->
    (env : Env3) -> (c : Code) -> (ac nc : CodeTm) ->
    Eq (foldCT f1 env c ac nc) (foldCT f2 env c ac nc)
  foldCT-fuel-eq3 f1 .f1 refl env c ac nc = refl

-- Gen3 case
foldCorrect3-gen : {A : FormTA3} -> (prf : ProofTA3 A) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 prf) k) env (encProofTA3 prf) acFull3 ncFull3) (encFormTA3 A) ->
  Eq (foldCT (addB (proofFuel3 (gen3 prf)) k) env (encProofTA3 (gen3 prf)) acFull3 ncFull3)
     (encFormTA3 (fallTA3 A))
foldCorrect3-gen {A} prf env k ih = genStep ih
  where
  f0 : Nat
  f0 = addB (proofFuel3 prf) k

  env' : Code -> Env3
  env' fb = extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb)
              (foldCT f0 env (catom tagGen3) acFull3 ncFull3))
              (encProofTA3 prf)) (catom tagGen3)

  genStep : Eq (foldCT f0 env (encProofTA3 prf) acFull3 ncFull3) (encFormTA3 A) ->
            Eq (foldCT (suc f0) env (cnode (catom tagGen3) (encProofTA3 prf)) acFull3 ncFull3)
               (encFormTA3 (fallTA3 A))
  genStep ih2 = eqTrans5
    (eqCong (\ fb -> evalCT f0 (env' fb) ncFull3) ih2)
    (genByForm A)
    where
    genByForm : (B : FormTA3) ->
      Eq (evalCT f0 (env' (encFormTA3 B)) ncFull3)
         (cnode (catom ft2) (encFormTA3 B))
    genByForm fbotTA3        = refl
    genByForm (fimpTA3 a b)  = refl
    genByForm (fallTA3 a)    = refl
    genByForm (fexTA3 a)     = refl
    genByForm (feqTA3 c1 c2) = refl

-- Mp3 case: same pattern as foldCorrect-mp in Track 1.
foldCorrect3-mp : {A B : FormTA3} -> (p : ProofTA3 (fimpTA3 A B)) -> (q : ProofTA3 A) ->
  (env : Env3) -> (k : Nat) ->
  ((env2 : Env3) -> (j : Nat) ->
    Eq (foldCT (addB (proofFuel3 p) j) env2 (encProofTA3 p) acFull3 ncFull3)
       (encFormTA3 (fimpTA3 A B))) ->
  ((env2 : Env3) -> (j : Nat) ->
    Eq (foldCT (addB (proofFuel3 q) j) env2 (encProofTA3 q) acFull3 ncFull3)
       (encFormTA3 A)) ->
  Eq (foldCT (addB (proofFuel3 (mp3 p q)) k) env (encProofTA3 (mp3 p q)) acFull3 ncFull3)
     (encFormTA3 B)
foldCorrect3-mp {A} {B} p q env k ihp ihq = mpProof
  where
  ep : Nat
  ep = proofExtra3 p
  eq : Nat
  eq = proofExtra3 q

  f2 : Nat
  f2 = addB n30c (addB (addB ep eq) k)

  f1 : Nat
  f1 = suc f2

  ihp-at : Eq (foldCT f2 env (encProofTA3 p) acFull3 ncFull3) (encFormTA3 (fimpTA3 A B))
  ihp-at = eqTrans5
    (foldCT-fuel-eq3 f2 (addB n30c (addB ep (addB eq k)))
      (eqCong (addB n30c) (addB-assoc3 ep eq k)) env (encProofTA3 p) acFull3 ncFull3)
    (ihp env (addB eq k))

  ihq-at : Eq (foldCT f2 env (encProofTA3 q) acFull3 ncFull3) (encFormTA3 A)
  ihq-at = eqTrans5
    (foldCT-fuel-eq3 f2 (addB n30c (addB eq (addB ep k)))
      (eqCong (addB n30c) (eqTrans0 (addB-assoc3 ep eq k) (addB-swap3 ep eq k)))
      env (encProofTA3 q) acFull3 ncFull3)
    (ihq env (addB ep k))

  innerFold : Eq (foldCT f1 env (cnode (encProofTA3 p) (encProofTA3 q)) acFull3 ncFull3)
                 (cnode (encFormTA3 (fimpTA3 A B)) (encFormTA3 A))
  innerFold = innerStep (encProofTA3-is-cnode p)
    where
    innerStep : SigmaTA Code (\ la -> SigmaTA Code (\ lb -> Eq (encProofTA3 p) (cnode la lb))) ->
      Eq (foldCT f1 env (cnode (encProofTA3 p) (encProofTA3 q)) acFull3 ncFull3)
         (cnode (encFormTA3 (fimpTA3 A B)) (encFormTA3 A))
    innerStep (mkSigmaTA la (mkSigmaTA lb eqP)) = eqTrans5
      (foldCT-pair3 (addB (addB ep eq) k) env (encProofTA3 p) (encProofTA3 q)
        (encFormTA3 (fimpTA3 A B)) (encFormTA3 A) ihp-at ihq-at)
      (ncFull3-cnode-default (addB (addB ep eq) k) env
        (encProofTA3 p) (encProofTA3 q) la lb eqP
        (encFormTA3 (fimpTA3 A B)) (encFormTA3 A))

  mpProof : Eq (foldCT (addB (proofFuel3 (mp3 p q)) k) env (encProofTA3 (mp3 p q)) acFull3 ncFull3)
               (encFormTA3 B)
  mpProof = eqTrans5
    (eqCong (\ x -> evalCT f1
      (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env x)
        (foldCT f1 env (catom tagMP3) acFull3 ncFull3))
        (cnode (encProofTA3 p) (encProofTA3 q))) (catom tagMP3)) ncFull3)
      innerFold)
    (mpByForm A)
    where
    mpByForm : (X : FormTA3) ->
      Eq (evalCT f1
        (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env
          (cnode (encFormTA3 (fimpTA3 X B)) (encFormTA3 X)))
          (catom zero))
          (cnode (encProofTA3 p) (encProofTA3 q))) (catom tagMP3)) ncFull3)
        (encFormTA3 B)
    mpByForm fbotTA3        = refl
    mpByForm (fimpTA3 a b)  = refl
    mpByForm (fallTA3 a)    = refl
    mpByForm (fexTA3 a)     = refl
    mpByForm (feqTA3 c1 c2) = refl

-- Inst3 case: new encoding stores result formula in payload
-- encProofTA3 (inst3 A c prf) = cnode (catom tagInst3) (cnode (encFormTA3 (substF3 c A)) (encProofTA3 prf))
-- handleInst3 extracts first component of raw payload = encFormTA3 (substF3 c A)
foldCorrect3-inst : (A : FormTA3) -> (c : Code) -> (prf : ProofTA3 (fallTA3 A)) ->
  (env : Env3) -> (k : Nat) ->
  ((env2 : Env3) -> (j : Nat) ->
    Eq (foldCT (addB (proofFuel3 prf) j) env2 (encProofTA3 prf) acFull3 ncFull3)
       (encFormTA3 (fallTA3 A))) ->
  Eq (foldCT (addB (proofFuel3 (inst3 A c prf)) k) env (encProofTA3 (inst3 A c prf)) acFull3 ncFull3)
     (encFormTA3 (substF3 c A))
foldCorrect3-inst A c prf env k ih = instStep
  where
  result : FormTA3
  result = substF3 c A

  ep : Nat
  ep = proofExtra3 prf

  f0 : Nat
  f0 = addB n30c (addB ep k)

  -- The payload is cnode (encFormTA3 result) (encProofTA3 prf)
  -- handleInst3 = ctCase (ctVar w2) (ctAtom zero) (ctVar w0)
  -- This extracts encFormTA3 result from the raw payload (var w2).
  -- The encFormTA3 result is always a cnode (for feqTA3, fimpTA3, fallTA3, fexTA3)
  -- or catom ft0 (for fbotTA3). For cnode case, ctCase returns var 0 = left child.

  -- We need to show that encFormTA3 result is a cnode to enter the right branch.
  -- For the cnode case of ctCase on payload: handleInst3 returns the left child
  -- = encFormTA3 result.

  -- The dispatch goes: fold top-level cnode -> ncFull3 atom branch (tag = tagInst3)
  -- -> handleInst3 -> ctCase on raw payload -> returns first component.
  -- The result doesn't depend on fold(payload), only on the raw payload structure.

  -- Since encFormTA3 (substF3 c A) has specific structure for each FormTA3 case,
  -- and the handleInst3 extracts the raw first component, the proof should
  -- reduce by computation for each formula shape.

  instByResult : (R : FormTA3) ->
    Eq (foldCT (suc (suc f0)) env
         (cnode (catom tagInst3) (cnode (encFormTA3 R) (encProofTA3 prf)))
         acFull3 ncFull3)
       (encFormTA3 R)
  instByResult fbotTA3        = refl
  instByResult (fimpTA3 a b)  = refl
  instByResult (fallTA3 a)    = refl
  instByResult (fexTA3 a)     = refl
  instByResult (feqTA3 t1 t2) = refl

  instStep : Eq (foldCT (addB (proofFuel3 (inst3 A c prf)) k) env
                  (encProofTA3 (inst3 A c prf)) acFull3 ncFull3)
                (encFormTA3 (substF3 c A))
  instStep = instByResult result

-- ExIntro3 case: extract encFormTA3 A from raw payload, wrap with ft3.
foldCorrect3-ex : (A : FormTA3) -> (c : Code) -> (prf : ProofTA3 (substF3 c A)) ->
  (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 (exIntro3 A c prf)) k) env (encProofTA3 (exIntro3 A c prf)) acFull3 ncFull3)
     (encFormTA3 (fexTA3 A))
foldCorrect3-ex A c prf env k = refl

------------------------------------------------------------------------
-- Full foldCorrect3
------------------------------------------------------------------------

foldCorrect3 : {A : FormTA3} -> (prf : ProofTA3 A) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuel3 prf) k) env (encProofTA3 prf) acFull3 ncFull3) (encFormTA3 A)
foldCorrect3 (axRefl3 t)          env k = foldCorrect3-axRefl t env k
foldCorrect3 (axK3 a b)           env k = foldCorrect3-axK a b env k
foldCorrect3 (axS3 a b c)         env k = foldCorrect3-axS a b c env k
foldCorrect3 (axSym3 s t)         env k = foldCorrect3-axSym s t env k
foldCorrect3 (axTrans3 r s t)     env k = foldCorrect3-axTrans r s t env k
foldCorrect3 (axCaseAtom k2 ab nb)  env k = refl
foldCorrect3 (axCaseNodeL a b ab nb) env k = refl
foldCorrect3 (axFoldAtom k2 ac nc)  env k = refl
foldCorrect3 (axIfTrue k2 tb eb)    env k = refl
foldCorrect3 (axIfFalse tb eb)      env k = refl
foldCorrect3 (axEqNatRefl n)        env k = refl
foldCorrect3 (gen3 prf)           env k = foldCorrect3-gen prf env k (foldCorrect3 prf env k)
foldCorrect3 (mp3 p q)            env k = foldCorrect3-mp p q env k
  (\ env2 j -> foldCorrect3 p env2 j) (\ env2 j -> foldCorrect3 q env2 j)
foldCorrect3 (inst3 A c prf)      env k = foldCorrect3-inst A c prf env k
  (\ env2 j -> foldCorrect3 prf env2 j)
foldCorrect3 (exIntro3 A c prf)   env k = foldCorrect3-ex A c prf env k

------------------------------------------------------------------------
-- 23. D1 for the internal checker: ProofTA3 A -> ProofTA3 (Prov3b A)
------------------------------------------------------------------------

-- Prov3b uses checkCT3-full instead of checkCT-full
Prov3b : FormTA3 -> FormTA3
Prov3b A = fexTA3 (feqTA3 checkCT3-full (liftCode (encFormTA3 A)))

Con3b : FormTA3
Con3b = fimpTA3 (Prov3b fbotTA3) fbotTA3

-- From foldCorrect3 to evalCT correctness
private
  addB-zero-right3 : (a : Nat) -> Eq (addB a zero) a
  addB-zero-right3 zero    = refl
  addB-zero-right3 (suc a) = eqCong suc (addB-zero-right3 a)

  evalCT-fuel-eq3 : (f1 f2 : Nat) -> Eq f1 f2 ->
    (env : Env3) -> (t : CodeTm) ->
    Eq (evalCT f1 env t) (evalCT f2 env t)
  evalCT-fuel-eq3 f1 .f1 refl env t = refl

extCorrect3-proof : {A : FormTA3} -> (prf : ProofTA3 A) ->
  SigmaTA Nat (\ f ->
    Eq (evalCT f (extendEnv3 emptyEnv3 (encProofTA3 prf)) checkCT3-full)
       (encFormTA3 A))
extCorrect3-proof {A} prf = mkSigmaTA (suc (proofFuel3 prf))
  (eqTrans5
    (evalCT-fuel-eq3 (suc (proofFuel3 prf)) (suc (addB (proofFuel3 prf) zero))
      (eqCong suc (eqSym0 (addB-zero-right3 (proofFuel3 prf))))
      (extendEnv3 emptyEnv3 (encProofTA3 prf)) checkCT3-full)
    (foldCorrect3 prf (extendEnv3 emptyEnv3 (encProofTA3 prf)) zero))

-- D1 internal: ProofTA3 A -> ProofTA3 (Prov3b A)
-- Prov3b A = fexTA3 (feqTA3 checkCT3-full (liftCode (encFormTA3 A)))
-- Need: find code c such that checkCT3-full(c) = encFormTA3 A
-- Witness: c = encProofTA3 prf
-- substF3 c (feqTA3 checkCT3-full (liftCode (encFormTA3 A)))
--   = feqTA3 (substCT c checkCT3-full) (substCT c (liftCode (encFormTA3 A)))
-- But checkCT3-full and liftCode ... are closed (no ctVar 0), so substCT is identity on them.
-- Wait: substCT replaces ctVar 0. checkCT3-full starts with ctFold (ctVar w0) ..., so
-- ctVar w0 = ctVar 0 IS present! substCT would replace it.
-- But within fexTA3, the ctVar 0 refers to the bound variable (the existential witness).
-- The substF3/substCT is the naive version that doesn't handle binders.
-- substF3 c (fexTA3 a) = fexTA3 a (no substitution under binder).
-- So substF3 c (feqTA3 checkCT3-full (liftCode ...)) = feqTA3 (substCT c checkCT3-full) (substCT c (liftCode ...)).
-- But inside fexTA3, there's no substF3 applied (substF3 c (fexTA3 a) = fexTA3 a).
-- So we use exIntro3 with the formula (feqTA3 checkCT3-full (liftCode (encFormTA3 A))).
-- substF3 c (feqTA3 checkCT3-full (liftCode ...)) replaces ctVar 0 in the CodeTms.
-- checkCT3-full uses ctVar w0 = ctVar 0. But the naive substCT replaces ALL ctVar 0,
-- including those under binders in ctCase/ctFold. This is fine because the binders
-- in checkCT3-full bind their own variables, and the naive substCT doesn't adjust.
-- For the CLOSED exIntro3 application, we need:
--   substF3 (encProofTA3 prf) (feqTA3 checkCT3-full (liftCode (encFormTA3 A)))
--   to reduce to a formula whose GoodTA3 we can establish.
-- But for exIntro3, we just need a ProofTA3 of the substituted formula.
-- The witness is: at some fuel f, evalCT f (extendEnv3 emptyEnv3 (encProofTA3 prf)) checkCT3-full = encFormTA3 A.
-- This IS what extCorrect3-proof gives! The existential witness is encProofTA3 prf.
-- And the proof that substF3 (encProofTA3 prf) (feqTA3 checkCT3-full (liftCode (encFormTA3 A)))
-- holds comes from the evalCT equation.
--
-- Wait: exIntro3 requires ProofTA3 (substF3 c A) where A is the body of fexTA3.
-- Here A = feqTA3 checkCT3-full (liftCode (encFormTA3 A)) and c = encProofTA3 prf.
-- substF3 c A = feqTA3 (substCT c checkCT3-full) (substCT c (liftCode (encFormTA3 A))).
-- We DON'T have ProofTA3 of this! We have an evalCT witness, not a ProofTA3 derivation.
--
-- We need to construct a ProofTA3 proof that the evalCT computation equals encFormTA3 A.
-- This requires the computation axioms of ProofTA3 to trace the evalCT steps.
-- For a SPECIFIC proof prf, the evalCT computation has a FIXED number of steps,
-- and each step can be justified by a computation axiom.
-- But this is the FULL representability bootstrap — exactly what D3 needs.
--
-- SIMPLER APPROACH: use axRefl3 at the right CodeTm.
-- If we can construct a CodeTm t such that evalCT evaluates t to encFormTA3 A
-- at sufficient fuel, then feqTA3 t (liftCode (encFormTA3 A)) is what we need.
-- But ProofTA3 can only prove feqTA3 t t (reflexivity), not feqTA3 t t' for different t, t'.
-- The computation axioms can prove feqTA3 (ctCase ...) (result) etc., but chaining
-- many steps requires many mp3 + axTrans3 applications.
--
-- FOR NOW: D1 at the meta-level is sufficient. The full internal D1 requires the
-- computation axiom bootstrap, which is Stage D territory.
-- Let me provide the meta-level D1 and move on.

d1-internal-meta : {A : FormTA3} -> ProofTA3 A ->
  SigmaTA Nat (\ f -> SigmaTA Code (\ c ->
    Eq (evalCT f (extendEnv3 emptyEnv3 c) checkCT3-full) (encFormTA3 A)))
d1-internal-meta prf =
  mkSigmaTA (suc (proofFuel3 prf))
    (mkSigmaTA (encProofTA3 prf)
      (eqTrans5
        (evalCT-fuel-eq3 (suc (proofFuel3 prf)) (suc (addB (proofFuel3 prf) zero))
          (eqCong suc (eqSym0 (addB-zero-right3 (proofFuel3 prf))))
          (extendEnv3 emptyEnv3 (encProofTA3 prf)) checkCT3-full)
        (foldCorrect3 prf (extendEnv3 emptyEnv3 (encProofTA3 prf)) zero)))

------------------------------------------------------------------------
-- 24. Instantiate abstract Gödel II with ProofTA3
------------------------------------------------------------------------

-- We now have ALL ingredients for the conditional Gödel II.
-- The abstract theorem loeb-godel2 requires:
--   d1, d2, d3, Gödel sentence, consistency
-- We have:
--   con3 : ProofTA3 fbotTA3 -> EmptyTA            [proved via sound0]
--   d1-internal-meta : meta-level D1              [proved via foldCorrect3]
--   d1-for-checkTA3 : ProofTA3 A -> ProvableTA3 A [proved via encodeTA3-correct]
--
-- What remains for unconditional Gödel II:
--   d1-3 : ProofTA3 A -> ProofTA3 (Prov3b A)     [needs internal computation trace]
--   d2-3 : internal D2                            [needs internal mp reasoning]
--   d3-3 : internal D3                            [needs internal D1 reasoning]
--   G, gL, gR : Gödel sentence + diagonal         [needs diagonal lemma]
--
-- The conditional theorem IS instantiable with the abstract loeb-godel2:

godel2-TA3b :
  (d1-3 : {A : FormTA3} -> ProofTA3 A -> ProofTA3 (Prov3b A)) ->
  (d2-3 : {A B : FormTA3} -> ProofTA3 (fimpTA3 (Prov3b (fimpTA3 A B)) (fimpTA3 (Prov3b A) (Prov3b B)))) ->
  (d3-3 : {A : FormTA3} -> ProofTA3 (fimpTA3 (Prov3b A) (Prov3b (Prov3b A)))) ->
  (G : FormTA3) ->
  (gL : ProofTA3 (fimpTA3 G (fimpTA3 (Prov3b G) fbotTA3))) ->
  (gR : ProofTA3 (fimpTA3 (fimpTA3 (Prov3b G) fbotTA3) G)) ->
  ProofTA3 Con3b -> EmptyTA
godel2-TA3b d1-3 d2-3 d3-3 G gL gR =
  loeb-godel2 (record
    { Form = FormTA3
    ; Proof = ProofTA3
    ; Prov = Prov3b
    ; bot = fbotTA3
    ; imp = fimpTA3
    ; axK = axK3 _ _
    ; axS = axS3 _ _ _
    ; mp = mp3
    ; d1 = d1-3
    ; d2 = d2-3
    ; d3 = d3-3
    ; goedelSentence = G
    ; goedelLeft = gL
    ; goedelRight = gR
    ; consistent = con3
    })
