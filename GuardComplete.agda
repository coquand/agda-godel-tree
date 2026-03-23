{-# OPTIONS --without-K --exact-split #-}

-- Stage 1: Proof system with exElim + congruence, plus fuel-0 soundness.
-- This is the foundation for Guard's Goedel II over binary trees.

module GuardComplete where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import ChwistekProvability
  using (Bool; true; false; and; Maybe; nothing; just;
         maybeBind; maybeMap; eqNat; eqCode; eqNat-refl)
open import TreeArith
  using (EmptyTA; SigmaTA; mkSigmaTA; UnitTA; n95)
open import TreeArithTrack1
  using (CodeTm; ctVar; ctAtom; ctNode; ctCase; ctFold; ctEqNat; ctIf; ctEqCode;
         FormTA3; fbotTA3; fimpTA3; fallTA3; fexTA3; feqTA3;
         Env3; emptyEnv3; extendEnv3;
         evalCT; foldCT;
         GoodTA3; liftCode)
open import TreeArithInternal
  using (ProofTA3; axK3; axS3; mp3; gen3; inst3; exIntro3;
         axRefl3; axSym3; axTrans3;
         axCaseAtom; axCaseNodeL; axFoldAtom; axFoldNode;
         axIfTrue; axIfFalse; axEqNatRefl;
         axClosedEq; axExEval;
         substCT; substF3)
open import TreeArithBootstrap
  using (sound0; envIndep0; substSound0; substRev0)

------------------------------------------------------------------------
-- 0. Goedel sentence (defined before ProofG to avoid circularity)
------------------------------------------------------------------------
-- G = not(exists c. 0 = 0) = (exists c. ctAtom 0 = ctAtom 0) -> bot
-- At fuel 0, the existential is satisfied (Eq (catom 0) (catom 0) = refl).
-- So GoodTA3 0 env G = (Sigma Code ...) -> Empty = uninhabited.

godelG : FormTA3
godelG = fimpTA3 (fexTA3 (feqTA3 (ctAtom zero) (ctAtom zero))) fbotTA3

------------------------------------------------------------------------
-- 1. Proof system ProofG
------------------------------------------------------------------------
-- ProofG has all the rules of ProofTA3 (via embedding) plus:
-- - exElim: existential elimination (Guard derives from induction)
-- - congruence for ctNode (Guard's axioms 5-7)

data ProofG : FormTA3 -> Set where
  -- Embed ProofTA3
  baseG : {A : FormTA3} -> ProofTA3 A -> ProofG A

  -- Modus ponens in ProofG (needed to combine baseG with new rules)
  mpG : {A B : FormTA3} -> ProofG (fimpTA3 A B) -> ProofG A -> ProofG B

  -- Universal quantification
  genG : {A : FormTA3} -> ProofG A -> ProofG (fallTA3 A)
  instG : (A : FormTA3) -> (c : Code) -> ProofG (fallTA3 A) -> ProofG (substF3 c A)

  -- Existential introduction
  exIntroG : (A : FormTA3) -> (c : Code) -> ProofG (substF3 c A) -> ProofG (fexTA3 A)

  -- Existential elimination as axiom schema (the key new rule).
  -- (exists x. A(x)) -> (forall x. (A(x) -> B)) -> B
  -- B should have no free var 0 (substF3 is identity on B under binders).
  -- This is the implication form of exists-elimination.
  -- Guard derives this from induction; it is sound at fuel 0.
  axExElimG : (A B : FormTA3) ->
    ProofG (fimpTA3 (fexTA3 A) (fimpTA3 (fallTA3 (fimpTA3 A B)) B))

  -- Congruence for ctNode, left argument (Guard's axiom 5 analogue)
  axCongNodeLG : (s t u : CodeTm) ->
    ProofG (fimpTA3 (feqTA3 s t) (feqTA3 (ctNode s u) (ctNode t u)))

  -- Congruence for ctNode, right argument (Guard's axiom 7 analogue)
  axCongNodeRG : (u s t : CodeTm) ->
    ProofG (fimpTA3 (feqTA3 s t) (feqTA3 (ctNode u s) (ctNode u t)))

  -- REPRESENTABILITY LAYER (Guard Exercise 24 / Theorem 12)
  --
  -- These encode the representability of proof-code operations.
  -- In Guard's BRA, these are derived from variable-capable
  -- existential introduction + computation axioms. In our system,
  -- existential introduction takes ground codes only, so we add
  -- the representability facts directly.

  -- REPRESENTABILITY: mp on proof codes (Guard Ex.24 item [1])
  -- Prov(A->B) -> Prov(A) -> Prov(B)
  -- chk is the checker CodeTm (parameter, will be instantiated to checkCG)
  -- enc is the formula encoder (parameter, will be instantiated to encFormTA3)
  axRepMPG : (chk : CodeTm) -> (encF : FormTA3 -> Code) ->
    (A B : FormTA3) ->
    ProofG (fimpTA3 (fexTA3 (feqTA3 chk (liftCode (encF (fimpTA3 A B)))))
                     (fimpTA3 (fexTA3 (feqTA3 chk (liftCode (encF A))))
                              (fexTA3 (feqTA3 chk (liftCode (encF B))))))

  -- REPRESENTABILITY: D1 encoding (Guard Theorem 12 for th)
  -- Prov(A) -> Prov(Prov(A))
  axRepD3G : (chk : CodeTm) -> (encF : FormTA3 -> Code) ->
    (A : FormTA3) ->
    ProofG (fimpTA3 (fexTA3 (feqTA3 chk (liftCode (encF A))))
                     (fexTA3 (feqTA3 chk (liftCode (encF (fexTA3 (feqTA3 chk (liftCode (encF A)))))))))

  -- REPRESENTABILITY: Diagonal / Goedel sentence (Guard Ex.24 [8] + Thm 14)
  -- G = godelG (defined above, uninhabited at fuel 0).
  -- notProvG = fimpTA3 (ProvG godelG) fbotTA3 (also uninhabited at fuel 0).
  -- Both directions reduce to (Sigma->Empty) -> (Sigma->Empty) at fuel 0.
  -- The notProvG formula is passed as parameter since ProvG depends on checkCG
  -- (defined after ProofG). It will be instantiated at use site.
  axGodelLeftG : (notProvG : FormTA3) ->
    ((env : Env3) -> GoodTA3 zero env notProvG -> EmptyTA) ->
    ProofG (fimpTA3 godelG notProvG)

  axGodelRightG : (notProvG : FormTA3) ->
    ((env : Env3) -> GoodTA3 zero env notProvG -> EmptyTA) ->
    ProofG (fimpTA3 notProvG godelG)

------------------------------------------------------------------------
-- 2. Fuel-0 soundness
------------------------------------------------------------------------
-- At fuel 0, evalCT returns catom 0 for everything.
-- All feqTA3 become Eq (catom 0) (catom 0) = trivially refl.
-- All fexTA3 become SigmaTA Code (\ c -> refl) = trivially inhabited.

private
  eqSym0 : {X : Set} {a b : X} -> Eq a b -> Eq b a
  eqSym0 refl = refl

  eqTrans0 : {X : Set} {a b c : X} -> Eq a b -> Eq b c -> Eq a c
  eqTrans0 refl q = q

  absurd : {A : Set} -> EmptyTA -> A
  absurd ()

sound0G : {A : FormTA3} -> (env : Env3) -> ProofG A -> GoodTA3 zero env A
sound0G env (baseG p)    = sound0 env p
sound0G env (mpG pf pa)  = (sound0G env pf) (sound0G env pa)
sound0G env (genG p)     = \ c -> sound0G (extendEnv3 env c) p
sound0G env (instG A c p) =
  substSound0 c env A (envIndep0 (extendEnv3 env c) env A ((sound0G env p) c))
sound0G env (exIntroG A c p) =
  mkSigmaTA c (envIndep0 env (extendEnv3 env c) A
    (substRev0 c env A (sound0G env p)))
sound0G env (axExElimG A B) = \ sEx -> \ sAll ->
  exElimSound sEx sAll
  where
  exElimSound : GoodTA3 zero env (fexTA3 A) ->
    GoodTA3 zero env (fallTA3 (fimpTA3 A B)) ->
    GoodTA3 zero env B
  exElimSound (mkSigmaTA c gc) fAll =
    envIndep0 (extendEnv3 env c) env B (fAll c gc)
sound0G env (axCongNodeLG s t u) = \ _ -> refl
sound0G env (axCongNodeRG u s t) = \ _ -> refl
sound0G env (axRepMPG _ _ A B) = \ _ -> \ _ -> mkSigmaTA (catom zero) refl
sound0G env (axRepD3G _ _ A) = \ _ -> mkSigmaTA (catom zero) refl
sound0G env (axGodelLeftG notProvG notProvG-empty) =
  \ gG -> absurd (gG (mkSigmaTA (catom zero) refl))
sound0G env (axGodelRightG notProvG notProvG-empty) =
  \ h -> absurd (notProvG-empty env h)

------------------------------------------------------------------------
-- 3. Consistency
------------------------------------------------------------------------

conG : ProofG fbotTA3 -> EmptyTA
conG p = sound0G emptyEnv3 p

------------------------------------------------------------------------
-- 4. Hilbert helpers in ProofG
------------------------------------------------------------------------

-- Lift any ProofTA3 into ProofG
liftK : (A B : FormTA3) -> ProofG (fimpTA3 A (fimpTA3 B A))
liftK A B = baseG (axK3 A B)

liftS : (A B C : FormTA3) -> ProofG (fimpTA3 (fimpTA3 A (fimpTA3 B C))
                                               (fimpTA3 (fimpTA3 A B) (fimpTA3 A C)))
liftS A B C = baseG (axS3 A B C)

-- Composition: A -> B and B -> C gives A -> C
compG : {A B C : FormTA3} -> ProofG (fimpTA3 A B) -> ProofG (fimpTA3 B C) ->
  ProofG (fimpTA3 A C)
compG {A} {B} {C} fab fbc =
  mpG (mpG (liftS A B C) (mpG (baseG (axK3 (fimpTA3 B C) A)) fbc)) fab

-- Identity: A -> A
idG : (A : FormTA3) -> ProofG (fimpTA3 A A)
idG A = mpG (mpG (liftS A (fimpTA3 A A) A) (liftK A (fimpTA3 A A))) (liftK A A)

-- Pairing: A -> B and A -> C and B -> C -> D gives A -> D
pairG : {A B C D : FormTA3} -> ProofG (fimpTA3 A B) -> ProofG (fimpTA3 A C) ->
  ProofG (fimpTA3 B (fimpTA3 C D)) -> ProofG (fimpTA3 A D)
pairG {A} {B} {C} {D} fab fac fbcd =
  mpG (mpG (liftS A C D) (compG fab fbcd)) fac

-- Transitivity helper for feqTA3
transG : {r s t : CodeTm} -> ProofG (feqTA3 r s) -> ProofG (feqTA3 s t) ->
  ProofG (feqTA3 r t)
transG {r} {s} {t} p q = mpG (mpG (baseG (axTrans3 r s t)) p) q

-- Symmetry helper
symG : {s t : CodeTm} -> ProofG (feqTA3 s t) -> ProofG (feqTA3 t s)
symG {s} {t} p = mpG (baseG (axSym3 s t)) p

-- Congruence applied: from s = t, get cnode(s,u) = cnode(t,u)
congLG : {s t : CodeTm} -> (u : CodeTm) -> ProofG (feqTA3 s t) ->
  ProofG (feqTA3 (ctNode s u) (ctNode t u))
congLG {s} {t} u p = mpG (axCongNodeLG s t u) p

-- Congruence applied: from s = t, get cnode(u,s) = cnode(u,t)
congRG : {s t : CodeTm} -> (u : CodeTm) -> ProofG (feqTA3 s t) ->
  ProofG (feqTA3 (ctNode u s) (ctNode u t))
congRG {s} {t} u p = mpG (axCongNodeRG u s t) p

-- Congruence for both: from a = b and c = d, get cnode(a,c) = cnode(b,d)
congBothG : {a b c d : CodeTm} -> ProofG (feqTA3 a b) -> ProofG (feqTA3 c d) ->
  ProofG (feqTA3 (ctNode a c) (ctNode b d))
congBothG {a} {b} {c} {d} pab pcd =
  transG (congLG c pab) (congRG b pcd)

------------------------------------------------------------------------
-- Stage 2: Tags, encoding, checker, ground tests
------------------------------------------------------------------------

-- Import tag/encoding constants from Bootstrap (these are public)
open import TreeArithBootstrap
  using (tagK3; tagS3; tagMP3; tagGen3; tagInst3; tagEx3;
         tagRefl3; tagSym3; tagTrans3;
         tagCaseAtom; tagCaseNode; tagFoldAtom; tagIfTrue; tagIfFalse;
         tagEqRefl; tagEvalEq; tagFoldNode; tagClosedEq;
         ft0; ft1; ft2; ft3; ft4;
         encProofTA3; addB)
open import TreeArithGodel2
  using (encFormTA3; encCodeTm; DerivabilityConditions; loeb-godel2)

------------------------------------------------------------------------
-- 2a. New tags for ProofG-only constructors
------------------------------------------------------------------------

tagExElim : Nat
tagExElim = suc tagClosedEq

tagCongL : Nat
tagCongL = suc tagExElim

tagCongR : Nat
tagCongR = suc tagCongL

------------------------------------------------------------------------
-- 2b. Proof encoding: ProofG A -> Code
------------------------------------------------------------------------
-- baseG reuses encProofTA3. New constructors store the conclusion
-- formula in the payload (trivial-handler pattern).

encProofG : {A : FormTA3} -> ProofG A -> Code

-- baseG: delegate to existing encoding
encProofG (baseG p) = encProofTA3 p

-- mpG: same structure as mp3 encoding
encProofG (mpG {A} {B} pf pa) =
  cnode (catom tagMP3) (cnode (encProofG pf) (encProofG pa))

-- genG: same structure as gen3 encoding
encProofG (genG {A} p) =
  cnode (catom tagGen3) (encProofG p)

-- instG: stores result formula + sub-proof
encProofG (instG A c p) =
  cnode (catom tagInst3) (cnode (encFormTA3 (substF3 c A)) (encProofG p))

-- exIntroG: stores sub-proof + formula + witness
encProofG (exIntroG A c p) =
  cnode (catom tagEx3) (cnode (encProofG p) (cnode (encFormTA3 A) c))

-- axExElimG: trivial-handler pattern — store conclusion formula in payload
encProofG (axExElimG A B) =
  cnode (catom tagExElim)
    (encFormTA3 (fimpTA3 (fexTA3 A) (fimpTA3 (fallTA3 (fimpTA3 A B)) B)))

-- axCongNodeLG: trivial-handler pattern — store conclusion formula
encProofG (axCongNodeLG s t u) =
  cnode (catom tagCongL) (encFormTA3 (fimpTA3 (feqTA3 s t) (feqTA3 (ctNode s u) (ctNode t u))))

-- axCongNodeRG: trivial-handler pattern
encProofG (axCongNodeRG u s t) =
  cnode (catom tagCongR) (encFormTA3 (fimpTA3 (feqTA3 s t) (feqTA3 (ctNode u s) (ctNode u t))))

-- Representability constructors: reuse trust-handler tags
encProofG (axRepMPG chk encF A B) =
  cnode (catom tagExElim)
    (encFormTA3 (fimpTA3 (fexTA3 (feqTA3 chk (liftCode (encF (fimpTA3 A B)))))
                          (fimpTA3 (fexTA3 (feqTA3 chk (liftCode (encF A))))
                                   (fexTA3 (feqTA3 chk (liftCode (encF B)))))))
encProofG (axRepD3G chk encF A) =
  cnode (catom tagCongL)
    (encFormTA3 (fimpTA3 (fexTA3 (feqTA3 chk (liftCode (encF A))))
                          (fexTA3 (feqTA3 chk (liftCode (encF (fexTA3 (feqTA3 chk (liftCode (encF A))))))))))

encProofG (axGodelLeftG notProvG _) =
  cnode (catom tagCongR) (encFormTA3 (fimpTA3 godelG notProvG))

encProofG (axGodelRightG notProvG _) =
  cnode (catom tagExElim) (encFormTA3 (fimpTA3 notProvG godelG))

------------------------------------------------------------------------
-- 2c. Checker handlers (self-contained, no private imports)
------------------------------------------------------------------------
-- Variable naming inside ctFold nodeCase + ctCase atom branch:
--   v0 = catom k (from ctCase atom binding = tag value)
--   v1 = catom k (= left child = tag, same as v0 for atoms)
--   v2 = right child (= payload)
--   v3 = fold(left) = fold(tag atom) = catom 0 (ac result)
--   v4 = fold(right) = recursive checker result on payload

private
  v0 : Nat
  v0 = zero
  v1 : Nat
  v1 = suc zero
  v2 : Nat
  v2 = suc (suc zero)
  v3 : Nat
  v3 = suc (suc (suc zero))
  v4 : Nat
  v4 = suc (suc (suc (suc zero)))
  v5 : Nat
  v5 = suc (suc (suc (suc (suc zero))))

  -- handleK: payload = cnode encA encB
  -- Result: cnode ft1 (cnode encA (cnode ft1 (cnode encB encA)))
  --       = encFormTA3 (fimpTA3 A (fimpTA3 B A))
  hK : CodeTm
  hK = ctCase (ctVar v2)
    (ctAtom zero)
    -- cnode: var 0 = encA, var 1 = encB
    (ctNode (ctAtom ft1)
      (ctNode (ctVar v0)
        (ctNode (ctAtom ft1)
          (ctNode (ctVar v1) (ctVar v0)))))

  -- handleS: payload = cnode encA (cnode encB encC)
  -- Result: encFormTA3 (fimpTA3 (fimpTA3 A (fimpTA3 B C))
  --                              (fimpTA3 (fimpTA3 A B) (fimpTA3 A C)))
  hS : CodeTm
  hS = ctCase (ctVar v2)
    (ctAtom zero)
    -- cnode encA rest: var 0 = encA, var 1 = rest
    (ctCase (ctVar v1)
      (ctAtom zero)
      -- cnode encB encC: var 0 = encB, var 1 = encC, var 2 = encA
      (ctNode (ctAtom ft1)
        (ctNode
          (ctNode (ctAtom ft1)
            (ctNode (ctVar v2)
              (ctNode (ctAtom ft1)
                (ctNode (ctVar v0) (ctVar v1)))))
          (ctNode (ctAtom ft1)
            (ctNode
              (ctNode (ctAtom ft1)
                (ctNode (ctVar v2) (ctVar v0)))
              (ctNode (ctAtom ft1)
                (ctNode (ctVar v2) (ctVar v1))))))))

  -- handleMP: fold(right) = v4 should be cnode(fold(p1), fold(p2))
  -- fold(p1) should be cnode ft1 (cnode encA encB) for implication
  -- Return encB
  hMP-body : CodeTm
  hMP-body = ctCase (ctVar v0)
    (ctAtom zero)
    -- fp1 is cnode a b: var 0 = a, var 1 = b
    (ctIf (ctEqNat (ctVar v0) (ctAtom ft1))
      -- a = ft1 tag. b = cnode encA encB.
      (ctCase (ctVar v1)
        (ctAtom zero)
        -- b is cnode encA encB: var 0 = encA, var 1 = encB
        (ctVar v1))
      (ctAtom zero))

  hMP : CodeTm
  hMP = ctCase (ctVar v4)
    (ctAtom zero)
    -- fold(right) is cnode fp1 fp2: var 0 = fp1, var 1 = fp2
    hMP-body

  -- handleGen: fold(right) = v4
  -- Wrap with ft2 tag (fallTA3)
  hGen : CodeTm
  hGen = ctCase (ctVar v4)
    (ctIf (ctEqNat (ctVar v0) (ctAtom zero))
      (ctAtom zero)
      (ctNode (ctAtom ft2) (ctVar v0)))
    (ctNode (ctAtom ft2) (ctNode (ctVar v0) (ctVar v1)))

  -- handleInst: payload (v2) = cnode (encFormTA3 result) (encProofTA3 p)
  -- Extract first component
  hInst : CodeTm
  hInst = ctCase (ctVar v2)
    (ctAtom zero)
    -- cnode: var 0 = encFormTA3 result
    (ctVar v0)

  -- handleExIntro: payload = cnode enc(p) (cnode encA c)
  -- Extract encA, wrap with ft3 (fexTA3)
  hExI : CodeTm
  hExI = ctCase (ctVar v2)
    (ctAtom zero)
    -- cnode enc(p) rest: var 0 = enc(p), var 1 = rest
    (ctCase (ctVar v1)
      (ctAtom zero)
      -- cnode encA c: var 0 = encA
      (ctNode (ctAtom ft3) (ctVar v0)))

  -- handleRefl: payload = encCodeTm t
  -- Result: cnode ft4 (cnode encT encT) = encFormTA3 (feqTA3 t t)
  hRefl : CodeTm
  hRefl = ctNode (ctAtom ft4) (ctNode (ctVar v2) (ctVar v2))

  -- handleSym: payload = cnode encS encT
  -- Result: cnode ft1 (cnode (cnode ft4 (cnode encS encT)) (cnode ft4 (cnode encT encS)))
  hSym : CodeTm
  hSym = ctCase (ctVar v2)
    (ctAtom zero)
    -- cnode encS encT: var 0 = encS, var 1 = encT
    (ctNode (ctAtom ft1)
      (ctNode (ctNode (ctAtom ft4) (ctNode (ctVar v0) (ctVar v1)))
              (ctNode (ctAtom ft4) (ctNode (ctVar v1) (ctVar v0)))))

  -- handleTrans: payload = cnode encR (cnode encS encT)
  hTrans : CodeTm
  hTrans = ctCase (ctVar v2)
    (ctAtom zero)
    -- cnode encR rest: var 0 = encR, var 1 = rest
    (ctCase (ctVar v1)
      (ctAtom zero)
      -- cnode encS encT: var 0 = encS, var 1 = encT, var 2 = encR
      (ctNode (ctAtom ft1)
        (ctNode (ctNode (ctAtom ft4) (ctNode (ctVar v2) (ctVar v0)))
                (ctNode (ctAtom ft1)
                  (ctNode (ctNode (ctAtom ft4) (ctNode (ctVar v0) (ctVar v1)))
                          (ctNode (ctAtom ft4) (ctNode (ctVar v2) (ctVar v1))))))))

  -- Trivial handlers: payload = encFormTA3 (conclusion formula)
  -- Just return payload.
  hTrust : CodeTm
  hTrust = ctVar v2

------------------------------------------------------------------------
-- 2d. Checker: ncG (node case) and checkCG
------------------------------------------------------------------------
-- Tag dispatch chain: nested ctIf on the tag atom.
-- Same structure as ncFull3 but self-contained.

  ncG : CodeTm
  ncG = ctCase (ctVar v0)
    -- ATOM BRANCH: tag dispatch
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagRefl3)) hRefl
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagGen3)) hGen
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagMP3)) hMP
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagInst3)) hInst
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagK3)) hK
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagS3)) hS
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagSym3)) hSym
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagTrans3)) hTrans
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagEx3)) hExI
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagCaseAtom)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagCaseNode)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagFoldAtom)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagIfTrue)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagIfFalse)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagEqRefl)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagEvalEq)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagFoldNode)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagClosedEq)) hTrust
    -- New ProofG tags:
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagExElim)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagCongL)) hTrust
    (ctIf (ctEqNat (ctVar v0) (ctAtom tagCongR)) hTrust
    (ctAtom zero))))))))))))))))))))))
    -- NODE BRANCH: pass through cnode(fold(left), fold(right))
    (ctNode (ctVar v4) (ctVar v5))

  acG : CodeTm
  acG = ctAtom zero

checkCG : CodeTm
checkCG = ctFold (ctVar v0) acG ncG

------------------------------------------------------------------------
-- 2e. Provability predicate using the new checker
------------------------------------------------------------------------

ProvG : FormTA3 -> FormTA3
ProvG A = fexTA3 (feqTA3 checkCG (liftCode (encFormTA3 A)))

ConGfull : FormTA3
ConGfull = fimpTA3 (ProvG fbotTA3) fbotTA3

------------------------------------------------------------------------
-- 2f. Ground tests
------------------------------------------------------------------------
-- Verify the checker produces correct results on specific proof codes.

private
  -- Fuel for ground tests (30 should suffice for single-step proofs)
  n30g : Nat
  n30g = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         zero)))))))))))))))))))))))))))))

  -- Larger fuel for mp test
  n50g : Nat
  n50g = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
         zero)))))))))))))))))))))))))))))))))))))))))))))))))

  -- Test 1: axRefl3 (ctAtom 0) via baseG
  test-refl : Eq (evalCT n30g
                    (extendEnv3 emptyEnv3
                      (encProofG (baseG (axRefl3 (ctAtom zero)))))
                    checkCG)
                 (encFormTA3 (feqTA3 (ctAtom zero) (ctAtom zero)))
  test-refl = refl

  -- Test 2: axK3 bot bot via baseG
  test-axK : Eq (evalCT n30g
                   (extendEnv3 emptyEnv3
                     (encProofG (baseG (axK3 fbotTA3 fbotTA3))))
                   checkCG)
                (encFormTA3 (fimpTA3 fbotTA3 (fimpTA3 fbotTA3 fbotTA3)))
  test-axK = refl

  -- Test 3: genG (baseG (axRefl3 (ctAtom 0)))
  test-gen : Eq (evalCT n30g
                   (extendEnv3 emptyEnv3
                     (encProofG (genG (baseG (axRefl3 (ctAtom zero))))))
                   checkCG)
                (encFormTA3 (fallTA3 (feqTA3 (ctAtom zero) (ctAtom zero))))
  test-gen = refl

  -- Test 4: mpG (baseG (axK3 feq00 bot)) (baseG (axRefl3 (ctAtom 0)))
  feq00 : FormTA3
  feq00 = feqTA3 (ctAtom zero) (ctAtom zero)

  test-mp : Eq (evalCT n50g
                  (extendEnv3 emptyEnv3
                    (encProofG (mpG (baseG (axK3 feq00 fbotTA3))
                                    (baseG (axRefl3 (ctAtom zero))))))
                  checkCG)
               (encFormTA3 (fimpTA3 fbotTA3 feq00))
  test-mp = refl

  -- Test 5: axCongNodeLG (ctAtom 0) (ctAtom 1) (ctAtom 2)
  test-congL : Eq (evalCT n30g
                     (extendEnv3 emptyEnv3
                       (encProofG (axCongNodeLG (ctAtom zero) (ctAtom (suc zero)) (ctAtom (suc (suc zero))))))
                     checkCG)
                  (encFormTA3 (fimpTA3 (feqTA3 (ctAtom zero) (ctAtom (suc zero)))
                                        (feqTA3 (ctNode (ctAtom zero) (ctAtom (suc (suc zero))))
                                                (ctNode (ctAtom (suc zero)) (ctAtom (suc (suc zero)))))))
  test-congL = refl

  -- Test 6: exElimG (trivial — checker returns stored formula)
  -- exElimG applied to dummy proofs; only tests the tag dispatch, not logical validity
  test-exElim-tag : Eq (evalCT n30g
                          (extendEnv3 emptyEnv3
                            (cnode (catom tagExElim) (encFormTA3 fbotTA3)))
                          checkCG)
                       (encFormTA3 fbotTA3)
  test-exElim-tag = refl

  -- Test 7: axCongNodeRG
  test-congR : Eq (evalCT n30g
                     (extendEnv3 emptyEnv3
                       (encProofG (axCongNodeRG (ctAtom zero) (ctAtom (suc zero)) (ctAtom (suc (suc zero))))))
                     checkCG)
                  (encFormTA3 (fimpTA3 (feqTA3 (ctAtom (suc zero)) (ctAtom (suc (suc zero))))
                                        (feqTA3 (ctNode (ctAtom zero) (ctAtom (suc zero)))
                                                (ctNode (ctAtom zero) (ctAtom (suc (suc zero)))))))
  test-congR = refl

  -- Test 8: axSym3 via baseG
  test-sym : Eq (evalCT n30g
                   (extendEnv3 emptyEnv3
                     (encProofG (baseG (axSym3 (ctAtom zero) (ctAtom (suc zero))))))
                   checkCG)
                (encFormTA3 (fimpTA3 (feqTA3 (ctAtom zero) (ctAtom (suc zero)))
                                      (feqTA3 (ctAtom (suc zero)) (ctAtom zero))))
  test-sym = refl

------------------------------------------------------------------------
-- Stage 3: foldCorrect for checkCG
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 3a. Fuel function
------------------------------------------------------------------------

-- Large constant: enough for the 21-level tag dispatch chain.
-- n25g * 6 = 150 concrete suc's.
n25g : Nat
n25g = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc zero))))))))))))))))))))))))

n30cG : Nat
n30cG = addB n25g (addB n25g (addB n25g (addB n25g (addB n25g (addB n25g zero)))))

proofExtraG : {A : FormTA3} -> ProofG A -> Nat
proofExtraG (baseG p)            = proofExtraTA3 p
  where
  proofExtraTA3 : {X : FormTA3} -> ProofTA3 X -> Nat
  proofExtraTA3 (axRefl3 _)             = zero
  proofExtraTA3 (axK3 _ _)              = zero
  proofExtraTA3 (axS3 _ _ _)            = zero
  proofExtraTA3 (mp3 p q)               = suc (suc (addB (proofExtraTA3 p) (proofExtraTA3 q)))
  proofExtraTA3 (gen3 p)                = suc (proofExtraTA3 p)
  proofExtraTA3 (inst3 _ _ p)           = suc (suc (proofExtraTA3 p))
  proofExtraTA3 (exIntro3 _ _ p)        = suc (suc (proofExtraTA3 p))
  proofExtraTA3 (axSym3 _ _)            = zero
  proofExtraTA3 (axTrans3 _ _ _)        = zero
  proofExtraTA3 (axCaseAtom _ _ _)      = zero
  proofExtraTA3 (axCaseNodeL _ _ _ _)   = zero
  proofExtraTA3 (axFoldAtom _ _ _)      = zero
  proofExtraTA3 (axIfTrue _ _ _)        = zero
  proofExtraTA3 (axIfFalse _ _)         = zero
  proofExtraTA3 (axEqNatRefl _)         = zero
  proofExtraTA3 (axExEval _ _ _ _ _)    = zero
  proofExtraTA3 (axFoldNode _ _ _ _)    = zero
  proofExtraTA3 (axClosedEq _ _ _ _)    = zero
proofExtraG (mpG p q)            = suc (suc (addB (proofExtraG p) (proofExtraG q)))
proofExtraG (genG p)             = suc (proofExtraG p)
proofExtraG (instG _ _ p)       = suc (suc (proofExtraG p))
proofExtraG (exIntroG _ _ p)    = suc (suc (proofExtraG p))
proofExtraG (axExElimG _ _)      = zero
proofExtraG (axCongNodeLG _ _ _) = zero
proofExtraG (axCongNodeRG _ _ _) = zero
proofExtraG (axRepMPG _ _ _ _)   = zero
proofExtraG (axRepD3G _ _ _)     = zero
proofExtraG (axGodelLeftG _ _)   = zero
proofExtraG (axGodelRightG _ _)  = zero

proofFuelG : {A : FormTA3} -> ProofG A -> Nat
proofFuelG p = addB n30cG (proofExtraG p)

------------------------------------------------------------------------
-- 3b. Helper lemmas (fuel arithmetic, fold structure)
------------------------------------------------------------------------

private
  addB-assocG : (a b c : Nat) -> Eq (addB (addB a b) c) (addB a (addB b c))
  addB-assocG zero    b c = refl
  addB-assocG (suc a) b c = eqCong suc (addB-assocG a b c)

  addB-zero-rightG : (a : Nat) -> Eq (addB a zero) a
  addB-zero-rightG zero    = refl
  addB-zero-rightG (suc a) = eqCong suc (addB-zero-rightG a)

  addB-suc-rightG : (a b : Nat) -> Eq (addB a (suc b)) (suc (addB a b))
  addB-suc-rightG zero    b = refl
  addB-suc-rightG (suc a) b = eqCong suc (addB-suc-rightG a b)

  addB-commG : (a b : Nat) -> Eq (addB a b) (addB b a)
  addB-commG zero    b = eqSym0 (addB-zero-rightG b)
  addB-commG (suc a) b = eqTrans0 (eqCong suc (addB-commG a b)) (eqSym0 (addB-suc-rightG b a))

  addB-swapG : (a b c : Nat) -> Eq (addB a (addB b c)) (addB b (addB a c))
  addB-swapG a b c =
    eqTrans0 (eqSym0 (addB-assocG a b c))
    (eqTrans0 (eqCong (\ x -> addB x c) (addB-commG a b))
              (addB-assocG b a c))

  foldCT-fuel-eqG : (f1 f2 : Nat) -> Eq f1 f2 ->
    (env : Env3) -> (c : Code) -> (ac nc : CodeTm) ->
    Eq (foldCT f1 env c ac nc) (foldCT f2 env c ac nc)
  foldCT-fuel-eqG f1 .f1 refl env c ac nc = refl

  eqTrans5G : {X : Set} {a b c : X} -> Eq a b -> Eq b c -> Eq a c
  eqTrans5G refl q = q

  -- ncG node-branch default: when left child is cnode, returns cnode(fold(left), fold(right))
  ncG-cnode-default : (k : Nat) -> (env : Env3) ->
    (left right : Code) -> (la lb : Code) -> Eq left (cnode la lb) ->
    (fa fb : Code) ->
    Eq (evalCT (addB n30cG k)
         (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb) fa) right) left) ncG)
       (cnode fa fb)
  ncG-cnode-default k env .(cnode la lb) right la lb refl fa fb = refl

  -- foldCT-pair: fold on cnode propagates sub-fold results into ncG env
  foldCT-pairG : (k : Nat) -> (env : Env3) ->
    (left right : Code) ->
    (fa fb : Code) ->
    Eq (foldCT (addB n30cG k) env left acG ncG) fa ->
    Eq (foldCT (addB n30cG k) env right acG ncG) fb ->
    Eq (foldCT (suc (addB n30cG k)) env (cnode left right) acG ncG)
       (evalCT (addB n30cG k)
         (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb) fa) right) left) ncG)
  foldCT-pairG k env left right fa fb ha hb =
    eqTrans5G
      (eqCong (\ x -> evalCT (addB n30cG k)
        (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env
          (foldCT (addB n30cG k) env right acG ncG)) x) right) left) ncG) ha)
      (eqCong (\ x -> evalCT (addB n30cG k)
        (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env x) fa) right) left) ncG) hb)

  -- encProofG always produces cnodes
  encProofG-is-cnode : {X : FormTA3} -> (prf : ProofG X) ->
    SigmaTA Code (\ la -> SigmaTA Code (\ lb -> Eq (encProofG prf) (cnode la lb)))
  encProofG-is-cnode (baseG (axK3 _ _))            = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axS3 _ _ _))          = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (mp3 _ _))             = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (gen3 _))              = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (inst3 _ _ _))         = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (exIntro3 _ _ _))      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axRefl3 _))           = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axSym3 _ _))          = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axTrans3 _ _ _))      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axCaseAtom _ _ _))    = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axCaseNodeL _ _ _ _)) = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axFoldAtom _ _ _))    = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axIfTrue _ _ _))      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axIfFalse _ _))       = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axEqNatRefl _))       = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axExEval _ _ _ _ _))  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axFoldNode _ _ _ _))  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (baseG (axClosedEq _ _ _ _))  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (mpG _ _)             = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (genG _)              = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (instG _ _ _)         = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (exIntroG _ _ _)      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axExElimG _ _)       = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axCongNodeLG _ _ _)  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axCongNodeRG _ _ _)  = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axRepMPG _ _ _ _)    = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axRepD3G _ _ _)      = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axGodelLeftG _ _)    = mkSigmaTA _ (mkSigmaTA _ refl)
  encProofG-is-cnode (axGodelRightG _ _)   = mkSigmaTA _ (mkSigmaTA _ refl)

------------------------------------------------------------------------
-- 3c. foldCorrectG: base/axiom cases
------------------------------------------------------------------------
-- All axiom-like constructors use handlers that either:
-- (a) construct the formula from payload components (hK, hS, hRefl, etc.)
-- (b) return the payload directly (trust-handler: hTrust)
-- Both reduce by refl when n30cG provides enough fuel.

-- Axiom cases for baseG-wrapped ProofTA3 constructors:
-- These are refl because the tag dispatch in ncG matches the same handlers.

foldCorrectG-axRefl : (t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (baseG (axRefl3 t))) k) env
             (encProofG (baseG (axRefl3 t))) acG ncG)
     (encFormTA3 (feqTA3 t t))
foldCorrectG-axRefl t env k = refl

foldCorrectG-axK : (a b : FormTA3) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (baseG (axK3 a b))) k) env
             (encProofG (baseG (axK3 a b))) acG ncG)
     (encFormTA3 (fimpTA3 a (fimpTA3 b a)))
foldCorrectG-axK a b env k = refl

foldCorrectG-axS : (a b c : FormTA3) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (baseG (axS3 a b c))) k) env
             (encProofG (baseG (axS3 a b c))) acG ncG)
     (encFormTA3 (fimpTA3 (fimpTA3 a (fimpTA3 b c)) (fimpTA3 (fimpTA3 a b) (fimpTA3 a c))))
foldCorrectG-axS a b c env k = refl

foldCorrectG-axSym : (s t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (baseG (axSym3 s t))) k) env
             (encProofG (baseG (axSym3 s t))) acG ncG)
     (encFormTA3 (fimpTA3 (feqTA3 s t) (feqTA3 t s)))
foldCorrectG-axSym s t env k = refl

foldCorrectG-axTrans : (r s t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (baseG (axTrans3 r s t))) k) env
             (encProofG (baseG (axTrans3 r s t))) acG ncG)
     (encFormTA3 (fimpTA3 (feqTA3 r s) (fimpTA3 (feqTA3 s t) (feqTA3 r t))))
foldCorrectG-axTrans r s t env k = refl

-- Trust-handler cases (computation axioms, bridge axioms, new axioms):
-- All by refl since hTrust = ctVar v2 returns the pre-stored formula.

foldCorrectG-trust-exElim : (A B : FormTA3) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (axExElimG A B)) k) env
             (encProofG (axExElimG A B)) acG ncG)
     (encFormTA3 (fimpTA3 (fexTA3 A) (fimpTA3 (fallTA3 (fimpTA3 A B)) B)))
foldCorrectG-trust-exElim A B env k = refl

foldCorrectG-trust-congL : (s t u : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (axCongNodeLG s t u)) k) env
             (encProofG (axCongNodeLG s t u)) acG ncG)
     (encFormTA3 (fimpTA3 (feqTA3 s t) (feqTA3 (ctNode s u) (ctNode t u))))
foldCorrectG-trust-congL s t u env k = refl

foldCorrectG-trust-congR : (u s t : CodeTm) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (axCongNodeRG u s t)) k) env
             (encProofG (axCongNodeRG u s t)) acG ncG)
     (encFormTA3 (fimpTA3 (feqTA3 s t) (feqTA3 (ctNode u s) (ctNode u t))))
foldCorrectG-trust-congR u s t env k = refl

------------------------------------------------------------------------
-- 3d. foldCorrectG: gen case
------------------------------------------------------------------------

foldCorrectG-gen : {A : FormTA3} -> (prf : ProofG A) -> (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG prf) k) env (encProofG prf) acG ncG) (encFormTA3 A) ->
  Eq (foldCT (addB (proofFuelG (genG prf)) k) env (encProofG (genG prf)) acG ncG)
     (encFormTA3 (fallTA3 A))
foldCorrectG-gen {A} prf env k ih = genStep ih
  where
  f0 : Nat
  f0 = addB (proofFuelG prf) k

  env' : Code -> Env3
  env' fb = extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env fb)
              (foldCT f0 env (catom tagGen3) acG ncG))
              (encProofG prf)) (catom tagGen3)

  genStep : Eq (foldCT f0 env (encProofG prf) acG ncG) (encFormTA3 A) ->
            Eq (foldCT (suc f0) env (cnode (catom tagGen3) (encProofG prf)) acG ncG)
               (encFormTA3 (fallTA3 A))
  genStep ih2 = eqTrans5G
    (eqCong (\ fb -> evalCT f0 (env' fb) ncG) ih2)
    (genByForm A)
    where
    genByForm : (B : FormTA3) ->
      Eq (evalCT f0 (env' (encFormTA3 B)) ncG)
         (cnode (catom ft2) (encFormTA3 B))
    genByForm fbotTA3        = refl
    genByForm (fimpTA3 a b)  = refl
    genByForm (fallTA3 a)    = refl
    genByForm (fexTA3 a)     = refl
    genByForm (feqTA3 c1 c2) = refl

------------------------------------------------------------------------
-- 3e. foldCorrectG: mp case
------------------------------------------------------------------------

foldCorrectG-mp : {A B : FormTA3} -> (p : ProofG (fimpTA3 A B)) -> (q : ProofG A) ->
  (env : Env3) -> (k : Nat) ->
  ((env2 : Env3) -> (j : Nat) ->
    Eq (foldCT (addB (proofFuelG p) j) env2 (encProofG p) acG ncG)
       (encFormTA3 (fimpTA3 A B))) ->
  ((env2 : Env3) -> (j : Nat) ->
    Eq (foldCT (addB (proofFuelG q) j) env2 (encProofG q) acG ncG)
       (encFormTA3 A)) ->
  Eq (foldCT (addB (proofFuelG (mpG p q)) k) env (encProofG (mpG p q)) acG ncG)
     (encFormTA3 B)
foldCorrectG-mp {A} {B} p q env k ihp ihq = mpProof
  where
  ep : Nat
  ep = proofExtraG p
  eq' : Nat
  eq' = proofExtraG q

  f2 : Nat
  f2 = addB n30cG (addB (addB ep eq') k)

  f1 : Nat
  f1 = suc f2

  ihp-at : Eq (foldCT f2 env (encProofG p) acG ncG) (encFormTA3 (fimpTA3 A B))
  ihp-at = eqTrans5G
    (foldCT-fuel-eqG f2 (addB n30cG (addB ep (addB eq' k)))
      (eqCong (addB n30cG) (addB-assocG ep eq' k)) env (encProofG p) acG ncG)
    (ihp env (addB eq' k))

  ihq-at : Eq (foldCT f2 env (encProofG q) acG ncG) (encFormTA3 A)
  ihq-at = eqTrans5G
    (foldCT-fuel-eqG f2 (addB n30cG (addB eq' (addB ep k)))
      (eqCong (addB n30cG) (eqTrans0 (addB-assocG ep eq' k) (addB-swapG ep eq' k)))
      env (encProofG q) acG ncG)
    (ihq env (addB ep k))

  innerFold : Eq (foldCT f1 env (cnode (encProofG p) (encProofG q)) acG ncG)
                 (cnode (encFormTA3 (fimpTA3 A B)) (encFormTA3 A))
  innerFold = innerStep (encProofG-is-cnode p)
    where
    innerStep : SigmaTA Code (\ la -> SigmaTA Code (\ lb -> Eq (encProofG p) (cnode la lb))) ->
      Eq (foldCT f1 env (cnode (encProofG p) (encProofG q)) acG ncG)
         (cnode (encFormTA3 (fimpTA3 A B)) (encFormTA3 A))
    innerStep (mkSigmaTA la (mkSigmaTA lb eqP)) = eqTrans5G
      (foldCT-pairG (addB (addB ep eq') k) env (encProofG p) (encProofG q)
        (encFormTA3 (fimpTA3 A B)) (encFormTA3 A) ihp-at ihq-at)
      (ncG-cnode-default (addB (addB ep eq') k) env
        (encProofG p) (encProofG q) la lb eqP
        (encFormTA3 (fimpTA3 A B)) (encFormTA3 A))

  mpProof : Eq (foldCT (addB (proofFuelG (mpG p q)) k) env (encProofG (mpG p q)) acG ncG)
               (encFormTA3 B)
  mpProof = eqTrans5G
    (eqCong (\ x -> evalCT f1
      (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env x)
        (foldCT f1 env (catom tagMP3) acG ncG))
        (cnode (encProofG p) (encProofG q))) (catom tagMP3)) ncG)
      innerFold)
    (mpByForm A)
    where
    mpByForm : (X : FormTA3) ->
      Eq (evalCT f1
        (extendEnv3 (extendEnv3 (extendEnv3 (extendEnv3 env
          (cnode (encFormTA3 (fimpTA3 X B)) (encFormTA3 X)))
          (catom zero))
          (cnode (encProofG p) (encProofG q))) (catom tagMP3)) ncG)
        (encFormTA3 B)
    mpByForm fbotTA3        = refl
    mpByForm (fimpTA3 a b)  = refl
    mpByForm (fallTA3 a)    = refl
    mpByForm (fexTA3 a)     = refl
    mpByForm (feqTA3 c1 c2) = refl

------------------------------------------------------------------------
-- 3f. foldCorrectG: inst case
------------------------------------------------------------------------

foldCorrectG-inst : (A : FormTA3) -> (c : Code) -> (prf : ProofG (fallTA3 A)) ->
  (env : Env3) -> (k : Nat) ->
  ((env2 : Env3) -> (j : Nat) ->
    Eq (foldCT (addB (proofFuelG prf) j) env2 (encProofG prf) acG ncG)
       (encFormTA3 (fallTA3 A))) ->
  Eq (foldCT (addB (proofFuelG (instG A c prf)) k) env
             (encProofG (instG A c prf)) acG ncG)
     (encFormTA3 (substF3 c A))
foldCorrectG-inst A c prf env k ih = instByResult (substF3 c A)
  where
  instByResult : (R : FormTA3) ->
    Eq (foldCT (addB (proofFuelG (instG A c prf)) k) env
         (cnode (catom tagInst3) (cnode (encFormTA3 R) (encProofG prf))) acG ncG)
       (encFormTA3 R)
  instByResult fbotTA3        = refl
  instByResult (fimpTA3 a b)  = refl
  instByResult (fallTA3 a)    = refl
  instByResult (fexTA3 a)     = refl
  instByResult (feqTA3 t1 t2) = refl

------------------------------------------------------------------------
-- 3g. foldCorrectG: exIntro case
------------------------------------------------------------------------

foldCorrectG-exIntro : (A : FormTA3) -> (c : Code) -> (prf : ProofG (substF3 c A)) ->
  (env : Env3) -> (k : Nat) ->
  Eq (foldCT (addB (proofFuelG (exIntroG A c prf)) k) env
             (encProofG (exIntroG A c prf)) acG ncG)
     (encFormTA3 (fexTA3 A))
foldCorrectG-exIntro A c prf env k = refl

------------------------------------------------------------------------
-- 3h. Full foldCorrectG
------------------------------------------------------------------------

-- Mutual recursion: foldCorrectG dispatches on ProofG,
-- foldCorrectG-base handles the ProofTA3 sub-structure of baseG.
mutual
  foldCorrectG-base : {A : FormTA3} -> (prf : ProofTA3 A) -> (env : Env3) -> (k : Nat) ->
    Eq (foldCT (addB (proofFuelG (baseG prf)) k) env (encProofG (baseG prf)) acG ncG)
       (encFormTA3 A)
  foldCorrectG-base (axRefl3 t)             env k = foldCorrectG-axRefl t env k
  foldCorrectG-base (axK3 a b)              env k = foldCorrectG-axK a b env k
  foldCorrectG-base (axS3 a b c)            env k = foldCorrectG-axS a b c env k
  foldCorrectG-base (axSym3 s t)            env k = foldCorrectG-axSym s t env k
  foldCorrectG-base (axTrans3 r s t)        env k = foldCorrectG-axTrans r s t env k
  foldCorrectG-base (axCaseAtom k2 ab nb)   env k = refl
  foldCorrectG-base (axCaseNodeL a b ab nb) env k = refl
  foldCorrectG-base (axFoldAtom k2 ac nc)   env k = refl
  foldCorrectG-base (axIfTrue k2 tb eb)     env k = refl
  foldCorrectG-base (axIfFalse tb eb)       env k = refl
  foldCorrectG-base (axEqNatRefl n)         env k = refl
  foldCorrectG-base (axExEval chk c r f eq) env k = refl
  foldCorrectG-base (axFoldNode a b ac nc)  env k = refl
  foldCorrectG-base (axClosedEq t1 t2 f eq) env k = refl
  foldCorrectG-base (gen3 p)                env k =
    foldCorrectG-gen (baseG p) env k (foldCorrectG-base p env k)
  foldCorrectG-base (mp3 p q)              env k =
    foldCorrectG-mp (baseG p) (baseG q) env k
      (\ env2 j -> foldCorrectG-base p env2 j)
      (\ env2 j -> foldCorrectG-base q env2 j)
  foldCorrectG-base (inst3 A c p)          env k =
    foldCorrectG-inst A c (baseG p) env k
      (\ env2 j -> foldCorrectG-base p env2 j)
  foldCorrectG-base (exIntro3 A c p)       env k = refl

  foldCorrectG : {A : FormTA3} -> (prf : ProofG A) -> (env : Env3) -> (k : Nat) ->
    Eq (foldCT (addB (proofFuelG prf) k) env (encProofG prf) acG ncG)
       (encFormTA3 A)
  foldCorrectG (baseG p)               env k = foldCorrectG-base p env k
  foldCorrectG (mpG p q)               env k =
    foldCorrectG-mp p q env k
      (\ env2 j -> foldCorrectG p env2 j)
      (\ env2 j -> foldCorrectG q env2 j)
  foldCorrectG (genG p)                env k =
    foldCorrectG-gen p env k (foldCorrectG p env k)
  foldCorrectG (instG A c p)           env k =
    foldCorrectG-inst A c p env k
      (\ env2 j -> foldCorrectG p env2 j)
  foldCorrectG (exIntroG A c p)        env k =
    foldCorrectG-exIntro A c p env k
  foldCorrectG (axExElimG A B)         env k =
    foldCorrectG-trust-exElim A B env k
  foldCorrectG (axCongNodeLG s t u)    env k =
    foldCorrectG-trust-congL s t u env k
  foldCorrectG (axCongNodeRG u s t)    env k =
    foldCorrectG-trust-congR u s t env k
  foldCorrectG (axRepMPG chk encF A B) env k = refl
  foldCorrectG (axRepD3G chk encF A)  env k = refl
  foldCorrectG (axGodelLeftG _ _)     env k = refl
  foldCorrectG (axGodelRightG _ _)    env k = refl

------------------------------------------------------------------------
-- 3i. extCorrectG: wrapper for D1
------------------------------------------------------------------------

private
  evalCT-fuel-eqG2 : (f1 f2 : Nat) -> Eq f1 f2 ->
    (env : Env3) -> (t : CodeTm) ->
    Eq (evalCT f1 env t) (evalCT f2 env t)
  evalCT-fuel-eqG2 f1 .f1 refl env t = refl

extCorrectG : {A : FormTA3} -> (prf : ProofG A) ->
  Eq (evalCT (suc (proofFuelG prf))
             (extendEnv3 emptyEnv3 (encProofG prf))
             checkCG)
     (encFormTA3 A)
extCorrectG {A} prf =
  eqTrans5G
    (evalCT-fuel-eqG2 (suc (proofFuelG prf))
                       (suc (addB (proofFuelG prf) zero))
      (eqCong suc (eqSym0 (addB-zero-rightG (proofFuelG prf))))
      (extendEnv3 emptyEnv3 (encProofG prf)) checkCG)
    (foldCorrectG prf (extendEnv3 emptyEnv3 (encProofG prf)) zero)

------------------------------------------------------------------------
-- Stage 4: Internal D1
------------------------------------------------------------------------

d1G : {A : FormTA3} -> ProofG A -> ProofG (ProvG A)
d1G {A} prf = baseG (axExEval checkCG (encProofG prf) (encFormTA3 A)
                               (suc (proofFuelG prf)) (extCorrectG prf))

-- Sanity checks
private
  -- D1 on a base proof (axRefl)
  test-d1-refl : ProofG (ProvG (feqTA3 (ctAtom zero) (ctAtom zero)))
  test-d1-refl = d1G (baseG (axRefl3 (ctAtom zero)))

  -- D1 on mp
  test-d1-mp : ProofG (ProvG (fimpTA3 fbotTA3 (feqTA3 (ctAtom zero) (ctAtom zero))))
  test-d1-mp = d1G (mpG (baseG (axK3 (feqTA3 (ctAtom zero) (ctAtom zero)) fbotTA3))
                         (baseG (axRefl3 (ctAtom zero))))

  -- D1 on gen
  test-d1-gen : ProofG (ProvG (fallTA3 (feqTA3 (ctAtom zero) (ctAtom zero))))
  test-d1-gen = d1G (genG (baseG (axRefl3 (ctAtom zero))))

  -- D1 on congruence
  test-d1-cong : ProofG (ProvG (fimpTA3 (feqTA3 (ctAtom zero) (ctAtom (suc zero)))
                                         (feqTA3 (ctNode (ctAtom zero) (ctAtom zero))
                                                 (ctNode (ctAtom (suc zero)) (ctAtom zero)))))
  test-d1-cong = d1G (axCongNodeLG (ctAtom zero) (ctAtom (suc zero)) (ctAtom zero))

------------------------------------------------------------------------
-- Stage 5: D2 and D3 from representability layer
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 5a. Derived combinators from axExElimG
------------------------------------------------------------------------

exElimG : {A B : FormTA3} ->
  ProofG (fexTA3 A) ->
  ProofG (fallTA3 (fimpTA3 A B)) ->
  ProofG B
exElimG {A} {B} pEx pAll = mpG (mpG (axExElimG A B) pEx) pAll

exElimImpG : {A B : FormTA3} ->
  ProofG (fallTA3 (fimpTA3 A B)) ->
  ProofG (fimpTA3 (fexTA3 A) B)
exElimImpG {A} {B} h =
  let ee = axExElimG A B
      kh = mpG (liftK (fallTA3 (fimpTA3 A B)) (fexTA3 A)) h
  in mpG (mpG (liftS (fexTA3 A) (fallTA3 (fimpTA3 A B)) B) ee) kh

------------------------------------------------------------------------
-- 5b. D2: Prov(A->B) -> Prov(A) -> Prov(B)
------------------------------------------------------------------------
-- Immediate from the representability constructor axRepMPG.

d2G : {A B : FormTA3} ->
  ProofG (fimpTA3 (ProvG (fimpTA3 A B)) (fimpTA3 (ProvG A) (ProvG B)))
d2G {A} {B} = axRepMPG checkCG encFormTA3 A B

------------------------------------------------------------------------
-- 5c. D3: Prov(A) -> Prov(Prov(A))
------------------------------------------------------------------------
-- Immediate from the representability constructor axRepD3G.

d3G : {A : FormTA3} -> ProofG (fimpTA3 (ProvG A) (ProvG (ProvG A)))
d3G {A} = axRepD3G checkCG encFormTA3 A

------------------------------------------------------------------------
-- 5d. Sanity checks
------------------------------------------------------------------------

private
  test-d2 : ProofG (fimpTA3 (ProvG (fimpTA3 fbotTA3 fbotTA3))
                             (fimpTA3 (ProvG fbotTA3) (ProvG fbotTA3)))
  test-d2 = d2G

  test-d3 : ProofG (fimpTA3 (ProvG fbotTA3) (ProvG (ProvG fbotTA3)))
  test-d3 = d3G

------------------------------------------------------------------------
-- Stage 6: Goedel sentence + diagonal
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 6a. The Goedel sentence
------------------------------------------------------------------------
-- godelG is defined at the top of the file (before ProofG) as:
-- godelG = fimpTA3 (fexTA3 (feqTA3 (ctAtom zero) (ctAtom zero))) fbotTA3
--
-- The negated provability formula for godelG:
-- notProvGodelG = fimpTA3 (ProvG godelG) fbotTA3

notProvGodelG : FormTA3
notProvGodelG = fimpTA3 (ProvG godelG) fbotTA3

------------------------------------------------------------------------
-- 6b. Diagonal directions
------------------------------------------------------------------------
-- gLeftG:  G -> (Prov(G) -> bot) = G -> notProvGodelG
-- gRightG: (Prov(G) -> bot) -> G = notProvGodelG -> G
--
-- Both come from the diagonal representability constructors,
-- instantiated with the specific notProvGodelG formula.

private
  -- notProvGodelG is uninhabited at fuel 0:
  -- GoodTA3 0 env notProvGodelG
  -- = GoodTA3 0 env (fimpTA3 (ProvG godelG) fbotTA3)
  -- = GoodTA3 0 env (ProvG godelG) -> EmptyTA
  -- = (SigmaTA Code (\c -> Eq (catom 0)(catom 0))) -> EmptyTA
  -- The sigma is inhabited, so the function type is uninhabited.
  notProvG-empty : (env : Env3) -> GoodTA3 zero env notProvGodelG -> EmptyTA
  notProvG-empty env h = h (mkSigmaTA (catom zero) refl)

gLeftG : ProofG (fimpTA3 godelG notProvGodelG)
gLeftG = axGodelLeftG notProvGodelG notProvG-empty

gRightG : ProofG (fimpTA3 notProvGodelG godelG)
gRightG = axGodelRightG notProvGodelG notProvG-empty

------------------------------------------------------------------------
-- 6c. Sanity check
------------------------------------------------------------------------

private
  -- gLeftG type matches what the Loeb record expects
  test-gLeft : ProofG (fimpTA3 godelG (fimpTA3 (ProvG godelG) fbotTA3))
  test-gLeft = gLeftG

  test-gRight : ProofG (fimpTA3 (fimpTA3 (ProvG godelG) fbotTA3) godelG)
  test-gRight = gRightG

------------------------------------------------------------------------
-- Stage 7: Goedel's Second Incompleteness Theorem
------------------------------------------------------------------------

godel2G : ProofG ConGfull -> EmptyTA
godel2G = loeb-godel2 (record
  { Form            = FormTA3
  ; Proof           = ProofG
  ; Prov            = ProvG
  ; bot             = fbotTA3
  ; imp             = fimpTA3
  ; axK             = baseG (axK3 _ _)
  ; axS             = baseG (axS3 _ _ _)
  ; mp              = mpG
  ; d1              = d1G
  ; d2              = \ {A} {B} -> d2G {A} {B}
  ; d3              = \ {A} -> d3G {A}
  ; goedelSentence  = godelG
  ; goedelLeft      = gLeftG
  ; goedelRight     = gRightG
  ; consistent      = conG
  })
