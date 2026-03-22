{-# OPTIONS --without-K --exact-split #-}

module NelsonDecomp where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekGodel2Genuine
open import BinaryTreeArith

-- 1. ProofN: tiny proof datatype

data ProofN : Set where
  pax    : Nat -> ProofN
  pmp    : ProofN -> ProofN -> ProofN
  psym   : ProofN -> ProofN
  ptrans : ProofN -> ProofN -> ProofN

-- 2. Complexity measures

private
  addND : Nat -> Nat -> Nat
  addND zero    m = m
  addND (suc n) m = suc (addND n m)

  maxN : Nat -> Nat -> Nat
  maxN zero    m       = m
  maxN (suc n) zero    = suc n
  maxN (suc n) (suc m) = suc (maxN n m)

sizeP : ProofN -> Nat
sizeP (pax _)      = suc zero
sizeP (pmp p q)    = suc (addND (sizeP p) (sizeP q))
sizeP (psym p)     = suc (sizeP p)
sizeP (ptrans p q) = suc (addND (sizeP p) (sizeP q))

rankP : ProofN -> Nat
rankP (pax _)      = zero
rankP (pmp p q)    = suc (maxN (rankP p) (rankP q))
rankP (psym p)     = suc (rankP p)
rankP (ptrans p q) = suc (maxN (rankP p) (rankP q))

private
  bothPositive : Nat -> Nat -> Nat
  bothPositive zero    _       = zero
  bothPositive (suc _) zero    = zero
  bothPositive (suc n) (suc m) = suc (addND n m)

backtrackP : ProofN -> Nat
backtrackP (pax _)      = zero
backtrackP (pmp p q)    = bothPositive (backtrackP p) (backtrackP q)
backtrackP (psym p)     = backtrackP p
backtrackP (ptrans p q) = suc (addND (backtrackP p) (backtrackP q))

-- 3. Local reduction

reduceN : ProofN -> ProofN
reduceN (psym (psym p)) = p
reduceN p               = p

backtrack-psym2 : (p : ProofN) -> Eq (backtrackP (reduceN (psym (psym p))))
                                      (backtrackP p)
backtrack-psym2 p = refl

-- 4. Encoding ProofN into Code

n50 : Nat
n50 = suc n39g

n51 : Nat
n51 = suc n50

n52 : Nat
n52 = suc n51

n53 : Nat
n53 = suc n52

private
  n50code : Code
  n50code = catom n50

  n51code : Code
  n51code = catom n51

  n52code : Code
  n52code = catom n52

  n53code : Code
  n53code = catom n53

encProofN : ProofN -> Code
encProofN (pax k)      = cnode n50code (catom k)
encProofN (pmp p q)    = cnode n51code (cnode (encProofN p) (encProofN q))
encProofN (psym p)     = cnode n52code (encProofN p)
encProofN (ptrans p q) = cnode n53code (cnode (encProofN p) (encProofN q))

private
  matchSym2 : Code -> Code
  matchSym2 (cnode (catom tag) inner) = ms1 (eqNat tag n52) inner
    where
    ms1 : Bool -> Code -> Code
    ms1 true (cnode (catom tag2) p) = ms2 (eqNat tag2 n52) p
      where
      ms2 : Bool -> Code -> Code
      ms2 true  p = p
      ms2 false p = cnode n52code (cnode (catom tag2) p)
    ms1 true  other = cnode n52code other
    ms1 false inner = cnode (catom tag) inner
  matchSym2 c = c

reduceCodeN : Code -> Code
reduceCodeN c = matchSym2 c

private
  eqNat-refl-ND : (n : Nat) -> Eq (eqNat n n) true
  eqNat-refl-ND zero    = refl
  eqNat-refl-ND (suc k) = eqNat-refl-ND k

reduceCodeN-correct : (p : ProofN) ->
  Eq (reduceCodeN (encProofN (psym (psym p)))) (encProofN p)
reduceCodeN-correct p = helper (eqNat-refl-ND n52)
  where
  helper : Eq (eqNat n52 n52) true ->
           Eq (reduceCodeN (encProofN (psym (psym p)))) (encProofN p)
  helper refl = refl

-- 5. ProofBD: extends ProofBTA with decomposition axiom
-- Local redefinitions of private helpers from BinaryTreeArith

private
  liftCTL : CodeTerm -> CodeTerm
  liftCTL (ctVar v)      = ctVar (cvs v)
  liftCTL (ctLit c)      = ctLit c
  liftCTL (ctNode t1 t2) = ctNode (liftCTL t1) (liftCTL t2)

  substCT0L : CodeTerm -> CodeTerm -> CodeTerm
  substCT0L s (ctVar cvz)     = s
  substCT0L s (ctVar (cvs v)) = ctVar v
  substCT0L s (ctLit c)       = ctLit c
  substCT0L s (ctNode t1 t2)  = ctNode (substCT0L s t1) (substCT0L s t2)

  substFA0L : CodeTerm -> FormulaBTA -> FormulaBTA
  substFA0L s fbotA        = fbotA
  substFA0L s (fimpA a b)  = fimpA (substFA0L s a) (substFA0L s b)
  substFA0L s (fcAllA a)   = fcAllA (substFA0L (liftCTL s) a)
  substFA0L s (fPrf p c)   = fPrf (substCT0L s p) (substCT0L s c)

data ProofBD : FormulaBTA -> Set where
  -- Structural rules
  mpBD    : {A B : FormulaBTA} -> ProofBD (fimpA A B) -> ProofBD A -> ProofBD B
  cgenBD  : {A : FormulaBTA} -> ProofBD A -> ProofBD (fcAllA A)
  cinstBD : {A : FormulaBTA} -> ProofBD (fcAllA A) -> (t : CodeTerm) ->
            ProofBD (substFA0L t A)
  axKBD   : (A B : FormulaBTA) -> ProofBD (fimpA A (fimpA B A))
  axSBD   : (A B C : FormulaBTA) ->
            ProofBD (fimpA (fimpA A (fimpA B C))
                           (fimpA (fimpA A B) (fimpA A C)))
  -- Lifted from ProofBTA (each checker axiom individually)
  liftBD-chkMP : {p1 p2 encA encB : CodeTerm} ->
    ProofBD (fimpA (fPrf p1 (ctNode (ctLit (catom (suc (suc (suc (suc (suc zero)))))))
                            (ctNode encA encB)))
                   (fimpA (fPrf p2 encA)
                          (fPrf (ctNode (ctLit (catom n33)) (ctNode p1 p2)) encB)))
  liftBD-prfCong : {p c1 c2 : CodeTerm} ->
    ProofBD (fimpA (fPrf p c1) (fPrf p c2))
  -- Decomposition axiom
  axDecompSym2 : {p c : CodeTerm} ->
    ProofBD (fimpA (fPrf (ctNode (ctLit n52code) (ctNode (ctLit n52code) p)) c)
                   (fPrf p c))

-- 6. GoodBD soundness

private
  GoodBD : CEnvG -> FormulaBTA -> Set
  GoodBD env fbotA        = EmptyG2
  GoodBD env (fimpA a b)  = GoodBD env a -> GoodBD env b
  GoodBD env (fcAllA a)   = (c : Code) -> GoodBD (extendCEnvG env c) a
  GoodBD env (fPrf _ _)   = UnitG2

  substGoodBD : (A : FormulaBTA) -> (env : CEnvG) -> (t : CodeTerm) ->
    ((c : Code) -> GoodBD (extendCEnvG env c) A) ->
    GoodBD env (substFA0L t A)
  unsubstGoodBD : (A : FormulaBTA) -> (env : CEnvG) -> (t : CodeTerm) ->
    (c : Code) ->
    GoodBD env (substFA0L t A) -> GoodBD (extendCEnvG env c) A

  substGoodBD fbotA env t g = g (catom zero)
  substGoodBD (fimpA a b) env t f =
    \ x -> substGoodBD b env t
      (\ c -> f c (unsubstGoodBD a env t c x))
  substGoodBD (fcAllA a) env t g =
    \ c -> substGoodBD a (extendCEnvG env c) (liftCTL t) (\ c' -> g c' c)
  substGoodBD (fPrf _ _) env t g = ttG2

  unsubstGoodBD fbotA env t c g = g
  unsubstGoodBD (fimpA a b) env t c g =
    \ x -> unsubstGoodBD b env t c
      (g (substGoodBD a env t (\ _ -> x)))
  unsubstGoodBD (fcAllA a) env t c g =
    \ c' -> unsubstGoodBD a (extendCEnvG env c') (liftCTL t) c (g c')
  unsubstGoodBD (fPrf _ _) env t c g = ttG2

  soundBD : {A : FormulaBTA} -> ProofBD A -> (env : CEnvG) -> GoodBD env A
  soundBD (mpBD pf1 pf2) env = soundBD pf1 env (soundBD pf2 env)
  soundBD (cgenBD pf) env = \ c -> soundBD pf (extendCEnvG env c)
  soundBD (cinstBD {A} pf t) env = substGoodBD A env t (soundBD pf env)
  soundBD (axKBD A B) env = \ x _ -> x
  soundBD (axSBD A B C) env = \ f g a -> f a (g a)
  soundBD liftBD-chkMP env = \ _ _ -> ttG2
  soundBD liftBD-prfCong env = \ _ -> ttG2
  soundBD axDecompSym2 env = \ _ -> ttG2

-- 7. sym2-reduce and universally quantified version

sym2-reduce : {p c : CodeTerm} ->
  ProofBD (fimpA (fPrf (ctNode (ctLit n52code) (ctNode (ctLit n52code) p)) c)
                 (fPrf p c))
sym2-reduce = axDecompSym2

sym2-reduce-univ : ProofBD (fcAllA (fcAllA
  (fimpA (fPrf (ctNode (ctLit n52code) (ctNode (ctLit n52code) (ctVar cvz)))
               (ctVar (cvs cvz)))
         (fPrf (ctVar cvz) (ctVar (cvs cvz))))))
sym2-reduce-univ = cgenBD (cgenBD axDecompSym2)

-- 8. ANALYSIS
-- axDecompSym2 enables inversion for specific code shapes:
--   psym(psym(p)) reduces to p when the code has tag n52 nested twice.
--
-- But UNIFORM reduction (for ALL codes) still requires case analysis
-- on code variables. Given an arbitrary CodeTerm, we cannot inspect
-- whether it starts with n52 -- CodeTerm has no case/match construct.
--
-- The decomposition barrier has TWO layers:
--   (1) Decomposition axioms: we can add finitely many axioms like
--       axDecompSym2 for each specific pattern. This is what ProofBD does.
--   (2) Conditional code analysis: to implement a general reduceCodeN
--       inside the proof system, we need to branch on the structure of
--       a CodeTerm variable. This requires ctCase in CodeTerm.
--
-- Both tracks (Track 1: add more decomposition axioms, Track 2: build
-- a full normalizer) need the SAME missing ingredient: ctCase in CodeTerm.
-- Without ctCase, we can only handle fixed patterns, not arbitrary codes.
