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
-- Encoding correctness: checkG accepts encoded proofs
------------------------------------------------------------------------

-- Split: base proofs (Proof) and extended proofs (ProofG)
-- Same pattern as ChwistekSoundness/ChwistekProofExtCheck

encodeBaseG-correct :
  {A : Formula} -> (prf : Proof A) -> (n : Nat) ->
  Eq (checkG (suc n) (encodeProof prf)) (just A)

encodeBaseG-correct (ax-refl t) n = refl-provable-lemma t

encodeBaseG-correct (ax-k A B) n =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ a -> maybeBind (decFormula (encFormula B))
              (\ b -> just (fimp a (fimp b a)))))
            (decFormula-encFormula A))
    (eqCong (\ r -> maybeBind r (\ b -> just (fimp A (fimp b A))))
            (decFormula-encFormula B))

encodeBaseG-correct (ax-s A B C) n =
  eqTrans
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
              (decFormula-encFormula C)))

encodeBaseG-correct (mp {A} {B} pf1 pf2) n =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ pf ->
              maybeBind (checkG n (encodeProof pf2)) (\ qf ->
              matchMP pf qf)))
            (encodeBaseG-correct pf1 n))
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
              (encodeBaseG-correct pf2 n))
      (guardEq-self A B))

encodeBaseG-correct (gen pf) n =
  eqCong (maybeMap fall) (encodeBaseG-correct pf n)

encodeBaseG-correct (cgen pf) n =
  eqCong (maybeMap fcAll) (encodeBaseG-correct pf n)

-- Extended cases
encodeProofG-correct :
  {n : Nat} {A : Formula} -> (prf : ProofG (suc n) A) ->
  Eq (checkG (suc n) (encodeProofG prf)) (just A)

encodeProofG-correct (baseG prf) = encodeBaseG-correct prf _

encodeProofG-correct (axEvalG e c eq) =
  eqCong (maybeMap (\ de -> fceq de (clit c))) (decCExp-encCExp e)

encodeProofG-correct (mpG {A} {B} pf1 pf2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ pf ->
              maybeBind (checkG _ (encodeProofG pf2)) (\ qf ->
              matchMP pf qf)))
            (encodeProofG-correct pf1))
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ qf -> matchMP (fimp A B) qf))
              (encodeProofG-correct pf2))
      (guardEq-self A B))

encodeProofG-correct (genG pf) =
  eqCong (maybeMap fall) (encodeProofG-correct pf)

encodeProofG-correct (cgenG pf) =
  eqCong (maybeMap fcAll) (encodeProofG-correct pf)

encodeProofG-correct (cinstG {A} pf c) =
  eqCong (\ r -> maybeBind r (\ pf2 -> matchCinst pf2 c))
         (encodeProofG-correct pf)

encodeProofG-correct (fceqTrG {e1} {e2} {e3} pf1 pf2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ f1 ->
              maybeBind (checkG _ (encodeProofG pf2)) (\ f2 ->
              matchFceqTr f1 f2)))
            (encodeProofG-correct pf1))
    (eqTrans
      (eqCong (\ r -> maybeBind r (\ f2 ->
                matchFceqTr (fceq e1 e2) f2))
              (encodeProofG-correct pf2))
      (eqSubst (\ b -> Eq (boolGuard b (just (fceq e1 e3)))
                           (just (fceq e1 e3)))
               (eqSym (eqCExp-refl e2))
               refl))

encodeProofG-correct (fceqSyG pf) =
  eqCong (\ r -> maybeBind r matchFceqSy) (encodeProofG-correct pf)

------------------------------------------------------------------------
-- Soundness of ProofG under TrueFN (STANDARD semantics)
------------------------------------------------------------------------

-- TrueFN uses evalCExpEnvN / checkProofN. For ProofG using checkG,
-- we need a version using evalG. Define TrueFG.

CEnvG : Set
CEnvG = CVar -> Code

emptyCEnvG : CEnvG
emptyCEnvG _ = catom zero

extendCEnvG : CEnvG -> Code -> CEnvG
extendCEnvG env c cvz     = c
extendCEnvG env c (cvs v) = env v

TEnvG : Set
TEnvG = Var -> Term

emptyTEnvG : TEnvG
emptyTEnvG v = tvar v

extendTEnvG : TEnvG -> Term -> TEnvG
extendTEnvG env t vz     = t
extendTEnvG env t (vs v) = env v

evalTermG : TEnvG -> Term -> Term
evalTermG env (tvar v)  = env v
evalTermG env tzero     = tzero
evalTermG env (tsucc t) = tsucc (evalTermG env t)

evalGEnv : Nat -> CEnvG -> CExp -> Maybe Code
evalGEnv n env (cvar v) = just (env v)
evalGEnv n env (clit c) = just c
evalGEnv zero env (ccheck _) = nothing
evalGEnv (suc n) env (ccheck e) =
  maybeBind (evalGEnv n env e) (\ p ->
  maybeBind (checkG n p) (\ a -> just (encFormula a)))
evalGEnv zero env (csub _ _) = nothing
evalGEnv (suc n) env (csub e1 e2) =
  maybeBind (evalGEnv n env e1) (\ c1 ->
  maybeBind (evalGEnv n env e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))

data EmptyG2 : Set where
data UnitG2 : Set where
  ttG2 : UnitG2

data Prod2 (A B : Set) : Set where
  mkProd2 : A -> B -> Prod2 A B

TrueCodeEqG : Nat -> CEnvG -> CExp -> CExp -> Set
TrueCodeEqG n cenv e1 e2 =
  Sigma Code (\ c -> Prod2 (Eq (evalGEnv n cenv e1) (just c))
                           (Eq (evalGEnv n cenv e2) (just c)))

TrueFG : Nat -> TEnvG -> CEnvG -> Formula -> Set
TrueFG n tenv cenv fbot         = EmptyG2
TrueFG n tenv cenv (feq s t)    = Eq (evalTermG tenv s) (evalTermG tenv t)
TrueFG n tenv cenv (fimp a b)   = TrueFG n tenv cenv a -> TrueFG n tenv cenv b
TrueFG n tenv cenv (fall a)     = (t : Term) -> TrueFG n (extendTEnvG tenv t) cenv a
TrueFG n tenv cenv (fcode c)    = Eq c c
TrueFG n tenv cenv (fceq e1 e2) = TrueCodeEqG n cenv e1 e2
TrueFG n tenv cenv (fcAll a)    = (c : Code) -> TrueFG n tenv (extendCEnvG cenv c) a

TrueFormulaG : Nat -> Formula -> Set
TrueFormulaG n A = (tenv : TEnvG) -> (cenv : CEnvG) -> TrueFG n tenv cenv A

-- evalGEnv agrees with evalG for closed CExps
evalGEnv-closed :
  (n : Nat) (e : CExp) (c : Code) (cv : CEnvG) ->
  Eq (evalG n e) (just c) -> Eq (evalGEnv n cv e) (just c)
evalGEnv-closed zero _ _ _ ()
evalGEnv-closed (suc n) (cvar _) _ _ ()
evalGEnv-closed (suc n) (clit _) c cv eq = eq
evalGEnv-closed (suc n) (ccheck e) c cv eq =
  chkH (evalG n e) refl eq
  where
  cont : Code -> Maybe Code
  cont p = maybeBind (checkG n p) (\ a -> just (encFormula a))
  chkH : (r : Maybe Code) -> Eq (evalG n e) r ->
         Eq (maybeBind r cont) (just c) ->
         Eq (maybeBind (evalGEnv n cv e) cont) (just c)
  chkH nothing  er ()
  chkH (just v) er h =
    eqTrans (eqCong (\ s -> maybeBind s cont)
                    (evalGEnv-closed n e v cv er)) h
evalGEnv-closed (suc n) (csub e1 e2) c cv eq =
  subH (evalG n e1) refl eq
  where
  subH : (r1 : Maybe Code) -> Eq (evalG n e1) r1 ->
         Eq (maybeBind r1 (\ c1 ->
             maybeBind (evalG n e2) (\ c2 ->
             maybeBind (decFormula c1) (\ a ->
             just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c) ->
         Eq (maybeBind (evalGEnv n cv e1) (\ c1 ->
             maybeBind (evalGEnv n cv e2) (\ c2 ->
             maybeBind (decFormula c1) (\ a ->
             just (encFormula (substFormulaCode0 (clit c2) a)))))) (just c)
  subH nothing  er1 ()
  subH (just v1) er1 h1 =
    eqTrans
      (eqCong (\ s -> maybeBind s (\ c1 ->
                maybeBind (evalGEnv n cv e2) (\ c2 ->
                maybeBind (decFormula c1) (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))))
              (evalGEnv-closed n e1 v1 cv er1))
      (subH2 (evalG n e2) refl h1)
    where
    subH2 : (r2 : Maybe Code) -> Eq (evalG n e2) r2 ->
            Eq (maybeBind r2 (\ c2 ->
                maybeBind (decFormula v1) (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))) (just c) ->
            Eq (maybeBind (evalGEnv n cv e2) (\ c2 ->
                maybeBind (decFormula v1) (\ a ->
                just (encFormula (substFormulaCode0 (clit c2) a))))) (just c)
    subH2 nothing  er2 ()
    subH2 (just v2) er2 h2 =
      eqTrans
        (eqCong (\ s -> maybeBind s (\ c2 ->
                  maybeBind (decFormula v1) (\ a ->
                  just (encFormula (substFormulaCode0 (clit c2) a)))))
                (evalGEnv-closed n e2 v2 cv er2))
        h2

-- Soundness

soundBaseG : {A : Formula} -> Proof A ->
  (n : Nat) -> TrueFormulaG n A
soundBaseG (ax-refl t) n tenv cenv = refl
soundBaseG (ax-k A B) n tenv cenv = \ x _ -> x
soundBaseG (ax-s A B C) n tenv cenv = \ f g a -> f a (g a)
soundBaseG (mp pf1 pf2) n tenv cenv =
  soundBaseG pf1 n tenv cenv (soundBaseG pf2 n tenv cenv)
soundBaseG (gen pf) n tenv cenv =
  \ t -> soundBaseG pf n (extendTEnvG tenv t) cenv
soundBaseG (cgen pf) n tenv cenv =
  \ c -> soundBaseG pf n tenv (extendCEnvG cenv c)

soundProofG : {n : Nat} {A : Formula} -> ProofG n A -> TrueFormulaG n A
soundProofG (baseG prf) = soundBaseG prf _
soundProofG (axEvalG e c eq) tenv cenv =
  mkSigma c (mkProd2 (evalGEnv-closed _ e c cenv eq) refl)
soundProofG (mpG pf1 pf2) tenv cenv =
  soundProofG pf1 tenv cenv (soundProofG pf2 tenv cenv)
soundProofG (genG pf) tenv cenv =
  \ t -> soundProofG pf (extendTEnvG tenv t) cenv
soundProofG (cgenG pf) tenv cenv =
  \ c -> soundProofG pf tenv (extendCEnvG cenv c)
soundProofG (cinstG {A} pf c) tenv cenv =
  substTFG A tenv cenv c (soundProofG pf tenv cenv c)
  where
  substTFG : (A : Formula) -> TEnvG -> CEnvG -> Code ->
    TrueFG _ tenv (extendCEnvG cenv c) A ->
    TrueFG _ tenv cenv (substFormulaCode0 (clit c) A)
  unsubstTFG : (A : Formula) -> TEnvG -> CEnvG -> Code ->
    TrueFG _ tenv cenv (substFormulaCode0 (clit c) A) ->
    TrueFG _ tenv (extendCEnvG cenv c) A
  substTFG fbot te ce c g = g
  substTFG (feq _ _) te ce c g = g
  substTFG (fimp a b) te ce c g = \ x -> substTFG b te ce c (g (unsubstTFG a te ce c x))
  substTFG (fall _) te ce c g = ttG2
  substTFG (fcode _) te ce c g = g
  substTFG (fceq _ _) te ce c g = g
  substTFG (fcAll a) te ce c g = \ c' -> substTFG a te (extendCEnvG ce c') c (g c')
  unsubstTFG fbot te ce c g = g
  unsubstTFG (feq _ _) te ce c g = g
  unsubstTFG (fimp a b) te ce c g = \ x -> unsubstTFG b te ce c (g (substTFG a te ce c x))
  unsubstTFG (fall _) te ce c g = ttG2
  unsubstTFG (fcode _) te ce c g = g
  unsubstTFG (fceq _ _) te ce c g = g
  unsubstTFG (fcAll a) te ce c g = \ c' -> unsubstTFG a te (extendCEnvG ce c') c (g c')
soundProofG (fceqTrG (mkSigma c1 (mkProd2 p1 p2)) (mkSigma c2 (mkProd2 q1 q2))) tenv cenv =
  ?
soundProofG (fceqSyG (mkSigma c (mkProd2 p1 p2))) tenv cenv =
  mkSigma c (mkProd2 p2 p1)

------------------------------------------------------------------------
-- Remaining work: fceqTrG soundness, then Goedel II
------------------------------------------------------------------------

-- fceqTrG soundness: if e1 and e2 eval to same code, and e2 and e3
-- eval to same code, then e1 and e3 eval to same code.
-- This requires showing c1 = c2 (from p2 and q1 both equaling
-- evalGEnv of e2).

-- The rest of Goedel II follows the same pattern as ChwistekGodel2SD:
-- Con-implies-G + soundness + encoding correctness -> contradiction.
