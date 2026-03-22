{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

-- Standard-semantics soundness for ProofG (separated from the main
-- Goedel II file because the cinstG/fcAll case requires a generalized
-- de Bruijn substitution lemma, left as a hole).
--
-- goedel2-genuine does NOT depend on this file.

module ChwistekGodel2Sound where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekGodel2Genuine

------------------------------------------------------------------------
-- Term environments and evaluation
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Code-expression evaluation with environments
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Truth predicate (standard semantics)
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- evalGEnv agrees with evalG for closed CExps
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Soundness helpers
------------------------------------------------------------------------

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

-- evalGEnv commutes with code substitution
evalGEnv-subst :
  (n : Nat) (ce : CEnvG) (cv : Code) (e : CExp) ->
  Eq (evalGEnv n (extendCEnvG ce cv) e) (evalGEnv n ce (substCExp0 (clit cv) e))
evalGEnv-subst n ce cv (cvar cvz) = refl
evalGEnv-subst n ce cv (cvar (cvs v)) = refl
evalGEnv-subst n ce cv (clit c) = refl
evalGEnv-subst zero ce cv (ccheck e) = refl
evalGEnv-subst (suc n) ce cv (ccheck e) =
  eqCong (\ r -> maybeBind r (\ p -> maybeBind (checkG n p) (\ a -> just (encFormula a))))
         (evalGEnv-subst n ce cv e)
evalGEnv-subst zero ce cv (csub e1 e2) = refl
evalGEnv-subst (suc n) ce cv (csub e1 e2) =
  eqTrans
    (eqCong (\ r -> maybeBind r (\ c1 ->
              maybeBind (evalGEnv n (extendCEnvG ce cv) e2) (\ c2 ->
              maybeBind (decFormula c1) (\ a ->
              just (encFormula (substFormulaCode0 (clit c2) a))))))
            (evalGEnv-subst n ce cv e1))
    (eqCong (\ r -> maybeBind (evalGEnv n ce (substCExp0 (clit cv) e1)) (\ c1 ->
              maybeBind r (\ c2 ->
              maybeBind (decFormula c1) (\ a ->
              just (encFormula (substFormulaCode0 (clit c2) a))))))
            (evalGEnv-subst n ce cv e2))

substTCEG : {n : Nat} (ce : CEnvG) (cv : Code) (e1 e2 : CExp) ->
  TrueCodeEqG n (extendCEnvG ce cv) e1 e2 ->
  TrueCodeEqG n ce (substCExp0 (clit cv) e1) (substCExp0 (clit cv) e2)
substTCEG {n} ce cv e1 e2 (mkSigma c (mkProd2 p1 p2)) =
  mkSigma c (mkProd2
    (eqTrans (eqSym (evalGEnv-subst n ce cv e1)) p1)
    (eqTrans (eqSym (evalGEnv-subst n ce cv e2)) p2))

unsubstTCEG : {n : Nat} (ce : CEnvG) (cv : Code) (e1 e2 : CExp) ->
  TrueCodeEqG n ce (substCExp0 (clit cv) e1) (substCExp0 (clit cv) e2) ->
  TrueCodeEqG n (extendCEnvG ce cv) e1 e2
unsubstTCEG {n} ce cv e1 e2 (mkSigma c (mkProd2 p1 p2)) =
  mkSigma c (mkProd2
    (eqTrans (evalGEnv-subst n ce cv e1) p1)
    (eqTrans (evalGEnv-subst n ce cv e2) p2))

justInj : {A : Set} {x y : A} -> Eq (just x) (just y) -> Eq x y
justInj refl = refl

------------------------------------------------------------------------
-- soundProofG (standard-semantics soundness for ProofG)
--
-- The cinstG/fcAll case requires a generalized de Bruijn env-swap
-- lemma (~100-150 lines). Left as a hole; does not affect Goedel II.
------------------------------------------------------------------------

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
  substTFG : (A : Formula) -> (te : TEnvG) -> (ce : CEnvG) -> (cv : Code) ->
    TrueFG _ te (extendCEnvG ce cv) A ->
    TrueFG _ te ce (substFormulaCode0 (clit cv) A)
  unsubstTFG : (A : Formula) -> (te : TEnvG) -> (ce : CEnvG) -> (cv : Code) ->
    TrueFG _ te ce (substFormulaCode0 (clit cv) A) ->
    TrueFG _ te (extendCEnvG ce cv) A
  substTFG fbot te ce cv g = g
  substTFG (feq _ _) te ce cv g = g
  substTFG (fimp a b) te ce cv g = \ x -> substTFG b te ce cv (g (unsubstTFG a te ce cv x))
  substTFG (fall a) te ce cv g = \ t -> substTFG a (extendTEnvG te t) ce cv (g t)
  substTFG (fcode _) te ce cv g = g
  substTFG (fceq e1 e2) te ce cv g = substTCEG ce cv e1 e2 g
  substTFG (fcAll a) te ce cv g = {!!}  -- requires generalized de Bruijn env-swap
  unsubstTFG fbot te ce cv g = g
  unsubstTFG (feq _ _) te ce cv g = g
  unsubstTFG (fimp a b) te ce cv g = \ x -> unsubstTFG b te ce cv (g (substTFG a te ce cv x))
  unsubstTFG (fall a) te ce cv g = \ t -> unsubstTFG a (extendTEnvG te t) ce cv (g t)
  unsubstTFG (fcode _) te ce cv g = g
  unsubstTFG (fceq e1 e2) te ce cv g = unsubstTCEG ce cv e1 e2 g
  unsubstTFG (fcAll a) te ce cv g = {!!}  -- requires generalized de Bruijn env-swap
soundProofG (fceqTrG {e1} {e2} {e3} pf1 pf2) tenv cenv =
  trHelper (soundProofG pf1 tenv cenv) (soundProofG pf2 tenv cenv)
  where
  trHelper : TrueCodeEqG _ cenv e1 e2 -> TrueCodeEqG _ cenv e2 e3 ->
    TrueCodeEqG _ cenv e1 e3
  trHelper (mkSigma c1 (mkProd2 p1 p2)) (mkSigma c2 (mkProd2 q1 q2)) =
    mkSigma c1 (mkProd2 p1
      (eqSubst (\ c -> Eq (evalGEnv _ cenv e3) (just c))
               (eqSym (justInj (eqTrans (eqSym p2) q1)))
               q2))
soundProofG (fceqSyG {e1} {e2} pf) tenv cenv =
  syHelper (soundProofG pf tenv cenv)
  where
  syHelper : TrueCodeEqG _ cenv e1 e2 -> TrueCodeEqG _ cenv e2 e1
  syHelper (mkSigma c (mkProd2 p1 p2)) = mkSigma c (mkProd2 p2 p1)
