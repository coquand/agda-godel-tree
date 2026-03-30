{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.EvalSubst where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqCong3; eqSubst;
         Maybe; nothing; just; maybeMap)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Rename using (rename; liftRen; liftRen2; liftRen4)
open import Rose.SubstAt
  using (absurdFin; injectTerm; thick; substAtVarMaybe; substAt)
open import Rose.Eval
  using (Env; emptyEnv; extEnv; extEnv2; extEnv4;
         evalEnv; evalCas; evalRec; evalNiter; eval)

------------------------------------------------------------------------
-- Pointwise environment equality.

EnvEq : {n : Nat} -> Env n -> Env n -> Set
EnvEq {n} env1 env2 = (i : Fin n) -> Eq (env1 i) (env2 i)

------------------------------------------------------------------------
-- insertK: insert a value at position k in an environment.

insertK : {n : Nat} -> Fin (suc n) -> Tree -> Env n -> Env (suc n)
insertK fz v env fz = v
insertK fz v env (fs i) = env i
insertK {suc n} (fs k) v env fz = env fz
insertK {suc n} (fs k) v env (fs i) = insertK k v (\ j -> env (fs j)) i

------------------------------------------------------------------------
-- envIrr: pointwise equal environments give same eval.

mutual

  envIrr : {n : Nat} -> (env1 env2 : Env n) -> EnvEq env1 env2 ->
    (t : Term n) -> Eq (evalEnv env1 t) (evalEnv env2 t)
  envIrr env1 env2 p (var i) = p i
  envIrr env1 env2 p leaf = refl
  envIrr env1 env2 p (pair a b) =
    eqCong2 nd (envIrr env1 env2 p a) (envIrr env1 env2 p b)
  envIrr env1 env2 p (cas t u v) =
    eiCas env1 env2 p (evalEnv env1 t) (evalEnv env2 t)
      (envIrr env1 env2 p t) u v
  envIrr env1 env2 p (rec t z s) =
    eiRec env1 env2 p (evalEnv env1 t) (evalEnv env2 t)
      (envIrr env1 env2 p t) z s
  envIrr env1 env2 p (niter t st s) =
    eiNiter env1 env2 p
      (evalEnv env1 t) (evalEnv env2 t) (envIrr env1 env2 p t)
      (evalEnv env1 st) (evalEnv env2 st) (envIrr env1 env2 p st)
      s

  eiCas : {n : Nat} -> (env1 env2 : Env n) -> EnvEq env1 env2 ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (u : Term n) -> (v : Term (suc (suc n))) ->
    Eq (evalCas env1 t1 u v) (evalCas env2 t2 u v)
  eiCas env1 env2 p lf lf refl u v = envIrr env1 env2 p u
  eiCas env1 env2 p (nd a b) (nd a b) refl u v =
    envIrr (extEnv2 env1 a b) (extEnv2 env2 a b) (ee2 p a b) v

  eiRec : {n : Nat} -> (env1 env2 : Env n) -> EnvEq env1 env2 ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (z : Term n) -> (s : Term (suc (suc (suc (suc n))))) ->
    Eq (evalRec env1 t1 z s) (evalRec env2 t2 z s)
  eiRec env1 env2 p lf lf refl z s = envIrr env1 env2 p z
  eiRec env1 env2 p (nd a b) (nd a b) refl z s =
    envIrr
      (extEnv4 env1 a b (evalRec env1 a z s) (evalRec env1 b z s))
      (extEnv4 env2 a b (evalRec env2 a z s) (evalRec env2 b z s))
      (ee4 p a b
        (evalRec env1 a z s) (evalRec env2 a z s)
        (eiRec env1 env2 p a a refl z s)
        (evalRec env1 b z s) (evalRec env2 b z s)
        (eiRec env1 env2 p b b refl z s))
      s

  eiNiter : {n : Nat} -> (env1 env2 : Env n) -> EnvEq env1 env2 ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (st1 st2 : Tree) -> Eq st1 st2 ->
    (s : Term (suc (suc n))) ->
    Eq (evalNiter env1 t1 st1 s) (evalNiter env2 t2 st2 s)
  eiNiter env1 env2 p lf lf refl st1 st2 q s = q
  eiNiter env1 env2 p (nd a k) (nd a k) refl st1 st2 q s =
    eiNiter env1 env2 p k k refl
      (evalEnv (extEnv2 env1 st1 k) s)
      (evalEnv (extEnv2 env2 st2 k) s)
      (envIrr (extEnv2 env1 st1 k) (extEnv2 env2 st2 k)
        (ee2s p st1 st2 q k) s)
      s

  ee2 : {n : Nat} -> {env1 env2 : Env n} -> EnvEq env1 env2 ->
    (a b : Tree) -> EnvEq (extEnv2 env1 a b) (extEnv2 env2 a b)
  ee2 p a b fz = refl
  ee2 p a b (fs fz) = refl
  ee2 p a b (fs (fs i)) = p i

  ee2s : {n : Nat} -> {env1 env2 : Env n} -> EnvEq env1 env2 ->
    (st1 st2 : Tree) -> Eq st1 st2 -> (k : Tree) ->
    EnvEq (extEnv2 env1 st1 k) (extEnv2 env2 st2 k)
  ee2s p st1 st2 q k fz = refl
  ee2s p st1 st2 q k (fs fz) = q
  ee2s p st1 st2 q k (fs (fs i)) = p i

  ee4 : {n : Nat} -> {env1 env2 : Env n} -> EnvEq env1 env2 ->
    (a b : Tree) ->
    (ra1 ra2 : Tree) -> Eq ra1 ra2 ->
    (rb1 rb2 : Tree) -> Eq rb1 rb2 ->
    EnvEq (extEnv4 env1 a b ra1 rb1) (extEnv4 env2 a b ra2 rb2)
  ee4 p a b ra1 ra2 qa rb1 rb2 qb fz = qb
  ee4 p a b ra1 ra2 qa rb1 rb2 qb (fs fz) = qa
  ee4 p a b ra1 ra2 qa rb1 rb2 qb (fs (fs fz)) = refl
  ee4 p a b ra1 ra2 qa rb1 rb2 qb (fs (fs (fs fz))) = refl
  ee4 p a b ra1 ra2 qa rb1 rb2 qb (fs (fs (fs (fs i)))) = p i

------------------------------------------------------------------------
-- evalRename: eval commutes with renaming.

mutual

  evalRename : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (t : Term m) ->
    Eq (evalEnv env (rename rho t)) (evalEnv (\ i -> env (rho i)) t)
  evalRename env rho (var i) = refl
  evalRename env rho leaf = refl
  evalRename env rho (pair a b) =
    eqCong2 nd (evalRename env rho a) (evalRename env rho b)
  evalRename env rho (cas t u v) =
    erCas env rho (evalEnv env (rename rho t))
      (evalEnv (\ i -> env (rho i)) t) (evalRename env rho t) u v
  evalRename env rho (rec t z s) =
    erRec env rho (evalEnv env (rename rho t))
      (evalEnv (\ i -> env (rho i)) t) (evalRename env rho t) z s
  evalRename env rho (niter t st s) =
    erNiter env rho
      (evalEnv env (rename rho t)) (evalEnv (\ i -> env (rho i)) t)
      (evalRename env rho t)
      (evalEnv env (rename rho st)) (evalEnv (\ i -> env (rho i)) st)
      (evalRename env rho st) s

  erCas : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (u : Term m) -> (v : Term (suc (suc m))) ->
    Eq (evalCas env t1 (rename rho u) (rename (liftRen2 rho) v))
       (evalCas (\ i -> env (rho i)) t2 u v)
  erCas env rho lf lf refl u v = evalRename env rho u
  erCas env rho (nd a b) (nd a b) refl u v =
    eqTrans
      (evalRename (extEnv2 env a b) (liftRen2 rho) v)
      (envIrr (\ j -> extEnv2 env a b (liftRen2 rho j))
              (extEnv2 (\ i -> env (rho i)) a b)
              (lr2 env rho a b) v)

  erRec : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (z : Term m) -> (s : Term (suc (suc (suc (suc m))))) ->
    Eq (evalRec env t1 (rename rho z) (rename (liftRen4 rho) s))
       (evalRec (\ i -> env (rho i)) t2 z s)
  erRec env rho lf lf refl z s = evalRename env rho z
  erRec env rho (nd a b) (nd a b) refl z s =
    let env' = \ i -> env (rho i) in
    let ra1 = evalRec env a (rename rho z) (rename (liftRen4 rho) s) in
    let ra2 = evalRec env' a z s in
    let rb1 = evalRec env b (rename rho z) (rename (liftRen4 rho) s) in
    let rb2 = evalRec env' b z s in
    eqTrans
      (evalRename (extEnv4 env a b ra1 rb1) (liftRen4 rho) s)
      (envIrr (\ j -> extEnv4 env a b ra1 rb1 (liftRen4 rho j))
              (extEnv4 env' a b ra2 rb2)
              (lr4 env rho a b ra1 ra2
                (erRec env rho a a refl z s)
                rb1 rb2 (erRec env rho b b refl z s))
              s)

  erNiter : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (st1 st2 : Tree) -> Eq st1 st2 ->
    (s : Term (suc (suc m))) ->
    Eq (evalNiter env t1 st1 (rename (liftRen2 rho) s))
       (evalNiter (\ i -> env (rho i)) t2 st2 s)
  erNiter env rho lf lf refl st1 st2 q s = q
  erNiter env rho (nd a k) (nd a k) refl st1 st2 q s =
    let env' = \ i -> env (rho i) in
    erNiter env rho k k refl
      (evalEnv (extEnv2 env st1 k) (rename (liftRen2 rho) s))
      (evalEnv (extEnv2 env' st2 k) s)
      (eqTrans
        (evalRename (extEnv2 env st1 k) (liftRen2 rho) s)
        (envIrr (\ j -> extEnv2 env st1 k (liftRen2 rho j))
                (extEnv2 env' st2 k)
                (lr2s env rho st1 st2 q k) s))
      s

  lr2 : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (a b : Tree) -> (j : Fin (suc (suc m))) ->
    Eq (extEnv2 env a b (liftRen2 rho j))
       (extEnv2 (\ i -> env (rho i)) a b j)
  lr2 env rho a b fz = refl
  lr2 env rho a b (fs fz) = refl
  lr2 env rho a b (fs (fs i)) = refl

  lr2s : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (st1 st2 : Tree) -> Eq st1 st2 -> (k : Tree) ->
    (j : Fin (suc (suc m))) ->
    Eq (extEnv2 env st1 k (liftRen2 rho j))
       (extEnv2 (\ i -> env (rho i)) st2 k j)
  lr2s env rho st1 st2 q k fz = refl
  lr2s env rho st1 st2 q k (fs fz) = q
  lr2s env rho st1 st2 q k (fs (fs i)) = refl

  lr4 : {m n : Nat} -> (env : Env n) -> (rho : Fin m -> Fin n) ->
    (a b : Tree) ->
    (ra1 ra2 : Tree) -> Eq ra1 ra2 ->
    (rb1 rb2 : Tree) -> Eq rb1 rb2 ->
    (j : Fin (suc (suc (suc (suc m))))) ->
    Eq (extEnv4 env a b ra1 rb1 (liftRen4 rho j))
       (extEnv4 (\ i -> env (rho i)) a b ra2 rb2 j)
  lr4 env rho a b ra1 ra2 qa rb1 rb2 qb fz = qb
  lr4 env rho a b ra1 ra2 qa rb1 rb2 qb (fs fz) = qa
  lr4 env rho a b ra1 ra2 qa rb1 rb2 qb (fs (fs fz)) = refl
  lr4 env rho a b ra1 ra2 qa rb1 rb2 qb (fs (fs (fs fz))) = refl
  lr4 env rho a b ra1 ra2 qa rb1 rb2 qb (fs (fs (fs (fs i)))) = refl

------------------------------------------------------------------------
-- eval-injectTerm: injecting a closed term preserves eval.

eval-injectTerm : {n : Nat} -> (env : Env n) -> (r : Term zero) ->
  Eq (evalEnv env (injectTerm r)) (eval r)
eval-injectTerm env r =
  eqTrans (evalRename env absurdFin r)
          (envIrr (\ i -> env (absurdFin i)) emptyEnv (\ ()) r)

------------------------------------------------------------------------
-- substVarFs: substAtVarMaybe distributes over maybeMap fs / rename.

substVarFs : {n : Nat} -> (env : Env (suc n)) -> (r : Term zero) ->
  (m : Maybe (Fin n)) ->
  Eq (evalEnv env (substAtVarMaybe r (maybeMap fs m)))
     (evalEnv (\ j -> env (fs j)) (substAtVarMaybe r m))
substVarFs env r nothing =
  eqTrans (eval-injectTerm env r)
          (eqSym (eval-injectTerm (\ j -> env (fs j)) r))
substVarFs env r (just j) = refl

------------------------------------------------------------------------
-- evalSubstAtK: eval commutes with substAt at arbitrary position k.
--
--   evalEnv env (substAt k r t) = evalEnv (insertK k (eval r) env) t

mutual

  evalSubstAtK : {n : Nat} -> (k : Fin (suc n)) -> (env : Env n) ->
    (r : Term zero) -> (t : Term (suc n)) ->
    Eq (evalEnv env (substAt k r t))
       (evalEnv (insertK k (eval r) env) t)
  evalSubstAtK k env r (var i) = evalVarCase k env r i
  evalSubstAtK k env r leaf = refl
  evalSubstAtK k env r (pair a b) =
    eqCong2 nd (evalSubstAtK k env r a) (evalSubstAtK k env r b)
  evalSubstAtK k env r (cas t u v) =
    esCas k env r
      (evalEnv env (substAt k r t))
      (evalEnv (insertK k (eval r) env) t)
      (evalSubstAtK k env r t)
      u v
  evalSubstAtK k env r (rec t z s) =
    esRec k env r
      (evalEnv env (substAt k r t))
      (evalEnv (insertK k (eval r) env) t)
      (evalSubstAtK k env r t)
      z s
  evalSubstAtK k env r (niter t st s) =
    esNiter k env r
      (evalEnv env (substAt k r t))
      (evalEnv (insertK k (eval r) env) t)
      (evalSubstAtK k env r t)
      (evalEnv env (substAt k r st))
      (evalEnv (insertK k (eval r) env) st)
      (evalSubstAtK k env r st)
      s

  -- Variable case
  evalVarCase : {n : Nat} -> (k : Fin (suc n)) -> (env : Env n) ->
    (r : Term zero) -> (i : Fin (suc n)) ->
    Eq (evalEnv env (substAtVarMaybe r (thick k i)))
       (insertK k (eval r) env i)
  evalVarCase fz env r fz = eval-injectTerm env r
  evalVarCase fz env r (fs i) = refl
  evalVarCase {suc n} (fs k) env r fz = refl
  evalVarCase {suc n} (fs k) env r (fs i) =
    eqTrans (substVarFs env r (thick k i))
            (evalVarCase k (\ j -> env (fs j)) r i)

  -- cas case
  esCas : {n : Nat} -> (k : Fin (suc n)) -> (env : Env n) ->
    (r : Term zero) ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (u : Term (suc n)) -> (v : Term (suc (suc (suc n)))) ->
    Eq (evalCas env t1 (substAt k r u) (substAt (fs (fs k)) r v))
       (evalCas (insertK k (eval r) env) t2 u v)
  esCas k env r lf lf refl u v = evalSubstAtK k env r u
  esCas k env r (nd a b) (nd a b) refl u v =
    eqTrans
      (evalSubstAtK (fs (fs k)) (extEnv2 env a b) r v)
      (envIrr (insertK (fs (fs k)) (eval r) (extEnv2 env a b))
              (extEnv2 (insertK k (eval r) env) a b)
              (ikCas k (eval r) env a b) v)

  -- rec case
  esRec : {n : Nat} -> (k : Fin (suc n)) -> (env : Env n) ->
    (r : Term zero) ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (z : Term (suc n)) ->
    (s : Term (suc (suc (suc (suc (suc n)))))) ->
    Eq (evalRec env t1 (substAt k r z) (substAt (fs (fs (fs (fs k)))) r s))
       (evalRec (insertK k (eval r) env) t2 z s)
  esRec k env r lf lf refl z s = evalSubstAtK k env r z
  esRec k env r (nd a b) (nd a b) refl z s =
    let env' = insertK k (eval r) env in
    let ra1 = evalRec env a (substAt k r z) (substAt (fs (fs (fs (fs k)))) r s) in
    let ra2 = evalRec env' a z s in
    let rb1 = evalRec env b (substAt k r z) (substAt (fs (fs (fs (fs k)))) r s) in
    let rb2 = evalRec env' b z s in
    eqTrans
      (evalSubstAtK (fs (fs (fs (fs k)))) (extEnv4 env a b ra1 rb1) r s)
      (envIrr (insertK (fs (fs (fs (fs k)))) (eval r) (extEnv4 env a b ra1 rb1))
              (extEnv4 env' a b ra2 rb2)
              (ikRec k (eval r) env a b
                ra1 ra2 (esRec k env r a a refl z s)
                rb1 rb2 (esRec k env r b b refl z s))
              s)

  -- niter case
  esNiter : {n : Nat} -> (k : Fin (suc n)) -> (env : Env n) ->
    (r : Term zero) ->
    (t1 t2 : Tree) -> Eq t1 t2 ->
    (st1 st2 : Tree) -> Eq st1 st2 ->
    (s : Term (suc (suc (suc n)))) ->
    Eq (evalNiter env t1 st1 (substAt (fs (fs k)) r s))
       (evalNiter (insertK k (eval r) env) t2 st2 s)
  esNiter k env r lf lf refl st1 st2 q s = q
  esNiter k env r (nd a kk) (nd a kk) refl st1 st2 q s =
    let env' = insertK k (eval r) env in
    esNiter k env r kk kk refl
      (evalEnv (extEnv2 env st1 kk) (substAt (fs (fs k)) r s))
      (evalEnv (extEnv2 env' st2 kk) s)
      (eqTrans
        (evalSubstAtK (fs (fs k)) (extEnv2 env st1 kk) r s)
        (envIrr (insertK (fs (fs k)) (eval r) (extEnv2 env st1 kk))
                (extEnv2 env' st2 kk)
                (ikNiter k (eval r) env st1 st2 q kk) s))
      s

  -- insertK commutes with extEnv2 for cas
  ikCas : {n : Nat} -> (k : Fin (suc n)) -> (v : Tree) ->
    (env : Env n) -> (a b : Tree) ->
    (j : Fin (suc (suc (suc n)))) ->
    Eq (insertK (fs (fs k)) v (extEnv2 env a b) j)
       (extEnv2 (insertK k v env) a b j)
  ikCas k v env a b fz = refl
  ikCas k v env a b (fs fz) = refl
  ikCas k v env a b (fs (fs i)) = refl

  -- insertK commutes with extEnv4 for rec
  ikRec : {n : Nat} -> (k : Fin (suc n)) -> (v : Tree) ->
    (env : Env n) -> (a b : Tree) ->
    (ra1 ra2 : Tree) -> Eq ra1 ra2 ->
    (rb1 rb2 : Tree) -> Eq rb1 rb2 ->
    (j : Fin (suc (suc (suc (suc (suc n)))))) ->
    Eq (insertK (fs (fs (fs (fs k)))) v (extEnv4 env a b ra1 rb1) j)
       (extEnv4 (insertK k v env) a b ra2 rb2 j)
  ikRec k v env a b ra1 ra2 qa rb1 rb2 qb fz = qb
  ikRec k v env a b ra1 ra2 qa rb1 rb2 qb (fs fz) = qa
  ikRec k v env a b ra1 ra2 qa rb1 rb2 qb (fs (fs fz)) = refl
  ikRec k v env a b ra1 ra2 qa rb1 rb2 qb (fs (fs (fs fz))) = refl
  ikRec k v env a b ra1 ra2 qa rb1 rb2 qb (fs (fs (fs (fs i)))) = refl

  -- insertK commutes with extEnv2 for niter
  ikNiter : {n : Nat} -> (k : Fin (suc n)) -> (v : Tree) ->
    (env : Env n) -> (st1 st2 : Tree) -> Eq st1 st2 ->
    (kk : Tree) ->
    (j : Fin (suc (suc (suc n)))) ->
    Eq (insertK (fs (fs k)) v (extEnv2 env st1 kk) j)
       (extEnv2 (insertK k v env) st2 kk j)
  ikNiter k v env st1 st2 q kk fz = refl
  ikNiter k v env st1 st2 q kk (fs fz) = q
  ikNiter k v env st1 st2 q kk (fs (fs i)) = refl

------------------------------------------------------------------------
-- Top-level corollary: eval of substAt fz for closed terms.

insertK-fz : {n : Nat} -> (v : Tree) -> (env : Env n) ->
  (i : Fin (suc n)) -> Eq (insertK fz v env i) (extEnv env v i)
insertK-fz v env fz = refl
insertK-fz v env (fs i) = refl

eval-substAt : (r : Term zero) -> (t : Term (suc zero)) ->
  Eq (eval (substAt fz r t)) (evalEnv (extEnv emptyEnv (eval r)) t)
eval-substAt r t =
  eqTrans (evalSubstAtK fz emptyEnv r t)
          (envIrr (insertK fz (eval r) emptyEnv) (extEnv emptyEnv (eval r))
                  (insertK-fz (eval r) emptyEnv) t)
