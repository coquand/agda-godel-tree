{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.CodeProps where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs; finToNat; natToFin;
         Eq; refl; eqCong; eqCong2; eqCong3; eqTrans;
         Maybe; nothing; just; maybeMap; maybeBind)
open import Rose.Tree using (Tree; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Rename using (rename; liftRen)
open import Rose.Code
  using (natCode; codeTerm; tagVar; tagPair; tagCase; tagRec; tagNiter;
         decodeTerm; decodeNat)
open import Rose.SubstAt using (absurdFin; injectTerm)

------------------------------------------------------------------------
-- Lifting preserves finToNat.

abstract

  liftRen-pres : {m n : Nat} -> (r : Fin m -> Fin n)
    -> ((i : Fin m) -> Eq (finToNat (r i)) (finToNat i))
    -> (j : Fin (suc m)) -> Eq (finToNat (liftRen r j)) (finToNat j)
  liftRen-pres r h fz     = refl
  liftRen-pres r h (fs i) = eqCong suc (h i)

------------------------------------------------------------------------
-- codeTerm is invariant under renamings that preserve finToNat.
--
-- This is the key general lemma.  It says codeTerm only sees the
-- numeric index of each variable, not its Fin provenance.

  codeTerm-rename :
    {m n : Nat} ->
    (r : Fin m -> Fin n) ->
    ((i : Fin m) -> Eq (finToNat (r i)) (finToNat i)) ->
    (t : Term m) ->
    Eq (codeTerm (rename r t)) (codeTerm t)
  codeTerm-rename r h (var i) =
    eqCong (\ x -> nd tagVar (natCode x)) (h i)
  codeTerm-rename r h leaf = refl
  codeTerm-rename r h (pair t u) =
    eqCong2 (\ x y -> nd tagPair (nd x y))
      (codeTerm-rename r h t)
      (codeTerm-rename r h u)
  codeTerm-rename r h (cas t u v) =
    eqCong3 (\ x y z -> nd tagCase (nd x (nd y z)))
      (codeTerm-rename r h t)
      (codeTerm-rename r h u)
      (codeTerm-rename (liftRen (liftRen r))
        (liftRen-pres (liftRen r) (liftRen-pres r h)) v)
  codeTerm-rename r h (rec t z s) =
    eqCong3 (\ x y w -> nd tagRec (nd x (nd y w)))
      (codeTerm-rename r h t)
      (codeTerm-rename r h z)
      (codeTerm-rename
        (liftRen (liftRen (liftRen (liftRen r))))
        (liftRen-pres (liftRen (liftRen (liftRen r)))
          (liftRen-pres (liftRen (liftRen r))
            (liftRen-pres (liftRen r)
              (liftRen-pres r h)))) s)
  codeTerm-rename r h (niter t st s) =
    eqCong3 (\ x y z -> nd tagNiter (nd x (nd y z)))
      (codeTerm-rename r h t)
      (codeTerm-rename r h st)
      (codeTerm-rename
        (liftRen (liftRen r))
        (liftRen-pres (liftRen r)
          (liftRen-pres r h)) s)

------------------------------------------------------------------------
-- Corollary: codeTerm commutes with injectTerm.

  absurdFinPres : {n : Nat} -> (i : Fin zero) ->
    Eq (finToNat (absurdFin {n} i)) (finToNat i)
  absurdFinPres ()

  codeTerm-injectTerm :
    {n : Nat} -> (t : Term zero) ->
    Eq (codeTerm {n} (injectTerm t)) (codeTerm {zero} t)
  codeTerm-injectTerm t = codeTerm-rename absurdFin absurdFinPres t

------------------------------------------------------------------------
-- Decode round-trip: decoding a coded value gives back the original.

  -- natCode round-trip.
  decodeNat-natCode : (k : Nat) -> Eq (decodeNat (natCode k)) (just k)
  decodeNat-natCode zero = refl
  decodeNat-natCode (suc k) = eqCong (maybeMap suc) (decodeNat-natCode k)

  -- natToFin round-trip.
  natToFin-finToNat : {n : Nat} (i : Fin n) ->
    Eq (natToFin n (finToNat i)) (just i)
  natToFin-finToNat fz = refl
  natToFin-finToNat (fs i) = eqCong (maybeMap fs) (natToFin-finToNat i)

  -- Main round-trip: decodeTerm n (codeTerm t) = just t.
  decodeTerm-codeTerm : {n : Nat} (t : Term n) ->
    Eq (decodeTerm n (codeTerm t)) (just t)
  decodeTerm-codeTerm leaf = refl
  decodeTerm-codeTerm (var i) =
    eqTrans
      (eqCong (\ x -> maybeBind x (\ k -> maybeMap var (natToFin _ k)))
              (decodeNat-natCode (finToNat i)))
      (eqCong (maybeMap var) (natToFin-finToNat i))
  decodeTerm-codeTerm (pair t u) =
    eqTrans
      (eqCong (\ x -> maybeBind x
                (\ t' -> maybeMap (pair t') (decodeTerm _ (codeTerm u))))
              (decodeTerm-codeTerm t))
      (eqCong (maybeMap (pair t)) (decodeTerm-codeTerm u))
  decodeTerm-codeTerm (cas t u v) =
    eqTrans
      (eqCong (\ x -> maybeBind x (\ t' ->
                maybeBind (decodeTerm _ (codeTerm u)) (\ u' ->
                maybeMap (cas t' u') (decodeTerm _ (codeTerm v)))))
              (decodeTerm-codeTerm t))
      (eqTrans
        (eqCong (\ x -> maybeBind x (\ u' ->
                  maybeMap (cas t u') (decodeTerm _ (codeTerm v))))
                (decodeTerm-codeTerm u))
        (eqCong (maybeMap (cas t u)) (decodeTerm-codeTerm v)))
  decodeTerm-codeTerm (rec t z s) =
    eqTrans
      (eqCong (\ x -> maybeBind x (\ t' ->
                maybeBind (decodeTerm _ (codeTerm z)) (\ z' ->
                maybeMap (rec t' z') (decodeTerm _ (codeTerm s)))))
              (decodeTerm-codeTerm t))
      (eqTrans
        (eqCong (\ x -> maybeBind x (\ z' ->
                  maybeMap (rec t z') (decodeTerm _ (codeTerm s))))
                (decodeTerm-codeTerm z))
        (eqCong (maybeMap (rec t z)) (decodeTerm-codeTerm s)))
  decodeTerm-codeTerm (niter t st s) =
    eqTrans
      (eqCong (\ x -> maybeBind x (\ t' ->
                maybeBind (decodeTerm _ (codeTerm st)) (\ st' ->
                maybeMap (niter t' st') (decodeTerm _ (codeTerm s)))))
              (decodeTerm-codeTerm t))
      (eqTrans
        (eqCong (\ x -> maybeBind x (\ st' ->
                  maybeMap (niter t st') (decodeTerm _ (codeTerm s))))
                (decodeTerm-codeTerm st))
        (eqCong (maybeMap (niter t st)) (decodeTerm-codeTerm s)))
