{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.CodeProps where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs; finToNat;
         Eq; refl; eqCong; eqCong2; eqCong3)
open import Rose.Tree using (Tree; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec)
open import Rose.Rename using (rename; liftRen)
open import Rose.Code
  using (natCode; codeTerm; tagVar; tagPair; tagCase; tagRec)
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

------------------------------------------------------------------------
-- Corollary: codeTerm commutes with injectTerm.

  absurdFinPres : {n : Nat} -> (i : Fin zero) ->
    Eq (finToNat (absurdFin {n} i)) (finToNat i)
  absurdFinPres ()

  codeTerm-injectTerm :
    {n : Nat} -> (t : Term zero) ->
    Eq (codeTerm {n} (injectTerm t)) (codeTerm {zero} t)
  codeTerm-injectTerm t = codeTerm-rename absurdFin absurdFinPres t
