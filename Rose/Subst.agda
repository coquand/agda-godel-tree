{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Subst where

open import Rose.Base using (Nat; zero; suc; Fin; fz; fs)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Rename using (rename)

------------------------------------------------------------------------
-- Lifting a substitution under one binder.
--
-- Variable 0 stays as variable 0; all others are weakened by rename fs.

liftSubst : {m n : Nat} -> (Fin m -> Term n) -> Fin (suc m) -> Term (suc n)
liftSubst sig fz     = var fz
liftSubst sig (fs i) = rename fs (sig i)

-- Lift under two binders (for cas step).
liftSubst2 : {m n : Nat} -> (Fin m -> Term n)
           -> Fin (suc (suc m)) -> Term (suc (suc n))
liftSubst2 sig = liftSubst (liftSubst sig)

-- Lift under four binders (for rec step).
liftSubst4 : {m n : Nat} -> (Fin m -> Term n)
           -> Fin (suc (suc (suc (suc m)))) -> Term (suc (suc (suc (suc n))))
liftSubst4 sig = liftSubst (liftSubst (liftSubst (liftSubst sig)))

------------------------------------------------------------------------
-- Substitution (action of (Fin m -> Term n) on terms).

subst : {m n : Nat} -> (Fin m -> Term n) -> Term m -> Term n
subst sig (var i)     = sig i
subst sig leaf        = leaf
subst sig (pair t u)  = pair (subst sig t) (subst sig u)
subst sig (cas t u v) = cas (subst sig t) (subst sig u) (subst (liftSubst2 sig) v)
subst sig (rec t z s) = rec (subst sig t) (subst sig z) (subst (liftSubst4 sig) s)
subst sig (niter t st s) = niter (subst sig t) (subst sig st) (subst (liftSubst2 sig) s)

------------------------------------------------------------------------
-- Single substitution: replace variable 0, shift the rest down.

singleSubst : {n : Nat} -> Term n -> Fin (suc n) -> Term n
singleSubst t fz     = t
singleSubst t (fs i) = var i

subst0 : {n : Nat} -> Term (suc n) -> Term n -> Term n
subst0 body arg = subst (singleSubst arg) body
