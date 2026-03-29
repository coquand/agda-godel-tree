{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Rename where

open import Rose.Base using (Nat; suc; Fin; fz; fs)
open import Rose.Term using (Term; var; leaf; pair; cas; rec)

------------------------------------------------------------------------
-- Lifting a renaming under one binder.

liftRen : {m n : Nat} -> (Fin m -> Fin n) -> Fin (suc m) -> Fin (suc n)
liftRen r fz     = fz
liftRen r (fs i) = fs (r i)

-- Lift under two binders (for cas step).
liftRen2 : {m n : Nat} -> (Fin m -> Fin n)
         -> Fin (suc (suc m)) -> Fin (suc (suc n))
liftRen2 r = liftRen (liftRen r)

-- Lift under four binders (for rec step).
liftRen4 : {m n : Nat} -> (Fin m -> Fin n)
         -> Fin (suc (suc (suc (suc m)))) -> Fin (suc (suc (suc (suc n))))
liftRen4 r = liftRen (liftRen (liftRen (liftRen r)))

------------------------------------------------------------------------
-- Renaming (action of Fin m -> Fin n on terms).

rename : {m n : Nat} -> (Fin m -> Fin n) -> Term m -> Term n
rename r (var i)    = var (r i)
rename r leaf       = leaf
rename r (pair t u) = pair (rename r t) (rename r u)
rename r (cas t u v) = cas (rename r t) (rename r u) (rename (liftRen2 r) v)
rename r (rec t z s) = rec (rename r t) (rename r z) (rename (liftRen4 r) s)
