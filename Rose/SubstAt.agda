{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.SubstAt where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs; finToNat;
         Maybe; nothing; just; maybeMap;
         Eq; refl; eqCong; eqCong2)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Rename using (rename)

------------------------------------------------------------------------
-- Thick map: remove one variable from the scope.
--
-- thick k i  returns  nothing   if  i = k   (variable hit)
--                     just j    if  i /= k  (adjusted variable)
--
-- This is a standard operation from de Bruijn index theory.

thick : {n : Nat} -> Fin (suc n) -> Fin (suc n) -> Maybe (Fin n)
thick fz     fz     = nothing
thick fz     (fs i) = just i
thick {suc n} (fs k) fz     = just fz
thick {suc n} (fs k) (fs i) = maybeMap fs (thick k i)

------------------------------------------------------------------------
-- Inject a closed term into an arbitrary scope.
--
-- Since closed terms have no variables, renaming with the empty
-- function (Fin 0 -> Fin n) preserves the structure while changing
-- the scope index.  rename handles lifting under binders.

absurdFin : {n : Nat} -> Fin zero -> Fin n
absurdFin ()

injectTerm : {n : Nat} -> Term zero -> Term n
injectTerm = rename absurdFin

------------------------------------------------------------------------
-- Substitute a closed term at a given variable position.
--
-- substAt k r t: in t : Term (suc n), replace variable k with
-- (injected) r : Term 0, and adjust all other variables.
--
-- Uses thick for the variable case.

substAtVarMaybe : {n : Nat} -> Term zero -> Maybe (Fin n) -> Term n
substAtVarMaybe r nothing  = injectTerm r
substAtVarMaybe r (just j) = var j

substAt : {n : Nat} -> Fin (suc n) -> Term zero -> Term (suc n) -> Term n
substAt k r (var i)     = substAtVarMaybe r (thick k i)
substAt k r leaf        = leaf
substAt k r (pair t u)  = pair (substAt k r t) (substAt k r u)
substAt k r (cas t u v) =
  cas (substAt k r t) (substAt k r u) (substAt (fs (fs k)) r v)
substAt k r (rec t z s) =
  rec (substAt k r t) (substAt k r z) (substAt (fs (fs (fs (fs k)))) r s)
substAt k r (niter t st s) =
  niter (substAt k r t) (substAt k r st) (substAt (fs (fs k)) r s)

------------------------------------------------------------------------
-- Specialized: substitute for variable 0.

substAt0 : {n : Nat} -> Term zero -> Term (suc n) -> Term n
substAt0 r t = substAt fz r t
