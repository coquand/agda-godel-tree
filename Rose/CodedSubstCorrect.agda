{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.CodedSubstCorrect where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs; finToNat;
         Maybe; nothing; just; maybeMap;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqCong3; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Code
  using (natCode; codeTerm; tagVar; tagPair; tagCase; tagRec; tagNiter)
open import Rose.SubstAt
  using (thick; substAtVarMaybe; substAt; injectTerm)
open import Rose.CodedSubst
  using (thickNatCode; thickVarResult; codedSubstVar;
         codedSubst; codedSubstTagged; codedSubst0)
open import Rose.CodeProps
  using (codeTerm-injectTerm)

------------------------------------------------------------------------
-- maybeMap fusion: nd lf wrapping corresponds to fs wrapping.

abstract

  maybeMapLift : {n : Nat} -> (x : Maybe (Fin n))
    -> Eq (maybeMap (nd lf) (maybeMap (\ j -> natCode (finToNat j)) x))
         (maybeMap (\ j -> natCode (finToNat j)) (maybeMap fs x))
  maybeMapLift nothing  = refl
  maybeMapLift (just j) = refl

------------------------------------------------------------------------
-- thickNatCode agrees with thick (up to natCode . finToNat).

  thickNatCode-correct :
    {n : Nat} -> (k : Fin (suc n)) -> (i : Fin (suc n)) ->
    Eq (thickNatCode (finToNat k) (natCode (finToNat i)))
       (maybeMap (\ j -> natCode (finToNat j)) (thick k i))
  thickNatCode-correct fz     fz     = refl
  thickNatCode-correct fz     (fs i) = refl
  thickNatCode-correct {suc n} (fs k) fz     = refl
  thickNatCode-correct {suc n} (fs k) (fs i) =
    eqTrans (eqCong (maybeMap (nd lf)) (thickNatCode-correct k i))
            (maybeMapLift (thick k i))

------------------------------------------------------------------------
-- Lifting the variable result through nd lf / fs.
--
-- Given the correspondence at the inner level (mt ~ mf),
-- derive the correspondence at the outer level
-- (maybeMap (nd lf) mt ~ maybeMap fs mf).

  liftVarCorrect :
    {n : Nat} -> (r : Term zero) ->
    (mt : Maybe Tree) -> (mf : Maybe (Fin n)) ->
    Eq mt (maybeMap (\ j -> natCode (finToNat j)) mf) ->
    Eq (thickVarResult (codeTerm r) (maybeMap (nd lf) mt))
       (codeTerm {suc n} (substAtVarMaybe r (maybeMap fs mf)))
  liftVarCorrect r mt nothing p =
    eqSubst
      (\ x -> Eq (thickVarResult (codeTerm r) (maybeMap (nd lf) x))
                  (codeTerm (injectTerm r)))
      (eqSym p)
      (eqSym (codeTerm-injectTerm r))
  liftVarCorrect r mt (just j) p =
    eqSubst
      (\ x -> Eq (thickVarResult (codeTerm r) (maybeMap (nd lf) x))
                  (nd tagVar (nd lf (natCode (finToNat j)))))
      (eqSym p)
      refl

------------------------------------------------------------------------
-- Variable case of the correctness theorem.

  codedSubstVar-correct :
    {n : Nat} -> (k : Fin (suc n)) -> (r : Term zero) ->
    (i : Fin (suc n)) ->
    Eq (codedSubstVar (codeTerm r) (finToNat k) (natCode (finToNat i)))
       (codeTerm {n} (substAtVarMaybe r (thick k i)))
  codedSubstVar-correct fz r fz =
    eqSym (codeTerm-injectTerm r)
  codedSubstVar-correct fz r (fs i) = refl
  codedSubstVar-correct {suc n} (fs k) r fz = refl
  codedSubstVar-correct {suc n} (fs k) r (fs i) =
    liftVarCorrect r
      (thickNatCode (finToNat k) (natCode (finToNat i)))
      (thick k i)
      (thickNatCode-correct k i)

------------------------------------------------------------------------
-- Main theorem: codedSubst on codes = codeTerm of substAt.
--
-- This is the binary-tree analogue of Rose's Section 3.4:
-- coded substitution agrees with syntactic substitution.

  codedSubst-correct :
    {n : Nat} -> (k : Fin (suc n)) -> (r : Term zero) ->
    (t : Term (suc n)) ->
    Eq (codedSubst (codeTerm r) (finToNat k) (codeTerm t))
       (codeTerm (substAt k r t))
  codedSubst-correct k r (var i) =
    codedSubstVar-correct k r i
  codedSubst-correct k r leaf = refl
  codedSubst-correct k r (pair t u) =
    eqCong2 (\ x y -> nd tagPair (nd x y))
      (codedSubst-correct k r t)
      (codedSubst-correct k r u)
  codedSubst-correct k r (cas t u v) =
    eqCong3 (\ x y z -> nd tagCase (nd x (nd y z)))
      (codedSubst-correct k r t)
      (codedSubst-correct k r u)
      (codedSubst-correct (fs (fs k)) r v)
  codedSubst-correct k r (rec t z s) =
    eqCong3 (\ x y w -> nd tagRec (nd x (nd y w)))
      (codedSubst-correct k r t)
      (codedSubst-correct k r z)
      (codedSubst-correct (fs (fs (fs (fs k)))) r s)
  codedSubst-correct k r (niter t st s) =
    eqCong3 (\ x y z -> nd tagNiter (nd x (nd y z)))
      (codedSubst-correct k r t)
      (codedSubst-correct k r st)
      (codedSubst-correct (fs (fs k)) r s)

------------------------------------------------------------------------
-- Corollary: codedSubst0 on codes = codeTerm of substAt at fz.

  codedSubst0-correct :
    {n : Nat} -> (r : Term zero) -> (t : Term (suc n)) ->
    Eq (codedSubst0 (codeTerm r) (codeTerm t))
       (codeTerm (substAt fz r t))
  codedSubst0-correct r t = codedSubst-correct fz r t
