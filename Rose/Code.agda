{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Code where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs; finToNat; natToFin;
         Maybe; nothing; just; maybeMap; maybeBind)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Equation using (Equation; equation)

------------------------------------------------------------------------
-- Encoding natural numbers as trees.
--
-- natCode 0     = lf
-- natCode (n+1) = nd lf (natCode n)

natCode : Nat -> Tree
natCode zero    = lf
natCode (suc n) = nd lf (natCode n)

------------------------------------------------------------------------
-- Tag constants.
--
-- Each term constructor gets a tag = natCode of its index.
-- This scheme is frozen: no further changes to tags.

tagLeaf : Tree
tagLeaf = lf

tagVar : Tree
tagVar = nd lf lf

tagPair : Tree
tagPair = nd lf (nd lf lf)

tagCase : Tree
tagCase = nd lf (nd lf (nd lf lf))

tagRec : Tree
tagRec = nd lf (nd lf (nd lf (nd lf lf)))

tagNiter : Tree
tagNiter = nd lf (nd lf (nd lf (nd lf (nd lf lf))))

------------------------------------------------------------------------
-- Encoding terms as trees (term codes).
--
-- Uniform format: nd TAG PAYLOAD
--
--   leaf       |->  nd tagLeaf lf
--   var i      |->  nd tagVar (natCode i)
--   pair t u   |->  nd tagPair (nd (code t) (code u))
--   cas t u v  |->  nd tagCase (nd (code t) (nd (code u) (code v)))
--   rec t z s  |->  nd tagRec  (nd (code t) (nd (code z) (code s)))
--
-- This replaces Rose's Section 3.1 numbering scheme.

codeTerm : {n : Nat} -> Term n -> Tree
codeTerm (var i)     = nd tagVar (natCode (finToNat i))
codeTerm leaf        = nd tagLeaf lf
codeTerm (pair t u)  = nd tagPair (nd (codeTerm t) (codeTerm u))
codeTerm (cas t u v) = nd tagCase (nd (codeTerm t) (nd (codeTerm u) (codeTerm v)))
codeTerm (rec t z s) = nd tagRec (nd (codeTerm t) (nd (codeTerm z) (codeTerm s)))
codeTerm (niter t st s) = nd tagNiter (nd (codeTerm t) (nd (codeTerm st) (codeTerm s)))

------------------------------------------------------------------------
-- Encoding equations as trees.

codeEquation : Equation -> Tree
codeEquation (equation l r) = nd (codeTerm l) (codeTerm r)

------------------------------------------------------------------------
-- Decoding natural numbers from trees.

decodeNat : Tree -> Maybe Nat
decodeNat lf              = just zero
decodeNat (nd lf t)       = maybeMap suc (decodeNat t)
decodeNat (nd (nd a b) t) = nothing

------------------------------------------------------------------------
-- Decoding terms from trees.
--
-- Every valid term code has the form (nd tag payload).
-- The tag is decoded as a Nat, then we dispatch on the tag number.

mutual

  decodeTerm : (n : Nat) -> Tree -> Maybe (Term n)
  decodeTerm n lf             = nothing
  decodeTerm n (nd tag payload) =
    maybeBind (decodeNat tag) (\ k -> decodeByTag n k payload)

  decodeByTag : (n : Nat) -> Nat -> Tree -> Maybe (Term n)
  -- tag 0 = leaf
  decodeByTag n zero lf = just leaf
  decodeByTag n zero (nd a b) = nothing
  -- tag 1 = var
  decodeByTag n (suc zero) payload =
    maybeBind (decodeNat payload) (\ k -> maybeMap var (natToFin n k))
  -- tag 2 = pair
  decodeByTag n (suc (suc zero)) lf = nothing
  decodeByTag n (suc (suc zero)) (nd ct cu) =
    maybeBind (decodeTerm n ct)
      (\ t -> maybeMap (pair t) (decodeTerm n cu))
  -- tag 3 = case
  decodeByTag n (suc (suc (suc zero))) lf = nothing
  decodeByTag n (suc (suc (suc zero))) (nd ct lf) = nothing
  decodeByTag n (suc (suc (suc zero))) (nd ct (nd cu cv)) =
    maybeBind (decodeTerm n ct) (\ t ->
    maybeBind (decodeTerm n cu) (\ u ->
    maybeMap  (cas t u) (decodeTerm (suc (suc n)) cv)))
  -- tag 4 = rec
  decodeByTag n (suc (suc (suc (suc zero)))) lf = nothing
  decodeByTag n (suc (suc (suc (suc zero)))) (nd ct lf) = nothing
  decodeByTag n (suc (suc (suc (suc zero)))) (nd ct (nd cz cs)) =
    maybeBind (decodeTerm n ct) (\ t ->
    maybeBind (decodeTerm n cz) (\ z ->
    maybeMap  (rec t z) (decodeTerm (suc (suc (suc (suc n)))) cs)))
  -- tag 5 = niter
  decodeByTag n (suc (suc (suc (suc (suc zero))))) lf = nothing
  decodeByTag n (suc (suc (suc (suc (suc zero))))) (nd ct lf) = nothing
  decodeByTag n (suc (suc (suc (suc (suc zero))))) (nd ct (nd cst cs)) =
    maybeBind (decodeTerm n ct) (\ t ->
    maybeBind (decodeTerm n cst) (\ st ->
    maybeMap  (niter t st) (decodeTerm (suc (suc n)) cs)))
  -- tag >= 6: invalid
  decodeByTag n (suc (suc (suc (suc (suc (suc k)))))) payload = nothing

------------------------------------------------------------------------
-- Decoding equations from trees.

decodeEquation : Tree -> Maybe Equation
decodeEquation lf = nothing
decodeEquation (nd cl cr) =
  maybeBind (decodeTerm zero cl) (\ l ->
  maybeMap  (equation l) (decodeTerm zero cr))

------------------------------------------------------------------------
-- TODO (future stages):
--
-- Rose Section 3.3 valuation:
--   Coded evaluation vo(x,y) / vl(x,y) operating on tree codes.
--   Now that eval handles case/rec, this becomes the internal
--   analogue definable in B*.
--
-- Rose Section 3.4 coded substitution:
--   codedSubst : Tree -> Tree -> Tree -> Tree
--   Operating on codes: substitute code x for the z-th variable
--   in term code y.  First define in Agda metatheory, then prove
--   correct, then represent as a closed Term 0.
--
-- Rose Section 3.7 theorem enumeration / proof checker:
--   th(y) or check : Tree -> Maybe Equation
--
-- Rose Theorem 17 (diagonal / fixed point):
--   Binary-tree analogue using codeTerm, reify, coded substitution.
--
-- Rose Theorem 18 (Goedel II):
--   Undecidability of consistency proposition in B.
