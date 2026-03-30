{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.ThEnum where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst;
         Maybe; nothing; just; maybeMap; maybeBind)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval using (eval; evalEnv; emptyEnv; TrueEq)
open import Rose.Equation using (Equation; equation)
open import Rose.Code using (codeTerm; codeEquation; decodeTerm)

------------------------------------------------------------------------
-- Default equation: leaf = leaf (trivially true).

defaultEq : Equation
defaultEq = equation leaf leaf

------------------------------------------------------------------------
-- Decode helpers: decode a term from a tree code, with a default.

fromMaybe0 : Maybe (Term zero) -> Term zero
fromMaybe0 nothing  = leaf
fromMaybe0 (just t) = t

fromMaybe2 : Maybe (Term (suc (suc zero))) -> Term (suc (suc zero))
fromMaybe2 nothing  = var fz
fromMaybe2 (just t) = t

fromMaybe4 : Maybe (Term (suc (suc (suc (suc zero))))) ->
             Term (suc (suc (suc (suc zero))))
fromMaybe4 nothing  = var fz
fromMaybe4 (just t) = t

decodeTm0 : Tree -> Term zero
decodeTm0 c = fromMaybe0 (decodeTerm zero c)

decodeTm2 : Tree -> Term (suc (suc zero))
decodeTm2 c = fromMaybe2 (decodeTerm (suc (suc zero)) c)

decodeTm4 : Tree -> Term (suc (suc (suc (suc zero))))
decodeTm4 c = fromMaybe4 (decodeTerm (suc (suc (suc (suc zero)))) c)

------------------------------------------------------------------------
-- Axiom dispatcher: ax : Tree -> Equation
--
-- Uses tree structure to select axiom scheme + parameters.
-- All patterns are non-overlapping for --exact-split.
--
-- Scheme selection by first child of outer nd:
--   lf              -> cas-leaf (payload = nd uc vc)
--   nd lf lf        -> rec-leaf (payload = nd zc sc)
--   nd lf (nd lf lf) -> niter-leaf (payload = nd stc stepc)
--   nd lf (nd lf (nd lf lf)) -> reflexivity (payload = tc)
--
-- Everything else -> defaultEq.

ax : Tree -> Equation
-- base
ax lf = defaultEq
-- scheme 0: cas-leaf
ax (nd lf lf) = defaultEq
ax (nd lf (nd uc vc)) =
  equation (cas leaf (decodeTm0 uc) (decodeTm2 vc)) (decodeTm0 uc)
-- scheme 1: rec-leaf
ax (nd (nd lf lf) lf) = defaultEq
ax (nd (nd lf lf) (nd zc sc)) =
  equation (rec leaf (decodeTm0 zc) (decodeTm4 sc)) (decodeTm0 zc)
-- scheme 2: niter-leaf
ax (nd (nd lf (nd lf lf)) lf) = defaultEq
ax (nd (nd lf (nd lf lf)) (nd stc stepc)) =
  equation (niter leaf (decodeTm0 stc) (decodeTm2 stepc)) (decodeTm0 stc)
-- scheme 3: reflexivity
ax (nd (nd lf (nd lf (nd lf lf))) tc) =
  equation (decodeTm0 tc) (decodeTm0 tc)
-- remaining: tag >= 4 or malformed
ax (nd (nd lf (nd lf (nd lf (nd a b)))) c) = defaultEq
ax (nd (nd lf (nd lf (nd (nd a b) c))) d) = defaultEq
ax (nd (nd lf (nd (nd a b) c)) d) = defaultEq
ax (nd (nd (nd a b) c) d) = defaultEq

------------------------------------------------------------------------
-- Axiom soundness.

ax-sound : (y : Tree) -> TrueEq (ax y)
ax-sound lf = refl
ax-sound (nd lf lf) = refl
ax-sound (nd lf (nd uc vc)) = refl
ax-sound (nd (nd lf lf) lf) = refl
ax-sound (nd (nd lf lf) (nd zc sc)) = refl
ax-sound (nd (nd lf (nd lf lf)) lf) = refl
ax-sound (nd (nd lf (nd lf lf)) (nd stc stepc)) = refl
ax-sound (nd (nd lf (nd lf (nd lf lf))) tc) = refl
ax-sound (nd (nd lf (nd lf (nd lf (nd a b)))) c) = refl
ax-sound (nd (nd lf (nd lf (nd (nd a b) c))) d) = refl
ax-sound (nd (nd lf (nd (nd a b) c)) d) = refl
ax-sound (nd (nd (nd a b) c) d) = refl

------------------------------------------------------------------------
-- Decidable tree equality: returns just refl if equal, nothing if not.

treeEqDec : (a b : Tree) -> Maybe (Eq a b)
treeEqDec lf lf = just refl
treeEqDec lf (nd a b) = nothing
treeEqDec (nd a b) lf = nothing
treeEqDec (nd a1 b1) (nd a2 b2) =
  maybeBind (treeEqDec a1 a2) (\ pa ->
  maybeMap (\ pb -> eqCong2 nd pa pb) (treeEqDec b1 b2))

------------------------------------------------------------------------
-- Equation operations.

eqLhs : Equation -> Term zero
eqLhs (equation l r) = l

eqRhs : Equation -> Term zero
eqRhs (equation l r) = r

symEq : Equation -> Equation
symEq (equation l r) = equation r l

symEq-sound : (e : Equation) -> TrueEq e -> TrueEq (symEq e)
symEq-sound (equation l r) p = eqSym p

------------------------------------------------------------------------
-- Transitivity helper.
--
-- Given eq1 and eq2, and a decision whether eval(rhs eq1) = eval(lhs eq2),
-- produce the transitive equation (or default if mismatch).

transEq : (eq1 eq2 : Equation) ->
  Maybe (Eq (eval (eqRhs eq1)) (eval (eqLhs eq2))) -> Equation
transEq eq1 eq2 nothing = defaultEq
transEq (equation l1 r1) (equation l2 r2) (just p) = equation l1 r2

transEq-sound : (eq1 eq2 : Equation) ->
  (m : Maybe (Eq (eval (eqRhs eq1)) (eval (eqLhs eq2)))) ->
  TrueEq eq1 -> TrueEq eq2 -> TrueEq (transEq eq1 eq2 m)
transEq-sound eq1 eq2 nothing s1 s2 = refl
transEq-sound (equation l1 r1) (equation l2 r2) (just p) s1 s2 =
  eqTrans s1 (eqTrans p s2)

------------------------------------------------------------------------
-- Theorem enumeration: thEq : Tree -> Equation
--
-- Proof tree structure:
--   lf -> axiom(lf)
--   nd lf payload -> axiom(payload)
--   nd (nd lf lf) proof -> symmetry of thEq(proof)
--   nd (nd lf (nd lf lf)) lf -> default
--   nd (nd lf (nd lf lf)) (nd p1 p2) -> transitivity
--   nd (nd lf (nd lf (nd a b))) c -> default (tag >= 3 or malformed)
--   nd (nd lf (nd (nd a b) c)) d -> default
--   nd (nd (nd a b) c) d -> default

thEq : Tree -> Equation
thEq lf = ax lf
thEq (nd lf payload) = ax payload
thEq (nd (nd lf lf) proof) = symEq (thEq proof)
thEq (nd (nd lf (nd lf lf)) lf) = defaultEq
thEq (nd (nd lf (nd lf lf)) (nd p1 p2)) =
  transEq (thEq p1) (thEq p2)
    (treeEqDec (eval (eqRhs (thEq p1))) (eval (eqLhs (thEq p2))))
thEq (nd (nd lf (nd lf (nd lf lf))) c) = defaultEq
thEq (nd (nd lf (nd lf (nd lf (nd a b)))) c) = defaultEq
thEq (nd (nd lf (nd lf (nd (nd a b) c))) d) = defaultEq
thEq (nd (nd lf (nd (nd a b) c)) d) = defaultEq
thEq (nd (nd (nd a b) c) d) = defaultEq

------------------------------------------------------------------------
-- Coded version.

th : Tree -> Tree
th y = codeEquation (thEq y)

------------------------------------------------------------------------
-- Soundness.

thEq-sound : (y : Tree) -> TrueEq (thEq y)
thEq-sound lf = ax-sound lf
thEq-sound (nd lf payload) = ax-sound payload
thEq-sound (nd (nd lf lf) proof) =
  symEq-sound (thEq proof) (thEq-sound proof)
thEq-sound (nd (nd lf (nd lf lf)) lf) = refl
thEq-sound (nd (nd lf (nd lf lf)) (nd p1 p2)) =
  transEq-sound (thEq p1) (thEq p2)
    (treeEqDec (eval (eqRhs (thEq p1))) (eval (eqLhs (thEq p2))))
    (thEq-sound p1) (thEq-sound p2)
thEq-sound (nd (nd lf (nd lf (nd lf lf))) c) = refl
thEq-sound (nd (nd lf (nd lf (nd lf (nd a b)))) c) = refl
thEq-sound (nd (nd lf (nd lf (nd (nd a b) c))) d) = refl
thEq-sound (nd (nd lf (nd (nd a b) c)) d) = refl
thEq-sound (nd (nd (nd a b) c) d) = refl

