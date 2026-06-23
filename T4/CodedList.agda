{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CodedList -- a clean INTERNAL library for reasoning about coded LISTS
-- (List = Nil | Cons Term List), the list half of the coded inductive-type
-- toolkit the PR-completion CR plan needs (RedStar = list of parallel steps;
-- cr by double list induction).  Companion of T4.BinTree / T4.BinTreeInd
-- (binary trees) and T4.CertTree (the 5-constructor cert tree).
--
-- DESIGN (the meta-shadow style proven keystone-free this session):
--  * a META inductive shadow  ListM  carrying the structure (Agda inductive),
--  * an embedding  codeL : ListM -> Term  into the uniformly-tagged coding
--      codeNil      = Pair (natCode 1) O
--      codeCons h t = Pair (natCode 2) (Pair h t),
--  * object PROJECTORS (lTag / lHead / lTail) with their Deriv equations
--    (from axFst / axSnd only -- the constructor/decoder interface),
--  * the structural INDUCTION principle  listInd  (prove an object property
--    Q : Term -> Formula of every coded list, by structural recursion on the
--    shadow), and the structural RECURSOR  listRecM  (define a meta function
--    on lists, producing object codes via the constructors).
--
-- The point: functions on lists (e.g. cr's diagram transport) are META
-- recursions on  ListM  producing codes via codeNil/codeCons, and their
-- specifications are proved by  listInd  chaining per-constructor object
-- equations + the IH -- NO opaque E-witness, NO surjective pairing, NO
-- course-of-values descent.  This is exactly the CertTree pattern.
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.CodedList where

open import T4.Base

------------------------------------------------------------------------
-- SECTION 0.  Coding.

codeNil : Term
codeNil = ap2 Pair (natCode 1) O

codeCons : Term -> Term -> Term
codeCons h t = ap2 Pair (natCode 2) (ap2 Pair h t)

------------------------------------------------------------------------
-- SECTION 1.  Projectors and their Deriv equations (axFst / axSnd only).

lTag : Term -> Term                      -- constructor tag
lTag l = ap1 Fst l

lArg : Term -> Term                      -- argument bundle
lArg l = ap1 Snd l

lHead : Term -> Term                     -- head of a cons = Fst (Snd l)
lHead l = ap1 Fst (ap1 Snd l)

lTail : Term -> Term                     -- tail of a cons = Snd (Snd l)
lTail l = ap1 Snd (ap1 Snd l)

lTag_nil : Deriv (eqF (lTag codeNil) (natCode 1))
lTag_nil = axFst (natCode 1) O

lTag_cons : (h t : Term) -> Deriv (eqF (lTag (codeCons h t)) (natCode 2))
lTag_cons h t = axFst (natCode 2) (ap2 Pair h t)

lHead_cons : (h t : Term) -> Deriv (eqF (lHead (codeCons h t)) h)
lHead_cons h t =
  ruleTrans (cong1 Fst (axSnd (natCode 2) (ap2 Pair h t))) (axFst h t)

lTail_cons : (h t : Term) -> Deriv (eqF (lTail (codeCons h t)) t)
lTail_cons h t =
  ruleTrans (cong1 Snd (axSnd (natCode 2) (ap2 Pair h t))) (axSnd h t)

------------------------------------------------------------------------
-- SECTION 2.  The META shadow and its embedding.

data ListM : Set where
  nilM  : ListM
  consM : Term -> ListM -> ListM

codeL : ListM -> Term
codeL nilM        = codeNil
codeL (consM h t) = codeCons h (codeL t)

------------------------------------------------------------------------
-- SECTION 3.  The structural INDUCTION principle.
--   Prove an object property  Q : Term -> Formula  of every coded list, by
--   structural recursion on the shadow (Agda recursion).

listInd :
  (Q : Term -> Formula) ->
  Deriv (Q codeNil) ->
  ((h : Term) (t : ListM) -> Deriv (Q (codeL t)) -> Deriv (Q (codeCons h (codeL t)))) ->
  (l : ListM) -> Deriv (Q (codeL l))
listInd Q qn qc nilM        = qn
listInd Q qn qc (consM h t) = qc h t (listInd Q qn qc t)

------------------------------------------------------------------------
-- SECTION 4.  The structural RECURSOR (define a meta-valued function on
--   lists; the carrier A is arbitrary, e.g. Term for code-producing maps).

listRecM :
  {A : Set} ->
  A ->
  (Term -> ListM -> A -> A) ->
  ListM -> A
listRecM z f nilM        = z
listRecM z f (consM h t) = f h t (listRecM z f t)
