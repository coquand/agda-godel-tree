{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.NotFree -- pointwise "var k does not occur" freshness, at a SINGLE
-- index (cf. T4.SbtFresh which is keyed on the maxVarF bound, hence
-- conflates "var k fresh" with "all vars >= k fresh").
--
-- Provides:
--   notFreeT / notFreeF : Nat -> Term/Formula -> Set   (structural)
--   substF_notFree      : the META substitution no-op       (no contract)
--   FreshNF.sbfInert_codeFormula : the OBJECT sbf inertness  (needs sbContract)
--
-- This lets a theorem assume only the per-variable freshness facts
-- (e.g. "var 0 and var 1 not free in A") rather than full sentencehood.

module T4.NotFree where

open import T4.Base
open import T4.Tags
open import T4.Code       using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import T4.SbContract using ( SbContract ; module SbContract )
open import BRA3.RuleInst2
  using ( maxVarT ; maxVarF ; NatLe ; le-trans
        ; maxN-le-left ; maxN-le-right
        ; natEq-lt-false ; natEq-refl ; natEqTrue_implies_eq )

------------------------------------------------------------------------
-- A tiny ASCII conjunction (no BRA-level product in scope).

record Both (P Q : Set) : Set where
  constructor both
  field
    fst1 : P
    snd1 : Q
open Both public

------------------------------------------------------------------------
-- "var k does not occur" -- structural, on the SOURCE term / formula.
-- At a var-leaf it is exactly  natEq k m = false  (k /= m), the premise
-- of  sbt_at_var_nomatch  and the discharge of  boolCase  in substT.

notFreeT : Nat -> Term -> Set
notFreeT k O           = Unit
notFreeT k (var m)     = Eq (natEq k m) false
notFreeT k (ap1 f a)   = notFreeT k a
notFreeT k (ap2 g a b) = Both (notFreeT k a) (notFreeT k b)

notFreeF : Nat -> Formula -> Set
notFreeF k (atomic (eqn a b)) = Both (notFreeT k a) (notFreeT k b)
notFreeF k (neg p)            = notFreeF k p
notFreeF k (imp p q)          = Both (notFreeF k p) (notFreeF k q)

------------------------------------------------------------------------
-- META substitution no-op :  notFreeT k t  ->  substT k X t = t .

substT_notFree :
  (k : Nat) (t : Term) (X : Term) -> notFreeT k t -> Eq (substT k X t) t
substT_notFree k O           X nf = refl
substT_notFree k (var m)     X nf =
  -- substT k X (var m) = boolCase (natEq k m) X (var m) ; nf : natEq k m = false .
  eqSubst (\ z -> Eq (boolCase z X (var m)) (var m)) (eqSym nf) refl
substT_notFree k (ap1 f a)   X nf =
  eqCong (ap1 f) (substT_notFree k a X nf)
substT_notFree k (ap2 g a b) X nf =
  let eq_a : Eq (substT k X a) a
      eq_a = substT_notFree k a X (fst1 nf)

      eq_b : Eq (substT k X b) b
      eq_b = substT_notFree k b X (snd1 nf)
  in eqTrans (eqCong (\ a' -> ap2 g a' (substT k X b)) eq_a)
             (eqCong (ap2 g a) eq_b)

substF_notFree :
  (k : Nat) (F : Formula) (X : Term) -> notFreeF k F -> Eq (substF k X F) F
substF_notFree k (atomic (eqn a b)) X nf =
  eqCong atomic
    (eqTrans (eqCong (\ a' -> eqn a' (substT k X b)) (substT_notFree k a X (fst1 nf)))
             (eqCong (eqn a)                          (substT_notFree k b X (snd1 nf))))
substF_notFree k (neg p)   X nf = eqCong neg (substF_notFree k p X nf)
substF_notFree k (imp p q) X nf =
  eqTrans (eqCong (\ p' -> imp p' (substF k X q)) (substF_notFree k p X (fst1 nf)))
          (eqCong (imp p)                         (substF_notFree k q X (snd1 nf)))

------------------------------------------------------------------------
-- OBJECT-level inertness :  sbt / sbf  is a no-op on  codeTerm t /
--  codeFormula F  at index  k , given  notFreeT k t / notFreeF k F .
-- Mirrors T4.SbtFresh.Fresh, with the per-leaf  natEq k m = false  now
-- coming from the structural predicate (any substituent  S ).

module FreshNF (sbt sbf : Fun2) (sbCon : SbContract sbt sbf) where
  open SbContract sbCon

  sbtInert_codeTerm :
    (k : Nat) (S : Term) (t : Term) -> notFreeT k t ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm t)) (codeTerm t))

  sbtInert_codeTerm k S O           nf = sbt_at_O (ap2 Pair (natCode k) S)
  sbtInert_codeTerm k S (var m)     nf = sbt_at_var_nomatch k m S nf
  sbtInert_codeTerm k S (ap1 f r)   nf =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        ih : Deriv (eqF (ap2 sbt spec (codeTerm r)) (codeTerm r))
        ih = sbtInert_codeTerm k S r nf

        step1 :
          Deriv (eqF (ap2 sbt spec (codeTerm (ap1 f r)))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (ap2 sbt spec (codeTerm r)))))
        step1 = sbt_at_ap1 k S f (codeTerm r)
    in ruleTrans step1
         (congR Pair (natCode tag_ap1) (congR Pair (codeFun1 f) ih))
  sbtInert_codeTerm k S (ap2 g a b) nf =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        ih_a : Deriv (eqF (ap2 sbt spec (codeTerm a)) (codeTerm a))
        ih_a = sbtInert_codeTerm k S a (fst1 nf)

        ih_b : Deriv (eqF (ap2 sbt spec (codeTerm b)) (codeTerm b))
        ih_b = sbtInert_codeTerm k S b (snd1 nf)

        step1 :
          Deriv (eqF (ap2 sbt spec (codeTerm (ap2 g a b)))
                      (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair
                            (ap2 sbt spec (codeTerm a))
                            (ap2 sbt spec (codeTerm b))))))
        step1 = sbt_at_ap2 k S g (codeTerm a) (codeTerm b)

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a) (codeTerm b)))
        inner = ruleTrans (congL Pair (ap2 sbt spec (codeTerm b)) ih_a)
                          (congR Pair (codeTerm a) ih_b)
    in ruleTrans step1
         (congR Pair (natCode tag_ap2) (congR Pair (codeFun2 g) inner))

  sbfInert_codeFormula :
    (k : Nat) (S : Term) (F : Formula) -> notFreeF k F ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (codeFormula F)) (codeFormula F))

  sbfInert_codeFormula k S (atomic (eqn a b)) nf =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        ih_a : Deriv (eqF (ap2 sbt spec (codeTerm a)) (codeTerm a))
        ih_a = sbtInert_codeTerm k S a (fst1 nf)

        ih_b : Deriv (eqF (ap2 sbt spec (codeTerm b)) (codeTerm b))
        ih_b = sbtInert_codeTerm k S b (snd1 nf)

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (atomic (eqn a b))))
                      (ap2 Pair (natCode tag_eq)
                        (ap2 Pair
                          (ap2 sbt spec (codeTerm a))
                          (ap2 sbt spec (codeTerm b)))))
        step1 = sbf_at_atomic k S (codeTerm a) (codeTerm b)

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbt spec (codeTerm a))
                                (ap2 sbt spec (codeTerm b)))
                      (ap2 Pair (codeTerm a) (codeTerm b)))
        inner = ruleTrans (congL Pair (ap2 sbt spec (codeTerm b)) ih_a)
                          (congR Pair (codeTerm a) ih_b)
    in ruleTrans step1 (congR Pair (natCode tag_eq) inner)
  sbfInert_codeFormula k S (neg p) nf =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        ih : Deriv (eqF (ap2 sbf spec (codeFormula p)) (codeFormula p))
        ih = sbfInert_codeFormula k S p nf

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (neg p)))
                      (ap2 Pair (natCode tag_neg) (ap2 sbf spec (codeFormula p))))
        step1 = sbf_at_neg k S (codeFormula p)
    in ruleTrans step1 (congR Pair (natCode tag_neg) ih)
  sbfInert_codeFormula k S (imp p q) nf =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        ih_p : Deriv (eqF (ap2 sbf spec (codeFormula p)) (codeFormula p))
        ih_p = sbfInert_codeFormula k S p (fst1 nf)

        ih_q : Deriv (eqF (ap2 sbf spec (codeFormula q)) (codeFormula q))
        ih_q = sbfInert_codeFormula k S q (snd1 nf)

        step1 :
          Deriv (eqF (ap2 sbf spec (codeFormula (imp p q)))
                      (ap2 Pair (natCode tag_imp)
                        (ap2 Pair
                          (ap2 sbf spec (codeFormula p))
                          (ap2 sbf spec (codeFormula q)))))
        step1 = sbf_at_imp k S (codeFormula p) (codeFormula q)

        inner :
          Deriv (eqF (ap2 Pair (ap2 sbf spec (codeFormula p))
                                (ap2 sbf spec (codeFormula q)))
                      (ap2 Pair (codeFormula p) (codeFormula q)))
        inner = ruleTrans (congL Pair (ap2 sbf spec (codeFormula q)) ih_p)
                          (congR Pair (codeFormula p) ih_q)
    in ruleTrans step1 (congR Pair (natCode tag_imp) inner)

------------------------------------------------------------------------
-- From a maxVar bound to the structural freshness predicate.

notFree_above_T :
  (k : Nat) (t : Term) -> NatLe (maxVarT t) k -> notFreeT k t
notFree_above_T k O           le = tt
notFree_above_T k (var m)     le = natEq-lt-false k m le
notFree_above_T k (ap1 f a)   le = notFree_above_T k a le
notFree_above_T k (ap2 g a b) le =
  both (notFree_above_T k a (le-trans (maxN-le-left  (maxVarT a) (maxVarT b)) le))
       (notFree_above_T k b (le-trans (maxN-le-right (maxVarT a) (maxVarT b)) le))

notFree_above_F :
  (k : Nat) (F : Formula) -> NatLe (maxVarF F) k -> notFreeF k F
notFree_above_F k (atomic (eqn a b)) le =
  both (notFree_above_T k a (le-trans (maxN-le-left  (maxVarT a) (maxVarT b)) le))
       (notFree_above_T k b (le-trans (maxN-le-right (maxVarT a) (maxVarT b)) le))
notFree_above_F k (neg p)   le = notFree_above_F k p le
notFree_above_F k (imp p q) le =
  both (notFree_above_F k p (le-trans (maxN-le-left  (maxVarF p) (maxVarF q)) le))
       (notFree_above_F k q (le-trans (maxN-le-right (maxVarF p) (maxVarF q)) le))

------------------------------------------------------------------------
-- Renaming round-trip :  substitute var 0 := var k  (k fresh for t),
-- then var k := var 0 , recovers t .

substT_back :
  (k : Nat) (t : Term) -> notFreeT k t ->
  Eq (substT k (var zero) (substT zero (var k) t)) t
substT_back k O               nf = refl
substT_back k (var zero)      nf =
  eqSubst (\ z -> Eq (boolCase z (var zero) (var k)) (var zero))
          (eqSym (natEq-refl k)) refl
substT_back k (var (suc m))   nf =
  eqSubst (\ z -> Eq (boolCase z (var zero) (var (suc m))) (var (suc m)))
          (eqSym nf) refl
substT_back k (ap1 f a)       nf = eqCong (ap1 f) (substT_back k a nf)
substT_back k (ap2 g a b)     nf =
  eqTrans (eqCong (\ a' -> ap2 g a' (substT k (var zero) (substT zero (var k) b)))
                  (substT_back k a (fst1 nf)))
          (eqCong (ap2 g a) (substT_back k b (snd1 nf)))

substF_back :
  (k : Nat) (F : Formula) -> notFreeF k F ->
  Eq (substF k (var zero) (substF zero (var k) F)) F
substF_back k (atomic (eqn a b)) nf =
  eqCong atomic
    (eqTrans (eqCong (\ a' -> eqn a' (substT k (var zero) (substT zero (var k) b)))
                     (substT_back k a (fst1 nf)))
             (eqCong (eqn a) (substT_back k b (snd1 nf))))
substF_back k (neg p)   nf = eqCong neg (substF_back k p nf)
substF_back k (imp p q) nf =
  eqTrans (eqCong (\ p' -> imp p' (substF k (var zero) (substF zero (var k) q)))
                  (substF_back k p (fst1 nf)))
          (eqCong (imp p) (substF_back k q (snd1 nf)))

------------------------------------------------------------------------
-- var 0 disappears after  substF 0 (var k)  (when k /= 0).

notFree0_after_T :
  (k : Nat) (t : Term) -> Eq (natEq zero k) false ->
  notFreeT zero (substT zero (var k) t)
notFree0_after_T k O             nfk = tt
notFree0_after_T k (var zero)    nfk = nfk
notFree0_after_T k (var (suc m)) nfk = refl
notFree0_after_T k (ap1 f a)     nfk = notFree0_after_T k a nfk
notFree0_after_T k (ap2 g a b)   nfk =
  both (notFree0_after_T k a nfk) (notFree0_after_T k b nfk)

notFree0_after_F :
  (k : Nat) (F : Formula) -> Eq (natEq zero k) false ->
  notFreeF zero (substF zero (var k) F)
notFree0_after_F k (atomic (eqn a b)) nfk =
  both (notFree0_after_T k a nfk) (notFree0_after_T k b nfk)
notFree0_after_F k (neg p)   nfk = notFree0_after_F k p nfk
notFree0_after_F k (imp p q) nfk =
  both (notFree0_after_F k p nfk) (notFree0_after_F k q nfk)

------------------------------------------------------------------------
-- Freshness of index j is preserved by  substF 0 (var k)  (when j /= k).

notFree_preserve_T :
  (j k : Nat) (t : Term) -> notFreeT j t -> Eq (natEq j k) false ->
  notFreeT j (substT zero (var k) t)
notFree_preserve_T j k O             nf jk = tt
notFree_preserve_T j k (var zero)    nf jk = jk
notFree_preserve_T j k (var (suc m)) nf jk = nf
notFree_preserve_T j k (ap1 f a)     nf jk = notFree_preserve_T j k a nf jk
notFree_preserve_T j k (ap2 g a b)   nf jk =
  both (notFree_preserve_T j k a (fst1 nf) jk)
       (notFree_preserve_T j k b (snd1 nf) jk)

notFree_preserve_F :
  (j k : Nat) (F : Formula) -> notFreeF j F -> Eq (natEq j k) false ->
  notFreeF j (substF zero (var k) F)
notFree_preserve_F j k (atomic (eqn a b)) nf jk =
  both (notFree_preserve_T j k a (fst1 nf) jk)
       (notFree_preserve_T j k b (snd1 nf) jk)
notFree_preserve_F j k (neg p)   nf jk = notFree_preserve_F j k p nf jk
notFree_preserve_F j k (imp p q) nf jk =
  both (notFree_preserve_F j k p (fst1 nf) jk)
       (notFree_preserve_F j k q (snd1 nf) jk)

------------------------------------------------------------------------
-- INDEX-GENERAL versions (arbitrary slot / substitution index), via a
-- boolean dispatch on the now-symbolic  natEq i m .

boolDispatch :
  {P : Set} (b : Bool) -> (Eq b true -> P) -> (Eq b false -> P) -> P
boolDispatch true  t f = t refl
boolDispatch false t f = f refl

-- Renaming round-trip at an arbitrary slot index  i :
--   substitute  var i := var k  (k fresh for t), then  var k := var i .

substT_back_at :
  (i k : Nat) (t : Term) -> notFreeT k t ->
  Eq (substT k (var i) (substT i (var k) t)) t
substT_back_at i k O           nf = refl
substT_back_at i k (var m)     nf =
  boolDispatch (natEq i m)
    (\ eqT -> eqSubst (\ b -> Eq (substT k (var i) (boolCase b (var k) (var m))) (var m))
                      (eqSym eqT)
                      (eqSubst (\ c -> Eq (boolCase c (var i) (var k)) (var m))
                               (eqSym (natEq-refl k))
                               (eqCong var (natEqTrue_implies_eq i m eqT))))
    (\ eqF -> eqSubst (\ b -> Eq (substT k (var i) (boolCase b (var k) (var m))) (var m))
                      (eqSym eqF)
                      (eqSubst (\ d -> Eq (boolCase d (var i) (var m)) (var m))
                               (eqSym nf)
                               refl))
substT_back_at i k (ap1 f a)   nf = eqCong (ap1 f) (substT_back_at i k a nf)
substT_back_at i k (ap2 g a b) nf =
  eqTrans (eqCong (\ a' -> ap2 g a' (substT k (var i) (substT i (var k) b)))
                  (substT_back_at i k a (fst1 nf)))
          (eqCong (ap2 g a) (substT_back_at i k b (snd1 nf)))

substF_back_at :
  (i k : Nat) (F : Formula) -> notFreeF k F ->
  Eq (substF k (var i) (substF i (var k) F)) F
substF_back_at i k (atomic (eqn a b)) nf =
  eqCong atomic
    (eqTrans (eqCong (\ a' -> eqn a' (substT k (var i) (substT i (var k) b)))
                     (substT_back_at i k a (fst1 nf)))
             (eqCong (eqn a) (substT_back_at i k b (snd1 nf))))
substF_back_at i k (neg p)   nf = eqCong neg (substF_back_at i k p nf)
substF_back_at i k (imp p q) nf =
  eqTrans (eqCong (\ p' -> imp p' (substF k (var i) (substF i (var k) q)))
                  (substF_back_at i k p (fst1 nf)))
          (eqCong (imp p) (substF_back_at i k q (snd1 nf)))

-- After  substF i (var k)  the slot index  i  itself is fresh (k /= i).

notFree_self_after_T :
  (i k : Nat) (t : Term) -> Eq (natEq i k) false ->
  notFreeT i (substT i (var k) t)
notFree_self_after_T i k O           ik = tt
notFree_self_after_T i k (var m)     ik =
  boolDispatch (natEq i m)
    (\ eqT -> eqSubst (\ b -> notFreeT i (boolCase b (var k) (var m))) (eqSym eqT) ik)
    (\ eqF -> eqSubst (\ b -> notFreeT i (boolCase b (var k) (var m))) (eqSym eqF) eqF)
notFree_self_after_T i k (ap1 f a)   ik = notFree_self_after_T i k a ik
notFree_self_after_T i k (ap2 g a b) ik =
  both (notFree_self_after_T i k a ik) (notFree_self_after_T i k b ik)

notFree_self_after_F :
  (i k : Nat) (F : Formula) -> Eq (natEq i k) false ->
  notFreeF i (substF i (var k) F)
notFree_self_after_F i k (atomic (eqn a b)) ik =
  both (notFree_self_after_T i k a ik) (notFree_self_after_T i k b ik)
notFree_self_after_F i k (neg p)   ik = notFree_self_after_F i k p ik
notFree_self_after_F i k (imp p q) ik =
  both (notFree_self_after_F i k p ik) (notFree_self_after_F i k q ik)

-- Freshness of index j survives  substF i (var k)  (j /= k), any slot i.

notFree_preserve_at_T :
  (i j k : Nat) (t : Term) -> notFreeT j t -> Eq (natEq j k) false ->
  notFreeT j (substT i (var k) t)
notFree_preserve_at_T i j k O           nf jk = tt
notFree_preserve_at_T i j k (var m)     nf jk =
  boolDispatch (natEq i m)
    (\ eqT -> eqSubst (\ b -> notFreeT j (boolCase b (var k) (var m))) (eqSym eqT) jk)
    (\ eqF -> eqSubst (\ b -> notFreeT j (boolCase b (var k) (var m))) (eqSym eqF) nf)
notFree_preserve_at_T i j k (ap1 f a)   nf jk = notFree_preserve_at_T i j k a nf jk
notFree_preserve_at_T i j k (ap2 g a b) nf jk =
  both (notFree_preserve_at_T i j k a (fst1 nf) jk)
       (notFree_preserve_at_T i j k b (snd1 nf) jk)

notFree_preserve_at_F :
  (i j k : Nat) (F : Formula) -> notFreeF j F -> Eq (natEq j k) false ->
  notFreeF j (substF i (var k) F)
notFree_preserve_at_F i j k (atomic (eqn a b)) nf jk =
  both (notFree_preserve_at_T i j k a (fst1 nf) jk)
       (notFree_preserve_at_T i j k b (snd1 nf) jk)
notFree_preserve_at_F i j k (neg p)   nf jk = notFree_preserve_at_F i j k p nf jk
notFree_preserve_at_F i j k (imp p q) nf jk =
  both (notFree_preserve_at_F i j k p (fst1 nf) jk)
       (notFree_preserve_at_F i j k q (snd1 nf) jk)
