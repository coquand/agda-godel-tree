{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.NatExp -- Phase R5, step (4) (CHAITIN-G1-FAITHFUL-BLUEPRINT.md S5bis
-- R5a): the META "2^x outgrows a linear function" fact, proved ONCE over
-- abstract constants and applied at the (abstract) program-size constant.
--
--   affine_dom : (b d : Nat) -> Sg Nat (\ k -> NatLe (addN b (mulc d k)) (powN k))
--
-- i.e. for every affine  b + d*k  there is a  k  with  b + d*k <= 2^k .  The
-- core is the clean polynomial-vs-exponential bound
--   sq_le_pow2 : (n) -> NatLe 4 n -> NatLe (n*n) (2^n)
-- (n^2 <= 2^n for n >= 4), from which  c*m <= m*m <= 2^m  for  m >= max(c,4) ,
-- and the affine reduction  b + d*k <= (b+d+1)*k .  No  2^x  is ever formed:
-- powN appears only under its doubling recurrence.  This is the formal shadow
-- of Chaitin's "|g_L| = const + log L < L for L large enough".
--
-- The companion  dom  converts a one-step recurrence (size (suc k) =
-- delta + size k) to the affine form, which is how the program size enters.

module BRA4.NatExp where

open import BRA4.Base
open import BRA4.Exp using ( powN )

open import BRA3.Code.Tag       using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right ; addN_suc_right )
open import BRA3.RuleInst2      using
  ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans )

-- addN associativity / commutativity (proved in the R1/R4a files).
open import BRA4.ProgEnc   using ( addN_assoc )
open import BRA4.ProgNodes using ( addN_comm )

------------------------------------------------------------------------
-- A local dependent pair.

record Sg (A : Set) (B : A -> Set) : Set where
  constructor mkSg
  field
    fst : A
    snd : B fst
open Sg public

------------------------------------------------------------------------
-- SECTION 1.  addN monotonicity and self-bounds.

le_self_addN_r : (a b : Nat) -> NatLe b (addN a b)
le_self_addN_r zero     b = le-refl b
le_self_addN_r (suc a') b = le-suc-right (le_self_addN_r a' b)

le_self_addN_l : (a b : Nat) -> NatLe a (addN a b)
le_self_addN_l zero     b = le-zero b
le_self_addN_l (suc a') b = le-suc (le_self_addN_l a' b)

addN_mono :
  {a a' b b' : Nat} -> NatLe a a' -> NatLe b b' ->
  NatLe (addN a b) (addN a' b')
addN_mono {b' = b'} (le-zero a')      leb = le-trans leb (le_self_addN_r a' b')
addN_mono            (le-suc {a} {a'} le) leb = le-suc (addN_mono le leb)

addN_mono_l : {a a' b : Nat} -> NatLe a a' -> NatLe (addN a b) (addN a' b)
addN_mono_l {b = b} le = addN_mono le (le-refl b)

addN_mono_r : {a b b' : Nat} -> NatLe b b' -> NatLe (addN a b) (addN a b')
addN_mono_r {a = a} le = addN_mono (le-refl a) le

------------------------------------------------------------------------
-- SECTION 2.  powN positivity and a >= 2 bound.

powN_pos : (n : Nat) -> NatLe (suc zero) (powN n)
powN_pos zero    = le-refl (suc zero)
powN_pos (suc m) = le-trans (powN_pos m) (le_self_addN_l (powN m) (powN m))

powN_ge2 : (m : Nat) -> NatLe (suc (suc zero)) (powN (suc m))
powN_ge2 m = addN_mono (powN_pos m) (powN_pos m)

------------------------------------------------------------------------
-- SECTION 3.  Meta multiplication  mulc a k = a*k  (recursion on  k ).

mulc : Nat -> Nat -> Nat
mulc a zero    = zero
mulc a (suc k) = addN a (mulc a k)

mulc_mono_l :
  {a a' : Nat} -> NatLe a a' -> (k : Nat) -> NatLe (mulc a k) (mulc a' k)
mulc_mono_l le zero    = le-zero zero
mulc_mono_l le (suc k) = addN_mono le (mulc_mono_l le k)

-- mulc (suc a) k = k + mulc a k .
mulc_suc_l : (a k : Nat) -> Eq (mulc (suc a) k) (addN k (mulc a k))
mulc_suc_l a zero    = refl
mulc_suc_l a (suc k) =
  -- mulc (suc a)(suc k) = addN (suc a)(addN k (mulc a k)) = suc (addN a (addN k M))  [IH]
  -- target  addN (suc k)(mulc a (suc k)) = suc (addN k (addN a M))   (M = mulc a k)
  eqTrans (eqCong (\ z -> addN (suc a) z) (mulc_suc_l a k))
    (eqCong suc
      (eqTrans (addN_assoc a k (mulc a k))
        (eqTrans (eqCong (\ z -> addN z (mulc a k)) (addN_comm a k))
          (eqSym (addN_assoc k a (mulc a k))))))

------------------------------------------------------------------------
-- SECTION 4.  The polynomial-vs-exponential core.
--   lin: 2n+1 <= 2^n  (n >= 3);   sq: n^2 <= 2^n  (n >= 4).
-- Both by gap-induction (n = addN <base> j , definitionally  suc^base j ).

-- (a)  2n+1 <= 2^n  for  n = 3 + j .
lin_gap :
  (j : Nat) ->
  NatLe (suc (addN (addN (suc (suc (suc zero))) j) (addN (suc (suc (suc zero))) j)))
        (powN (addN (suc (suc (suc zero))) j))
lin_gap zero    = le-suc-right (le-refl (suc (suc (suc (suc (suc (suc (suc zero))))))))
lin_gap (suc j) =
  -- n = suc(suc(suc j)) ;  N = suc n .  suc(addN N N) = suc(suc(suc(addN n n))).
  let n  : Nat
      n  = addN (suc (suc (suc zero))) j
      ih : NatLe (suc (addN n n)) (powN n)
      ih = lin_gap j
      le2 : NatLe (suc (suc zero)) (powN n)
      le2 = powN_ge2 (addN (suc (suc zero)) j)
      main : NatLe (addN (suc (suc zero)) (suc (addN n n))) (addN (powN n) (powN n))
      main = le-trans (addN_mono_l le2) (addN_mono_r ih)
      eq : Eq (suc (addN (suc n) (suc n))) (addN (suc (suc zero)) (suc (addN n n)))
      eq = eqCong suc (eqCong suc (addN_suc_right n n))
  in eqSubst (\ z -> NatLe z (powN (suc n))) (eqSym eq) main

lin_le_pow2 : (n : Nat) -> NatLe (suc (suc (suc zero))) n ->
              NatLe (suc (addN n n)) (powN n)
lin_le_pow2 n le =
  -- n = 3 + (n-3) .  Reuse  le_to_addN  pattern inline via addN_comm.
  eqSubst (\ m -> NatLe (suc (addN m m)) (powN m)) (eqSym n3) (lin_gap j)
  where
    -- extract  j  with  n = addN 3 j .
    split : (m : Nat) -> NatLe (suc (suc (suc zero))) m -> Sg Nat (\ j -> Eq m (addN (suc (suc (suc zero))) j))
    split (suc m) (le-suc (le-suc (le-suc (le-zero g)))) = mkSg g refl
    j   : Nat
    j   = fst (split n le)
    n3  : Eq n (addN (suc (suc (suc zero))) j)
    n3  = snd (split n le)

-- (b)  n^2 <= 2^n  for  n = 4 + j .
sq_gap :
  (j : Nat) ->
  NatLe (mulc (addN (suc (suc (suc (suc zero)))) j) (addN (suc (suc (suc (suc zero)))) j))
        (powN (addN (suc (suc (suc (suc zero)))) j))
sq_gap zero    = le-refl (mulc (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))))
sq_gap (suc j) =
  let n  : Nat
      n  = addN (suc (suc (suc (suc zero)))) j
      ih : NatLe (mulc n n) (powN n)
      ih = sq_gap j
      le3n : NatLe (suc (suc (suc zero))) n
      le3n = le-suc (le-suc (le-suc (le-zero (suc j))))
      -- mulc (suc n)(suc n) = addN (suc (addN n n)) (mulc n n)
      expand : Eq (mulc (suc n) (suc n)) (addN (suc (addN n n)) (mulc n n))
      expand =
        eqTrans (eqCong (\ z -> addN (suc n) z) (mulc_suc_l n n))
          (eqCong suc (addN_assoc n n (mulc n n)))
      bound : NatLe (addN (suc (addN n n)) (mulc n n)) (addN (powN n) (powN n))
      bound = addN_mono (lin_le_pow2 n le3n) ih
  in eqSubst (\ z -> NatLe z (powN (suc n))) (eqSym expand) bound

sq_le_pow2 : (n : Nat) -> NatLe (suc (suc (suc (suc zero)))) n ->
             NatLe (mulc n n) (powN n)
sq_le_pow2 n le =
  eqSubst (\ m -> NatLe (mulc m m) (powN m)) (eqSym n4) (sq_gap j)
  where
    split : (m : Nat) -> NatLe (suc (suc (suc (suc zero)))) m ->
            Sg Nat (\ j -> Eq m (addN (suc (suc (suc (suc zero)))) j))
    split (suc m) (le-suc (le-suc (le-suc (le-suc (le-zero g))))) = mkSg g refl
    j  : Nat
    j  = fst (split n le)
    n4 : Eq n (addN (suc (suc (suc (suc zero)))) j)
    n4 = snd (split n le)

------------------------------------------------------------------------
-- SECTION 5.  mul_dom :  c*m <= 2^m  for  m >= c  and  m >= 4 .

mul_dom :
  (c m : Nat) -> NatLe c m -> NatLe (suc (suc (suc (suc zero)))) m ->
  NatLe (mulc c m) (powN m)
mul_dom c m lecm le4m =
  le-trans (mulc_mono_l lecm m) (sq_le_pow2 m le4m)

------------------------------------------------------------------------
-- SECTION 6.  Affine reduction and the domination.

-- b + d*(suc k') <= (b+d+1)*(suc k') .
affine_le_mulc :
  (b d k' : Nat) ->
  NatLe (addN b (mulc d (suc k')))
        (mulc (suc (addN b d)) (suc k'))
affine_le_mulc b d k' =
  -- LHS = addN (addN b d) (mulc d k')              [assoc]
  -- RHS = suc (addN (addN b d) (mulc (suc(addN b d)) k'))
  eqSubst (\ z -> NatLe z (mulc (suc (addN b d)) (suc k')))
          (eqSym (addN_assoc b d (mulc d k')))
          (le-suc-right
            (addN_mono_r (mulc_mono_l dLeC k')))
  where
    dLeC : NatLe d (suc (addN b d))
    dLeC = le-suc-right (le_self_addN_r b d)

-- the pieces of the chosen witness  k = suc (addN (addN b d) 8) .
affine_dom :
  (b d : Nat) -> Sg Nat (\ k -> NatLe (addN b (mulc d k)) (powN k))
affine_dom b d =
  mkSg k chain
  where
    bd  : Nat
    bd  = addN b d
    c   : Nat
    c   = suc bd
    -- k = suc (bd + 8)  (so  k >= c ,  k >= 4 ,  k = suc _ ).
    k'  : Nat
    k'  = addN bd (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    k   : Nat
    k   = suc k'
    -- c <= k :  suc bd <= suc (bd + 8) .
    leck : NatLe c k
    leck = le-suc (le_self_addN_l bd (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    -- 4 <= k :  4 <= 8 <= bd + 8 <= suc (bd + 8) = k .
    le48 : NatLe (suc (suc (suc (suc zero))))
                 (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    le48 = le-suc (le-suc (le-suc (le-suc (le-zero (suc (suc (suc (suc zero))))))))
    le4k : NatLe (suc (suc (suc (suc zero)))) k
    le4k = le-suc-right
             (le-trans le48
               (le_self_addN_r bd (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    step1 : NatLe (addN b (mulc d k)) (mulc c k)
    step1 = affine_le_mulc b d k'
    step2 : NatLe (mulc c k) (powN k)
    step2 = mul_dom c k leck le4k
    chain : NatLe (addN b (mulc d k)) (powN k)
    chain = le-trans step1 step2

------------------------------------------------------------------------
-- SECTION 7.  dom : a one-step recurrence  size (suc k) = delta + size k
-- gives  size k = size 0 + delta*k , hence is dominated by  powN .

size_closed :
  (delta : Nat) (size : Nat -> Nat) ->
  ((k : Nat) -> Eq (size (suc k)) (addN delta (size k))) ->
  (k : Nat) -> Eq (size k) (addN (size zero) (mulc delta k))
size_closed delta size rec zero    = eqSym (addN_zero_right (size zero))
size_closed delta size rec (suc k) =
  -- size (suc k) = delta + size k
  --             = delta + (size 0 + delta*k)         [IH]
  --             = size 0 + (delta + delta*k)         [comm/assoc]
  --             = size 0 + delta*(suc k)
  eqTrans (rec k)
    (eqTrans (eqCong (\ z -> addN delta z) (size_closed delta size rec k))
      (eqTrans (addN_assoc delta (size zero) (mulc delta k))
        (eqTrans (eqCong (\ z -> addN z (mulc delta k)) (addN_comm delta (size zero)))
          (eqSym (addN_assoc (size zero) delta (mulc delta k))))))

-- ABSTRACT: sealed so that at a use site  dom delta size rec  is NOT unfolded
-- (its body would otherwise force the concrete  size 0 , normalising the huge
-- program skeleton).  The witness/proof are obtained via the Sg projections.
abstract
  dom :
    (delta : Nat) (size : Nat -> Nat) ->
    ((k : Nat) -> Eq (size (suc k)) (addN delta (size k))) ->
    Sg Nat (\ k -> NatLe (size k) (powN k))
  dom delta size rec =
    let r = affine_dom (size zero) delta
    in mkSg (fst r)
            (eqSubst (\ z -> NatLe z (powN (fst r)))
                     (eqSym (size_closed delta size rec (fst r)))
                     (snd r))
