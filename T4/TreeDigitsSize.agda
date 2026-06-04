{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TreeDigitsSize -- the HONEST size fact for the number-code Chaitin redo,
-- handled EARLY (the riskiest obligation; cf [[feedback_no_discharge_later_parameters]]).
--
-- The diagonal program  gL  becomes the NUMBER  n0 = rank (treeToDigits gL) .
-- The K-formula guard is  p < N  ( initial segment ), so the size obligation is
--
--   n0 = rank (treeToDigits gL)  <  3^(nodes gL + 1) .
--
-- This is PURE base-3 combinatorics on the bijective-base-3 rank, true for ANY
-- tree, proved here CONCRETELY ( not assumed as a parameter ).  Combined with the
-- existing fixed-point  T4.NatExp.affine_dom  ( nodes gL <= 2^k for some k , the
-- same engine that powers the old  boundDef ) and monotonicity of  pow3 , it
-- gives  n0 < 3^(2^k + 1) = N  -- the honest, dischargeable size pin.
--
-- The strict bound holds via the TIGHT invariant  2*rank + 3 <= 3^(len+1)
-- ( a looser  rank < 3^(len+1)  loses strictness in the inductive step ).

module T4.TreeDigitsSize where

open import T4.Base
open import T4.ProgEnc       using ( nodes )
open import T4.CandidateCover using
  ( Tri ; t1 ; t2 ; t3 ; triVal ; TStr ; tnil ; tcons ; rank ; idx )
open import T4.TreeToDigits  using ( treeToDigits ; treeToDigitsApp )

open import BRA3.Code.Tag        using ( addN )
open import BRA3.Code.NatLemmas  using ( addN_zero_right ; addN_suc_right )
open import BRA3.Code.CantorGrowth using ( addN_comm ; addN_assoc )
open import BRA3.RuleInst2 using
  ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans )
open import T4.NatExp using
  ( addN_mono ; addN_mono_l ; addN_mono_r ; le_self_addN_l )

------------------------------------------------------------------------
-- SECTION 0.  Meta abbreviations.

dbl : Nat -> Nat
dbl x = addN x x

m3 : Nat -> Nat
m3 x = addN x (addN x x)

pow3 : Nat -> Nat
pow3 zero    = suc zero
pow3 (suc k) = addN (pow3 k) (addN (pow3 k) (pow3 k))      -- = m3 (pow3 k)

------------------------------------------------------------------------
-- SECTION 1.  Small  addN  suc-tower helpers ( the second argument carries
-- the sucs; the first-argument case reduces definitionally ).

addN_suc2 : (a x : Nat) -> Eq (addN a (suc (suc x))) (suc (suc (addN a x)))
addN_suc2 a x =
  eqTrans (addN_suc_right a (suc x)) (eqCong suc (addN_suc_right a x))

addN_suc3 : (a x : Nat) -> Eq (addN a (suc (suc (suc x)))) (suc (suc (suc (addN a x))))
addN_suc3 a x =
  eqTrans (addN_suc_right a (suc (suc x))) (eqCong suc (addN_suc2 a x))

addN_suc6 :
  (a x : Nat) ->
  Eq (addN a (suc (suc (suc (suc (suc (suc x)))))))
     (suc (suc (suc (suc (suc (suc (addN a x)))))))
addN_suc6 a x =
  eqTrans (addN_suc3 a (suc (suc (suc x)))) (eqCong (\ z -> suc (suc (suc z))) (addN_suc3 a x))

------------------------------------------------------------------------
-- SECTION 2.  dbl distributes over addN.   dbl (a+b) = dbl a + dbl b.

dbl_addN : (a b : Nat) -> Eq (dbl (addN a b)) (addN (dbl a) (dbl b))
dbl_addN a b =
  eqTrans (addN_assoc a b (addN a b))
  (eqTrans (eqCong (addN a) (eqSym (addN_assoc b a b)))
  (eqTrans (eqCong (\ z -> addN a (addN z b)) (addN_comm b a))
  (eqTrans (eqCong (addN a) (addN_assoc a b b))
           (eqSym (addN_assoc a a (addN b b))))))

------------------------------------------------------------------------
-- SECTION 3.  idx d r = d + 3 r , in addN form ( m3 r = 3 r ).

m3_suc : (r : Nat) -> Eq (m3 (suc r)) (suc (suc (suc (m3 r))))
m3_suc r =
  -- m3 (suc r) = addN (suc r) (addN (suc r) (suc r))
  --            = suc (addN r (addN (suc r) (suc r)))            (def)
  let inner_eq : Eq (addN (suc r) (suc r)) (suc (suc (addN r r)))
      inner_eq = eqCong suc (addN_suc_right r r)
  in eqCong suc
       (eqTrans (eqCong (addN r) inner_eq) (addN_suc2 r (addN r r)))

idx_eq : (d r : Nat) -> Eq (idx d r) (addN d (m3 r))
idx_eq d zero    = eqSym (addN_zero_right d)
idx_eq d (suc r) =
  -- idx d (suc r) = suc (suc (suc (idx d r)))                  (def)
  eqTrans (eqCong (\ z -> suc (suc (suc z))) (idx_eq d r))
          (eqTrans (eqSym (addN_suc3 d (m3 r)))
                   (eqCong (addN d) (eqSym (m3_suc r))))

------------------------------------------------------------------------
-- SECTION 4.  triVal d <= 3 .

triVal_le3 : (d : Tri) -> NatLe (triVal d) (suc (suc (suc zero)))
triVal_le3 t1 = le-suc (le-zero (suc (suc zero)))
triVal_le3 t2 = le-suc (le-suc (le-zero (suc zero)))
triVal_le3 t3 = le-suc (le-suc (le-suc (le-zero zero)))

------------------------------------------------------------------------
-- SECTION 5.  The inductive heart.   Given  td <= 3  and  3 + 2 r <= B ,
--   3 + 2 (idx td r)  <=  3 B  ( = m3 B = pow3 successor step ).

-- 3 + 2 (idx td r)  <=  3 + 2 (3 + 3 r) = 9 + 6 r = 3 (3 + 2 r) , and  3+2r <= B .

-- the equality  3 + 2 (3 + 3 r) = 3 (3 + 2 r)  ( both = 9 + 6 r ), at td = 3.
suc9 : Nat -> Nat
suc9 z = suc (suc (suc (suc (suc (suc (suc (suc (suc z))))))))

s4 : (r : Nat) ->
     Eq (suc (suc (suc (dbl (suc (suc (suc (m3 r))))))))
        (m3 (suc (suc (suc (dbl r)))))
s4 r =
  let -- LHS:  3 + dbl (3 + m3 r)  =  9 + dbl (m3 r) .
      lhs1 : Eq (dbl (suc (suc (suc (m3 r)))))
                (suc (suc (suc (suc (suc (suc (dbl (m3 r))))))))
      lhs1 = eqCong (\ z -> suc (suc (suc z))) (addN_suc3 (m3 r) (m3 r))
      -- dbl (m3 r) = addN (dbl r) (dbl (dbl r))   ( m3 r = 3r , distributing ).
      dd : Eq (dbl (m3 r)) (addN (dbl r) (dbl (dbl r)))
      dd = dbl_addN r (addN r r)
      -- RHS:  m3 (3 + dbl r)  =  9 + addN (dbl r) (dbl (dbl r)) .
      addXX : Eq (addN (suc (suc (suc (dbl r)))) (suc (suc (suc (dbl r)))))
                 (suc (suc (suc (suc (suc (suc (dbl (dbl r))))))))
      addXX = eqCong (\ z -> suc (suc (suc z))) (addN_suc3 (dbl r) (dbl r))
      rhs1 : Eq (m3 (suc (suc (suc (dbl r))))) (suc9 (addN (dbl r) (dbl (dbl r))))
      rhs1 =
        eqTrans (eqCong (\ z -> suc (suc (suc (addN (dbl r) z)))) addXX)
                (eqCong (\ z -> suc (suc (suc z))) (addN_suc6 (dbl r) (dbl (dbl r))))
  in eqTrans (eqCong (\ z -> suc (suc (suc z))) lhs1)
     (eqTrans (eqCong suc9 dd)
              (eqSym rhs1))

coreStep :
  (td r B : Nat) ->
  NatLe td (suc (suc (suc zero))) ->
  NatLe (suc (suc (suc (dbl r)))) B ->
  NatLe (suc (suc (suc (dbl (idx td r))))) (addN B (addN B B))
coreStep td r B ltd hB =
  let -- idx td r <= 3 + m3 r  (= suc^3 (m3 r)) .
      idx_le3 : NatLe (idx td r) (suc (suc (suc (m3 r))))
      idx_le3 =
        eqSubst (\ z -> NatLe z (suc (suc (suc (m3 r))))) (eqSym (idx_eq td r))
                (addN_mono_l ltd)
      -- 3 + 2 (idx td r)  <=  3 + 2 (3 + m3 r) .
      step1 : NatLe (suc (suc (suc (dbl (idx td r)))))
                    (suc (suc (suc (dbl (suc (suc (suc (m3 r))))))))
      step1 = le-suc (le-suc (le-suc (addN_mono idx_le3 idx_le3)))
      -- 3 + 2 (3 + m3 r)  =  3 (3 + 2 r)  =  m3 (3 + 2 r) .
      step2 : NatLe (suc (suc (suc (dbl (suc (suc (suc (m3 r))))))))
                    (m3 (suc (suc (suc (dbl r)))))
      step2 = eqSubst (\ z -> NatLe (suc (suc (suc (dbl (suc (suc (suc (m3 r)))))))) z)
                      (s4 r) (le-refl _)
      -- m3 (3 + 2 r)  <=  m3 B  =  3 B   ( B >= 3 + 2 r ) .
      step3 : NatLe (m3 (suc (suc (suc (dbl r))))) (addN B (addN B B))
      step3 = addN_mono hB (addN_mono hB hB)
  in le-trans step1 (le-trans step2 step3)

------------------------------------------------------------------------
-- SECTION 6.  String length, the invariant, and the strict rank bound.

lenTStr : TStr -> Nat
lenTStr tnil         = zero
lenTStr (tcons _ ys) = suc (lenTStr ys)

rankInv :
  (xs : TStr) ->
  NatLe (suc (suc (suc (dbl (rank xs))))) (pow3 (suc (lenTStr xs)))
rankInv tnil         = le-refl (suc (suc (suc zero)))
rankInv (tcons d ys) =
  coreStep (triVal d) (rank ys) (pow3 (suc (lenTStr ys)))
           (triVal_le3 d) (rankInv ys)

-- the strict bound:  rank xs < 3^(len xs + 1) .
rank_lt :
  (xs : TStr) -> NatLe (suc (rank xs)) (pow3 (suc (lenTStr xs)))
rank_lt xs =
  let le_r : NatLe (suc (rank xs)) (suc (suc (suc (dbl (rank xs)))))
      le_r = le-suc (le-suc-right (le-suc-right (le_self_addN_l (rank xs) (rank xs))))
  in le-trans le_r (rankInv xs)

------------------------------------------------------------------------
-- SECTION 7.  The length of the digit-string = the node count.

lenTStr_treeToDigitsApp :
  (t : Term) (rest : TStr) ->
  Eq (lenTStr (treeToDigitsApp t rest)) (addN (nodes t) (lenTStr rest))
lenTStr_treeToDigitsApp O          rest = refl
lenTStr_treeToDigitsApp (var k)    rest = refl
lenTStr_treeToDigitsApp (ap1 f t)  rest =
  eqCong suc (lenTStr_treeToDigitsApp t rest)
lenTStr_treeToDigitsApp (ap2 g a b) rest =
  eqCong suc
    (eqTrans (lenTStr_treeToDigitsApp a (treeToDigitsApp b rest))
    (eqTrans (eqCong (addN (nodes a)) (lenTStr_treeToDigitsApp b rest))
             (eqSym (addN_assoc (nodes a) (nodes b) (lenTStr rest)))))

lenTStr_treeToDigits :
  (t : Term) -> Eq (lenTStr (treeToDigits t)) (nodes t)
lenTStr_treeToDigits t =
  eqTrans (lenTStr_treeToDigitsApp t tnil) (addN_zero_right (nodes t))

------------------------------------------------------------------------
-- SECTION 8.  HEADLINE:  the honest size fact ( strict ), for ANY tree :
--   rank (treeToDigits t)  <  3^(nodes t + 1) .

n0_lt_pow3 :
  (t : Term) -> NatLe (suc (rank (treeToDigits t))) (pow3 (suc (nodes t)))
n0_lt_pow3 t =
  eqSubst (\ m -> NatLe (suc (rank (treeToDigits t))) (pow3 (suc m)))
          (lenTStr_treeToDigits t)
          (rank_lt (treeToDigits t))
