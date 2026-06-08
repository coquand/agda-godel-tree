{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmExpLinear -- brick D of the non-computability proof: exp beats linear.
--
-- The Berry program  berry Kf L  has size  <=  baseN + PDmax * D + Wf (BerryF Kf)
-- (T4.KolmBerry.berrySize), with  D = lenDL (digits3 L)  the base-3 digit count
-- of L.  Choosing  L = pow3 k  for a large  k  (supplied by  T4.NatExp.affine_dom,
-- the "2^k outgrows any affine b + d*k" fact) makes  D <= k+1  ( a base-3 number
-- 3^k has k+1 digits, via  digit_log + pow3 reflecting <= ), so the whole size is
-- dominated by  pow3 k = L :
--
--   sizeFits :  Sg L. nodes (mcode1 (berry Kf L)) <= L .
--
-- This is the formal shadow of Chaitin's  |program| = const + log L < L .

module T4.KolmExpLinear where

open import T4.Base
open import BRA3.Code.Tag       using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right ; addN_suc_right )
open import BRA3.RuleInst2 using
  ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans )
open import T4.ProgEnc   using ( nodes ; addN_assoc )
open import T4.ProgNodes using ( addN_comm )
open import T4.EvalU     using ( mcode1 )
open import T4.TreeDigitsSize using ( pow3 )
open import T4.Exp       using ( powN )
open import T4.NatExp    using
  ( Sg ; mkSg ; mulc ; affine_dom ; addN_mono ; addN_mono_l ; addN_mono_r
  ; le_self_addN_l )
open import T4.KolmLog   using ( pow3_ge1 ; pow3_mono ; pr0 ; digit_log )
open import T4.KolmDigits using ( digits3 )
open import T4.KolmSize  using ( baseN ; PDmax ; repAdd ; lenDL ; Wf ; le_addN_2nd )
open import T4.KolmBoundedSearch using ( BerryF )
open import T4.KolmBerry using ( berry ; berrySize )
open import T4.KolmMonusLemmas using ( leLt )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS ; Or ; inl ; inr )

------------------------------------------------------------------------
-- Small Nat helpers.

noSucLe : (k : Nat) -> NatLe (suc k) k -> Empty
noSucLe (suc k) (le-suc h) = noSucLe k h

lt_to_le : {a b : Nat} -> Lt a b -> NatLe (suc a) b
lt_to_le (ltZ n)       = le-suc (le-zero n)
lt_to_le (ltS a b h)   = le-suc (lt_to_le h)

addN_p_one : (p : Nat) -> Eq (addN p (suc zero)) (suc p)
addN_p_one p = eqTrans (addN_suc_right p zero) (eqCong suc (addN_zero_right p))

repAdd_eq_mulc : (c n : Nat) -> Eq (repAdd c n) (mulc c n)
repAdd_eq_mulc c zero    = refl
repAdd_eq_mulc c (suc n) = eqCong (\ z -> addN c z) (repAdd_eq_mulc c n)

repAdd_mono : (c : Nat) {m n : Nat} -> NatLe m n -> NatLe (repAdd c m) (repAdd c n)
repAdd_mono c (le-zero n)            = le-zero (repAdd c n)
repAdd_mono c (le-suc {m'} {n'} h)   = le_addN_2nd c (repAdd_mono c h)

------------------------------------------------------------------------
-- powN <= pow3  and  pow3 reflects <= .

powN_le_pow3 : (k : Nat) -> NatLe (powN k) (pow3 k)
powN_le_pow3 zero    = le-refl (suc zero)
powN_le_pow3 (suc m) =
  le-trans (addN_mono (powN_le_pow3 m) (powN_le_pow3 m))
           (addN_mono_r (le_self_addN_l (pow3 m) (pow3 m)))

-- one strict step:  suc (pow3 m) <= pow3 (suc m) .
pow3_step : (m : Nat) -> NatLe (suc (pow3 m)) (pow3 (suc m))
pow3_step m =
  eqSubst (\ z -> NatLe z (pow3 (suc m))) (addN_p_one (pow3 m))
    (addN_mono_r one_le)
  where
    one_le : NatLe (suc zero) (addN (pow3 m) (pow3 m))
    one_le = le-trans (pow3_ge1 m) (le_self_addN_l (pow3 m) (pow3 m))

pow3_reflect_le : (a b : Nat) -> NatLe (pow3 a) (pow3 b) -> NatLe a b
pow3_reflect_le a b h = decide (leLt b a)
  where
    decide : Or (NatLe a b) (Lt b a) -> NatLe a b
    decide (inl le) = le
    decide (inr lt) =
      let strict : NatLe (suc (pow3 b)) (pow3 a)
          strict = le-trans (pow3_step b) (pow3_mono (lt_to_le lt))
      in emptyElim (noSucLe (pow3 b) (le-trans strict h))

------------------------------------------------------------------------
-- The digit count of  pow3 k  is at most  k+1 .

prToD : {D k : Nat} -> NatLe (pr0 D) k -> NatLe D (suc k)
prToD {zero}   le = le-zero (suc _)
prToD {suc D'} le = le-suc le

digitsBound : (k : Nat) -> NatLe (lenDL (digits3 (pow3 k))) (suc k)
digitsBound k =
  prToD (pow3_reflect_le (pr0 (lenDL (digits3 (pow3 k)))) k
          (digit_log (pow3 k) (pow3 k) (pow3_ge1 k) (le-refl (pow3 k))))

------------------------------------------------------------------------
-- THE SIZE-FITS LEMMA.
--
-- The affine size constant is SEALED abstract (bC).  Otherwise the chosen
-- exponent  k0 = suc (bC + ... + 8)  carries the concrete numeral baseN/PDmax as
-- a deep prefix, and  pow3 k0 / affine_dom / digit_log  evaluate a ~3^30 term
-- (cold typecheck blows up).  With  bC  opaque,  k0 = suc (stuck) , so pow3 k0
-- stays a small symbolic term and nothing exponential is forced.

abstract
  bC : Fun1 -> Nat
  bC Kf = addN (addN baseN (Wf (BerryF Kf))) PDmax

  bC_unfold : (Kf : Fun1) -> Eq (bC Kf) (addN (addN baseN (Wf (BerryF Kf))) PDmax)
  bC_unfold Kf = refl

  -- the chosen exponent, SEALED so that  pow3 (chosenK Kf)  is a single opaque
  -- symbol (not  pow3 (suc stuck) , which would unfold into three copies and
  -- bog the unifier down).
  chosenK : Fun1 -> Nat
  chosenK Kf = Sg.fst (affine_dom (bC Kf) PDmax)

  chosenK_spec :
    (Kf : Fun1) ->
    NatLe (addN (bC Kf) (mulc PDmax (chosenK Kf))) (powN (chosenK Kf))
  chosenK_spec Kf = Sg.snd (affine_dom (bC Kf) PDmax)

sizeFits :
  (Kf : Fun1) -> Sg Nat (\ L -> NatLe (nodes (mcode1 (berry Kf L))) L)
sizeFits Kf = mkSg L (le-trans (berrySize Kf L) finalBound)
  where
    W : Nat
    W = Wf (BerryF Kf)
    a0 : Nat
    a0 = addN baseN W
    k0 : Nat
    k0 = chosenK Kf
    affBound : NatLe (addN (addN a0 PDmax) (mulc PDmax k0)) (powN k0)
    affBound = eqSubst (\ z -> NatLe (addN z (mulc PDmax k0)) (powN k0))
                       (bC_unfold Kf) (chosenK_spec Kf)

    L : Nat
    L = pow3 k0
    D : Nat
    D = lenDL (digits3 L)

    Dle : NatLe D (suc k0)
    Dle = digitsBound k0

    -- grow the digit term to  repAdd PDmax (suc k0) .
    grow : NatLe (addN (addN baseN (repAdd PDmax D)) W)
                 (addN (addN baseN (repAdd PDmax (suc k0))) W)
    grow = addN_mono_l {b = W} (addN_mono_r {a = baseN} (repAdd_mono PDmax Dle))

    -- reassociate  (baseN + R) + W  =  (baseN + W) + R  =  a0 + R .
    reassoc : (Rr : Nat) -> Eq (addN (addN baseN Rr) W) (addN a0 Rr)
    reassoc Rr =
      eqTrans (addN_assoc baseN Rr W)
        (eqTrans (eqCong (\ z -> addN baseN z) (addN_comm Rr W))
                 (eqSym (addN_assoc baseN W Rr)))

    -- a0 + PDmax*(suc k0)  =  (a0 + PDmax) + PDmax*k0  <=  powN k0  <=  pow3 k0 .
    affChain : NatLe (addN a0 (mulc PDmax (suc k0))) L
    affChain =
      eqSubst (\ z -> NatLe z L) (eqSym (addN_assoc a0 PDmax (mulc PDmax k0)))
        (le-trans affBound (powN_le_pow3 k0))

    -- (baseN + PDmax*(suc k0)) + W  =  a0 + PDmax*(suc k0)  [as mulc].
    bridge : Eq (addN (addN baseN (repAdd PDmax (suc k0))) W)
                (addN a0 (mulc PDmax (suc k0)))
    bridge = eqTrans (reassoc (repAdd PDmax (suc k0)))
                     (eqCong (\ z -> addN a0 z) (repAdd_eq_mulc PDmax (suc k0)))

    finalBound : NatLe (addN (addN baseN (repAdd PDmax D)) W) L
    finalBound =
      le-trans grow (eqSubst (\ z -> NatLe z L) (eqSym bridge) affChain)
