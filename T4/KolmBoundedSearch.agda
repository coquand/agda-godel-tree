{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmBoundedSearch -- brick A of the non-computability proof: the runnable
-- Berry search program.
--
-- Given a candidate computer  Kf : Fun1  for Kolmogorov complexity, we build a
-- FIXED (Kf-dependent but L-independent) mu-free  BerryF : Fun1  whose meta
-- value at L is
--
--   bfun Kf L  =  the least  x < 3^(L+1)+1  with  evalN1 Kf x > L , or the
--                 bound itself if none.
--
-- The object program is the FirstHit-style search recursor
--   searchRec = R o gStep Pair ,  driven to depth  suc (pow3 (suc L)) ,
-- with the per-step combinator  gStep  assembled from Fan / Post / Lift /
-- condFork / sub / isZero / Kf .  Its meta semantics is computed via the
-- T4.KolmEvalMeta library (cantor projections by reflection, arithmetic
-- structurally) so that  evalN1 (BerryF Kf) L = bfun Kf L  ( berryMeta ).
--
-- The search SUCCEEDS (bfun_hit:  L < evalN1 Kf (bfun Kf L)) because some
-- x <= 3^(L+1) is incompressible-above-L (T4.KolmIncompress.incompressible),
-- which the "realizes" clause turns into a hit.

module T4.KolmBoundedSearch where

open import T4.Base
open import T4.EvalUCorrect using ( evalN1 ; evalN2 )
open import BRA3.Church     using ( sub ; isZero )
open import T4.Exp3         using ( exp3 )
open import T4.TreeDigitsSize using ( pow3 )
open import T4.Code         using ( falseF )
open import T4.SurpriseG2.NumNeq using ( Not )
open import T4.KolmEvalMeta using
  ( predN ; monus ; iszN ; caseNat ; eqCong2
  ; evalN2_Lift1 ; evalN2_Lift2 ; evalN1_compose1U
  ; evalN1_isZero ; evalN2_sub ; evalN2_condFork0 ; evalN2_condForkS
  ; fstP ; sndP ; evalN1_exp3 ; fanMeta ; postMeta )
open import T4.KolmMonusLemmas using ( monusZeroLt ; monusPosLe )
open import BRA3.RuleInst2  using ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right )
open import T4.SurpriseG2.MetaPigeonhole using
  ( Lt ; ltZ ; ltS ; ltAbsurd ; ltSucCases ; Or ; inl ; inr )
open import T4.KolmCount      using ( Kle )
open import T4.KolmIncompress using ( incompressible ; AllCompressible )

------------------------------------------------------------------------
-- SECTION 1.  The object combinators.

-- gStep Kf :  ap2 (gStep Kf) (Pair L n) prev
--   = condFork (Pair prev (s n)) (isZero (sub (s L) (Kf prev)))
-- i.e. freeze at prev if  Kf prev > L , else advance to  s n .
gStep : Fun1 -> Fun2
gStep Kf =
  Fan (Fan v (Lift1 (compose1U s Snd)) Pair)
      (Post isZero (Fan (Lift1 (compose1U s Fst)) (Lift2 Kf) sub))
      condFork

searchRec : Fun1 -> Fun2
searchRec Kf = R o (gStep Kf) Pair

-- boundF L = suc (pow3 (suc L)) = 3^(L+1) + 1 .
boundF : Fun1
boundF = compose1U s (compose1U exp3 s)

BerryF : Fun1 -> Fun1
BerryF Kf = C (searchRec Kf) u boundF

------------------------------------------------------------------------
-- SECTION 2.  The meta search.

-- gtB Kf L x = 0  iff  evalN1 Kf x > L .
gtB : Fun1 -> Nat -> Nat -> Nat
gtB Kf L x = monus (suc L) (evalN1 Kf x)

gsearch : Fun1 -> Nat -> Nat -> Nat
gsearch Kf L zero    = zero
gsearch Kf L (suc n) =
  caseNat (gtB Kf L (gsearch Kf L n)) (gsearch Kf L n) (suc n)

bfun : Fun1 -> Nat -> Nat
bfun Kf L = gsearch Kf L (suc (pow3 (suc L)))

------------------------------------------------------------------------
-- SECTION 3.  gStep meta law.

condForkCase :
  Not (Deriv falseF) -> (a b m : Nat) ->
  Eq (evalN2 condFork (evalN2 Pair a b) (iszN m)) (caseNat m a b)
condForkCase con a b zero    =
  eqTrans (evalN2_condForkS (evalN2 Pair a b) zero) (fstP con a b)
condForkCase con a b (suc d) =
  eqTrans (evalN2_condFork0 (evalN2 Pair a b)) (sndP con a b)

gStepMeta :
  Not (Deriv falseF) -> (Kf : Fun1) (L n prev : Nat) ->
  Eq (evalN2 (gStep Kf) (evalN2 Pair L n) prev)
     (caseNat (monus (suc L) (evalN1 Kf prev)) prev (suc n))
gStepMeta con Kf L n prev =
  let pkg : Nat
      pkg = evalN2 Pair L n
      makeZ : Fun2
      makeZ = Fan v (Lift1 (compose1U s Snd)) Pair
      subPair : Fun2
      subPair = Fan (Lift1 (compose1U s Fst)) (Lift2 Kf) sub
      makeF : Fun2
      makeF = Post isZero subPair
      -- makeZ value = Pair prev (suc n)
      mz_fan : Eq (evalN2 makeZ pkg prev)
                  (evalN2 Pair prev (evalN2 (Lift1 (compose1U s Snd)) pkg prev))
      mz_fan = fanMeta con v (Lift1 (compose1U s Snd)) Pair pkg prev
      mz_snd : Eq (evalN2 (Lift1 (compose1U s Snd)) pkg prev) (suc n)
      mz_snd = eqTrans (evalN2_Lift1 (compose1U s Snd) pkg prev)
                 (eqTrans (evalN1_compose1U s Snd pkg) (eqCong suc (sndP con L n)))
      mz : Eq (evalN2 makeZ pkg prev) (evalN2 Pair prev (suc n))
      mz = eqTrans mz_fan (eqCong (\ z -> evalN2 Pair prev z) mz_snd)
      -- makeF value = iszN (monus (suc L) (Kf prev))
      sp_fan : Eq (evalN2 subPair pkg prev)
                  (evalN2 sub (evalN2 (Lift1 (compose1U s Fst)) pkg prev)
                              (evalN2 (Lift2 Kf) pkg prev))
      sp_fan = fanMeta con (Lift1 (compose1U s Fst)) (Lift2 Kf) sub pkg prev
      sp_fst : Eq (evalN2 (Lift1 (compose1U s Fst)) pkg prev) (suc L)
      sp_fst = eqTrans (evalN2_Lift1 (compose1U s Fst) pkg prev)
                 (eqTrans (evalN1_compose1U s Fst pkg) (eqCong suc (fstP con L n)))
      sp_kf : Eq (evalN2 (Lift2 Kf) pkg prev) (evalN1 Kf prev)
      sp_kf = evalN2_Lift2 Kf pkg prev
      sp : Eq (evalN2 subPair pkg prev) (monus (suc L) (evalN1 Kf prev))
      sp = eqTrans sp_fan
             (eqTrans (eqCong2 (evalN2 sub) sp_fst sp_kf)
                      (evalN2_sub (suc L) (evalN1 Kf prev)))
      mf : Eq (evalN2 makeF pkg prev) (iszN (monus (suc L) (evalN1 Kf prev)))
      mf = eqTrans (postMeta con isZero subPair pkg prev)
             (eqTrans (eqCong (evalN1 isZero) sp)
                      (evalN1_isZero (monus (suc L) (evalN1 Kf prev))))
      -- assemble
      top : Eq (evalN2 (gStep Kf) pkg prev)
               (evalN2 condFork (evalN2 makeZ pkg prev) (evalN2 makeF pkg prev))
      top = fanMeta con makeZ makeF condFork pkg prev
      cf_args : Eq (evalN2 condFork (evalN2 makeZ pkg prev) (evalN2 makeF pkg prev))
                   (evalN2 condFork (evalN2 Pair prev (suc n))
                                    (iszN (monus (suc L) (evalN1 Kf prev))))
      cf_args = eqCong2 (evalN2 condFork) mz mf
  in eqTrans top
       (eqTrans cf_args
         (condForkCase con prev (suc n) (monus (suc L) (evalN1 Kf prev))))

------------------------------------------------------------------------
-- SECTION 4.  searchRec / BerryF meta values.

searchMeta :
  Not (Deriv falseF) -> (Kf : Fun1) (L m : Nat) ->
  Eq (evalN2 (searchRec Kf) L m) (gsearch Kf L m)
searchMeta con Kf L zero    = refl
searchMeta con Kf L (suc n) =
  eqTrans (gStepMeta con Kf L n (evalN2 (searchRec Kf) L n))
          (eqCong (\ z -> caseNat (monus (suc L) (evalN1 Kf z)) z (suc n))
                  (searchMeta con Kf L n))

boundE : Not (Deriv falseF) -> (L : Nat) -> Eq (evalN1 boundF L) (suc (pow3 (suc L)))
boundE con L =
  eqTrans (evalN1_compose1U s (compose1U exp3 s) L)
          (eqCong suc (eqTrans (evalN1_compose1U exp3 s L) (evalN1_exp3 con (suc L))))

berryMeta :
  Not (Deriv falseF) -> (Kf : Fun1) (L : Nat) ->
  Eq (evalN1 (BerryF Kf) L) (bfun Kf L)
berryMeta con Kf L =
  eqTrans (eqCong (\ z -> evalN2 (searchRec Kf) L z) (boundE con L))
          (searchMeta con Kf L (suc (pow3 (suc L))))

------------------------------------------------------------------------
-- SECTION 5.  Meta search properties.

searchLe : (Kf : Fun1) (L n : Nat) -> NatLe (gsearch Kf L n) n
searchLe Kf L zero    = le-zero zero
searchLe Kf L (suc m) = help (gtB Kf L (gsearch Kf L m)) refl
  where
    help : (g : Nat) -> Eq (gtB Kf L (gsearch Kf L m)) g ->
           NatLe (gsearch Kf L (suc m)) (suc m)
    help zero eq =
      eqSubst (\ z -> NatLe z (suc m))
              (eqSym (eqCong (\ z -> caseNat z (gsearch Kf L m) (suc m)) eq))
              (le-suc-right (searchLe Kf L m))
    help (suc d) eq =
      eqSubst (\ z -> NatLe z (suc m))
              (eqSym (eqCong (\ z -> caseNat z (gsearch Kf L m) (suc m)) eq))
              (le-refl (suc m))

-- either the search reached the frontier n, or its value is a hit.
searchHitOrFront :
  (Kf : Fun1) (L n : Nat) ->
  Or (Eq (gsearch Kf L n) n) (Eq (gtB Kf L (gsearch Kf L n)) zero)
searchHitOrFront Kf L zero    = inl refl
searchHitOrFront Kf L (suc m) = help (gtB Kf L (gsearch Kf L m)) refl
  where
    help : (g : Nat) -> Eq (gtB Kf L (gsearch Kf L m)) g ->
           Or (Eq (gsearch Kf L (suc m)) (suc m))
              (Eq (gtB Kf L (gsearch Kf L (suc m))) zero)
    help zero eq =
      let eGS : Eq (gsearch Kf L (suc m)) (gsearch Kf L m)
          eGS = eqCong (\ z -> caseNat z (gsearch Kf L m) (suc m)) eq
      in inr (eqTrans (eqCong (gtB Kf L) eGS) eq)
    help (suc d) eq =
      inl (eqCong (\ z -> caseNat z (gsearch Kf L m) (suc m)) eq)

-- if the search reached the frontier n, no  x < n  is a hit.
searchScan :
  (Kf : Fun1) (L n : Nat) -> Eq (gsearch Kf L n) n ->
  (x : Nat) -> Lt x n -> Not (Eq (gtB Kf L x) zero)
searchScan Kf L zero    H x lt = ltAbsurd lt
searchScan Kf L (suc m) H x lt = conclude
  where
    -- gsearch Kf L m = m  (else the frontier could not have reached suc m).
    gmm : Eq (gsearch Kf L m) m
    gmm = case (searchHitOrFront Kf L m)
      where
        case : Or (Eq (gsearch Kf L m) m) (Eq (gtB Kf L (gsearch Kf L m)) zero) ->
               Eq (gsearch Kf L m) m
        case (inl e)   = e
        case (inr hit) =
          -- then gsearch (suc m) = gsearch m <= m , contradicting H : = suc m .
          let eGS : Eq (gsearch Kf L (suc m)) (gsearch Kf L m)
              eGS = eqCong (\ z -> caseNat z (gsearch Kf L m) (suc m)) hit
              eSm : Eq (suc m) (gsearch Kf L m)
              eSm = eqTrans (eqSym H) eGS
              -- suc m <= m  is impossible.
              bad : NatLe (suc m) m
              bad = eqSubst (\ z -> NatLe z m) (eqSym eSm) (searchLe Kf L m)
          in emptyElim (noSucLe m bad)
          where
            noSucLe : (k : Nat) -> NatLe (suc k) k -> Empty
            noSucLe (suc k) (le-suc h) = noSucLe k h

    -- gtB Kf L m /= 0  (index m itself is a hit).
    hitm : Not (Eq (gtB Kf L m) zero)
    hitm e0 =
      let eGSm : Eq (gtB Kf L (gsearch Kf L m)) zero
          eGSm = eqTrans (eqCong (gtB Kf L) gmm) e0
          eGS : Eq (gsearch Kf L (suc m)) (gsearch Kf L m)
          eGS = eqCong (\ z -> caseNat z (gsearch Kf L m) (suc m)) eGSm
          -- suc m = gsearch (suc m) = gsearch m = m  : impossible.
          eSm : Eq (suc m) m
          eSm = eqTrans (eqSym H) (eqTrans eGS gmm)
      in sucNeq m eSm
      where
        sucNeq : (k : Nat) -> Not (Eq (suc k) k)
        sucNeq (suc k) e = sucNeq k (sucInj e)
          where sucInj : {a b : Nat} -> Eq (suc a) (suc b) -> Eq a b
                sucInj refl = refl

    conclude : Not (Eq (gtB Kf L x) zero)
    conclude = byCase (ltSucCases lt)
      where
        byCase : Or (Lt x m) (Eq x m) -> Not (Eq (gtB Kf L x) zero)
        byCase (inl ltm) = searchScan Kf L m gmm x ltm
        byCase (inr e)   = \ h0 -> hitm (eqTrans (eqSym (eqCong (gtB Kf L) e)) h0)

------------------------------------------------------------------------
-- SECTION 6.  The Berry hit (brick A deliverable).

-- "Kf realizes K":  Kf x <= L  implies  x is describable within length L .
RealizesAt : Fun1 -> Set
RealizesAt Kf = (L x : Nat) -> NatLe (evalN1 Kf x) L -> Kle L x

-- the search value is genuinely incompressible above L.
bfun_hit :
  Not (Deriv falseF) -> (Kf : Fun1) -> RealizesAt Kf ->
  (L : Nat) -> Lt L (evalN1 Kf (bfun Kf L))
bfun_hit con Kf realizes L =
  orCase (searchHitOrFront Kf L (suc (pow3 (suc L))))
  where
    orCase : Or (Eq (gsearch Kf L (suc (pow3 (suc L)))) (suc (pow3 (suc L))))
                (Eq (gtB Kf L (gsearch Kf L (suc (pow3 (suc L))))) zero) ->
             Lt L (evalN1 Kf (bfun Kf L))
    orCase (inr hit) = monusZeroLt L (evalN1 Kf (bfun Kf L)) hit
    orCase (inl front) = emptyElim (incompressible con L allK)
      where
        allK : AllCompressible L
        allK i lt =
          realizes L i
            (monusPosLe L (evalN1 Kf i)
              (searchScan Kf L (suc (pow3 (suc L))) front i lt))
