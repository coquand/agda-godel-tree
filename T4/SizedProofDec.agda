{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SizedProofDec -- the DECODER interface for the size-prefixed proof coding
-- (T4.SizedProof).  Constructor-tag and child projectors, with their Deriv
-- equations (axFst / axSnd only -- the constructor/decoder interface, no
-- induction).  The diamond interpreter dispatches on  pTag  and reads children
-- with  pArg / pL / pR ; under the verified-constructor branch the size-descent
-- (T4.SizedProof.descP_*) feeds the recursive calls.
--
-- Layout (T4.SizedProof):  code = Pair size (Pair tag arg) , arg = child | Pair l r.
--   pBody d = Snd d            -- = Pair tag arg
--   pTag  d = Fst (Snd d)      -- constructor tag 0..4
--   pArg  d = Snd (Snd d)      -- payload: O (cZe) | child (cSu/cRO) | Pair l r (cAd/cRS)
--   pL    d = Fst (Snd (Snd d))   -- first child (binary)
--   pR    d = Snd (Snd (Snd d))   -- second child (binary)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.SizedProofDec where

open import T4.Base

open import T4.SizedProof using
  ( pSize ; pcZe ; pcSu ; pcAd ; pcRO ; pcRS )

open import BRA3.Church using ( sigma )

------------------------------------------------------------------------
-- SECTION 1.  Projectors.

pTag : Term -> Term
pTag d = ap1 Fst (ap1 Snd d)

pArg : Term -> Term
pArg d = ap1 Snd (ap1 Snd d)

pL : Term -> Term
pL d = ap1 Fst (ap1 Snd (ap1 Snd d))

pR : Term -> Term
pR d = ap1 Snd (ap1 Snd (ap1 Snd d))

------------------------------------------------------------------------
-- SECTION 2.  Tag equations.

pTag_cZe : Deriv (eqF (pTag pcZe) (natCode 0))
pTag_cZe =
  ruleTrans (cong1 Fst (axSnd (natCode 1) (ap2 Pair (natCode 0) O)))
            (axFst (natCode 0) O)

pTag_cSu : (c : Term) -> Deriv (eqF (pTag (pcSu c)) (natCode 1))
pTag_cSu c =
  ruleTrans (cong1 Fst (axSnd (ap1 s (pSize c)) (ap2 Pair (natCode 1) c)))
            (axFst (natCode 1) c)

pTag_cAd : (l r : Term) -> Deriv (eqF (pTag (pcAd l r)) (natCode 2))
pTag_cAd l r =
  ruleTrans (cong1 Fst (axSnd (ap1 s (ap2 sigma (pSize l) (pSize r)))
                              (ap2 Pair (natCode 2) (ap2 Pair l r))))
            (axFst (natCode 2) (ap2 Pair l r))

pTag_cRO : (c : Term) -> Deriv (eqF (pTag (pcRO c)) (natCode 3))
pTag_cRO c =
  ruleTrans (cong1 Fst (axSnd (ap1 s (pSize c)) (ap2 Pair (natCode 3) c)))
            (axFst (natCode 3) c)

pTag_cRS : (l r : Term) -> Deriv (eqF (pTag (pcRS l r)) (natCode 4))
pTag_cRS l r =
  ruleTrans (cong1 Fst (axSnd (ap1 s (ap2 sigma (pSize l) (pSize r)))
                              (ap2 Pair (natCode 4) (ap2 Pair l r))))
            (axFst (natCode 4) (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 3.  Child equations (unary via pArg; binary via pArg = Pair l r).

pArg_cSu : (c : Term) -> Deriv (eqF (pArg (pcSu c)) c)
pArg_cSu c =
  ruleTrans (cong1 Snd (axSnd (ap1 s (pSize c)) (ap2 Pair (natCode 1) c)))
            (axSnd (natCode 1) c)

pArg_cRO : (c : Term) -> Deriv (eqF (pArg (pcRO c)) c)
pArg_cRO c =
  ruleTrans (cong1 Snd (axSnd (ap1 s (pSize c)) (ap2 Pair (natCode 3) c)))
            (axSnd (natCode 3) c)

pArg_cAd : (l r : Term) -> Deriv (eqF (pArg (pcAd l r)) (ap2 Pair l r))
pArg_cAd l r =
  ruleTrans (cong1 Snd (axSnd (ap1 s (ap2 sigma (pSize l) (pSize r)))
                              (ap2 Pair (natCode 2) (ap2 Pair l r))))
            (axSnd (natCode 2) (ap2 Pair l r))

pArg_cRS : (l r : Term) -> Deriv (eqF (pArg (pcRS l r)) (ap2 Pair l r))
pArg_cRS l r =
  ruleTrans (cong1 Snd (axSnd (ap1 s (ap2 sigma (pSize l) (pSize r)))
                              (ap2 Pair (natCode 4) (ap2 Pair l r))))
            (axSnd (natCode 4) (ap2 Pair l r))

pL_cAd : (l r : Term) -> Deriv (eqF (pL (pcAd l r)) l)
pL_cAd l r = ruleTrans (cong1 Fst (pArg_cAd l r)) (axFst l r)

pR_cAd : (l r : Term) -> Deriv (eqF (pR (pcAd l r)) r)
pR_cAd l r = ruleTrans (cong1 Snd (pArg_cAd l r)) (axSnd l r)

pL_cRS : (l r : Term) -> Deriv (eqF (pL (pcRS l r)) l)
pL_cRS l r = ruleTrans (cong1 Fst (pArg_cRS l r)) (axFst l r)

pR_cRS : (l r : Term) -> Deriv (eqF (pR (pcRS l r)) r)
pR_cRS l r = ruleTrans (cong1 Snd (pArg_cRS l r)) (axSnd l r)
