{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrFunValidCanon -- the canonical funcodes all validate:
--   funValid cSuc = O,  funValid cZero = O,  funValid cId = O,  funValid cProj = O,
--   funValid (cComp g h1 h2) = O,  funValid (cRec g h1 h2) = O   (universal in g h1 h2)
--
-- funValid is a SHALLOW (one-level) check: funValid f = eqDecO f (recon f), and
-- recon f only reconstructs the head + the immediate components via projections
-- (cG/cH1/cH2), NOT recursively.  So funValid of a compound funcode holds for
-- ARBITRARY sub-funcodes -- no induction needed.  This is exactly what
-- wfFunRec_shadow needs: every shadow-coded funcode validates.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrFunValidCanon where

open import T4.Base

open import T4.PrCodeObj
  using ( cSuc ; cZero ; cId ; cComp ; cProj ; cRec
        ; hd_cSuc ; hd_cZero ; hd_cId ; hd_cComp ; hd_cProj ; hd_cRec
        ; compFun ; compH1 ; compH2 ; recFun ; recH1 ; recH2 )
open import T4.PrFunValid
  using ( funValid ; recon ; cG ; cH1 ; cH2
        ; recon_s ; recon_o ; recon_u ; recon_C ; recon_v ; recon_R )
open import T4.EqDecO using ( eqDecO_complete )

open import BRA3.PairAlgebra using ( I ; axI ; compose1U ; compose1U_eq )
open import BRA3.Church       using ( isZero )
open import BRA3.SubT.NatEq    using ( natEqF )

------------------------------------------------------------------------
-- SECTION -1.  funValid as a Fun1 object code  funValidF .

funValidF : Fun1
funValidF = compose1U isZero (C natEqF I recon)

funValidF_eq : (x : Term) -> Deriv (eqF (ap1 funValidF x) (funValid x))
funValidF_eq x =
  ruleTrans (compose1U_eq isZero (C natEqF I recon) x)
    (cong1 isZero
      (ruleTrans (ax_C natEqF I recon x)
                 (congL natEqF (ap1 recon x) (axI x))))

------------------------------------------------------------------------
-- SECTION 0.  3-arg congruence for the compound funcode shapes.

congTriple : (a a' b b' c c' : Term) ->
  Deriv (eqF a a') -> Deriv (eqF b b') -> Deriv (eqF c c') ->
  Deriv (eqF (ap2 Pair a (ap2 Pair b c)) (ap2 Pair a' (ap2 Pair b' c')))
congTriple a a' b b' c c' ea eb ec =
  ruleTrans (congL Pair (ap2 Pair b c) ea)
            (congR Pair a' (ruleTrans (congL Pair c eb) (congR Pair b' ec)))

congComp : (a a' b b' c c' : Term) ->
  Deriv (eqF a a') -> Deriv (eqF b b') -> Deriv (eqF c c') ->
  Deriv (eqF (cComp a b c) (cComp a' b' c'))
congComp a a' b b' c c' ea eb ec =
  congR Pair (natCode 6) (congTriple a a' b b' c c' ea eb ec)

congRec : (a a' b b' c c' : Term) ->
  Deriv (eqF a a') -> Deriv (eqF b b') -> Deriv (eqF c c') ->
  Deriv (eqF (cRec a b c) (cRec a' b' c'))
congRec a a' b b' c c' ea eb ec =
  congR Pair (natCode 8) (congTriple a a' b b' c c' ea eb ec)

------------------------------------------------------------------------
-- SECTION 1.  Nullary funcodes.

funValid_cSuc : Deriv (eqF (funValid cSuc) O)
funValid_cSuc = eqDecO_complete cSuc (ap1 recon cSuc) (ruleSym (recon_s cSuc hd_cSuc))

funValid_cZero : Deriv (eqF (funValid cZero) O)
funValid_cZero = eqDecO_complete cZero (ap1 recon cZero) (ruleSym (recon_o cZero hd_cZero))

funValid_cId : Deriv (eqF (funValid cId) O)
funValid_cId = eqDecO_complete cId (ap1 recon cId) (ruleSym (recon_u cId hd_cId))

funValid_cProj : Deriv (eqF (funValid cProj) O)
funValid_cProj = eqDecO_complete cProj (ap1 recon cProj) (ruleSym (recon_v cProj hd_cProj))

------------------------------------------------------------------------
-- SECTION 2.  Compound funcodes (universal in the sub-funcodes).

funValid_cComp : (g h1 h2 : Term) -> Deriv (eqF (funValid (cComp g h1 h2)) O)
funValid_cComp g h1 h2 =
  let f = cComp g h1 h2
      recEq : Deriv (eqF (ap1 recon f) (cComp g h1 h2))
      recEq = ruleTrans (recon_C f (hd_cComp g h1 h2))
                (congComp (cG f) g (cH1 f) h1 (cH2 f) h2
                  (compFun g h1 h2) (compH1 g h1 h2) (compH2 g h1 h2))
  in eqDecO_complete f (ap1 recon f) (ruleSym recEq)

funValid_cRec : (g h1 h2 : Term) -> Deriv (eqF (funValid (cRec g h1 h2)) O)
funValid_cRec g h1 h2 =
  let f = cRec g h1 h2
      recEq : Deriv (eqF (ap1 recon f) (cRec g h1 h2))
      recEq = ruleTrans (recon_R f (hd_cRec g h1 h2))
                (congRec (cG f) g (cH1 f) h1 (cH2 f) h2
                  (recFun g h1 h2) (recH1 g h1 h2) (recH2 g h1 h2))
  in eqDecO_complete f (ap1 recon f) (ruleSym recEq)
