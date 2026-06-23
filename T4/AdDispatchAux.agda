{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.AdDispatchAux -- small arithmetic facts for the Ad sub-dispatch:
--
--   dtag_O        : dtag O = dgZe          (Fst (Snd O) = O , via pi_O_O + T116/T117)
--   neL_from_htagL: dtag c = dgSu  =>  c != O   (else dtag c = dtag O = dgZe = dgSu)
--
-- The second is how the Ad_Su branch recovers the bare  pL != O  it needs for the
-- opaque Su recursion on the left child + the grandchild bound.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.AdDispatchAux where

open import T4.Base

open import T4.DerCodeS using ( dtag )
open import T4.DerCode  using ( dgZe ; dgSu )
open import T4.ParEnds  using ( pi_O_O )
open import BRA3.ChurchT116 using ( Snd )
open import BRA3.ChurchT117 using ( Fst )
open import BRA3.Dispatch   using ( T116_at_terms ; T117_at_terms ; closed_O )
open import BRA3.Classical  using ( axContrapos )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impLift ; impEqTrans )
open import BRA3.Contrapositive using ( identP )

------------------------------------------------------------------------
-- Fst O = O ,  Snd O = O ,  dtag O = dgZe .

SndO : Deriv (eqF (ap1 Snd O) O)
SndO = ruleTrans (cong1 Snd (ruleSym pi_O_O)) (T116_at_terms O O closed_O)

FstO : Deriv (eqF (ap1 Fst O) O)
FstO = ruleTrans (cong1 Fst (ruleSym pi_O_O)) (T117_at_terms O O closed_O)

dtag_O : Deriv (eqF (dtag O) dgZe)
dtag_O = ruleTrans (cong1 Fst SndO) FstO

------------------------------------------------------------------------
-- neL_from_htagL :  dtag c = dgSu  =>  c != O .

neL_from_htagL : (c : Term) -> Deriv (eqF (dtag c) dgSu) -> Deriv (neg (eqF c O))
neL_from_htagL c htagL =
  let P : Formula
      P = eqF c O
      a1 : Deriv (imp P (eqF (dtag c) (dtag O)))
      a1 = impCong1 Fst (ap1 Snd c) (ap1 Snd O)
             (impCong1 Snd c O (identP P))
      imp_c0_sO : Deriv (imp P (eqF (ap1 s O) O))
      imp_c0_sO =
        impEqTrans (ap1 s O) (dtag c) O
          (impLift {P} (ruleSym htagL))
          (impEqTrans (dtag c) (dtag O) O a1 (impLift {P} dtag_O))
  in mp (mp (axContrapos P (eqF (ap1 s O) O)) imp_c0_sO) ax_succ_nonzero
