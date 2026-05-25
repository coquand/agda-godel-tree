{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KOut -- Phase E2 (CHAITIN-G1-STANDARD-DIRECTION.md SS5): the search
-- PROJECTOR  out_L  that reads the subject  z0  back off a matched proof.
-- The standard-route analog of BRA4.ChaitinG1Out, simpler: the K-formula
-- skeleton (BRA4.KFormula) is a PURE right-spine (every constant on the
-- left), so the subject slot is reached by  Snd^9  -- no Fst detour.
--
--   out_L L w  =  decode (Snd^9 (thmT w))
--   out_L_correct : thmT w = codeFormula (Kgt L (natCode z0))  ==>  out_L L w = natCode z0
--     (via the generic  skelOf_proj  + the Decode round-trip  decode (num t) = t).

module BRA4.KOut where

open import BRA4.Base
open import BRA4.Code      using ( codeTerm ; codeFormula )
open import BRA4.ThmT      using ( thmT )
open import BRA4.Num       using ( num )
open import BRA4.IsNat     using ( num_eq_code )
open import BRA4.NumContract using ( isNat_natCode )
open import BRA4.Decode    using ( decode ; decode_num_id_at )
open import BRA4.KFormula  using ( Kgt ; kgtConsts )
open import BRA4.NegAtomCode using ( NVList ; nvnil ; nvcons ; skelOf )

open import BRA3.ChurchT116 using ( Snd )
open import BRA3.PairAlgebra using ( axFst ; axSnd ; compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- SECTION 1.  Generic right-spine projector: from  skelOf cs h  read off  h
-- by applying  Snd  once per constant.

sndProj : NVList -> Fun1
sndProj nvnil           = u
sndProj (nvcons c _ cs) = compose1U (sndProj cs) Snd

skelOf_proj :
  (cs : NVList) (h : Term) ->
  Deriv (eqF (ap1 (sndProj cs) (skelOf cs h)) h)
skelOf_proj nvnil           h = ax_u h
skelOf_proj (nvcons c _ cs) h =
  ruleTrans (compose1U_eq (sndProj cs) Snd (ap2 Pair c (skelOf cs h)))
    (ruleTrans (cong1 (sndProj cs) (axSnd c (skelOf cs h)))
               (skelOf_proj cs h))

------------------------------------------------------------------------
-- SECTION 2.  The K-formula projector  proj_L L , and  out_L .

proj_L : Term -> Fun1
proj_L L = sndProj (kgtConsts L)

-- reads the subject slot:  proj_L L (codeFormula (Kgt L x)) = codeTerm x .
-- (codeFormula (Kgt L x) is definitionally  skelOf (kgtConsts L) (codeTerm x)
-- by KFormula.skel_pins, so this is the generic skelOf_proj.)
proj_at :
  (L x : Term) ->
  Deriv (eqF (ap1 (proj_L L) (codeFormula (Kgt L x))) (codeTerm x))
proj_at L x = skelOf_proj (kgtConsts L) (codeTerm x)

out_L : Term -> Fun1
out_L L = compose1U decode (compose1U (proj_L L) thmT)

out_L_correct :
  (L : Term) (w : Term) (z0 : Nat) ->
  Deriv (eqF (ap1 thmT w) (codeFormula (Kgt L (natCode z0)))) ->
  Deriv (eqF (ap1 (out_L L) w) (natCode z0))
out_L_correct L w z0 matched =
  let e1 : Deriv (eqF (ap1 (out_L L) w)
                      (ap1 decode (ap1 (compose1U (proj_L L) thmT) w)))
      e1 = compose1U_eq decode (compose1U (proj_L L) thmT) w
      e2 : Deriv (eqF (ap1 (compose1U (proj_L L) thmT) w)
                      (ap1 (proj_L L) (ap1 thmT w)))
      e2 = compose1U_eq (proj_L L) thmT w
      e3 : Deriv (eqF (ap1 (proj_L L) (ap1 thmT w)) (codeTerm (natCode z0)))
      e3 = ruleTrans (cong1 (proj_L L) matched) (proj_at L (natCode z0))
      e4 : Deriv (eqF (ap1 decode (codeTerm (natCode z0))) (natCode z0))
      e4 = ruleTrans (cong1 decode (ruleSym (num_eq_code (natCode z0) (isNat_natCode z0))))
                     (decode_num_id_at (natCode z0))
  in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)
