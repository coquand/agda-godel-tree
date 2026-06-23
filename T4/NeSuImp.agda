{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.NeSuImp -- the IMP-FORM of  neL_from_htagL :
--   neSu_imp : imp (dtag c = dgSu) (neg (c = O)) .
-- The object Ad_Su sub-dispatch supplies  dtag (pL) = dgSu  as an ANTECEDENT
-- (no deduction theorem), so the  pL != O  it needs for the opaque left-child
-- Su unfold + grandchild bound must come from htagL in imp-form.
--
-- Proof: c = O would give dtag c = dtag O = dgZe = dgSu = s O = O (absurd).
-- The htag fact is threaded as the antecedent H; the rest is bare-in-(c=O),
-- combined in the depth-2 context [H, (c=O)] (T4.CtxKit).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.NeSuImp where

open import T4.Base

open import T4.DerCodeS using ( dtag )
open import T4.DerCode  using ( dgSu )
open import T4.AdDispatchAux using ( dtag_O )

open import BRA3.Classical  using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.CtxKit using ( trans2c )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impCong1 ; impRuleSym ; impEqTrans )

------------------------------------------------------------------------

neSu_imp : (c : Term) -> Deriv (imp (eqF (dtag c) dgSu) (neg (eqF c O)))
neSu_imp c =
  let H : Formula
      H = eqF (dtag c) dgSu
      P : Formula
      P = eqF c O
      Q : Formula
      Q = eqF (ap1 s O) O
      -- htag leg:  imp H (imp P (s O = dtag c)) .
      hsym : Deriv (imp H (eqF (ap1 s O) (dtag c)))
      hsym = impRuleSym (identP H)
      leg1 : Deriv (imp H (imp P (eqF (ap1 s O) (dtag c))))
      leg1 = compI hsym (axK (eqF (ap1 s O) (dtag c)) P)
      -- (c=O) leg:  imp P (dtag c = O) , then lifted to add H .
      a1 : Deriv (imp P (eqF (dtag c) (dtag O)))
      a1 = impCong1 Fst (ap1 Snd c) (ap1 Snd O) (impCong1 Snd c O (identP P))
      bareLeg : Deriv (imp P (eqF (dtag c) O))
      bareLeg = impEqTrans (dtag c) (dtag O) O a1 (impLift {P} dtag_O)
      leg2 : Deriv (imp H (imp P (eqF (dtag c) O)))
      leg2 = impLift {H} bareLeg
      -- combine in [H, P] :  imp H (imp P (s O = O)) .
      imp_c0_sO_H : Deriv (imp H (imp P Q))
      imp_c0_sO_H = trans2c (ap1 s O) (dtag c) O leg1 leg2
      contraStep : Deriv (imp H (imp (neg Q) (neg P)))
      contraStep = impMp (impLift {H} (axContrapos P Q)) imp_c0_sO_H
  in impMp contraStep (impLift {H} ax_succ_nonzero)
