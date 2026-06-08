{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmNumReflect -- numeral disequality reflects into the object system:
-- if a /= b then a proof of  natCode a = natCode b  yields a proof of  0 = 1 .
-- (Used by the counting bound: a program describes at most one value, ON PAIN OF
-- INCONSISTENCY.)  No consistency is assumed here -- this is the bridge that the
-- Con hypothesis is then applied to.

module T4.KolmNumReflect where

open import T4.Base
open import BRA3.Code.Tag       using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right ; addN_suc_right )
open import BRA3.Dispatch       using ( eqAtT ; eqAtT_match ; eqAtT_above )
open import T4.Code             using ( falseF )
open import T4.SurpriseG2.NumNeq using ( Not )

------------------------------------------------------------------------
-- local Sigma / Or.

record Sg (A : Set) (B : A -> Set) : Set where
  constructor mkSg
  field
    fst : A
    snd : B fst

data Or (P Q : Set) : Set where
  inl : P -> Or P Q
  inr : Q -> Or P Q

------------------------------------------------------------------------
-- order with an additive witness:  a /= b  =>  one is  suc (d + other) .

AddForm : Nat -> Nat -> Set
AddForm a b =
  Or (Sg Nat (\ d -> Eq b (suc (addN d a))))
     (Sg Nat (\ d -> Eq a (suc (addN d b))))

cmpStep : (a b : Nat) -> AddForm a b -> AddForm (suc a) (suc b)
cmpStep a b (inl (mkSg d e)) =
  inl (mkSg d (eqTrans (eqCong suc e) (eqSym (eqCong suc (addN_suc_right d a)))))
cmpStep a b (inr (mkSg d e)) =
  inr (mkSg d (eqTrans (eqCong suc e) (eqSym (eqCong suc (addN_suc_right d b)))))

cmpAddN : (a b : Nat) -> Not (Eq a b) -> AddForm a b
cmpAddN zero    zero    ne = emptyElim (ne refl)
cmpAddN zero    (suc b) _  = inl (mkSg b (eqCong suc (eqSym (addN_zero_right b))))
cmpAddN (suc a) zero    _  = inr (mkSg a (eqCong suc (eqSym (addN_zero_right a))))
cmpAddN (suc a) (suc b) ne = cmpStep a b (cmpAddN a b (\ e -> ne (eqCong suc e)))

------------------------------------------------------------------------
-- eqAtT B applied to  natCode (smaller)  is O, to  natCode B  is  s O ;
-- the assumed equation then collapses  O = s O = falseF .

discr :
  (B A d : Nat) -> Eq B (suc (addN d A)) ->
  Deriv (eqF (natCode A) (natCode B)) -> Deriv falseF
discr B A d eB hAB =
  let above : Deriv (eqF (ap1 (eqAtT B) (natCode A)) O)
      above = eqSubst (\ z -> Deriv (eqF (ap1 (eqAtT z) (natCode A)) O))
                      (eqSym eB) (eqAtT_above d A)
      match : Deriv (eqF (ap1 (eqAtT B) (natCode B)) (ap1 s O))
      match = eqAtT_match B
      cg : Deriv (eqF (ap1 (eqAtT B) (natCode A)) (ap1 (eqAtT B) (natCode B)))
      cg = cong1 (eqAtT B) hAB
  in ruleTrans (ruleSym above) (ruleTrans cg match)

numEqToFalse :
  (a b : Nat) -> Not (Eq a b) ->
  Deriv (eqF (natCode a) (natCode b)) -> Deriv falseF
numEqToFalse a b ne h = useOrder (cmpAddN a b ne)
  where
    useOrder : AddForm a b -> Deriv falseF
    useOrder (inl (mkSg d eb)) = discr b a d eb h
    useOrder (inr (mkSg d ea)) = discr a b d ea (ruleSym h)
