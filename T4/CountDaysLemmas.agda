{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CountDaysLemmas -- general arithmetic facts about  countDays  ( the day-count
-- of  BigConjFormulaN ) w.r.t.  suc  and  < , for a GENERIC bound  n .
--
-- These are the lemmas the surprise external induction applies at the ( sealed,
-- suc-shaped )  Ncount .   The KEY one,  countDays_suc_step , is marked  abstract
-- so its body is NEVER inlined / re-elaborated at the call site -- otherwise the
-- general  countDays_step  would reduce  countAux (suc Ncount) _  and blow up.
-- The bound  n  is an ordinary universally-quantified argument ( no fixed  N ).
--
--   countDays_suc_step n r (r < n) :
--     Eq (suc (countDays n (suc (suc r)))) (countDays n (suc r))
--
-- "for  r < n  the day-range  [r+1..n]  is non-empty, so  countDays n (suc r)
--  is a successor" -- the day-r clash's index condition.

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe ; le-zero ; le-suc ; le-suc-right ; le-refl )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS )
open import T4.SurpriseG2.BigConjFormula using ( countDays ; countAux )
open import T4.StepFrontEndN using ( countDays_step )
open import T4.StageBaseFN using ( natLe_to_lt )

module T4.CountDaysLemmas where

-- ALL lemmas are  abstract  : their bodies pattern-match on  n  ( suc / le-suc ),
-- so inlining at the sealed  Ncount  ( = suc Mcount ) would force  n = suc _
-- and blow up ;  hiding the body leaves only the ( n -inert ) signature.

abstract
  -- < / <= conversions ( general, pure order arithmetic ).
  ltToNatLe : (a b : Nat) -> Lt a b -> NatLe (suc a) b
  ltToNatLe .zero    .(suc n) (ltZ n)     = le-suc (le-zero n)
  ltToNatLe .(suc m) .(suc n) (ltS m n h) = le-suc (ltToNatLe m n h)

  natLeSuc_to_Lt : (m n : Nat) -> NatLe (suc m) n -> Lt m n
  natLeSuc_to_Lt m (suc n') (le-suc le') = natLe_to_lt n' m le'

  -- predecessor on the LEFT :  suc m <= n  =>  m <= n .
  natLe_pred_left : (m n : Nat) -> NatLe (suc m) n -> NatLe m n
  natLe_pred_left m (suc n') (le-suc le') = le-suc-right le'

  -- the day-count successor step ( for  r < n ).
  countDays_suc_step :
    (n r : Nat) -> Lt r n ->
    Eq (suc (countDays n (suc (suc r)))) (countDays n (suc r))
  countDays_suc_step n r ltrn =
    eqSym (countDays_step n (suc r) (ltToNatLe r n ltrn))

  -- the day-count COLLAPSE above n :  countDays n (suc n) = 0  ( empty range ).
  countAux_zero_ge : (cap r : Nat) -> NatLe cap r -> Eq (countAux cap r) zero
  countAux_zero_ge zero    r        _           = refl
  countAux_zero_ge (suc n) zero     ()
  countAux_zero_ge (suc n) (suc r') (le-suc le) = countAux_zero_ge n r' le

  countDays_above : (n : Nat) -> Eq (countDays n (suc n)) zero
  countDays_above n = countAux_zero_ge (suc n) (suc n) (le-refl (suc n))
