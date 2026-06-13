{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ThmTCompleteE -- per-constructor completeness for the two E rules.
--
--   thmT_complete_E_intro :
--     (f : Fun1) (t : Term) (dP : Deriv (eqF (ap1 f t) O)) ->
--     Deriv (eqF (ap1 thmT (encode (E_intro f t dP))) (codeFormula (E f)))
--
--   thmT_complete_E_elim :
--     (f : Fun1) (a : Nat) (A : Formula)
--     (nf : (t : Term) -> Eq (substF a t A) A)
--     (d1 : Deriv (imp (eqF (ap1 f (var a)) O) A)) (d2 : Deriv (E f)) ->
--     Deriv (eqF (ap1 thmT (encode (E_elim f a A nf d1 d2))) (codeFormula A))
--
-- Both reduce DEFINITIONALLY (Pair = pi) to the universal closures
-- T4.ThmTAtE.thmT_at_eintro / thmT_at_eelim with the sub-codes plugged
-- in.  Since the E branches are pure validating decoders (they read the
-- conclusion code straight off the body), NO IH-equation premise is
-- required -- the sub-derivations enter only as the embedded code Terms
-- (encode dP / encode d1 / encode d2), which the branches do not inspect.

module T4.ThmTCompleteE where

open import T4.Base
open import T4.Tags
open import T4.Code
open import T4.Encode using ( encode )
open import T4.ThmT   using ( thmT )
open import T4.ThmTAtE using ( thmT_at_eintro ; thmT_at_eelim_codeF ; thmT_at_eintroax )

------------------------------------------------------------------------
-- CASE  E_intro f t dP .   conclusion  E f .
-- encode = pi tag_eintro (pi (pi (codeFun1 f) (codeTerm t)) (encode dP)) .
-- thmT_at_eintro outputs  pi (natCode tag_exists) (codeFun1 f) = codeFormula (E f) .

thmT_complete_E_intro :
  (f : Fun1) (t : Term) (dP : Deriv (eqF (ap1 f t) O)) ->
  Deriv (eqF (ap1 thmT (encode (E_intro f t dP))) (codeFormula (E f)))
thmT_complete_E_intro f t dP =
  thmT_at_eintro (codeFun1 f) (codeTerm t) (encode dP)

------------------------------------------------------------------------
-- CASE  E_elim f a A nf d1 d2 .   conclusion  A .
-- encode = pi tag_eelim
--            (pi (pi (codeFun1 f) (pi (natCode a) (codeFormula A)))
--                (pi (encode d1) (encode d2))) .
-- thmT_at_eelim outputs  codeFormula A  (= Snd (Snd (Fst body))).

thmT_complete_E_elim :
  (f : Fun1) (a : Nat) (A : Formula)
  (nf : (t : Term) -> Eq (substF a t A) A)
  (d1 : Deriv (imp (eqF (ap1 f (var a)) O) A))
  (d2 : Deriv (E f))
  (ih1 : Deriv (eqF (ap1 thmT (encode d1))
                     (codeFormula (imp (eqF (ap1 f (var a)) O) A))))
  (ih2 : Deriv (eqF (ap1 thmT (encode d2)) (codeFormula (E f)))) ->
  Deriv (eqF (ap1 thmT (encode (E_elim f a A nf d1 d2))) (codeFormula A))
thmT_complete_E_elim f a A nf d1 d2 ih1 ih2 =
  thmT_at_eelim_codeF f a A nf (encode d1) (encode d2) ih1 ih2

------------------------------------------------------------------------
-- CASE  eIntroAx f t .   conclusion  imp (eqF (ap1 f t) O) (E f) .
-- encode = pi tag_eintroax (pi (codeFun1 f) (codeTerm t)) .
-- thmT_at_eintroax constructs codeFormula (imp (eqF (ap1 f t) O) (E f)).

thmT_complete_eIntroAx :
  (f : Fun1) (t : Term) ->
  Deriv (eqF (ap1 thmT (encode (eIntroAx f t)))
              (codeFormula (imp (eqF (ap1 f t) O) (E f))))
thmT_complete_eIntroAx f t =
  thmT_at_eintroax (codeFun1 f) (codeTerm t)
