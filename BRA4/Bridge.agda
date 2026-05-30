{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Bridge -- the mathematical core of the Chaitin search's  bridge  lemma
-- (CHAITIN-G1-SEARCH-DESIGN.md, step 3), built NUMERICALLY (the user's point:
-- codes are naturals under the injective Pair/pi pairing, and  eqF  IS numeric
-- equality, so the comparison is the shipped numeric equality indicator  eqInd ,
-- NOT a structural Pair-tree recursion).
--
--   eqInd a b  (Counting.agda)  = indLt a (s b) - indLt a b  in {0, s O} ;
--                = s O  iff  a = b .
--
-- THE REFLECTION (eqInd_sound) is the hard part, and it is the SHIPPED
-- antisymmetry packaged in  eqInd_at_neq  (a /= b => eqInd a b = O): its
-- contrapositive + DNE + (s O /= O) gives  eqInd a b = s O => a = b .  NO new
-- arithmetic, NO tree recursion.
--
-- bridgeCore  then composes the reflection with the PROVED  negAtomCodeOf_correct :
-- if the numeric test between  thmT proofCode  and  negAtomCodeOf ell (natCode n)
-- fires, then  thmT proofCode = codeFormula (neg (atomForm ell (natCode n))) .
-- This IS the  bridge 's content; wiring it into  SpikeChaitin.Search.bridge  is
-- thin plumbing once  enum / hit / out  exist ( hit = eqInd o (thmT o Snd ,
-- negAtomCodeOf o Fst) , out = Fst ).  Every step here is a PROVED Deriv.

module BRA4.Bridge where

open import BRA4.Base
open import BRA4.Code using ( codeFormula ; falseF )
open import BRA4.ThmT using ( thmT )
open import BRA4.DefWit using ( atomForm )
open import BRA4.NegAtomCode using ( negAtomCodeOf ; negAtomCodeOf_correct )
open import BRA4.Counting
  using ( eqInd ; eqInd_at_neq_imp ; eqInd_le_one
        ; negToImpFalse ; impFalseToNeg_imp )

open import BRA3.ChurchLeq using ( leq )
open import BRA3.Logic using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI ; DNE )

------------------------------------------------------------------------
-- SECTION 1.  The numeric-equality reflection (the bridge's real content).
--
--   eqInd a b = s O   =>   a = b .
-- Contrapositive of  eqInd_at_neq  (a /= b => eqInd a b = O) + DNE + s O /= O:
-- under  neg (a = b) ,  eqInd a b  is both  O  (eqInd_at_neq) and  s O  (hyp),
-- so  s O = O  -- false (ax_succ_nonzero) -- giving  neg (neg (a=b)) , then DNE.

eqInd_sound :
  (a b : Term) ->
  Deriv (eqF (eqInd a b) (ap1 s O)) ->
  Deriv (eqF a b)
eqInd_sound a b h =
  let nq : Formula
      nq = neg (eqF a b)
      d_O : Deriv (imp nq (eqF (eqInd a b) O))
      d_O = eqInd_at_neq_imp a b
      -- rewrite  eqInd a b = O  to  s O = O  using (sym h).
      rw : Deriv (imp (eqF (eqInd a b) O) (eqF (ap1 s O) O))
      rw = prependEqLeft (ap1 s O) (eqInd a b) O (ruleSym h)
      d_soO : Deriv (imp nq (eqF (ap1 s O) O))
      d_soO = compI d_O rw
      d_false : Deriv (imp nq falseF)
      d_false = compI d_soO (negToImpFalse (eqF (ap1 s O) O) ax_succ_nonzero)
      dnn : Deriv (neg nq)
      dnn = mp (impFalseToNeg_imp nq) d_false
  in mp (DNE (eqF a b)) dnn

------------------------------------------------------------------------
-- SECTION 2.  bridgeCore -- the bridge for a numeral subject  natCode n .
--
-- If the numeric test between the proof's verified formula  thmT proofCode  and
-- the expected incompressibility code  negAtomCodeOf ell (natCode n)  fires, then
-- thmT proofCode = codeFormula (neg (atomForm ell (natCode n))) .  Reflection
-- (eqInd_sound) + the PROVED  negAtomCodeOf_correct .

bridgeCore :
  (ell : Term) (n : Nat) (proofCode : Term) ->
  Deriv (eqF (eqInd (ap1 thmT proofCode) (ap1 (negAtomCodeOf ell) (natCode n)))
             (ap1 s O)) ->
  Deriv (eqF (ap1 thmT proofCode)
             (codeFormula (neg (atomForm ell (natCode n)))))
bridgeCore ell n proofCode hmatch =
  ruleTrans (eqInd_sound (ap1 thmT proofCode)
                         (ap1 (negAtomCodeOf ell) (natCode n)) hmatch)
            (negAtomCodeOf_correct ell n)

------------------------------------------------------------------------
-- SECTION 3.  out = Fst (trivial subject projection); the 0/1 bound is the
-- shipped  eqInd_le_one  (= hit_le_one once  hit  is wired through enum).

out : Fun1
out = Fst

hitBound :
  (a b : Term) -> Deriv (leq (eqInd a b) (ap1 s O))
hitBound = eqInd_le_one
