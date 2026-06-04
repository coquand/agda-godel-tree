{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EqDecide -- the internal decidable equality interface the surprise-GII
-- run-monotonicity needs:  the object indicator  eqInd : Term -> Term -> Term
-- ( T4.Counting ,  eqInd a t = sub (indLt a (s t)) (indLt a t)  in {0,1} )
-- DECIDES equality, with reflection both ways as Derivs -- valid for ALL terms
-- t1, t2 (free object variables included), NOT just numerals.
--
--   eqInd_neq0_imp_eq :  imp (eqInd t1 t2 =/= 0) (t1 = t2)   ( "test fires => equal" )
--   eqInd_eq_neq0     :  (t1 = t2) => (eqInd t1 t2 =/= 0)     ( converse, meta )
--
-- where  X =/= 0  abbreviates  neg (eqF X O) .  The forward direction is just
-- the contrapositive of the SHIPPED  eqInd_at_neq_imp  (a =/= t => eqInd a t = 0)
-- composed with  DNE  -- no boolean-totality argument needed.  The converse rests
-- on  eqInd_self  ( eqInd a a = s O ), proved here from  notLeqSucSelf  +  the
--  indLt  indicator facts, plus a congruence through the  ap2 sub / indLt
-- structure.
--
-- This corrects the earlier (wrong) claim that symbolic equality reflection is
-- not internally available: it IS, via  eqInd  on the numeric structure
-- ( leq -antisymmetry,  T4.Counting.antisym_curry ).  The forward direction is
-- exactly the internal  natEq -reflection that the readout / config-mode test
-- needs (modulo identifying the machine's mode test with  eqInd ).
--
-- ( NB:  u , v  are BRA combinators ( u : Fun1 , v : Fun2 ), so the term
--  arguments are named  t1 , t2  here. )

module T4.EqDecide where

open import T4.Base
open import T4.Code using ( falseF )

open import BRA3.Church using ( sub )
open import T4.PHP using ( indLt )
open import T4.Counting
  using ( eqInd ; eqInd_at_neq_imp ; indLt_at_lt_imp ; indLt_at_ge_imp
        ; negToImpFalse ; impFalseToNeg_imp )
open import BRA3.ChurchT73     using ( T73 )
open import BRA3.ChurchT87     using ( notLeqSucSelf )
open import BRA3.ChurchSubSucc using ( T_sub_O )
open import BRA3.Logic         using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI ; DNE ; axContrapos )

------------------------------------------------------------------------
-- SECTION 1.  FORWARD reflection :  eqInd t1 t2 =/= 0  =>  t1 = t2 .
--
-- Contrapositive of  eqInd_at_neq_imp : (t1 =/= t2) -> (eqInd t1 t2 = 0) , then DNE.

eqInd_neq0_imp_eq :
  (t1 t2 : Term) ->
  Deriv (imp (neg (eqF (eqInd t1 t2) O)) (eqF t1 t2))
eqInd_neq0_imp_eq t1 t2 =
  let g : Deriv (imp (neg (eqF t1 t2)) (eqF (eqInd t1 t2) O))
      g = eqInd_at_neq_imp t1 t2

      cp : Deriv (imp (neg (eqF (eqInd t1 t2) O)) (neg (neg (eqF t1 t2))))
      cp = mp (axContrapos (neg (eqF t1 t2)) (eqF (eqInd t1 t2) O)) g
  in compI cp (DNE (eqF t1 t2))

------------------------------------------------------------------------
-- SECTION 2.  eqInd a a = s O  ( the indicator fires on the diagonal ).
--   indLt a (s a) = s O   ( a < a+1 , via  T73 at (s a) )
--   indLt a a     = O     ( not a < a , via  notLeqSucSelf )
--   eqInd a a = sub (s O) O = s O   ( T_sub_O ).

eqInd_self : (a : Term) -> Deriv (eqF (eqInd a a) (ap1 s O))
eqInd_self a =
  let X : Term
      X = indLt a (ap1 s a)
      Y : Term
      Y = indLt a a

      eX : Deriv (eqF X (ap1 s O))
      eX = mp (indLt_at_lt_imp a (ap1 s a)) (ruleInst 0 (ap1 s a) T73)

      eY : Deriv (eqF Y O)
      eY = mp (indLt_at_ge_imp a a) (ruleInst 0 a notLeqSucSelf)

      e1 : Deriv (eqF (ap2 sub X Y) (ap2 sub (ap1 s O) Y))
      e1 = congL sub Y eX

      e2 : Deriv (eqF (ap2 sub (ap1 s O) Y) (ap2 sub (ap1 s O) O))
      e2 = congR sub (ap1 s O) eY

      e3 : Deriv (eqF (ap2 sub (ap1 s O) O) (ap1 s O))
      e3 = T_sub_O (ap1 s O)
  in ruleTrans e1 (ruleTrans e2 e3)

------------------------------------------------------------------------
-- SECTION 3.  eqInd t1 t2 = eqInd t1 t1   given   t2 = t1   ( congruence
-- through the  ap2 sub / indLt  structure ;  indLt a b = sub (s O) (sub (s a) b) ).

eqInd_cong :
  (t1 t2 : Term) -> Deriv (eqF t2 t1) ->
  Deriv (eqF (eqInd t1 t2) (eqInd t1 t1))
eqInd_cong t1 t2 t2t1 =
  let e_s : Deriv (eqF (ap1 s t2) (ap1 s t1))
      e_s = cong1 s t2t1

      inner1 : Deriv (eqF (ap2 sub (ap1 s t1) (ap1 s t2)) (ap2 sub (ap1 s t1) (ap1 s t1)))
      inner1 = congR sub (ap1 s t1) e_s

      indLt1 : Deriv (eqF (indLt t1 (ap1 s t2)) (indLt t1 (ap1 s t1)))
      indLt1 = congR sub (ap1 s O) inner1

      inner2 : Deriv (eqF (ap2 sub (ap1 s t1) t2) (ap2 sub (ap1 s t1) t1))
      inner2 = congR sub (ap1 s t1) t2t1

      indLt2 : Deriv (eqF (indLt t1 t2) (indLt t1 t1))
      indLt2 = congR sub (ap1 s O) inner2

      eL : Deriv (eqF (eqInd t1 t2)
                      (ap2 sub (indLt t1 (ap1 s t1)) (indLt t1 t2)))
      eL = congL sub (indLt t1 t2) indLt1

      eR : Deriv (eqF (ap2 sub (indLt t1 (ap1 s t1)) (indLt t1 t2))
                      (eqInd t1 t1))
      eR = congR sub (indLt t1 (ap1 s t1)) indLt2
  in ruleTrans eL eR

------------------------------------------------------------------------
-- SECTION 4.  CONVERSE reflection (meta) :  t1 = t2  =>  eqInd t1 t2 =/= 0 .
--   eqInd t1 t2 = eqInd t1 t1 = s O ,  and  s O =/= O .

eqInd_eq_neq0 :
  (t1 t2 : Term) -> Deriv (eqF t1 t2) ->
  Deriv (neg (eqF (eqInd t1 t2) O))
eqInd_eq_neq0 t1 t2 h =
  let eSO : Deriv (eqF (eqInd t1 t2) (ap1 s O))
      eSO = ruleTrans (eqInd_cong t1 t2 (ruleSym h)) (eqInd_self t1)

      rw : Deriv (imp (eqF (eqInd t1 t2) O) (eqF (ap1 s O) O))
      rw = prependEqLeft (ap1 s O) (eqInd t1 t2) O (ruleSym eSO)

      toFalse : Deriv (imp (eqF (eqInd t1 t2) O) falseF)
      toFalse = compI rw (negToImpFalse (eqF (ap1 s O) O) ax_succ_nonzero)
  in mp (impFalseToNeg_imp (eqF (eqInd t1 t2) O)) toFalse
