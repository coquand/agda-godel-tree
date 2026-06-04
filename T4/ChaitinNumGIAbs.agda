{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinNumGIAbs -- THE HEADLINE.  Chaitin-Goedel-I, number-code form, at
-- the HONEST p<N / runProgN guard, as the ENCODED ( object-level ) implication
--
--   chaitinGI_imp w :
--     Deriv (imp (eqF (ap1 thmT w) (ap1 KcodeN (ap1 outKdefN w)))
--                (eqF (ap1 thmT (gFunN w)) codeFalse))
--
-- i.e.  thmT(w) = code( K(out w) > L* )  =>  thmT(G w) = code(0 = 1) , with
-- G w = gFunN w the diagonal program.  Derived in ONE line ( a la
-- T4.ChaitinGIAbs ) from the deduction-theorem internalisation
-- T4.CgFalseImpN.cgFalseImpDedN at the fresh  var 2  ( closed at vars 0/1,
-- witnesses refl ), then  ruleInst 2 w .  L* / N are the CONCRETE fixed-point
-- threshold ( T4.KGodel1BridgeDefN ); the size pin is PROVEN ( T4.dLenStarDefN ).
-- No holes, no postulates, no discharge-later hypotheses.

module T4.ChaitinNumGIAbs where

open import T4.Base
open import T4.Code  using ( codeFalse )
open import T4.ThmT  using ( thmT )
open import T4.KGodel1BridgeDefN using ( NthrN )
open import T4.KdefN     NthrN using ( KcodeN )
open import T4.KdefRecogN NthrN using ( outKdefN )
open import T4.CgFalseImpN using ( HypAtN ; cgFalseImpDedN )
open import T4.CgiClashImp using ( Sigma )

------------------------------------------------------------------------
-- The diagonal program  G w = gFunN w  ( the var-2 self-referential
-- diagonal, specialised to  w  by substitution ).

gFunN : Term -> Term
gFunN w =
  substT (suc (suc zero)) w
    (Sigma.fst (cgFalseImpDedN (var (suc (suc zero)))
                  (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl)))

------------------------------------------------------------------------
-- THE THEOREM.

chaitinGI_imp :
  (w : Term) ->
  Deriv (imp (eqF (ap1 thmT w) (ap1 KcodeN (ap1 outKdefN w)))
             (eqF (ap1 thmT (gFunN w)) codeFalse))
chaitinGI_imp w =
  ruleInst (suc (suc zero)) w
    (Sigma.snd (cgFalseImpDedN (var (suc (suc zero)))
                  (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl)))
