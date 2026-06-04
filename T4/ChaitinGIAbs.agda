{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinGIAbs -- the ABSTRACT Chaitin-Goedel-I closer : the closed
-- implication, parametric in  w , with NO closedness assumption on  w .
--
--   chaitinGI checkFires w :
--     Deriv (imp (eqF (ap1 thmT w) (ap1 KcodeAlph (ap1 outKdefAlph w)))
--                (eqF (ap1 thmT (gFunAbs w)) codeFalse))
--
-- where  gFunAbs w = substT 2 w (cgFunAlph (var 2))  is the diagonal at  w .
-- Derived in ONE line from the shipped  cgFalseImpDedAlph  by instantiating it
-- at the fresh  var 2  ( trivially closed at vars 0/1 , witnesses refl ) and
-- then  ruleInst (suc (suc zero)) w .   So it applies to ANY  w  -- in
-- particular a proof code open in  var 0  ( the surprise-GII  x0 ) -- with
-- closeW  acting only on  var 2  inside the lemma, never on  w .

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.ChaitinGIAbs
  (Lstar_meta : Nat)
  where

open import T4.Code  using ( codeFalse )
open import T4.ThmT  using ( thmT )
open import T4.CheckAlphN using ( checkAlphN )
open import T4.ProgEnc using ( enc )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta using ( outKdefAlph )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.CgFunAlph Lstar_meta using ( cgFunAlph )
open import T4.CgFalseImpAlph Lstar_meta using ( cgFalseImpDedAlph )

-- the abstract diagonal at  w  ( var 2 -specialised ).
gFunAbs : Term -> Term
gFunAbs w = substT (suc (suc zero)) w (cgFunAlph (var (suc (suc zero))))

chaitinGI :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->  -- checkFires
  (w : Term) ->
  Deriv (imp (eqF (ap1 thmT w) (ap1 KcodeAlph (ap1 outKdefAlph w)))
             (eqF (ap1 thmT (gFunAbs w)) codeFalse))
chaitinGI checkFires w =
  ruleInst (suc (suc zero)) w
    (cgFalseImpDedAlph checkFires (var (suc (suc zero)))
      (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl))
