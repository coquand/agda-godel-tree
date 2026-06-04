{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinGISize -- the UNCONDITIONAL abstract Chaitin-GI in the  szLeqApp
-- SIZE form ( T4.Kdef.Kdef ), plus its  n -specialised corollary.
--
-- Unlike the  checkAlphN  "Alph" route, the size-form closer  cgFalseImpDed
-- ( T4.CgFalseImp ) takes ONLY closedness ( NO  checkFires ) : its diagonal
-- size premise is discharged INTERNALLY by the proved size bound
-- T4.dLenStarDef.dLenStarDef / T4.KGodel1Canon.dLenStar .   So at the fresh
-- witness  var 2  ( closedness = refl ) and  ruleInst 2 w  we get, for EVERY w :
--
--   chaitinGIsize w :
--     imp (thmT w = Kcode Lstar (outKdef Lstar w)) (thmT (f w) = code(0=1))
--
-- with  f w = substT 2 w (cgFun (var 2)) , and NO hypotheses.   The corollary
-- pins the subject :  given  n : Nat ,  from  thmT w = code(K(n)>L*)  derive
--   thmT (f w) = code(0=1) .

open import T4.Base
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.ChaitinGISize where

open import T4.Code      using ( codeFalse ; codeFormula )
open import T4.ThmT      using ( thmT )
open import T4.Kdef      using ( Kdef ; Kcode ; Kcode_correct )
open import T4.KdefRecog using ( outKdef ; outKdef_correct )
open import T4.CgFun     using ( cgFun )
open import T4.CgFalseImp using ( cgFalseImpDed )

------------------------------------------------------------------------
-- The fresh witness and the diagonal builder  f .

v2 : Term
v2 = var (suc (suc zero))

fSize : Term -> Term
fSize w = substT (suc (suc zero)) w (cgFun v2)

------------------------------------------------------------------------
-- The UNCONDITIONAL size-form abstract Chaitin-GI ( no checkFires ).

chaitinGIsize :
  (w : Term) ->
  Deriv (imp (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))
             (eqF (ap1 thmT (fSize w)) codeFalse))
chaitinGIsize w =
  ruleInst (suc (suc zero)) w
    (cgFalseImpDed v2 (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl))

------------------------------------------------------------------------
-- The  n -specialised corollary :  given  n , build  f  with
--   thmT w = code(K(n)>L*)  =>  thmT (f w) = code(0=1) .

chaitinCorollary :
  (n : Nat) (w : Term) ->
  Deriv (eqF (ap1 thmT w) (codeFormula (Kdef Lstar (natCode n)))) ->
  Deriv (eqF (ap1 thmT (fSize w)) codeFalse)
chaitinCorollary n w hyp =
  let -- bridge  code(Kdef Lstar (natCode n))  =  Kcode Lstar (natCode n) .
      hypK : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (natCode n)))
      hypK = ruleTrans hyp (ruleSym (Kcode_correct Lstar n))

      -- subject read-back :  outKdef Lstar w = natCode n .
      dRecog : Deriv (eqF (ap1 (outKdef Lstar) w) (natCode n))
      dRecog = outKdef_correct Lstar w (natCode n) hypK

      -- re-point  Kcode Lstar (natCode n)  to  Kcode Lstar (outKdef Lstar w) .
      hyp' : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))
      hyp' = ruleTrans hypK (cong1 (Kcode Lstar) (ruleSym dRecog))
  in mp (chaitinGIsize w) hyp'
