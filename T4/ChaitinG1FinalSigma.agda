{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1FinalSigma -- the Sigma-shape (Con-FREE) Chaitin-Goedel I
-- assembly, parallel to T4.ChaitinG1Final.Assemble.chaitin_G1.
--
-- Uses T4.KClashSigma.kr_clash_Sigma in place of the con-consuming
-- T4.KClash.kr_clash, and produces:
--
--   chaitin_G1_Sigma :
--     (x : Term)(nx : isNat x)(d : Deriv (Kgt Lstar x)) ->
--     isNat (out_L Lstar (firstProof x nx d)) ->
--     Closed (out_L Lstar (firstProof x nx d)) ->
--     (nTerm : Term) -> Closed nTerm ->
--     Deriv (evalU (parse (enc (gLcode Lstar))) nTerm
--             = s (out_L Lstar (firstProof x nx d))) ->
--     Sigma Term (\ z -> Deriv (thmT z = codeFalse))
--
-- The hypothesis  d  is at the Deriv level (matches the existing
-- chaitin_G1's signature); the conclusion is the documented CGI_core
-- form  Sigma z. thmT z = codeFalse , with no  con  hypothesis.

module T4.ChaitinG1FinalSigma where

open import T4.Base
open import T4.Code        using ( codeFormula ; codeFalse )
open import T4.ThmT        using ( thmT )
open import T4.IsNat       using ( isNat )
open import T4.KFormula    using ( Kgt ; negKgtCodeOf ; negKgtCodeOf_correct_T )
open import T4.KRecog      using ( hitK ; hitK_le_one ; dNeg_from_hitK )
open import T4.KOut        using ( out_L )
open import T4.KFire       using ( fireAtProof_T )
open import T4.KClashSigma using ( kr_clash_Sigma ; Sigma ; mkSigma )
open import T4.KDiag       using ( gLcode )
open import T4.KGodel1Bridge using ( Lstar )
open import T4.KGodel1Canon  using ( dLenStar )
open import T4.EvalUEval   using ( evalU )
open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse )
open import T4.Encode      using ( encode )

import T4.FirstHit

------------------------------------------------------------------------
-- The Sigma-shape assembly.   No  con  consumed.

module Assemble where

  open T4.FirstHit.Search (hitK Lstar (out_L Lstar))
                            (hitK_le_one Lstar (out_L Lstar))
    using ( leastNumber ; LeastNumber )

  firstProof : (x : Term) -> isNat x -> Deriv (Kgt Lstar x) -> Term
  firstProof x nx d =
    LeastNumber.w1 (leastNumber (encode d) (fireAtProof_T Lstar x nx d))

  chaitin_G1_Sigma :
    (x : Term) (nx : isNat x) (d : Deriv (Kgt Lstar x)) ->
    isNat   (ap1 (out_L Lstar) (firstProof x nx d)) ->
    Closed  (ap1 (out_L Lstar) (firstProof x nx d)) ->
    (nTerm : Term) -> Closed nTerm ->
    Deriv (eqF (ap2 evalU (ap1 parse (enc (gLcode Lstar))) nTerm)
               (ap1 s (ap1 (out_L Lstar) (firstProof x nx d)))) ->
    Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
  chaitin_G1_Sigma x nx d nOut clOut nTerm clN dEval =
    let ln : LeastNumber (encode d)
        ln = leastNumber (encode d) (fireAtProof_T Lstar x nx d)
        w0 : Term
        w0 = LeastNumber.w1 ln
        zT : Term
        zT = ap1 (out_L Lstar) w0
        dNegOpen : Deriv (eqF (ap1 thmT w0) (codeFormula (Kgt Lstar zT)))
        dNegOpen = ruleTrans (dNeg_from_hitK Lstar (out_L Lstar) w0 (LeastNumber.isHit ln))
                             (negKgtCodeOf_correct_T Lstar zT nOut)
    in kr_clash_Sigma Lstar (enc (gLcode Lstar)) nTerm zT w0
         clN clOut dLenStar dEval dNegOpen
