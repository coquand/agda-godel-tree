{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KClashSigma -- Sigma-shape (Con-FREE) variant of T4.KClash.
--
-- Parallel to  T4.KClash  but stops the two-encoded_mp chain at  mp2
-- (which already gives  Deriv (thmT finalProof = codeFalse)) and
-- returns the witness as a  Sigma  (no  con  hypothesis consumed):
--
--   kr_clash_Sigma : (L gLcode nTerm zTerm w0 ...)
--                ->  Sigma Term (\ z -> Deriv (thmT z = codeFalse))
--
-- The "Right" Chaitin-Goedel I (CGI_core) wires this with a Discharge to
-- yield  Deriv (thmT w = code(K(x_) > L0))  ->  Sigma z.  thmT z = codeFalse .

module T4.KClashSigma where

open import T4.Base
open import T4.Code            using ( codeTerm ; codeFormula ; codeFalse )
open import T4.ThmT            using ( thmT )
open import T4.DefWit          using ( cImp ; dExFGen )
open import T4.ConInj          using ( cmp )
open import T4.Encode          using ( encode )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.KClash          using ( instSb ; kgtInstEq ; sbWrap )
open import T4.DefWit          using ( fAnd )
open import T4.CompressCanonical using ( andIntro )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.KFormula        using ( Kgt )
open import T4.KFormula        using ( szLeqApp )
open import T4.Code            using ( falseF )
open import T4.EvalUEval       using ( evalU )
open import T4.ProgParse       using ( parse )

open import BRA3.Dispatch        using ( Closed )
open import BRA3.Contrapositive  using ( axExFalso )

------------------------------------------------------------------------
-- Local Sigma (BRA3/T4 don't export one publicly used here).

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- SECTION 1.  Sigma-shape generic finish (parallel to KClash.clashFinish).
--
-- Stops at the second encoded_mp; no  con  consumed.

clashFinish_Sigma :
  (A : Formula) (cPos pNeg : Term) ->
  Deriv (eqF (ap1 thmT cPos) (codeFormula A)) ->
  Deriv (eqF (ap1 thmT pNeg) (codeFormula (neg A))) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
clashFinish_Sigma A cPos pNeg dPos dNeg =
  let cExF : Term
      cExF = encode (axExFalso A falseF)
      consImp : Term
      consImp = cImp (codeFormula (neg A)) codeFalse
      mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos)) consImp)
      mp1 = encoded_mp cExF cPos (codeFormula A) consImp (dExFGen A) dPos
      finalProof : Term
      finalProof = cmp (cmp cExF cPos) pNeg
      mp2 : Deriv (eqF (ap1 thmT finalProof) codeFalse)
      mp2 = encoded_mp (cmp cExF cPos) pNeg (codeFormula (neg A)) codeFalse mp1 dNeg
  in mkSigma finalProof mp2

------------------------------------------------------------------------
-- SECTION 2.  Sigma-shape  kr_clash :  same setup as  KClash.kr_clash
-- (the K-formula instantiation bridge), Con-FREE conclusion.

kr_clash_Sigma :
  (L gLcode nTerm zTerm w0 : Term) -> Closed nTerm -> Closed zTerm ->
  Deriv (eqF (szLeqApp L gLcode) (ap1 s O)) ->
  Deriv (eqF (ap2 evalU (ap1 parse gLcode) nTerm) (ap1 s zTerm)) ->
  Deriv (eqF (ap1 thmT w0) (codeFormula (Kgt L zTerm))) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
kr_clash_Sigma L gLcode nTerm zTerm w0 clN clZ dLenEq dEval dNegOpen =
  let
    pp : Formula
    pp = eqF (szLeqApp L gLcode) (ap1 s O)
    qq : Formula
    qq = eqF (ap2 evalU (ap1 parse gLcode) nTerm) (ap1 s zTerm)
    A : Formula
    A = fAnd pp qq
    cPos : Term
    cPos = encode (andIntro pp qq dLenEq dEval)
    dPos : Deriv (eqF (ap1 thmT cPos) (codeFormula A))
    dPos = thmT_complete_rec (andIntro pp qq dLenEq dEval)
    sb2 : Term
    sb2 = sbWrap 0 gLcode (sbWrap 1 nTerm w0)
    dNeg1 : Deriv (eqF (ap1 thmT (sbWrap 1 nTerm w0))
                       (codeFormula (substF 1 nTerm (Kgt L zTerm))))
    dNeg1 = instSb 1 nTerm w0 (Kgt L zTerm) dNegOpen
    dNeg2raw : Deriv (eqF (ap1 thmT sb2)
                          (codeFormula (substF 0 gLcode (substF 1 nTerm (Kgt L zTerm)))))
    dNeg2raw = instSb 0 gLcode (sbWrap 1 nTerm w0)
                      (substF 1 nTerm (Kgt L zTerm)) dNeg1
    dNeg2 : Deriv (eqF (ap1 thmT sb2) (codeFormula (neg A)))
    dNeg2 = eqSubst (\ F -> Deriv (eqF (ap1 thmT sb2) (codeFormula F)))
                    (kgtInstEq L gLcode nTerm zTerm clN clZ) dNeg2raw
  in clashFinish_Sigma A cPos sb2 dPos dNeg2
