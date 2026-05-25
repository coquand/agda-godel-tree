{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KClash -- Phase E3 (CHAITIN-G1-STANDARD-DIRECTION.md SS6): the CLASH.
-- Given the standard-route legs
--   dLen  :  szLeq(⌜g_L⌝,L) = 1                       (the description fits L)
--   dEval :  evalU(⌜g_L⌝, num n0) = s z0              (the machine halts -- evalU_correct/search)
--   dNeg  :  T ⊢ Kgt L z0  (= thmT w0 = codeFormula (Kgt L (num z0)))   (the search found a proof)
-- and Con, the clash derives  falseF :
--   * dPos := T ⊢ (szLeq=1 ∧ evalU=s z0)   built by andIntro + thmT_complete_rec (Σ₁-completeness);
--   * the OPEN dNeg is instantiated at  e:=⌜g_L⌝, n:=num n0  by two  thmT_at_sb  + sbfEq_codeFormula
--     (the one new wrinkle vs the closed-atom route) -> thmT(sb2) = codeFormula (neg A);
--   * the shipped ex-falso spine (dExFGen + two encoded_mp) gives  thmT f = codeFalse, Con-free;
--   * Con (ConSchema) refutes it ⟹ falseF.
--
-- Parametric in the search (takes dLen/dEval/dNeg as hypotheses); the search
-- wiring that DISCHARGES them (g_L, enum, the μ-loop producing w0, dEval by
-- running g_L) is E3.2.  This is the chaitinBarrierFinishComp pattern, re-pointed
-- to the open evalU K-formula.

module BRA4.KClash where

open import BRA4.Base
open import BRA4.Tags using ( tag_sb )
open import BRA4.Code using ( codeTerm ; codeFormula ; codeFalse ; falseF )
open import BRA4.ThmT using ( thmT )
open import BRA4.Encode using ( encode )
open import BRA4.ThmTCompleteRec using ( thmT_complete_rec )
open import BRA4.ThmTComplete using ( sbfEq_codeFormula )
open import BRA4.SbF using ( sbf )
open import BRA4.ThmTAtSb using ( thmT_at_sb )
open import BRA4.DefWit using ( fAnd ; cImp ; dExFGen )
open import BRA4.ConInj using ( ConSchema ; cmp )
open import BRA4.CompressCanonical using ( andIntro )
open import BRA4.Thm12.EncodedMp using ( encoded_mp )
open import BRA4.KFormula using ( szLeqApp ; Kgt )
open import BRA4.EvalUEval using ( evalU )

open import BRA3.Church using ( pi )
open import BRA3.Contrapositive using ( axExFalso )
open import BRA3.Dispatch using ( Closed ; closedAt )

------------------------------------------------------------------------
-- SECTION 1.  The open->closed instantiation step (thmT_at_sb + commute).
--
--   sbWrap k t cPf  -- the proof code of  ruleInst k t  applied to proof  cPf .
--   instSb : from  thmT cPf = codeFormula F  derive
--            thmT (sbWrap k t cPf) = codeFormula (substF k t F) .

sbWrap : Nat -> Term -> Term -> Term
sbWrap k t cPf =
  ap2 pi (natCode tag_sb) (ap2 pi (ap2 Pair (natCode k) (codeTerm t)) cPf)

instSb :
  (k : Nat) (t : Term) (cPf : Term) (F : Formula) ->
  Deriv (eqF (ap1 thmT cPf) (codeFormula F)) ->
  Deriv (eqF (ap1 thmT (sbWrap k t cPf)) (codeFormula (substF k t F)))
instSb k t cPf F dF =
  let spec : Term
      spec = ap2 Pair (natCode k) (codeTerm t)
  in ruleTrans (thmT_at_sb spec cPf)
       (ruleTrans (congR sbf spec dF) (sbfEq_codeFormula k t F))

------------------------------------------------------------------------
-- SECTION 2.  The generic ex-falso finish (the chaitinBarrierFinishComp
-- pattern, generic in the clashing formula  A ).

clashFinish :
  Deriv ConSchema -> (A : Formula) (cPos pNeg : Term) ->
  Deriv (eqF (ap1 thmT cPos) (codeFormula A)) ->
  Deriv (eqF (ap1 thmT pNeg) (codeFormula (neg A))) ->
  Deriv falseF
clashFinish con A cPos pNeg dPos dNeg =
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
      con_inst : Deriv (neg (eqF (ap1 thmT finalProof) codeFalse))
      con_inst = ruleInst zero finalProof con
  in mp (mp (axExFalso (eqF (ap1 thmT finalProof) codeFalse) falseF) mp2) con_inst

------------------------------------------------------------------------
-- SECTION 3.  The substitution bridge:  instantiating the open Kgt at
--   e := ⌜g_L⌝ (var 0), n := nTerm (var 1)  produces  neg (the closed
-- conjunction) .  The program/runtime slots (var 0, var 1) reduce
-- definitionally; the subject  zTerm  and fuel  nTerm  are Closed, so their
-- substitutions are no-ops (closedAt).

kgtInstEq :
  (L gLcode nTerm zTerm : Term) -> Closed nTerm -> Closed zTerm ->
  Eq (substF 0 gLcode (substF 1 nTerm (Kgt L zTerm)))
     (neg (fAnd (eqF (szLeqApp L gLcode) (ap1 s O))
                (eqF (ap2 evalU gLcode nTerm) (ap1 s zTerm))))
kgtInstEq L gLcode nTerm zTerm clN clZ =
  let eN : Eq (substT 0 gLcode nTerm) nTerm
      eN = closedAt clN 0 gLcode
      eZ : Eq (substT 0 gLcode (substT 1 nTerm zTerm)) zTerm
      eZ = eqTrans (eqCong (substT 0 gLcode) (closedAt clZ 1 nTerm))
                   (closedAt clZ 0 gLcode)
      qqBridge :
        Eq (eqF (ap2 evalU gLcode (substT 0 gLcode nTerm))
                (ap1 s (substT 0 gLcode (substT 1 nTerm zTerm))))
           (eqF (ap2 evalU gLcode nTerm) (ap1 s zTerm))
      qqBridge =
        eqTrans
          (eqCong (\ t -> eqF (ap2 evalU gLcode t)
                              (ap1 s (substT 0 gLcode (substT 1 nTerm zTerm)))) eN)
          (eqCong (\ t -> eqF (ap2 evalU gLcode nTerm) (ap1 s t)) eZ)
  in eqCong (\ q -> neg (neg (imp (eqF (szLeqApp L gLcode) (ap1 s O)) (neg q))))
            qqBridge

------------------------------------------------------------------------
-- SECTION 4.  The clash.

kr_clash :
  Deriv ConSchema ->
  (L gLcode nTerm zTerm w0 : Term) -> Closed nTerm -> Closed zTerm ->
  Deriv (eqF (szLeqApp L gLcode) (ap1 s O)) ->                          -- dLen (szLeq=1)
  Deriv (eqF (ap2 evalU gLcode nTerm) (ap1 s zTerm)) ->                 -- dEval (halts)
  Deriv (eqF (ap1 thmT w0) (codeFormula (Kgt L zTerm))) ->              -- dNeg (open)
  Deriv falseF
kr_clash con L gLcode nTerm zTerm w0 clN clZ dLenEq dEval dNegOpen =
  let pp : Formula
      pp = eqF (szLeqApp L gLcode) (ap1 s O)
      qq : Formula
      qq = eqF (ap2 evalU gLcode nTerm) (ap1 s zTerm)
      A : Formula
      A = fAnd pp qq
      cPos : Term
      cPos = encode (andIntro pp qq dLenEq dEval)
      dPos : Deriv (eqF (ap1 thmT cPos) (codeFormula A))
      dPos = thmT_complete_rec (andIntro pp qq dLenEq dEval)
      -- instantiate the open dNeg at  n := nTerm (var 1)  then  e := ⌜g_L⌝ (var 0) .
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
  in clashFinish con A cPos sb2 dPos dNeg2
