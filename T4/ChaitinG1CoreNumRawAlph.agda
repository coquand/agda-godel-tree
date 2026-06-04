{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1CoreNumRawAlph -- Chaitin-Goedel-I, num-raw, at the
-- checkAlphN -guard shape.   Analog of  T4.ChaitinG1CoreNumRaw .
--
-- The SIZE residual  dLenStarDef  ( "the diagonal program fits  Lstar" ) is
-- replaced by the VALIDITY residual  checkFires  ( "the diagonal program is
-- a valid code of depth <= Lstar_meta" ) -- the direct analog of the carried
-- abstract size bound  ( see T4.dLenStarDef / lstarLe ).   Because
-- Lstar_meta  is an ABSTRACT module parameter ( the whole coverBridge /
-- internalCover / KdefAlph chain is parametric in it ), this fact cannot be
-- proven here ; it is the "L* large enough" assumption of the surprise-exam
-- argument, carried as a hypothesis.

open import T4.Base

module T4.ChaitinG1CoreNumRawAlph (Lstar_meta : Nat) where

open import T4.Code            using ( codeFalse ; codeFun1 )
open import T4.Tags            using ( tag_eq ; tag_ap1 ; tag_s )
open import T4.ThmT            using ( thmT )
open import T4.Num             using ( num ; num_at_O ; num_at_S )
open import T4.DefWit          using ( cEqTm )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.CheckAlphN      using ( checkAlphN )
open import T4.CgiClashAlph Lstar_meta
  using ( SomeProof ; mkProof ; cgiClashAlph ; cAp1f )
open import T4.ProgEnc         using ( enc )
open import T4.Thm12.Thm13     using ( codeFXeqY1 ; thm13_singulary )
open import T4.Thm12.All       using ( thm12 ; fst )

import T4.ChaitinG1DischargeKdefAlph
import T4.ChaitinG1ChainKdefAlph

open import BRA3.RuleInst2       using ( simSubstT )
open import T4.CloseW          using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )
open import BRA3.PairAlgebra   using ( Pair )

------------------------------------------------------------------------
-- Local Sigma.

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- The canonical short program NAME ( the diagonal loop  gLcodeDefAlph ).

gLnameAlph : Term
gLnameAlph = enc gLcodeDefAlph

------------------------------------------------------------------------
-- The closed validity-formula code that cgiClashAlph expects.

chkClosedAlph : Term
chkClosedAlph = cEqTm (cAp1f (checkAlphN Lstar_meta) (ap1 num gLnameAlph)) (cAp1f s O)

------------------------------------------------------------------------
-- Sigma1-completeness internalisation of the validity fact ( parallel to
-- T4.ChaitinG1CoreNumRaw.dSizeDef , at the validity atom ).

cValidProofAlph : Term
cValidProofAlph = ap1 (fst (thm12 (checkAlphN Lstar_meta))) gLnameAlph

dValidAlph :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) gLnameAlph) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT cValidProofAlph) chkClosedAlph)
dValidAlph checkFires =
  let bRHS : Deriv (eqF (ap1 num (ap1 s O)) (cAp1f s O))
      bRHS = ruleTrans (num_at_S O)
               (congR Pair (natCode tag_ap1) (congR Pair (natCode tag_s) num_at_O))

      bridge : Deriv (eqF (codeFXeqY1 (checkAlphN Lstar_meta) gLnameAlph (ap1 s O))
                          chkClosedAlph)
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp1f (checkAlphN Lstar_meta) (ap1 num gLnameAlph)) bRHS)
  in ruleTrans (thm13_singulary (checkAlphN Lstar_meta) gLnameAlph (ap1 s O) checkFires)
               bridge

------------------------------------------------------------------------
-- THE THEOREM.

CGI_core_num_raw_Alph :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) gLnameAlph) (ap1 s O)) ->     -- checkFires
  (w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeAlph x)) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
CGI_core_num_raw_Alph checkFires w x hyp =
  let hyp1 :
        Deriv (eqF (ap1 thmT (substT (suc zero) O w))
                    (ap1 KcodeAlph (substT (suc zero) O x)))
      hyp1 = ruleInst (suc zero) O hyp

      hyp2 :
        Deriv (eqF (ap1 thmT (closeW w)) (ap1 KcodeAlph (closeW x)))
      hyp2 = ruleInst zero O hyp1

      open T4.ChaitinG1DischargeKdefAlph.DischargeKdefAlph
             Lstar_meta (closeW w) (closeW x) hyp2
             (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( k_max ; x' ; dNeg_at_kmax )

      open T4.ChaitinG1ChainKdefAlph.ChainKdefAlph
             Lstar_meta (closeW w) (closeW x) hyp2
             (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( nTerm ; dEval_witness )

      proof : SomeProof
      proof = cgiClashAlph gLnameAlph nTerm x' k_max cValidProofAlph
                dNeg_at_kmax (dValidAlph checkFires) dEval_witness
  in mkSigma (SomeProof.pf proof) (SomeProof.isPf proof)
