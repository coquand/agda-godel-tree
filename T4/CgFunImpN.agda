{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFunImpN -- the number-code re-pointing of T4.CgFunImp : the closure-
-- witnessed Carneiro-lifted CGI-self assembly  cgFalseImp_generalN .  Wires
-- DischargeKdefImpN + ChainKdefImpN + imp_cgiClashN at the canonical threshold
-- NthrN, with the size-pin internalisation ( thmT_complete_rec ) and the
-- runProgN run-bridge ( ParseN.parseN_at_diag ) -- the same bridges as the
-- non-imp CGI_core_num_raw_N, imp-lifted.

module T4.CgFunImpN where

open import T4.Base
open import T4.Code             using ( codeFalse ; codeFun2 ; codeTerm ; codeFormula )
open import T4.Tags             using ( tag_eq ; tag_ap2 )
open import T4.ThmT             using ( thmT )
open import T4.Num              using ( num )
open import T4.Encode           using ( encode )
open import T4.ThmTCompleteRec  using ( thmT_complete_rec )
open import T4.IsNat            using ( num_eq_code )
open import T4.NumContract      using ( isNat_natCode )
open import T4.Exp              using ( exp2 )
open import T4.Exp3             using ( exp3 )
open import T4.ProgEnc          using ( enc )
open import T4.ProgParse        using ( parse ; InAlph )
open import T4.ParseN           using ( parseN ; runProgN ; diagRank ; parseN_at_diag )
open import T4.EvalUEval        using ( evalU )
open import T4.SbStep           using ( NumCode ; ncO ; ncAp1 )
open import T4.KGodel1BridgeDefN using ( NthrN ; boundDefN )
open import T4.dLenStarDefN     using ( sizePinN ; n0 ; gLN ; gLN_eq )
open import T4.CgiClashN        using ( leqAtomTN ; cAp2f )
open import T4.CgiClashImpN     using ( imp_cgiClashN )
open import T4.CgiClashImp      using ( ImpSomeProof )

open import T4.StepU2          using ( step ; cfgEV ; cfgRT )
open import T4.EvalU           using ( mcodeMu ; mcode1 )
open import T4.KdefN     NthrN using ( KcodeN )
open import T4.KdefRecogN NthrN using ( outKdefN ; hitKdefN ; hitKdefN_le_one )
open import T4.KdefDiagN  NthrN using ( gLcodeDefN ; predFlipDefN
                                       ; inAlph_gLcodeDefN ; dRT_gLDefN )

import T4.ChaitinG1DischargeKdefImpN
import T4.ChaitinG1ChainKdefImpN
import T4.FirstHit

open T4.FirstHit.Search (hitKdefN outKdefN) (hitKdefN_le_one outKdefN)
  using ( gRec )

open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )
open import T4.NatExp using ( fst )

open import BRA3.Church          using ( pi ; sigma ; sub )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- w-independent size / NumCode pieces ( canonical threshold ).

numCodeNat : (n : Nat) -> NumCode (codeTerm (natCode n))
numCodeNat zero    = ncO
numCodeNat (suc m) = ncAp1 s (codeTerm (natCode m)) (numCodeNat m)

numCodeNthrN : NumCode (codeTerm NthrN)
numCodeNthrN =
  ncAp1 exp3 _ (ncAp1 s _ (ncAp1 exp2 _ (numCodeNat (fst boundDefN))))

progNum : Term
progNum = natCode n0

cSizeN : Term
cSizeN = encode sizePinN

------------------------------------------------------------------------
-- cgFalseImp_generalN .

cgFalseImp_generalN :
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substT zero a w) w) ->
  ((a : Term) -> Eq (substT (suc zero) a w) w) ->
  ((a b : Term) -> Eq (simSubstT zero a (suc zero) b w) w) ->
  Deriv (imp Rf (eqF (ap1 thmT w) (ap1 KcodeN (ap1 outKdefN w)))) ->
  (fuelMu_fun : Fun2) ->
  ((x_outer K0 : Term) ->
     Deriv (imp Rf
            (eqF (ap2 (iter step)
                       (cfgEV (mcodeMu (mcode1 predFlipDefN)) x_outer K0)
                       (ap2 sigma (ap1 s O)
                                   (ap2 fuelMu_fun
                                        (ap2 gRec O (ap1 s w))
                                        (ap2 gRec O (ap1 s w)))))
                  (cfgRT (ap2 gRec O (ap1 s w)) K0)))) ->
  ImpSomeProof Rf
cgFalseImp_generalN Rf w sub0_w sub1_w sim_w hyp_imp fuelMu_fun imp_runs_mu =
  let x_subj : Term
      x_subj = ap1 outKdefN w

      open T4.ChaitinG1DischargeKdefImpN.DischargeKdefImpN
             NthrN Rf w x_subj hyp_imp sub0_w sub1_w sim_w
        using ( k_max ; x' ; imp_dNeg_at_kmax )

      open T4.ChaitinG1ChainKdefImpN.ChainKdefImpN
             NthrN Rf w x_subj hyp_imp sub0_w sub1_w sim_w
        using ( module Chain )

      open Chain fuelMu_fun imp_runs_mu
        using ( nTerm ; imp_dEval_witness )

      -- the internalised size pin:  thmT cSizeN = leqAtomTN (num progNum) .
      eaProg : Deriv (eqF (codeTerm progNum) (ap1 num progNum))
      eaProg = ruleSym (num_eq_code progNum (isNat_natCode n0))

      bridgeSize :
        Deriv (eqF (codeFormula (eqF (ap2 sub progNum NthrN) O))
                   (leqAtomTN NthrN numCodeNthrN progNum nTerm x' (ap1 num progNum)))
      bridgeSize =
        congR Pair (natCode tag_eq)
          (congL Pair (codeTerm O)
            (congR Pair (natCode tag_ap2)
              (congR Pair (codeFun2 sub)
                (congL Pair (codeTerm NthrN) eaProg))))

      dSizeN :
        Deriv (eqF (ap1 thmT cSizeN)
                   (leqAtomTN NthrN numCodeNthrN progNum nTerm x' (ap1 num progNum)))
      dSizeN = ruleTrans (thmT_complete_rec sizePinN) bridgeSize

      -- the imp-lifted run, re-pointed to runProgN on the program NUMBER.
      inAlph_gLN : InAlph gLN
      inAlph_gLN = eqSubst InAlph (eqSym gLN_eq) inAlph_gLcodeDefN

      parseN_prog : Deriv (eqF (ap1 parseN progNum) (ap1 parse (enc gLcodeDefN)))
      parseN_prog =
        ruleTrans (parseN_at_diag gLN inAlph_gLN)
                  (eqSubst (\ g -> Deriv (eqF g (ap1 parse (enc gLcodeDefN))))
                           (eqSym gLN_eq) (ruleSym dRT_gLDefN))

      run_bridge :
        Deriv (eqF (ap2 evalU (ap1 parseN progNum) nTerm)
                   (ap2 evalU (ap1 parse (enc gLcodeDefN)) nTerm))
      run_bridge = congL evalU nTerm parseN_prog

      imp_run :
        Deriv (imp Rf (eqF (ap2 evalU (ap1 parseN progNum) nTerm) (ap1 s x')))
      imp_run =
        impEqTrans (ap2 evalU (ap1 parseN progNum) nTerm)
                   (ap2 evalU (ap1 parse (enc gLcodeDefN)) nTerm)
                   (ap1 s x') (impLift {Rf} run_bridge) imp_dEval_witness

  in imp_cgiClashN Rf NthrN numCodeNthrN progNum nTerm x' k_max cSizeN
       imp_dNeg_at_kmax dSizeN imp_run
