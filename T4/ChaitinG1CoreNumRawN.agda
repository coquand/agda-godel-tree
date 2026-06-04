{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1CoreNumRawN -- the number-code re-pointing of
-- T4.ChaitinG1CoreNumRaw : Chaitin-Goedel-I at the honest p<N / runProgN guard.
-- Wires DischargeKdefN ( dNeg_at_kmax ) + ChainKdefN ( the diagonal's run ) +
-- cgiClashN ( the clash ) + the OBJECT size pin  sizePinN  ( internalised here
-- via thmT_complete_rec , NO  num Nthr  needed -- the binary-sub guard is fine ).
-- The diagonal's program is the NUMBER  progNum = natCode (diagRank gLN) ; its
-- run feeds  runProgN  via  ParseN.parseN_at_diag .

module T4.ChaitinG1CoreNumRawN where

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
open import T4.ParseN           using ( parseN ; diagRank ; parseN_at_diag )
open import T4.EvalUEval        using ( evalU )
open import T4.SbStep           using ( NumCode ; ncO ; ncAp1 )
open import T4.KGodel1BridgeDefN using ( NthrN ; boundDefN )
open import T4.dLenStarDefN     using ( sizePinN ; n0 ; gLN ; gLN_eq )
open import T4.CgiClashN        using ( cgiClashN ; leqAtomTN ; SomeProof )
open import T4.ProgParse        using ( parse ; InAlph )

open import T4.KdefN     NthrN using ( KcodeN )
open import T4.KdefRecogN NthrN using ( outKdefN )
open import T4.KdefDiagN  NthrN using ( gLcodeDefN ; inAlph_gLcodeDefN ; dRT_gLDefN )

import T4.ChaitinG1DischargeKdefN
import T4.ChaitinG1ChainKdefN

open import T4.CloseW using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )
open import T4.NatExp using ( fst )

open import BRA3.Church  using ( sub ; pi )
open import BRA3.RuleInst2 using ( simSubstT )

------------------------------------------------------------------------
-- Local Sigma.

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- NumCode of the threshold code  codeTerm NthrN  ( exp3/s/exp2 tower over
-- the numeral  natCode (fst boundDefN) ).

numCodeNat : (n : Nat) -> NumCode (codeTerm (natCode n))
numCodeNat zero    = ncO
numCodeNat (suc m) = ncAp1 s (codeTerm (natCode m)) (numCodeNat m)

numCodeNthrN : NumCode (codeTerm NthrN)
numCodeNthrN =
  ncAp1 exp3 _ (ncAp1 s _ (ncAp1 exp2 _ (numCodeNat (fst boundDefN))))

------------------------------------------------------------------------
-- The diagonal's number  progNum = natCode (diagRank gLN) .

progNum : Term
progNum = natCode n0          -- n0 = diagRank gLN  ( T4.dLenStarDefN )

------------------------------------------------------------------------
-- THE THEOREM.

CGI_core_num_raw_N :
  (w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeN x)) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
CGI_core_num_raw_N w x hyp =
  let hyp1 : Deriv (eqF (ap1 thmT (substT (suc zero) O w))
                        (ap1 KcodeN (substT (suc zero) O x)))
      hyp1 = ruleInst (suc zero) O hyp

      hyp2 : Deriv (eqF (ap1 thmT (closeW w)) (ap1 KcodeN (closeW x)))
      hyp2 = ruleInst zero O hyp1

      open T4.ChaitinG1DischargeKdefN.DischargeKdefN
             NthrN (closeW w) (closeW x) hyp2
             (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( k_max ; x' ; dNeg_at_kmax )

      open T4.ChaitinG1ChainKdefN.ChainKdefN
             NthrN (closeW w) (closeW x) hyp2
             (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( nTerm ; dEval_witness )

      -- the internalised size pin:  thmT cSizeN = leqAtomTN (num progNum) .
      cSizeN : Term
      cSizeN = encode sizePinN

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

      -- the run, re-pointed to  runProgN  on the program NUMBER.  gLN is SEALED,
      -- so InAlph / the diagonal run are bridged from  gLcodeDefN NthrN  via  gLN_eq
      -- ( eqSubst keeps  gLN  inert -- no normalisation of the thmT-embedding diagonal ).
      inAlph_gLN : InAlph gLN
      inAlph_gLN = eqSubst InAlph (eqSym gLN_eq) inAlph_gLcodeDefN

      evalU_gLN : Deriv (eqF (ap2 evalU gLN nTerm) (ap1 s x'))
      evalU_gLN =
        eqSubst (\ g -> Deriv (eqF (ap2 evalU g nTerm) (ap1 s x'))) (eqSym gLN_eq)
                (ruleTrans (ruleSym (congL evalU nTerm dRT_gLDefN)) dEval_witness)

      run : Deriv (eqF (ap2 evalU (ap1 parseN progNum) nTerm) (ap1 s x'))
      run = ruleTrans (congL evalU nTerm (parseN_at_diag gLN inAlph_gLN)) evalU_gLN

      proof : SomeProof
      proof = cgiClashN NthrN numCodeNthrN progNum nTerm x' k_max cSizeN
                dNeg_at_kmax dSizeN run
  in mkSigma (SomeProof.pf proof) (SomeProof.isPf proof)
