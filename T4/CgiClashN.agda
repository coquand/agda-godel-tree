{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashN -- the number-code re-pointing of T4.CgiClash : the INTEGRATED
-- clash at the honest p<N / runProgN K-formula.   Mirrors CgiClash, with the
-- guard atom reshaped from the unary  cAp1f (szLeqFun L) prog  to the binary
--   leqAtomTN prog = cEqTm (cAp2f sub prog (codeTerm Nthr)) (codeTerm O)
-- ( leq prog N = sub prog N = O ;  codeTerm Nthr inert via a NumCode witness ),
-- and  runProg -> runProgN  ( DN / dPosN , T4.CgiDPosN ).
--
-- PERF NOTE: this file type-checks in ~25-55s ( the same shared encoded-clash
-- machinery cost as the original T4.CgiClash -- the conversion checker re-walks
-- the large nested-Pair K-formula skeletons at every sbf/sbt/encoded junction ).
-- Sealing the builders / splitting into files did NOT help ( the cost is emergent
-- from co-location, not localisable ); kept simple.  The math is complete.

module T4.CgiClashN where

open import T4.Base
open import T4.Tags using
  ( tag_sb ; tag_var ; tag_ap1 ; tag_ap2 ; tag_eq ; tag_neg ; tag_imp ; tag_s )
open import T4.Code using ( codeFun1 ; codeFun2 ; codeTerm ; codeFalse )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt ; sbt_at_O )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.SbStep using
  ( sbf_step_imp ; sbf_step_atomic ; sbf_step_neg ; sbt_step_ap1 ; sbt_step_ap2
  ; NumCode ; ncO ; ncNum ; ncAp1 ; sbt_inert_NumCode )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.ChaitinG1 using ( chaitin_G1_assembly )
open import T4.EvalUEval using ( evalU )
open import T4.ParseN using ( parseN ; runProgN )
open import T4.CgiDPosN using ( DN ; dPosN )
open import T4.Thm12.All using ( thm12_Fun2 ; fst )

import T4.KdefN

open import BRA3.Church using ( pi ; sub )

------------------------------------------------------------------------
-- Local codeTerm-shape constructors.

cAp1f : Fun1 -> Term -> Term
cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

cAp2f : Fun2 -> Term -> Term -> Term
cAp2f g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

cVarc : Nat -> Term
cVarc k = ap2 Pair (natCode tag_var) (natCode k)

record SomeProof : Set where
  constructor mkProof
  field
    pf   : Term
    isPf : Deriv (eqF (ap1 thmT pf) codeFalse)

------------------------------------------------------------------------
-- The clash, at fixed threshold  Nthr  ( + its NumCode inertness ),
-- program code  gL , halt fuel  n0 , subject  x' .

module _ (Nthr : Term) (ncN : NumCode (codeTerm Nthr)) (gL n0 x' : Term) where

  -- the guard atom code:  leq prog Nthr = ( sub prog Nthr = O ) .
  leqAtomTN : Term -> Term
  leqAtomTN prog = cEqTm (cAp2f sub prog (codeTerm Nthr)) (codeTerm O)

  -- definable code:  runProgN(prog, fuel) = s x' .
  defEqTN : Term -> Term -> Term
  defEqTN prog fuel = cEqTm (cAp2f runProgN prog fuel) (cAp1f s (ap1 num x'))

  KTN : Term -> Term -> Term
  KTN prog fuel = cImp (leqAtomTN prog) (cNeg (defEqTN prog fuel))

  ----------------------------------------------------------------
  -- The generic single substitution pass over  KTN .

  passKN :
    (k : Nat) (S prog prog' fuel fuel' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) prog) prog') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) fuel) fuel') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (KTN prog fuel))
                (KTN prog' fuel'))
  passKN k S prog prog' fuel fuel' eProg eFuel =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        e_NC : Deriv (eqF (ap2 sbt spec (codeTerm Nthr)) (codeTerm Nthr))
        e_NC = sbt_inert_NumCode (codeTerm Nthr) ncN k S

        e_Oc : Deriv (eqF (ap2 sbt spec (codeTerm O)) (codeTerm O))
        e_Oc = sbt_at_O spec

        e_sHole : Deriv (eqF (ap2 sbt spec (cAp1f s (ap1 num x')))
                              (cAp1f s (ap1 num x')))
        e_sHole = sbt_inert_NumCode (cAp1f s (ap1 num x'))
                    (ncAp1 s (ap1 num x') (ncNum x')) k S

        e_guardLHS : Deriv (eqF (ap2 sbt spec (cAp2f sub prog (codeTerm Nthr)))
                                 (cAp2f sub prog' (codeTerm Nthr)))
        e_guardLHS = sbt_step_ap2 k S sub prog (codeTerm Nthr) prog' (codeTerm Nthr)
                       eProg e_NC

        e_guard : Deriv (eqF (ap2 sbf spec (leqAtomTN prog)) (leqAtomTN prog'))
        e_guard = sbf_step_atomic k S
                    (cAp2f sub prog (codeTerm Nthr)) (codeTerm O)
                    (cAp2f sub prog' (codeTerm Nthr)) (codeTerm O)
                    e_guardLHS e_Oc

        e_defLHS : Deriv (eqF (ap2 sbt spec (cAp2f runProgN prog fuel))
                               (cAp2f runProgN prog' fuel'))
        e_defLHS = sbt_step_ap2 k S runProgN prog fuel prog' fuel' eProg eFuel

        e_def : Deriv (eqF (ap2 sbf spec (defEqTN prog fuel)) (defEqTN prog' fuel'))
        e_def = sbf_step_atomic k S
                  (cAp2f runProgN prog fuel) (cAp1f s (ap1 num x'))
                  (cAp2f runProgN prog' fuel') (cAp1f s (ap1 num x'))
                  e_defLHS e_sHole

        e_negdef : Deriv (eqF (ap2 sbf spec (cNeg (defEqTN prog fuel)))
                               (cNeg (defEqTN prog' fuel')))
        e_negdef = sbf_step_neg k S (defEqTN prog fuel) (defEqTN prog' fuel') e_def
    in sbf_step_imp k S (leqAtomTN prog) (cNeg (defEqTN prog fuel))
         (leqAtomTN prog') (cNeg (defEqTN prog' fuel')) e_guard e_negdef

------------------------------------------------------------------------
-- The integrated clash.

cgiClashN :
  (Nthr : Term) (ncN : NumCode (codeTerm Nthr)) (gL n0 x' w0 cSize : Term) ->
  Deriv (eqF (ap1 thmT w0) (ap1 (T4.KdefN.KcodeN Nthr) x')) ->            -- dNeg
  Deriv (eqF (ap1 thmT cSize) (leqAtomTN Nthr ncN gL n0 x' (ap1 num gL))) ->  -- dSize
  Deriv (eqF (ap2 evalU (ap1 parseN gL) n0) (ap1 s x')) ->                -- run
  SomeProof
cgiClashN Nthr ncN gL n0 x' w0 cSize dNeg dSize run =
  let S0 : Term
      S0 = ap1 num gL
      S1 : Term
      S1 = ap1 num n0
      spec0 : Term
      spec0 = ap2 Pair (natCode zero) S0
      spec1 : Term
      spec1 = ap2 Pair (natCode (suc zero)) S1

      KOpen : Term
      KOpen = KTN Nthr ncN gL n0 x' (cVarc zero) (cVarc (suc zero))
      KMid : Term
      KMid  = KTN Nthr ncN gL n0 x' (cVarc zero) (ap1 num n0)
      KClosed : Term
      KClosed = KTN Nthr ncN gL n0 x' (ap1 num gL) (ap1 num n0)

      innerEq : Deriv (eqF (ap2 sbf spec1 KOpen) KMid)
      innerEq =
        passKN Nthr ncN gL n0 x' (suc zero) S1
          (cVarc zero) (cVarc zero) (cVarc (suc zero)) (ap1 num n0)
          (sbt_at_var_nomatch (suc zero) zero S1 refl)
          (sbt_at_var_match (suc zero) S1)

      outerEq : Deriv (eqF (ap2 sbf spec0 KMid) KClosed)
      outerEq =
        passKN Nthr ncN gL n0 x' zero S0
          (cVarc zero) (ap1 num gL) (ap1 num n0) (ap1 num n0)
          (sbt_at_var_match zero S0)
          (sbt_num_inert zero S0 n0)

      substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KOpen)) KClosed)
      substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

      dNegOpen : Deriv (eqF (ap1 thmT w0) KOpen)
      dNegOpen = ruleTrans dNeg (T4.KdefN.KcodeN_eval Nthr x')

      innerWrap : Term
      innerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)
      outerWrap : Term
      outerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

      dInner : Deriv (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen))
      dInner = ruleTrans (thmT_at_sb spec1 w0) (congR sbf spec1 dNegOpen)

      dInst : Deriv (eqF (ap1 thmT outerWrap) KClosed)
      dInst = ruleTrans (thmT_at_sb spec0 innerWrap)
                (ruleTrans (congR sbf spec0 dInner) substBoth)

      dNegFinal : Deriv (eqF (ap1 thmT (cmp outerWrap cSize)) (cNeg (DN gL n0 x')))
      dNegFinal =
        encoded_mp outerWrap cSize (leqAtomTN Nthr ncN gL n0 x' (ap1 num gL))
          (cNeg (DN gL n0 x')) dInst dSize

      cPos : Term
      cPos = ap2 (fst (thm12_Fun2 runProgN)) gL n0

      dPosD : Deriv (eqF (ap1 thmT cPos) (DN gL n0 x'))
      dPosD = dPosN gL n0 x' run

      dExF : Deriv (eqF (ap1 thmT (exfProof (DN gL n0 x') codeFalse))
                         (cImp (DN gL n0 x') (cImp (cNeg (DN gL n0 x')) codeFalse)))
      dExF = encoded_exfalso (DN gL n0 x') codeFalse

      final : Deriv (eqF (ap1 thmT
                           (cmp (cmp (exfProof (DN gL n0 x') codeFalse) cPos)
                                (cmp outerWrap cSize)))
                          codeFalse)
      final = chaitin_G1_assembly (DN gL n0 x') cPos (exfProof (DN gL n0 x') codeFalse)
                (cmp outerWrap cSize) dPosD dNegFinal dExF
  in mkProof
       (cmp (cmp (exfProof (DN gL n0 x') codeFalse) cPos) (cmp outerWrap cSize))
       final
