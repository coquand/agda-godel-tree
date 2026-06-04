{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashAlph -- the integrated single-conjunct clash at the
-- checkAlphN -guard shape.   Analog of  T4.CgiClash , re-pointed from the
-- SIZE atom  szLeqFun L  to the VALIDITY atom  checkAlphN Lstar_meta , and
-- from  Kcode L  to  KcodeAlph .   The positive leg ( D / dPos / runProg /
-- thm12_Fun2 runProg ) is guard-INDEPENDENT and reused verbatim.

open import T4.Base

module T4.CgiClashAlph (Lstar_meta : Nat) where

open import T4.Tags using
  ( tag_sb ; tag_var ; tag_ap1 ; tag_ap2 ; tag_eq ; tag_neg ; tag_imp ; tag_s )
open import T4.Code using ( codeFun1 ; codeFun2 ; codeFalse )
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
open import T4.CheckAlphN using ( checkAlphN )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.Kdef using ( runProg )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph ; KcodeAlph_eval )
open import T4.CgiDPos using ( D ; dPos )
open import T4.Thm12.All using ( thm12_Fun2 ; fst )

open import BRA3.Church using ( pi )

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
-- The clash, at program code  gL , halt fuel  n0 , subject  x' .

module _ (gL n0 x' : Term) where

  -- the VALIDITY atom code:  checkAlphN Lstar_meta (prog) = s O .
  chkAtomT : Term -> Term
  chkAtomT prog = cEqTm (cAp1f (checkAlphN Lstar_meta) prog) (cAp1f s O)

  -- definable code:  runProg(prog, fuel) = s x'  (subject hole = num x').
  defEqT : Term -> Term -> Term
  defEqT prog fuel = cEqTm (cAp2f runProg prog fuel) (cAp1f s (ap1 num x'))

  -- the open K-code = cImp chkAtom (cNeg definable).
  KT : Term -> Term -> Term
  KT prog fuel = cImp (chkAtomT prog) (cNeg (defEqT prog fuel))

  ----------------------------------------------------------------
  -- The generic single substitution pass over  KT .

  passK :
    (k : Nat) (S prog prog' fuel fuel' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) prog) prog') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) fuel) fuel') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (KT prog fuel))
                (KT prog' fuel'))
  passK k S prog prog' fuel fuel' eProg eFuel =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        e_sO : Deriv (eqF (ap2 sbt spec (cAp1f s O)) (cAp1f s O))
        e_sO = sbt_inert_NumCode (cAp1f s O) (ncAp1 s O ncO) k S

        e_sHole : Deriv (eqF (ap2 sbt spec (cAp1f s (ap1 num x')))
                              (cAp1f s (ap1 num x')))
        e_sHole = sbt_inert_NumCode (cAp1f s (ap1 num x'))
                    (ncAp1 s (ap1 num x') (ncNum x')) k S

        e_chkLHS : Deriv (eqF (ap2 sbt spec (cAp1f (checkAlphN Lstar_meta) prog))
                               (cAp1f (checkAlphN Lstar_meta) prog'))
        e_chkLHS = sbt_step_ap1 k S (checkAlphN Lstar_meta) prog prog' eProg

        e_chk : Deriv (eqF (ap2 sbf spec (chkAtomT prog)) (chkAtomT prog'))
        e_chk = sbf_step_atomic k S
                  (cAp1f (checkAlphN Lstar_meta) prog) (cAp1f s O)
                  (cAp1f (checkAlphN Lstar_meta) prog') (cAp1f s O) e_chkLHS e_sO

        e_defLHS : Deriv (eqF (ap2 sbt spec (cAp2f runProg prog fuel))
                               (cAp2f runProg prog' fuel'))
        e_defLHS = sbt_step_ap2 k S runProg prog fuel prog' fuel' eProg eFuel

        e_def : Deriv (eqF (ap2 sbf spec (defEqT prog fuel)) (defEqT prog' fuel'))
        e_def = sbf_step_atomic k S
                  (cAp2f runProg prog fuel) (cAp1f s (ap1 num x'))
                  (cAp2f runProg prog' fuel') (cAp1f s (ap1 num x'))
                  e_defLHS e_sHole

        e_negdef : Deriv (eqF (ap2 sbf spec (cNeg (defEqT prog fuel)))
                               (cNeg (defEqT prog' fuel')))
        e_negdef = sbf_step_neg k S (defEqT prog fuel) (defEqT prog' fuel') e_def
    in sbf_step_imp k S (chkAtomT prog) (cNeg (defEqT prog fuel))
         (chkAtomT prog') (cNeg (defEqT prog' fuel')) e_chk e_negdef

------------------------------------------------------------------------
-- The integrated clash.

cgiClashAlph :
  (gL n0 x' w0 cValid : Term) ->
  Deriv (eqF (ap1 thmT w0) (ap1 KcodeAlph x')) ->                       -- dNeg
  Deriv (eqF (ap1 thmT cValid) (chkAtomT gL n0 x' (ap1 num gL))) ->     -- dValid
  Deriv (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x')) ->                -- run
  SomeProof
cgiClashAlph gL n0 x' w0 cValid dNeg dValid run =
  let S0 : Term
      S0 = ap1 num gL
      S1 : Term
      S1 = ap1 num n0
      spec0 : Term
      spec0 = ap2 Pair (natCode zero) S0
      spec1 : Term
      spec1 = ap2 Pair (natCode (suc zero)) S1

      KOpen : Term
      KOpen = KT gL n0 x' (cVarc zero) (cVarc (suc zero))
      KMid : Term
      KMid  = KT gL n0 x' (cVarc zero) (ap1 num n0)
      KClosed : Term
      KClosed = KT gL n0 x' (ap1 num gL) (ap1 num n0)

      innerEq : Deriv (eqF (ap2 sbf spec1 KOpen) KMid)
      innerEq =
        passK gL n0 x' (suc zero) S1
          (cVarc zero) (cVarc zero) (cVarc (suc zero)) (ap1 num n0)
          (sbt_at_var_nomatch (suc zero) zero S1 refl)
          (sbt_at_var_match (suc zero) S1)

      outerEq : Deriv (eqF (ap2 sbf spec0 KMid) KClosed)
      outerEq =
        passK gL n0 x' zero S0
          (cVarc zero) (ap1 num gL) (ap1 num n0) (ap1 num n0)
          (sbt_at_var_match zero S0)
          (sbt_num_inert zero S0 n0)

      substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KOpen)) KClosed)
      substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

      dNegOpen : Deriv (eqF (ap1 thmT w0) KOpen)
      dNegOpen = ruleTrans dNeg (KcodeAlph_eval x')

      innerWrap : Term
      innerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)
      outerWrap : Term
      outerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

      dInner : Deriv (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen))
      dInner = ruleTrans (thmT_at_sb spec1 w0) (congR sbf spec1 dNegOpen)

      dInst : Deriv (eqF (ap1 thmT outerWrap) KClosed)
      dInst = ruleTrans (thmT_at_sb spec0 innerWrap)
                (ruleTrans (congR sbf spec0 dInner) substBoth)

      -- KClosed = cImp (chkAtom (num gL)) (cNeg (D gL n0 x')); strip with dValid.
      dNegFinal : Deriv (eqF (ap1 thmT (cmp outerWrap cValid)) (cNeg (D gL n0 x')))
      dNegFinal =
        encoded_mp outerWrap cValid (chkAtomT gL n0 x' (ap1 num gL))
          (cNeg (D gL n0 x')) dInst dValid

      cPos : Term
      cPos = ap2 (fst (thm12_Fun2 runProg)) gL n0

      dPosD : Deriv (eqF (ap1 thmT cPos) (D gL n0 x'))
      dPosD = dPos gL n0 x' run

      dExF : Deriv (eqF (ap1 thmT (exfProof (D gL n0 x') codeFalse))
                         (cImp (D gL n0 x') (cImp (cNeg (D gL n0 x')) codeFalse)))
      dExF = encoded_exfalso (D gL n0 x') codeFalse

      final : Deriv (eqF (ap1 thmT
                           (cmp (cmp (exfProof (D gL n0 x') codeFalse) cPos)
                                (cmp outerWrap cValid)))
                          codeFalse)
      final = chaitin_G1_assembly (D gL n0 x') cPos (exfProof (D gL n0 x') codeFalse)
                (cmp outerWrap cValid) dPosD dNegFinal dExF
  in mkProof
       (cmp (cmp (exfProof (D gL n0 x') codeFalse) cPos) (cmp outerWrap cValid))
       final
