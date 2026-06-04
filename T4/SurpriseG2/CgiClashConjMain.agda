{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.CgiClashConjMain -- the INTEGRATED clash for the
-- conjunction-shape K-formula  KdefConj M enum subject  ( per
-- T4/NEXT-SESSION-ENUMRUNPROG-REFACTOR.md ) .
--
-- Split off from  T4.SurpriseG2.CgiClashConj  for typecheck-
-- isolation reasons :   keeping  cgiClashConj  in the SAME file as
-- the heavy top-level lemmas  dPosConjAt , dAnteConjAt , passKAt
-- caused the unification of  defEqTAt (enumRunProgOf enum) ...
-- with the substituted KcodeConj skeleton to blow past 60s ; with
-- the split , typecheck stays  < 2s  warm  ( see  CgiClashConj.agda
-- header note ) .   Per memory/feedback_slow_typecheck_means_abstract_constants .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- `cgiClashConj`  --  given
--
--   * `M` , `enum`  --  the surprise-exam meta data ;
--   * `kStar` , `kStarBound : NatLe kStar M`  --  the META index of
--     the diagonal program in the enumeration ;
--   * `gLname` , `nTerm` , `x'` , `w0` : Term ;
--   * `dNeg`        : `thmT w0 = KcodeConj M enum x'` ;
--   * `runEnumForm` : `enumRunProgOf enum (natCode kStar) nTerm = s x'` ;
--
-- builds  SomeProof  =  (witness , Deriv (thmT witness = codeFalse))
-- by composing the four stages :
--   ( i )   substitution :  thmT_at_sb  twice + passKAt twice ;
--   ( ii )  leq-antecedent strip :  encoded_mp + dAnteConjAt ;
--   ( iii ) positive leg :  dPosConjAt ;
--   ( iv )  assemble :  cgiClashConjFromLegs .

module T4.SurpriseG2.CgiClashConjMain where

open import T4.Base
open import T4.Tags using ( tag_sb )
open import T4.Num using ( num )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.DefWit using ( cNeg )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp )

open import T4.SurpriseG2.EnumRunProg using ( enumRunProgOf )
open import T4.SurpriseG2.KcodeConj using ( KcodeConj ; KcodeConj_eval )
open import T4.SurpriseG2.CgiClashConj
  using ( cVarc ; SomeProof
        ; KTAt ; passKAt ; anteAt ; defEqTAt
        ; cAnteProofOf ; dAnteConjAt
        ; cPosOf ; dPosConjAt
        ; cgiClashConjFromLegs )

open import BRA3.Church using ( pi )
open import BRA3.RuleInst2 using ( NatLe )

------------------------------------------------------------------------
-- The integrated clash .

cgiClashConj :
  (M : Nat) (enum : Fun1) ->
  (kStar : Nat) (kStarBound : NatLe kStar M) ->
  (gLname nTerm x' w0 : Term) ->
  Deriv (eqF (ap1 thmT w0) (ap1 (KcodeConj M enum) x')) ->
  Deriv (eqF (ap2 (enumRunProgOf enum) (natCode kStar) nTerm) (ap1 s x')) ->
  SomeProof
cgiClashConj M enum kStar kStarBound gLname nTerm x' w0 dNeg runEnumForm =
  let -- The program-slot Fun2 .
      prgFun : Fun2
      prgFun = enumRunProgOf enum

      -- Substitution values .
      S0 : Term
      S0 = ap1 num (natCode kStar)
      S1 : Term
      S1 = ap1 num nTerm

      spec0 : Term
      spec0 = ap2 Pair (natCode zero) S0
      spec1 : Term
      spec1 = ap2 Pair (natCode (suc zero)) S1

      -- KT-shape at the open / mid / closed forms .
      KOpen : Term
      KOpen   = KTAt M prgFun x' (cVarc zero) (cVarc (suc zero))
      KMid : Term
      KMid    = KTAt M prgFun x' (cVarc zero) S1
      KClosed : Term
      KClosed = KTAt M prgFun x' S0 S1

      -- (i)  Two-stage substitution :  inner ( var 1 := S1 ) ,
      --      outer ( var 0 := S0 ) .

      innerEq : Deriv (eqF (ap2 sbf spec1 KOpen) KMid)
      innerEq =
        passKAt M prgFun x' (suc zero) S1
          (cVarc zero) (cVarc zero) (cVarc (suc zero)) S1
          (sbt_at_var_nomatch (suc zero) zero S1 refl)
          (sbt_at_var_match (suc zero) S1)

      outerEq : Deriv (eqF (ap2 sbf spec0 KMid) KClosed)
      outerEq =
        passKAt M prgFun x' zero S0
          (cVarc zero) S0 S1 S1
          (sbt_at_var_match zero S0)
          (sbt_num_inert zero S0 nTerm)

      substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KOpen)) KClosed)
      substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

      -- KOpen  = kdefConjSkel M enum (num x')  via the Pair-chain
      -- match between  skelOf  and the  KTAt  layout when
      -- prgFun = enumRunProgOf enum  ( definitional , by refl ) .
      dNegOpen : Deriv (eqF (ap1 thmT w0) KOpen)
      dNegOpen = ruleTrans dNeg (KcodeConj_eval M enum x')

      innerWrap : Term
      innerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)
      outerWrap : Term
      outerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

      dInner : Deriv (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen))
      dInner = ruleTrans (thmT_at_sb spec1 w0) (congR sbf spec1 dNegOpen)

      dInst : Deriv (eqF (ap1 thmT outerWrap) KClosed)
      dInst = ruleTrans (thmT_at_sb spec0 innerWrap)
                (ruleTrans (congR sbf spec0 dInner) substBoth)

      -- (ii)  Strip the leq-antecedent via  encoded_mp .

      cAnteProof : Term
      cAnteProof = cAnteProofOf kStar M

      dAnte :
        Deriv (eqF (ap1 thmT cAnteProof) (anteAt M S0))
      dAnte = dAnteConjAt M kStar kStarBound

      dNegFinal :
        Deriv (eqF (ap1 thmT (cmp outerWrap cAnteProof))
                    (cNeg (defEqTAt prgFun x' S0 S1)))
      dNegFinal =
        encoded_mp outerWrap cAnteProof (anteAt M S0)
          (cNeg (defEqTAt prgFun x' S0 S1)) dInst dAnte

      -- (iii)  The positive leg .

      dPos :
        Deriv (eqF (ap1 thmT (cPosOf enum kStar nTerm))
                    (defEqTAt prgFun x' S0 S1))
      dPos = dPosConjAt enum kStar nTerm x' runEnumForm

      -- (iv)  Assemble .
  in cgiClashConjFromLegs (defEqTAt prgFun x' S0 S1) (cPosOf enum kStar nTerm)
       (cmp outerWrap cAnteProof) dPos dNegFinal
