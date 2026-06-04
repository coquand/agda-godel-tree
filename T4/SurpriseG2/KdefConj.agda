{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.KdefConj -- the SHAPED equivalence between the
-- finite-conjunction form  K(r) > L*  (M+1 per-program negs) and the
-- universal-over-v0 form  (imp (leq v0 (natCode M))
-- (neg (eqF (ap2 (enumRunProgOf enum) v0 v1) (s subject))))  of the
-- K-formula .
--
-- =====================================================================
-- WHY THIS FILE  ( and why the NEW MATRIX uses  enumRunProgOf ).
-- =====================================================================
--
-- The earlier  Kdef L subject = imp (size_le_L v0) (~definable v0 ...)
-- form needed  sizeExhaust  to bridge from the M+1 per-program negs to
-- the open-v0 K-formula ; sizeExhaust  is NOT directly BRA-provable
-- ( see  T4/NEXT-SESSION-SIZEEXHAUST.md ) .
--
-- A first reformulation replaced the size predicate with an INDEX-bound
-- leq v0 (natCode M) and an enumerator  enum : Fun1 .   That worked for
-- the SHAPED equivalence ( kdefConjFromNegs ) but blocked the
-- downstream  CgiClashConj  :  the substituted ~def code at the
-- runProg-headed shape had a  cAp1f enum  wrapping that  thm13_binary
-- does NOT produce literally .
--
-- SECOND ITERATION  ( this file's current form ) :  push the enumerator
-- INSIDE the Fun2  by working with the combinator
--   enumRunProgOf enum := Fan (Lift1 enum) v runProg
-- ( see  T4.SurpriseG2.EnumRunProg ) .   The K-formula matrix becomes
--   imp (leq v0 (natCode M))
--       (neg (eqF (ap2 (enumRunProgOf enum) v0 v1) (s subject)))
-- whose substituted ~def code  cAp2f (enumRunProgOf enum) S0 S1  matches
-- thm13_binary at  enumRunProgOf enum  literally , so  CgiClashConj
-- becomes a mechanical parallel of OLD  CgiClash .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * KdefConj M enum subject  :  Formula
--   The new K-formula at index-bound shape with enumerator pushed
--   inside the Fun2 .   Free  var 0 = enumeration index ,  var 1 = fuel .
--
-- * kdefConjFromNegs :
--     (M : Nat) (enum : Fun1) (subject : Term) ->
--     ((k : Nat) -> NatLe k M ->
--       Deriv (neg (definable (ap1 enum (natCode k)) subject (var (suc zero))))) ->
--     Deriv (KdefConj M enum subject)
--
--   The PRINCIPAL deliverable :  replaces  kdefFromNegs  in the
--   framework's pipeline .   The per-program-neg API is UNCHANGED
--   ( still uses  definable (ap1 enum (natCode k)) ...  on the
--   runProg shape ; the matrix-shape bridge lives in  transportEnum
--   via  enumRunProgOf_eq ) , so callers do not need to migrate .
--
-- =====================================================================
-- ARCHITECTURE OF  transportEnum.
-- =====================================================================
--
-- Internally  transportEnum  builds the same OLD chain as before
-- ( imp (eqF v0 k_term) (neg (eqF (ap2 runProg (ap1 enum v0) v1) (s subject))) )
-- then APPENDS a single bridge  neg E_old -> neg E_new  obtained from
-- enumRunProgOf_eq  +  ax_eqTrans  +  axContrapos .   This keeps the
-- per-program-neg API identical while the new matrix shape is delivered.

module T4.SurpriseG2.KdefConj where

open import T4.Base
open import BRA3.Church          using ( sub )

open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchSubSucc   using ( T_sub_O )
open import BRA3.ChurchT82       using ( T82 )
open import BRA3.RuleInst2       using ( NatLe ; le-zero ; le-suc
                                       ; le-refl ; le-suc-right )
open import BRA3.Logic           using ( impTrans ; prependEqLeft )
open import BRA3.Contrapositive  using ( liftP ; bComb ; compI ; axContrapos )
open import BRA3.ChurchDChurchAsSub using ( caseElimUnderOne )
open import T4.Kdef            using ( runProg ; definable )
open import T4.SurpriseG2.EnumRunProg using ( enumRunProgOf ; enumRunProgOf_eq )

------------------------------------------------------------------------
-- The new K-formula matrix .   Enumerator pushed inside the Fun2 .

KdefConj : (M : Nat) (enum : Fun1) (subject : Term) -> Formula
KdefConj M enum subject =
  imp (leq (var zero) (natCode M))
      (neg (eqF (ap2 (enumRunProgOf enum) (var zero) (var (suc zero)))
                 (ap1 s subject)))

------------------------------------------------------------------------
-- Helper 1 : leq v0 O  ->  eqF v0 O  ( unchanged from the previous
-- reformulation ) .

leq_v0_O_to_eq_O : Deriv (imp (leq (var zero) O) (eqF (var zero) O))
leq_v0_O_to_eq_O =
  prependEqLeft (var zero) (ap2 sub (var zero) O) O
                (ruleSym (T_sub_O (var zero)))

------------------------------------------------------------------------
-- Helper 2 :  transportEnum  --  from a closed OLD-shape neg at
-- enum (k_term) , derive  imp (eqF v0 k_term) (neg <NEW-shape matrix>) .
--
-- Internally :  ( i ) build the OLD-shape transport
--   imp (eqF v0 k_term) (neg (eqF (ap2 runProg (ap1 enum v0) v1) (s subject)))
-- by the  contrapDefImp pattern with  ax_eqCong1 enum  +  ax_eqCongL runProg ;
-- ( ii ) bridge  neg E_old -> neg E_new  via  enumRunProgOf_eq  +
-- ax_eqTrans + axContrapos .

transportEnum :
  (enum : Fun1) (k_term : Term) (subject : Term) ->
  Deriv (neg (definable (ap1 enum k_term) subject (var (suc zero)))) ->
  Deriv (imp (eqF (var zero) k_term)
              (neg (eqF (ap2 (enumRunProgOf enum) (var zero) (var (suc zero)))
                         (ap1 s subject))))
transportEnum enum k_term subject negDefAtK =
  let v0 : Term
      v0 = var zero

      v1 : Term
      v1 = var (suc zero)

      rhs : Term
      rhs = ap1 s subject

      progRun : Term
      progRun = ap2 runProg (ap1 enum k_term) v1

      v0Run : Term
      v0Run = ap2 runProg (ap1 enum v0) v1

      v0RunNew : Term
      v0RunNew = ap2 (enumRunProgOf enum) v0 v1

      -- (i)  OLD-shape transport :  imp (eqF v0 k_term) (neg (eqF v0Run rhs)) .

      congEnum :
        Deriv (imp (eqF v0 k_term)
                    (eqF (ap1 enum v0) (ap1 enum k_term)))
      congEnum = ax_eqCong1 enum v0 k_term

      congRun :
        Deriv (imp (eqF (ap1 enum v0) (ap1 enum k_term))
                    (eqF v0Run progRun))
      congRun = ax_eqCongL runProg (ap1 enum v0) (ap1 enum k_term) v1

      v0Run_eq_progRun :
        Deriv (imp (eqF v0 k_term) (eqF v0Run progRun))
      v0Run_eq_progRun = impTrans congEnum congRun

      transAx :
        Deriv (imp (eqF v0Run progRun)
                    (imp (eqF v0Run rhs) (eqF progRun rhs)))
      transAx = ax_eqTrans v0Run progRun rhs

      defImp :
        Deriv (imp (eqF v0 k_term)
                    (imp (eqF v0Run rhs) (eqF progRun rhs)))
      defImp = compI v0Run_eq_progRun transAx

      contraposAx :
        Deriv (imp (imp (eqF v0Run rhs) (eqF progRun rhs))
                    (imp (neg (eqF progRun rhs)) (neg (eqF v0Run rhs))))
      contraposAx = axContrapos (eqF v0Run rhs) (eqF progRun rhs)

      step1 :
        Deriv (imp (eqF v0 k_term)
                    (imp (neg (eqF progRun rhs)) (neg (eqF v0Run rhs))))
      step1 = compI defImp contraposAx

      liftedNeg :
        Deriv (imp (eqF v0 k_term) (neg (eqF progRun rhs)))
      liftedNeg = liftP (eqF v0 k_term) negDefAtK

      oldOut :
        Deriv (imp (eqF v0 k_term) (neg (eqF v0Run rhs)))
      oldOut = bComb step1 liftedNeg

      -- (ii)  Bridge to the NEW matrix shape .
      --
      --   enumRunProgOf_eq enum v0 v1  :  eqF v0RunNew v0Run .
      --   ax_eqTrans v0RunNew v0Run rhs  : eqF v0RunNew v0Run ->
      --       (eqF v0RunNew rhs -> eqF v0Run rhs) .
      --   mp                            : imp (eqF v0RunNew rhs)
      --                                       (eqF v0Run rhs) .
      --   axContrapos + mp              : imp (neg (eqF v0Run rhs))
      --                                       (neg (eqF v0RunNew rhs)) .

      eq_new_old :
        Deriv (eqF v0RunNew v0Run)
      eq_new_old = enumRunProgOf_eq enum v0 v1

      bridgeImpl :
        Deriv (imp (eqF v0RunNew rhs) (eqF v0Run rhs))
      bridgeImpl = mp (ax_eqTrans v0RunNew v0Run rhs) eq_new_old

      contraBridge :
        Deriv (imp (neg (eqF v0Run rhs)) (neg (eqF v0RunNew rhs)))
      contraBridge =
        mp (axContrapos (eqF v0RunNew rhs) (eqF v0Run rhs)) bridgeImpl
  in compI oldOut contraBridge

------------------------------------------------------------------------
-- The main lemma -- reverse direction (per-k -> univ).
--
-- External induction on  M .   Base  M = 0 :  use  leq_v0_O_to_eq_O  +
-- transportEnum  at  k_term := O .   Step  M = suc M' :  IH gives
-- the univ at  M' ;  the top neg (at  k = suc M' ) is transported to
-- (eqF v0 (natCode (suc M'))) -> Rf  ;  combine via  caseElimUnderOne
-- on the under-one split of  leq v0 (natCode (suc M')) ,  with the
-- split-direction from  T82 .

kdefConjFromNegs :
  (M : Nat) (enum : Fun1) (subject : Term) ->
  ((k : Nat) -> NatLe k M ->
    Deriv (neg (definable (ap1 enum (natCode k)) subject (var (suc zero))))) ->
  Deriv (KdefConj M enum subject)
kdefConjFromNegs zero enum subject negs =
  let v0 : Term
      v0 = var zero

      v1 : Term
      v1 = var (suc zero)

      negAt0 : Deriv (neg (definable (ap1 enum O) subject v1))
      negAt0 = negs zero (le-zero zero)

      transp :
        Deriv (imp (eqF v0 O)
                    (neg (eqF (ap2 (enumRunProgOf enum) v0 v1)
                               (ap1 s subject))))
      transp = transportEnum enum O subject negAt0
  in impTrans leq_v0_O_to_eq_O transp
kdefConjFromNegs (suc M') enum subject negs =
  let v0 : Term
      v0 = var zero

      v1 : Term
      v1 = var (suc zero)

      -- Sub-hypothesis for the per-k restricted family at  M' .
      negsBelow : (k : Nat) -> NatLe k M' ->
        Deriv (neg (definable (ap1 enum (natCode k)) subject v1))
      negsBelow k le = negs k (le-suc-right le)

      -- IH  :  the univ at  M' .
      ih : Deriv (KdefConj M' enum subject)
      ih = kdefConjFromNegs M' enum subject negsBelow

      -- Top neg : at  k := suc M' .   Use  le-refl  to witness  NatLe (suc M') (suc M') .
      topNeg :
        Deriv (neg (definable (ap1 enum (natCode (suc M'))) subject v1))
      topNeg = negs (suc M') (le-refl (suc M'))

      -- The caseElimUnderOne instance.
      P1 : Formula
      P1 = leq v0 (natCode (suc M'))           -- = leq v0 (ap1 s (natCode M'))

      X : Formula
      X = leq v0 (natCode M')

      Y : Formula
      Y = eqF v0 (natCode (suc M'))            -- = eqF v0 (ap1 s (natCode M'))

      Rf : Formula
      Rf = neg (eqF (ap2 (enumRunProgOf enum) v0 v1) (ap1 s subject))

      -- T82 at  var 1 := natCode M'  :
      --   imp (leq v0 (s natCode M')) (imp (neg (leq v0 natCode M')) (eqF v0 (s natCode M'))) .
      negX_Y : Deriv (imp P1 (imp (neg X) Y))
      negX_Y = ruleInst (suc zero) (natCode M') T82

      -- IH  lifted under  P1  .
      X_R : Deriv (imp P1 (imp X Rf))
      X_R = liftP P1 ih

      -- Top neg, transported to  (eqF v0 (natCode (suc M')) -> Rf) ,  lifted under  P1 .
      transp_top : Deriv (imp Y Rf)
      transp_top = transportEnum enum (natCode (suc M')) subject topNeg

      Y_R : Deriv (imp P1 (imp Y Rf))
      Y_R = liftP P1 transp_top
  in caseElimUnderOne {P1 = P1} {X = X} {Y = Y} {Rf = Rf}
                       negX_Y X_R Y_R

------------------------------------------------------------------------
-- Forward direction ( univ -> per-k ) deferred .   The forward
-- direction is a sanity check and is NOT needed for the framework
-- rewire .
