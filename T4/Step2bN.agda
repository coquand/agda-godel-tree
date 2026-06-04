{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step2bN -- clos STEP 2b :  install the num-raw subject  ( substitute, IN THE
-- CODE,  x0 = var 0  by  num x0 = ap1 num (var 0) ).
--
-- Step 2 ( T4.Step2N ) gives  thmT w = code( Kr x0 = O  =>  Q(x1) ) .   Here we
-- wrap  w  with the substitution box  pi tag_sb (pi spec0 _)  ( spec0 maps the
-- coded  x0  to  num x0 ) and reduce by  thmT_at_sb  :  the antecedent's subject
-- becomes  num x0  ( recogniser-readable ), while the consequent  Q  -- which has
-- NO free  x0  ( only the run-length  x1 = var 1 ) -- is left INERT by
-- sbfInert_codeFormula :
--
--   step2b ... : Deriv (eqF (ap1 thmT (wStep2b ...))
--                          (cImp (cEqTm (cAp1f (Kr r k) (num x0)) O)
--                                (codeFormula (KdefBigConjNF F1 M r))))
--
-- = thmT(w') = code( Kr(num x0) = O  =>  Q(x1) ) , the antecedent now matching
-- the  thm13  output of clos Step 4.

open import T4.Base
open import BRA3.Church using ( pi )
open import BRA3.PairAlgebra using ( Pair )
open import BRA3.RuleInst2 using ( NatLe )
open import T4.Tags using ( tag_sb )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.DefWit using ( cEqTm ; cImp )
open import T4.CgiClash using ( cAp1f ; cVarc )
open import T4.SbT using ( sbt )
open import T4.SbF using ( sbf )
open import T4.SbfAtClosures using ( sbContract )
open import T4.SbStep using ( sbf_step_imp ; sbf_step_atomic ; sbt_step_ap1
                            ; sbt_inert_NumCode ; ncO )
open import T4.SbtAtVar using ( sbt_at_var_match )
open import T4.NotFree using ( notFreeF ; notFreeT ; both ; module FreshNF )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( KdefBigConjNF ; perProgNegNF ; F1 )

module T4.Step2bN (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN picks using ( Kr )
open import T4.Step2N  Lstar picks using ( wStep2 ; step2 )

module FNF = FreshNF sbt sbf sbContract

------------------------------------------------------------------------
-- SECTION 0.  notFreeF 0  of the consequent  Q = KdefBigConjNF F1 M r .

nfT_natCode : (k j : Nat) -> notFreeT k (natCode j)
nfT_natCode k zero    = tt
nfT_natCode k (suc j) = nfT_natCode k j

-- one conjunct  perProgNegNF F1 r j = neg ( runProgN (natCode j) (var 1) = s (natCode r) ) .
nfPP : (r j : Nat) -> notFreeF zero (perProgNegNF F1 r j)
nfPP r j = both (both (nfT_natCode zero j) refl) (nfT_natCode zero r)

nfKBC : (r M' : Nat) -> notFreeF zero (KdefBigConjNF F1 M' r)
nfKBC r zero      = nfPP r zero
nfKBC r (suc M'') = both (nfPP r (suc M'')) (nfKBC r M'')

------------------------------------------------------------------------
-- SECTION 1.  The substituent and the substitution passes.

S0 : Term
S0 = ap1 num (var zero)

spec0 : Term
spec0 = ap2 Pair (natCode zero) S0

-- the antecedent atom  Kr x0 = O  picks up  num x0 .
passAnt :
  (r k : Nat) ->
  Deriv (eqF (ap2 sbf spec0 (cEqTm (cAp1f (Kr r k) (cVarc zero)) O))
             (cEqTm (cAp1f (Kr r k) S0) O))
passAnt r k =
  let eVar : Deriv (eqF (ap2 sbt spec0 (cVarc zero)) S0)
      eVar = sbt_at_var_match zero S0
      eAnt : Deriv (eqF (ap2 sbt spec0 (cAp1f (Kr r k) (cVarc zero)))
                        (cAp1f (Kr r k) S0))
      eAnt = sbt_step_ap1 zero S0 (Kr r k) (cVarc zero) S0 eVar
      eO : Deriv (eqF (ap2 sbt spec0 O) O)
      eO = sbt_inert_NumCode O ncO zero S0
  in sbf_step_atomic zero S0 (cAp1f (Kr r k) (cVarc zero)) O
       (cAp1f (Kr r k) S0) O eAnt eO

-- the consequent  Q  is inert ( no free  x0 ).
passQ :
  (r : Nat) ->
  Deriv (eqF (ap2 sbf spec0 (codeFormula (KdefBigConjNF F1 M r)))
             (codeFormula (KdefBigConjNF F1 M r)))
passQ r = FNF.sbfInert_codeFormula zero S0 (KdefBigConjNF F1 M r) (nfKBC r M)

-- the whole implication.
passImp :
  (r k : Nat) ->
  Deriv (eqF (ap2 sbf spec0
               (cImp (cEqTm (cAp1f (Kr r k) (cVarc zero)) O)
                     (codeFormula (KdefBigConjNF F1 M r))))
             (cImp (cEqTm (cAp1f (Kr r k) S0) O)
                   (codeFormula (KdefBigConjNF F1 M r))))
passImp r k =
  sbf_step_imp zero S0
    (cEqTm (cAp1f (Kr r k) (cVarc zero)) O)
    (codeFormula (KdefBigConjNF F1 M r))
    (cEqTm (cAp1f (Kr r k) S0) O)
    (codeFormula (KdefBigConjNF F1 M r))
    (passAnt r k) (passQ r)

------------------------------------------------------------------------
-- SECTION 2.  Step 2b = wrap  w  with the sb-box and reduce.

wStep2b :
  (r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r -> (bound : PicksBound N M picks) -> Term
wStep2b r k kEq rleN Sr bound =
  ap2 pi (natCode tag_sb) (ap2 pi spec0 (wStep2 r k kEq rleN Sr bound))

step2b :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (eqF (ap1 thmT (wStep2b r k kEq rleN Sr bound))
             (cImp (cEqTm (cAp1f (Kr r k) S0) O)
                   (codeFormula (KdefBigConjNF F1 M r))))
step2b r k kEq rleN Sr bound =
  let w : Term
      w = wStep2 r k kEq rleN Sr bound
      dOpen : Deriv (eqF (ap1 thmT w)
                         (codeFormula (imp (eqF (ap1 (Kr r k) (var zero)) O)
                                           (KdefBigConjNF F1 M r))))
      dOpen = step2 r k kEq rleN Sr bound
  in ruleTrans (thmT_at_sb spec0 w)
       (ruleTrans (congR sbf spec0 dOpen) (passImp r k))
