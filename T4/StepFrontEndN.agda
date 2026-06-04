{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepFrontEndN -- the number-code FRONT END ( clos lines 25-35, Step 1 ) of
-- surprise-GII's inductive step :  given  S(r)  and a target family
-- (picks, bound) at day  r+1 , produce
--
--   frontEndN :
--     ... -> Deriv (imp (BigConjFormulaN N (suc r) picks) (KdefBigConjN M r))
--
-- "if days [r+1..N] are jointly describable ( K_rest ) then no program  k <= M
--  describes day r" -- the per-program / pigeonhole content of Kritchman-Raz step 3.
--
-- Number-code mirror of  T4.SurpriseG2.StepFrontEnd.frontEnd  ( describeAt/runProg
-- -> describeAtN/runProgN , enum = identity ).   The construction is verbatim : for
-- each program index  kin <= M  extend  picks  at day r with  kin , apply  S(r) ,
-- structurally unfold  K(picks';r) = describeAtN kin r /\ K_rest , peel via
-- negConjToImpRtoNegL , and aggregate the  M+1  per-program negations.

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right )
open import T4.SurpriseG2.BigConjFormula using ( conjF ; countDays ; countAux )
open import T4.SurpriseG2.AndLemmas using ( negConjToImpRtoNegL ; liftedAndIntro )
open import T4.StagePredFN
  using ( describeAtN ; bigConjCountN ; openFuel ; BigConjFormulaN
        ; StagePredFN ; Picks ; PicksBound )
open import T4.KdefBigConjN using ( perProgNegN ; KdefBigConjN )

module T4.StepFrontEndN where

------------------------------------------------------------------------
-- Boolean + decidable Nat-equality ( verbatim from StepFrontEnd ).

data BB : Set where
  bT : BB
  bF : BB

ite : {A : Set} -> BB -> A -> A -> A
ite bT x y = x
ite bF x y = y

natEqb : Nat -> Nat -> BB
natEqb zero    zero    = bT
natEqb zero    (suc _) = bF
natEqb (suc _) zero    = bF
natEqb (suc m) (suc n) = natEqb m n

natEqb_refl : (n : Nat) -> Eq (natEqb n n) bT
natEqb_refl zero    = refl
natEqb_refl (suc n) = natEqb_refl n

------------------------------------------------------------------------
-- addO  and shift lemmas ( verbatim ).

addO : Nat -> Nat -> Nat
addO start zero      = start
addO start (suc ofs) = suc (addO start ofs)

addO_suc_left : (start ofs : Nat) -> Eq (addO (suc start) ofs) (suc (addO start ofs))
addO_suc_left start zero      = refl
addO_suc_left start (suc ofs) = eqCong suc (addO_suc_left start ofs)

natEqb_sucAddO : (r i : Nat) -> Eq (natEqb (suc (addO r i)) r) bF
natEqb_sucAddO zero    i = refl
natEqb_sucAddO (suc r) i =
  eqTrans (eqCong (\ z -> natEqb (suc z) (suc r)) (addO_suc_left r i))
          (natEqb_sucAddO r i)

------------------------------------------------------------------------
-- countDays step ( verbatim ).

countAux0 : (n : Nat) -> Eq (countAux n zero) n
countAux0 zero    = refl
countAux0 (suc n) = refl

countAux_sucShift :
  (N r : Nat) -> NatLe r N -> Eq (countAux (suc N) r) (suc (countAux N r))
countAux_sucShift N        zero    (le-zero .N)   = eqCong suc (eqSym (countAux0 N))
countAux_sucShift (suc N') (suc r') (le-suc le')  = countAux_sucShift N' r' le'

countDays_step :
  (N r : Nat) -> NatLe r N -> Eq (countDays N r) (suc (countDays N (suc r)))
countDays_step N r le = countAux_sucShift N r le

------------------------------------------------------------------------
-- bigConjCountN extensionality in  picks  ( over the days it reads ).

bigConjExtN :
  (count start : Nat) (p1 p2 : Nat -> Nat) ->
  ((i : Nat) -> Eq (p1 (addO start i)) (p2 (addO start i))) ->
  Eq (bigConjCountN count start p1 openFuel) (bigConjCountN count start p2 openFuel)
bigConjExtN zero    start p1 p2 agree = refl
bigConjExtN (suc c) start p1 p2 agree =
  let headEq : Eq (p1 start) (p2 start)
      headEq = agree zero
      tailAgree : (i : Nat) ->
        Eq (p1 (addO (suc start) i)) (p2 (addO (suc start) i))
      tailAgree i =
        eqTrans (eqCong p1 (addO_suc_left start i))
                (eqTrans (agree (suc i))
                         (eqSym (eqCong p2 (addO_suc_left start i))))
      ih : Eq (bigConjCountN c (suc start) p1 openFuel)
              (bigConjCountN c (suc start) p2 openFuel)
      ih = bigConjExtN c (suc start) p1 p2 tailAgree
  in eqTrans (eqCong (\ pr -> conjF (describeAtN pr start (var zero))
                                     (bigConjCountN c (suc start) p1 openFuel)) headEq)
             (eqCong (\ T -> conjF (describeAtN (p2 start) start (var zero)) T) ih)

------------------------------------------------------------------------
-- The day-r picks extension and its equalities ( verbatim ).

extPicks : (picks : Nat -> Nat) (r kin : Nat) -> Nat -> Nat
extPicks picks r kin d = ite (natEqb d r) kin (picks d)

extAt_r : (picks : Nat -> Nat) (r kin : Nat) ->
          Eq (extPicks picks r kin r) kin
extAt_r picks r kin = eqCong (\ b -> ite b kin (picks r)) (natEqb_refl r)

extAt_above : (picks : Nat -> Nat) (r kin i : Nat) ->
              Eq (extPicks picks r kin (addO (suc r) i)) (picks (addO (suc r) i))
extAt_above picks r kin i =
  eqCong (\ b -> ite b kin (picks (addO (suc r) i)))
         (eqTrans (eqCong (\ z -> natEqb z r) (addO_suc_left r i))
                  (natEqb_sucAddO r i))

iteLe : (M : Nat) (b : BB) (x y : Nat) ->
        NatLe x M -> NatLe y M -> NatLe (ite b x y) M
iteLe M bT x y hx hy = hx
iteLe M bF x y hx hy = hy

------------------------------------------------------------------------
-- The lifted aggregation of the per-program negations.

aggregateImpN :
  (r : Nat) (X : Formula) (M' : Nat) ->
  ((k : Nat) -> NatLe k M' -> Deriv (imp X (perProgNegN r k))) ->
  Deriv (imp X (KdefBigConjN M' r))
aggregateImpN r X zero      negs = negs zero (le-zero zero)
aggregateImpN r X (suc M'') negs =
  let top : Deriv (imp X (perProgNegN r (suc M'')))
      top = negs (suc M'') (le-refl (suc M''))
      below : (k : Nat) -> NatLe k M'' -> Deriv (imp X (perProgNegN r k))
      below k le = negs k (le-suc-right le)
      ih : Deriv (imp X (KdefBigConjN M'' r))
      ih = aggregateImpN r X M'' below
  in liftedAndIntro X (perProgNegN r (suc M''))
                      (KdefBigConjN M'' r) top ih

------------------------------------------------------------------------
-- The front end ( clos Step 1 ).

frontEndN :
  (N M r : Nat) -> NatLe r N -> StagePredFN N M r ->
  (picks : Picks) (bound : PicksBound N M picks) ->
  Deriv (imp (BigConjFormulaN N (suc r) picks) (KdefBigConjN M r))
frontEndN N M r rleN Sr picks bound =
  let X : Formula
      X = BigConjFormulaN N (suc r) picks

      perProgImp :
        (kin : Nat) -> NatLe kin M ->
        Deriv (imp X (perProgNegN r kin))
      perProgImp kin kle =
        let picks' : Nat -> Nat
            picks' = extPicks picks r kin

            bound' : PicksBound N M picks'
            bound' d dleN =
              iteLe M (natEqb d r) kin (picks d) kle (bound d dleN)

            Sr_at : Deriv (neg (BigConjFormulaN N r picks'))
            Sr_at = Sr picks' bound'

            TL : Formula
            TL = bigConjCountN (countDays N (suc r)) (suc r) picks' openFuel

            step_count :
              Eq (BigConjFormulaN N r picks')
                 (conjF (describeAtN (picks' r) r (var zero)) TL)
            step_count =
              eqCong (\ c -> bigConjCountN c r picks' openFuel) (countDays_step N r rleN)

            step_progr :
              Eq (conjF (describeAtN (picks' r) r (var zero)) TL)
                 (conjF (describeAtN kin r (var zero)) TL)
            step_progr =
              eqCong (\ ix -> conjF (describeAtN ix r (var zero)) TL) (extAt_r picks r kin)

            tailEq : Eq TL (BigConjFormulaN N (suc r) picks)
            tailEq =
              bigConjExtN (countDays N (suc r)) (suc r) picks' picks
                          (extAt_above picks r kin)

            step_tail :
              Eq (conjF (describeAtN kin r (var zero)) TL)
                 (conjF (describeAtN kin r (var zero)) (BigConjFormulaN N (suc r) picks))
            step_tail =
              eqCong (\ T -> conjF (describeAtN kin r (var zero)) T) tailEq

            unfoldEq :
              Eq (BigConjFormulaN N r picks')
                 (conjF (describeAtN kin r (var zero)) X)
            unfoldEq = eqTrans step_count (eqTrans step_progr step_tail)

            Sr_conj : Deriv (neg (conjF (describeAtN kin r (var zero)) X))
            Sr_conj = eqSubst (\ F -> Deriv (neg F)) unfoldEq Sr_at

            ncll : Deriv (imp (neg (conjF (describeAtN kin r (var zero)) X))
                               (imp X (neg (describeAtN kin r (var zero)))))
            ncll = negConjToImpRtoNegL (describeAtN kin r (var zero)) X
        in mp ncll Sr_conj
  in aggregateImpN r X M perProgImp
