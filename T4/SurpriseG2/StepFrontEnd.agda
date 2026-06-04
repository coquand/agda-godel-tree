{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StepFrontEnd --
--
-- The FORMULA-LEVEL "front end" of the surprise-G2 inductive step
-- (T4/clos lines 25-31).   Given  S(r)  and a target family
-- (picks, bound) at day  r+1 , produce
--
--   Deriv (imp K_rest (KdefBigConj M enum (natCode r)))
--
-- where  K_rest = BigConjFormula consts (suc r) picks  and the right-hand
-- side is the bare-runProg big-conjunction of the M+1 per-program
-- negations "no enumerated short program describes day r".
--
-- Construction (uses only SHIPPED tools + small Nat helpers):
--   * For each enum-index  k_in <= M , extend  picks  at day r with
--     k_in  (extPicks) ;   apply  S(r)  at the extended family ;
--   * bridge the resulting  neg (BigConjFormula consts r picks')  to
--     neg (conjF (describeAt enum k_in r) K_rest)  via the structural
--     count-unfold + bigConjCount extensionality ;
--   * negConjToImpRtoNegL  yields  imp K_rest (neg (describeAt enum k_in r))
--     = imp K_rest (perProgNeg enum (natCode r) k_in) ;
--   * aggregate the M+1 of these via  liftedAndIntro  into
--     imp K_rest (KdefBigConj M enum (natCode r)) .
--
-- This is the per-program / pigeonhole content of Kritchman-Raz step 3.
-- The size-predicate bridge (sizeExhaust), the encoded calculus and the
-- CGI clash are downstream (T4.SurpriseG2.StageStepFromConInt).

module T4.SurpriseG2.StepFrontEnd where

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; le-zero ; le-suc
                                          ; le-refl ; le-suc-right )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula
  using ( BigConjFormula ; bigConjCount ; conjF ; describeAt ; countDays ; countAux )
open import T4.SurpriseG2.KdefBigConj     using ( KdefBigConj ; perProgNeg )
open import T4.SurpriseG2.AndLemmas       using ( negConjToImpRtoNegL ; liftedAndIntro )
open import T4.SurpriseG2.StagePredFormula
  using ( StagePredF ; Picks ; PicksBound )

------------------------------------------------------------------------
-- A tiny Boolean + decidable-on-Nat equality (local, ASCII).

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
-- addO  (offset addition) and its shift lemma.

addO : Nat -> Nat -> Nat
addO start zero      = start
addO start (suc ofs) = suc (addO start ofs)

addO_suc_left : (start ofs : Nat) -> Eq (addO (suc start) ofs) (suc (addO start ofs))
addO_suc_left start zero      = refl
addO_suc_left start (suc ofs) = eqCong suc (addO_suc_left start ofs)

-- natEqb (suc (addO r i)) r = bF :  every offset above r differs from r.
natEqb_sucAddO : (r i : Nat) -> Eq (natEqb (suc (addO r i)) r) bF
natEqb_sucAddO zero    i = refl
natEqb_sucAddO (suc r) i =
  eqTrans (eqCong (\ z -> natEqb (suc z) (suc r)) (addO_suc_left r i))
          (natEqb_sucAddO r i)

------------------------------------------------------------------------
-- countDays step :  for  r <= N ,  countDays N r = suc (countDays N (suc r)) .

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
-- bigConjCount is extensional in  picks  over the days it actually reads
-- (start , start+1 , ... , start+count-1 ).

bigConjExt :
  (enum : Fun1) (count start : Nat) (p1 p2 : Nat -> Nat) ->
  ((i : Nat) -> Eq (p1 (addO start i)) (p2 (addO start i))) ->
  Eq (bigConjCount enum count start p1) (bigConjCount enum count start p2)
bigConjExt enum zero    start p1 p2 agree = refl
bigConjExt enum (suc c) start p1 p2 agree =
  let headEq : Eq (p1 start) (p2 start)
      headEq = agree zero
      tailAgree : (i : Nat) ->
        Eq (p1 (addO (suc start) i)) (p2 (addO (suc start) i))
      tailAgree i =
        eqTrans (eqCong p1 (addO_suc_left start i))
                (eqTrans (agree (suc i))
                         (eqSym (eqCong p2 (addO_suc_left start i))))
      ih : Eq (bigConjCount enum c (suc start) p1)
              (bigConjCount enum c (suc start) p2)
      ih = bigConjExt enum c (suc start) p1 p2 tailAgree
  in eqTrans (eqCong (\ pr -> conjF (describeAt enum pr start)
                                     (bigConjCount enum c (suc start) p1)) headEq)
             (eqCong (\ T -> conjF (describeAt enum (p2 start) start) T) ih)

------------------------------------------------------------------------
-- The day-r picks extension and its key equalities.

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
-- The Carneiro-LIFTED aggregation, mirroring  KdefBigConj.kdefBigConjFromNegs
-- but under a common hypothesis  X .

aggregateImp :
  (enum : Fun1) (subj : Term) (X : Formula) (M' : Nat) ->
  ((k : Nat) -> NatLe k M' -> Deriv (imp X (perProgNeg enum subj k))) ->
  Deriv (imp X (KdefBigConj M' enum subj))
aggregateImp enum subj X zero      negs = negs zero (le-zero zero)
aggregateImp enum subj X (suc M'') negs =
  let top : Deriv (imp X (perProgNeg enum subj (suc M'')))
      top = negs (suc M'') (le-refl (suc M''))
      below : (k : Nat) -> NatLe k M'' -> Deriv (imp X (perProgNeg enum subj k))
      below k le = negs k (le-suc-right le)
      ih : Deriv (imp X (KdefBigConj M'' enum subj))
      ih = aggregateImp enum subj X M'' below
  in liftedAndIntro X (perProgNeg enum subj (suc M''))
                      (KdefBigConj M'' enum subj) top ih

------------------------------------------------------------------------
-- The front end.

frontEnd :
  (consts : SurpriseConstsConj) (r : Nat) ->
  NatLe r (SurpriseConstsConj.N consts) ->
  StagePredF consts r ->
  (picks : Picks) (bound : PicksBound consts picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
              (KdefBigConj (SurpriseConstsConj.M consts)
                           (SurpriseConstsConj.enum consts) (natCode r)))
frontEnd consts r rleN Sr picks bound =
  let N : Nat
      N = SurpriseConstsConj.N consts
      M : Nat
      M = SurpriseConstsConj.M consts
      enum : Fun1
      enum = SurpriseConstsConj.enum consts

      X : Formula
      X = BigConjFormula consts (suc r) picks

      -- per-program implication at index  kin <= M .
      perProgImp :
        (kin : Nat) -> NatLe kin M ->
        Deriv (imp X (perProgNeg enum (natCode r) kin))
      perProgImp kin kle =
        let picks' : Nat -> Nat
            picks' = extPicks picks r kin

            bound' : PicksBound consts picks'
            bound' d dleN =
              iteLe M (natEqb d r) kin (picks d) kle (bound d dleN)

            Sr_at : Deriv (neg (BigConjFormula consts r picks'))
            Sr_at = Sr picks' bound'

            TL : Formula
            TL = bigConjCount enum (countDays N (suc r)) (suc r) picks'

            -- structural unfold of K(picks'; r) into head /\ tail .
            step_count :
              Eq (BigConjFormula consts r picks')
                 (conjF (describeAt enum (picks' r) r) TL)
            step_count =
              eqCong (\ c -> bigConjCount enum c r picks') (countDays_step N r rleN)

            step_progr :
              Eq (conjF (describeAt enum (picks' r) r) TL)
                 (conjF (describeAt enum kin r) TL)
            step_progr =
              eqCong (\ ix -> conjF (describeAt enum ix r) TL) (extAt_r picks r kin)

            tailEq : Eq TL (BigConjFormula consts (suc r) picks)
            tailEq =
              bigConjExt enum (countDays N (suc r)) (suc r) picks' picks
                         (extAt_above picks r kin)

            step_tail :
              Eq (conjF (describeAt enum kin r) TL)
                 (conjF (describeAt enum kin r) (BigConjFormula consts (suc r) picks))
            step_tail =
              eqCong (\ T -> conjF (describeAt enum kin r) T) tailEq

            unfoldEq :
              Eq (BigConjFormula consts r picks')
                 (conjF (describeAt enum kin r) X)
            unfoldEq = eqTrans step_count (eqTrans step_progr step_tail)

            Sr_conj : Deriv (neg (conjF (describeAt enum kin r) X))
            Sr_conj = eqSubst (\ F -> Deriv (neg F)) unfoldEq Sr_at

            ncll : Deriv (imp (neg (conjF (describeAt enum kin r) X))
                               (imp X (neg (describeAt enum kin r))))
            ncll = negConjToImpRtoNegL (describeAt enum kin r) X
        in mp ncll Sr_conj
  in aggregateImp enum (natCode r) X M perProgImp
