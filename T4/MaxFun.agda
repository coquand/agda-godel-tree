{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.MaxFun -- the object-level binary maximum as a genuine  Fun2 .
--
--   maxFun : Fun2  with   ap2 maxFun a b = sigma (sub a b) b   (= max(a,b)),
--   using BRA3's object addition  sigma  and truncated subtraction  sub
--   ( leq a b := sub a b = O ,  Church p.51).
--
-- With the two leq bounds proved internally for ALL Terms a, b (free object
-- variables included):
--
--   leq_a_max :  leq a (ap2 maxFun a b)        ( a <= max a b )
--   leq_b_max :  leq b (ap2 maxFun a b)        ( b <= max a b )
--
-- This is the  x0 <= max x0 x1  device of surprise-GII at the OBJECT level:
-- the two run-lengths  x0, x1  may now be free object variables, both bounded
-- by the single object term  ap2 maxFun x0 x1 .
--
-- The  b -side ( a <= max a b , the harder direction  a <= (a-b)+b ) is the
-- arithmetic lemma  leqSelfSubAdd , proved by classical case-elimination on
--  leq a b :  the  a<=b  branch collapses  sigma (sub a b) b = sigma O b = b
-- (T33sym) leaving  leq a b ; the  a>b  branch uses  T68  ( ~(a<=b) ->
--  (a-b)+b = a ) leaving  leq a a  (T73).

module T4.MaxFun where

open import T4.Base

open import BRA3.Church        using ( sigma ; sub ; T33sym )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.ChurchT68     using ( T68 )
open import BRA3.ChurchT73     using ( T73 )
open import BRA3.ChurchCM      using ( caseElim )
open import BRA3.Contrapositive using ( identP )
open import BRA3.RuleInst2     using ( ruleInst2 )

open import T4.LeqMono       using ( leq_sigma_right )
open import T4.Thm12.ImpHelpers using ( impLift ; impCongL ; impCongR ; impEqTrans )

------------------------------------------------------------------------
-- SECTION 1.  The arithmetic core :  a <= (a -. b) + b   for all a, b.

-- Universal form at  var 0 = a ,  var 1 = b .
leqSelfSubAdd_univ :
  Deriv (leq (var 0) (ap2 sigma (ap2 sub (var 0) (var 1)) (var 1)))
leqSelfSubAdd_univ =
  caseElim {leq (var 0) (var 1)} {neg (leq (var 0) (var 1))}
           {leq (var 0) SS}
           (identP (neg (leq (var 0) (var 1))))
           caseTrue
           caseFalse
  where
    x : Term
    x = var 0

    y : Term
    y = var 1

    d : Term
    d = ap2 sub x y

    SS : Term
    SS = ap2 sigma d y

    H : Formula
    H = leq x y          -- = eqF d O

    -- a<=b branch :  sigma (sub a b) b = sigma O b = b , so the goal
    --   sub a (sigma (sub a b) b) = sub a b = O  is the hypothesis  H .
    caseTrue : Deriv (imp H (leq x SS))
    caseTrue =
      let step_a : Deriv (imp H (eqF SS (ap2 sigma O y)))
          step_a = impCongL {H} sigma d O y (identP H)

          step_b : Deriv (imp H (eqF (ap2 sigma O y) y))
          step_b = impLift {H} T33sym

          SS_eq_y : Deriv (imp H (eqF SS y))
          SS_eq_y = impEqTrans {H} SS (ap2 sigma O y) y step_a step_b

          step_c : Deriv (imp H (eqF (ap2 sub x SS) (ap2 sub x y)))
          step_c = impCongR {H} sub SS y x SS_eq_y
      in impEqTrans {H} (ap2 sub x SS) (ap2 sub x y) O step_c (identP H)

    -- a>b branch :  T68 gives  sigma (sub a b) b = a , so the goal
    --   sub a (sigma (sub a b) b) = sub a a = O  (T73).
    caseFalse : Deriv (imp (neg H) (leq x SS))
    caseFalse =
      let t68 : Deriv (imp (neg H) (eqF SS x))
          t68 = T68

          step_d : Deriv (imp (neg H) (eqF (ap2 sub x SS) (ap2 sub x x)))
          step_d = impCongR {neg H} sub SS x x t68

          step_e : Deriv (imp (neg H) (eqF (ap2 sub x x) O))
          step_e = impLift {neg H} T73
      in impEqTrans {neg H} (ap2 sub x SS) (ap2 sub x x) O step_d step_e

-- General form for arbitrary Terms.
leqSelfSubAdd :
  (a b : Term) ->
  Deriv (leq a (ap2 sigma (ap2 sub a b) b))
leqSelfSubAdd a b = ruleInst2 0 a 1 b refl leqSelfSubAdd_univ

------------------------------------------------------------------------
-- SECTION 2.  The  Fun2  maximum and its evaluation.
--   maxFun = Fan sub v sigma ,  ap2 maxFun a b = sigma (sub a b) (v a b)
--                                              = sigma (sub a b) b .

maxFun : Fun2
maxFun = Fan sub v sigma

maxFun_eval :
  (a b : Term) ->
  Deriv (eqF (ap2 maxFun a b) (ap2 sigma (ap2 sub a b) b))
maxFun_eval a b =
  ruleTrans (axFan sub v sigma a b)
            (congR sigma (ap2 sub a b) (ax_v a b))

------------------------------------------------------------------------
-- SECTION 3.  The two leq bounds for the object max.

leq_a_max :
  (a b : Term) ->
  Deriv (leq a (ap2 maxFun a b))
leq_a_max a b =
  let e : Deriv (eqF (ap2 maxFun a b) (ap2 sigma (ap2 sub a b) b))
      e = maxFun_eval a b

      base : Deriv (leq a (ap2 sigma (ap2 sub a b) b))
      base = leqSelfSubAdd a b

      cong : Deriv (eqF (ap2 sub a (ap2 maxFun a b))
                        (ap2 sub a (ap2 sigma (ap2 sub a b) b)))
      cong = congR sub a e
  in ruleTrans cong base

leq_b_max :
  (a b : Term) ->
  Deriv (leq b (ap2 maxFun a b))
leq_b_max a b =
  let e : Deriv (eqF (ap2 maxFun a b) (ap2 sigma (ap2 sub a b) b))
      e = maxFun_eval a b

      base : Deriv (leq b (ap2 sigma (ap2 sub a b) b))
      base = leq_sigma_right (ap2 sub a b) b

      cong : Deriv (eqF (ap2 sub b (ap2 maxFun a b))
                        (ap2 sub b (ap2 sigma (ap2 sub a b) b)))
      cong = congR sub b e
  in ruleTrans cong base
