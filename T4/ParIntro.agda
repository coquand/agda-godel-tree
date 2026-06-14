{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParIntro -- STAGE 4b (deliverable 2e): the OBJECT  E -Par predicate and
-- the introduction rule that turns a Par-CERTIFICATE into a genuine object
-- existential derivation:
--
--     Par t u  :=  E (parBody t u)               -- object Formula
--     parIntro : ParCert (code t)(code u) -> Deriv (Par (code t)(code u))
--
-- where  parBody t u : Fun1  is the characteristic function of a witness  d :
--     ap1 (parBody t u) d  =  pi (pi (isCert d) (eqTest (src d) t))
--                                (eqTest (tgt d) u)
-- with the Cantor pair  pi  as binary AND ( pi a b = O  iff  a = b = O ) and
-- the equality test  eqTest a b := pi (sub a b) (sub b a)  ( = O  iff  a = b,
-- since  sub a a = O  by  leq_refl ).  Hence  ap1 (parBody t u) d = O  iff
-- d  is a valid certificate ( isCert d = O ) whose endpoints are  t , u  --
-- exactly the relational  "exists a valid cert from t to u".
--
-- The Fun1 fork is the BRA composition constructor  C  ( ax_C :
-- ap1 (C h f g) d = ap2 h (ap1 f d)(ap1 g d) ); endpoint constants are
-- injected by  constTermFun1  (T4.Thm12.ConstTermFun1).  parIntro fires
-- E_intro at the witness  wit pc , discharging  parBody t u (wit) = O  from
-- the ParCert side conditions  valid / srcEq / tgtEq .

module T4.ParIntro where

open import T4.Base

open import T4.ParEnds     using ( src ; tgt ; isCert ; pi_O_O )
open import T4.ParReflPres using
  ( Tm ; ze ; su ; ad ; code
  ; ParCert ; wit ; valid ; srcEq ; tgtEq )
open import T4.Thm12.ConstTermFun1 using
  ( NoVar ; NoVarAnd ; mkAnd ; constTermFun1 ; constTermFun1_eq )

open import BRA3.Church          using ( pi ; sub )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )

------------------------------------------------------------------------
-- NoVar for coded terms (closed: built from O / ap1 s / ap2 Pair).

noVarCode : (t : Tm) -> NoVar (code t)
noVarCode ze       = mkAnd tt tt
noVarCode (su t)   = mkAnd tt (noVarCode t)
noVarCode (ad a b) = mkAnd tt (mkAnd (noVarCode a) (noVarCode b))

------------------------------------------------------------------------
-- The equality-test fork  eqTestF g1 g2  and its application law:
--   ap1 (eqTestF g1 g2) d = pi (sub (g1 d)(g2 d)) (sub (g2 d)(g1 d)) .

eqTestF : Fun1 -> Fun1 -> Fun1
eqTestF g1 g2 = C pi (C sub g1 g2) (C sub g2 g1)

eqTestF_app : (g1 g2 : Fun1) (d : Term) ->
  Deriv (eqF (ap1 (eqTestF g1 g2) d)
             (ap2 pi (ap2 sub (ap1 g1 d) (ap1 g2 d))
                     (ap2 sub (ap1 g2 d) (ap1 g1 d))))
eqTestF_app g1 g2 d =
  ruleTrans (ax_C pi (C sub g1 g2) (C sub g2 g1) d)
    (ruleTrans (congL pi (ap1 (C sub g2 g1) d) (ax_C sub g1 g2 d))
               (congR pi (ap2 sub (ap1 g1 d) (ap1 g2 d)) (ax_C sub g2 g1 d)))

------------------------------------------------------------------------
-- eqTest is zero on equal arguments:  if  a = b  then  pi(sub a b)(sub b a)=O.

eqTest_zero : (a b : Term) -> Deriv (eqF a b) ->
  Deriv (eqF (ap2 pi (ap2 sub a b) (ap2 sub b a)) O)
eqTest_zero a b e =
  let sAB : Deriv (eqF (ap2 sub a b) O)
      sAB = ruleTrans (congL sub b e) (sub_self b)
      sBA : Deriv (eqF (ap2 sub b a) O)
      sBA = ruleTrans (congR sub b e) (sub_self b)
  in ruleTrans (congL pi (ap2 sub b a) sAB)
       (ruleTrans (congR pi O sBA) pi_O_O)

------------------------------------------------------------------------
-- eqTestF against a constant endpoint:  if  g d = z  ( z var-free ),
-- then  ap1 (eqTestF g (constTermFun1 z)) d = O .

eqTestF_const_zero : (g : Fun1) (z : Term) -> NoVar z -> (d : Term) ->
  Deriv (eqF (ap1 g d) z) ->
  Deriv (eqF (ap1 (eqTestF g (constTermFun1 z)) d) O)
eqTestF_const_zero g z nz d e =
  let ce : Deriv (eqF (ap1 (constTermFun1 z) d) z)
      ce = constTermFun1_eq z nz d
      rwA : Deriv (eqF (ap2 sub (ap1 g d) (ap1 (constTermFun1 z) d))
                       (ap2 sub (ap1 g d) z))
      rwA = congR sub (ap1 g d) ce
      rwB : Deriv (eqF (ap2 sub (ap1 (constTermFun1 z) d) (ap1 g d))
                       (ap2 sub z (ap1 g d)))
      rwB = congL sub (ap1 g d) ce
      step1 : Deriv (eqF (ap2 pi (ap2 sub (ap1 g d) (ap1 (constTermFun1 z) d))
                                 (ap2 sub (ap1 (constTermFun1 z) d) (ap1 g d)))
                         (ap2 pi (ap2 sub (ap1 g d) z)
                                 (ap2 sub (ap1 (constTermFun1 z) d) (ap1 g d))))
      step1 = congL pi (ap2 sub (ap1 (constTermFun1 z) d) (ap1 g d)) rwA
      step2 : Deriv (eqF (ap2 pi (ap2 sub (ap1 g d) z)
                                 (ap2 sub (ap1 (constTermFun1 z) d) (ap1 g d)))
                         (ap2 pi (ap2 sub (ap1 g d) z)
                                 (ap2 sub z (ap1 g d))))
      step2 = congR pi (ap2 sub (ap1 g d) z) rwB
  in ruleTrans (eqTestF_app g (constTermFun1 z) d)
       (ruleTrans step1 (ruleTrans step2 (eqTest_zero (ap1 g d) z e)))

------------------------------------------------------------------------
-- The Par body Fun1 and its application law.

parBody : Term -> Term -> Fun1
parBody t uu =
  C pi (C pi isCert (eqTestF src (constTermFun1 t)))
       (eqTestF tgt (constTermFun1 uu))

parBody_app : (t uu d : Term) ->
  Deriv (eqF (ap1 (parBody t uu) d)
             (ap2 pi (ap2 pi (ap1 isCert d)
                             (ap1 (eqTestF src (constTermFun1 t)) d))
                     (ap1 (eqTestF tgt (constTermFun1 uu)) d)))
parBody_app t uu d =
  ruleTrans (ax_C pi (C pi isCert (eqTestF src (constTermFun1 t)))
                     (eqTestF tgt (constTermFun1 uu)) d)
    (congL pi (ap1 (eqTestF tgt (constTermFun1 uu)) d)
       (ax_C pi isCert (eqTestF src (constTermFun1 t)) d))

------------------------------------------------------------------------
-- The object  E -Par predicate and the introduction rule.

Par : Term -> Term -> Formula
Par t uu = E (parBody t uu)

parIntro : (t uu : Tm) -> ParCert (code t) (code uu) ->
           Deriv (Par (code t) (code uu))
parIntro t uu pc =
  E_intro (parBody (code t) (code uu)) (wit pc) bodyZero
  where
    w : Term
    w = wit pc
    eSrc : Deriv (eqF (ap1 (eqTestF src (constTermFun1 (code t))) w) O)
    eSrc = eqTestF_const_zero src (code t) (noVarCode t) w (srcEq pc)
    eTgt : Deriv (eqF (ap1 (eqTestF tgt (constTermFun1 (code uu))) w) O)
    eTgt = eqTestF_const_zero tgt (code uu) (noVarCode uu) w (tgtEq pc)
    innerZero :
      Deriv (eqF (ap2 pi (ap1 isCert w)
                         (ap1 (eqTestF src (constTermFun1 (code t))) w)) O)
    innerZero =
      ruleTrans (congL pi (ap1 (eqTestF src (constTermFun1 (code t))) w) (valid pc))
        (ruleTrans (congR pi O eSrc) pi_O_O)
    outerZero :
      Deriv (eqF (ap2 pi (ap2 pi (ap1 isCert w)
                                 (ap1 (eqTestF src (constTermFun1 (code t))) w))
                         (ap1 (eqTestF tgt (constTermFun1 (code uu))) w)) O)
    outerZero =
      ruleTrans (congL pi (ap1 (eqTestF tgt (constTermFun1 (code uu))) w) innerZero)
        (ruleTrans (congR pi O eTgt) pi_O_O)
    bodyZero : Deriv (eqF (ap1 (parBody (code t) (code uu)) w) O)
    bodyZero = ruleTrans (parBody_app (code t) (code uu) w) outerZero
