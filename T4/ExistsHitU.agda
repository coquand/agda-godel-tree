{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.ExistsHitU -- the SUBJECT-UNIFORM bounded-existential indicator and its
-- one-hit lemma (CHAITIN-G1-ATOM-CORRECTION.md, recogniser plan C.1).
--
-- This generalises T4.ExistsHit: there the per-index test is a Fun1 at a
-- FIXED subject (the recursor's parameter slot is pinned to O); here the test
-- is a Fun2  test : Fun2  reading the CARRIED subject  x  ( = Fst of the
-- recursor package  pi x n , which  R  already threads as its unchanging first
-- argument).  This is exactly the  compHit_L(x)  of the corrected predicate:
--   compHit_L(x)  =  exists j <= B : test_comp(x, j) ,
-- the program  p  QUANTIFIED inside the bounded search (the test reads
-- thmT(enum j) and only checks the LHS code-SIZE -- no program is ever coded).
--
-- existsHitU x r  =  1   iff   some  j in 0..r  has  test (x, j) = 1 ,
-- a Fun2 recursing on  r  with the subject  x  carried:
--   existsHitU x O      = test (x, O)                                  (base)
--   existsHitU x (s n)  = condFork (pi 1 (existsHitU x n)) (test (x, s n))  (step)
--
-- one-hit (existsHitU_settles): a single witness  test (x, p0) = 1  with
-- p0 <= B  forces  existsHitU x B = 1 .  Proof = ONE object ruleIndNat with the
-- subject x carried as a SPECTATOR through the induction (never touched by the
-- recursion on r), the merged reachability invariant
--   Inv r = (leq p0 r) -> (existsHitU x r = 1) , at abstract Closed  x , p0 , B .
-- The shape is verbatim T4.ExistsHit.existsHit_settles plus one extra closeCoe
-- layer for the abstract closed subject  x  (the old subject was the literal O,
-- inert under substT; an abstract  x  is not, so it is coerced too).
--
-- This is the object kernel that discharges  T4.ChaitinG1Hit.chaitin_G1_hit 's
-- hypothesis  h : Deriv (compHit z0 = 1)  (the witnessed bounded-exists-intro),
-- with  compHit = compHitOf constB = C existsHitURec u constB : Fun1 .

module T4.ExistsHitU where

open import T4.Base
open import T4.Code   using ( falseF )
open import T4.PHP    using ( byCases )

open import T4.Counting
  using ( mapUnder1 ; mapUnder2 ; negToImpFalse ; impFalseToNeg_imp
        ; bCombThree )
open import T4.CountingObj
  using ( closeCoe ; trans2 ; identImp )

open import BRA3.Church          using ( pi ; sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchSubSucc   using ( T_sub_O )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.Dispatch        using ( condFork ; condFork_false ; condFork_true_nc )
open import BRA3.Contrapositive  using ( compI ; bComb ; bCombTwo ; liftP )

-- Section-0 order lemmas (imp-form) are subject-independent: reuse from
-- T4.ExistsHit verbatim (they reference only Counting/BRA3, not the test).
open import T4.ExistsHit       using ( le_one_neq_zero ; le_succ_neq_curry )

------------------------------------------------------------------------
-- SECTION 1.  The subject-uniform bounded-exists indicator.

module IndU
  (test : Fun2)
  (test_le_one : (x j : Term) -> Deriv (leq (ap2 test x j) (ap1 s O)))
  where

  -- the constant  1  function:  ap1 oneConst x = s (o x) = s O .
  oneConst : Fun1
  oneConst = compose1U s o

  -- base:  ap1 baseU x = test (x, O) .
  baseU : Fun1
  baseU = C test u o

  -- step: condFork (pi 1 prev) (test (Fst pkg) (s (Snd pkg))) , i.e. the
  -- right branch reads the CARRIED subject  Fst pkg = x  via  C test Fst (...) .
  stepEU : Fun2
  stepEU = Fan (Fan (Lift1 oneConst) v pi)
               (Lift1 (C test Fst (compose1U s Snd)))
               condFork

  existsHitURec : Fun2
  existsHitURec = R baseU stepEU pi

  existsHitU : Term -> Term -> Term
  existsHitU x r = ap2 existsHitURec x r

  -- stepEU evaluation at a packaged input  pi x n  and accumulator  prev .
  stepEU_eq :
    (x n prev : Term) ->
    Deriv (eqF (ap2 stepEU (ap2 pi x n) prev)
               (ap2 condFork (ap2 pi (ap1 s O) prev) (ap2 test x (ap1 s n))))
  stepEU_eq x n prev =
    let pkg : Term
        pkg = ap2 pi x n
        ZP : Fun2
        ZP = Fan (Lift1 oneConst) v pi
        WF : Fun1
        WF = C test Fst (compose1U s Snd)
        HF : Fun2
        HF = Lift1 WF

        e1 : Deriv (eqF (ap2 stepEU pkg prev)
                        (ap2 condFork (ap2 ZP pkg prev) (ap2 HF pkg prev)))
        e1 = axFan ZP HF condFork pkg prev

        zfan : Deriv (eqF (ap2 ZP pkg prev)
                          (ap2 pi (ap2 (Lift1 oneConst) pkg prev) (ap2 v pkg prev)))
        zfan = axFan (Lift1 oneConst) v pi pkg prev

        zleft : Deriv (eqF (ap2 (Lift1 oneConst) pkg prev) (ap1 s O))
        zleft = ruleTrans (axLift oneConst pkg prev)
                  (ruleTrans (axComp s o pkg) (cong1 s (ax_o pkg)))

        zright : Deriv (eqF (ap2 v pkg prev) prev)
        zright = ax_v pkg prev

        zp_eq : Deriv (eqF (ap2 ZP pkg prev) (ap2 pi (ap1 s O) prev))
        zp_eq = ruleTrans zfan
                  (ruleTrans (congL pi (ap2 v pkg prev) zleft)
                             (congR pi (ap1 s O) zright))

        -- right branch:  ap2 HF pkg prev = test (Fst pkg) (s (Snd pkg)) = test x (s n) .
        inner_s : Deriv (eqF (ap1 (compose1U s Snd) pkg) (ap1 s n))
        inner_s = ruleTrans (axComp s Snd pkg) (cong1 s (axSnd x n))

        hf_eq : Deriv (eqF (ap2 HF pkg prev) (ap2 test x (ap1 s n)))
        hf_eq = ruleTrans (axLift WF pkg prev)
                  (ruleTrans (ax_C test Fst (compose1U s Snd) pkg)
                    (ruleTrans (congL test (ap1 (compose1U s Snd) pkg) (axFst x n))
                               (congR test x inner_s)))
    in ruleTrans e1
         (ruleTrans (congL condFork (ap2 HF pkg prev) zp_eq)
                    (congR condFork (ap2 pi (ap1 s O) prev) hf_eq))

  existsHitU_at_O : (x : Term) -> Deriv (eqF (existsHitU x O) (ap2 test x O))
  existsHitU_at_O x =
    ruleTrans (ax_R_base baseU stepEU pi x)
              (ruleTrans (ax_C test u o x)
                (ruleTrans (congL test (ap1 o x) (ax_u x))
                           (congR test x (ax_o x))))

  existsHitU_succ :
    (x n : Term) ->
    Deriv (eqF (existsHitU x (ap1 s n))
               (ap2 condFork (ap2 pi (ap1 s O) (existsHitU x n)) (ap2 test x (ap1 s n))))
  existsHitU_succ x n =
    ruleTrans (ax_R_step baseU stepEU pi x n)
              (stepEU_eq x n (existsHitU x n))

  ----------------------------------------------------------------------
  -- SECTION 2.  The two condFork-reduction facts at a step.

  -- test (x, s m) fires  =>  existsHitU x (s m) = 1  (condFork-true; no IH).
  existsHitU_fires :
    (x m : Term) ->
    Deriv (imp (eqF (ap2 test x (ap1 s m)) (ap1 s O))
               (eqF (existsHitU x (ap1 s m)) (ap1 s O)))
  existsHitU_fires x m =
    let hyp : Formula
        hyp = eqF (ap2 test x (ap1 s m)) (ap1 s O)
        zz : Term
        zz = ap2 pi (ap1 s O) (existsHitU x m)
        condTm : Term
        condTm = ap2 condFork zz (ap2 test x (ap1 s m))
        base_eq : Deriv (eqF (existsHitU x (ap1 s m)) condTm)
        base_eq = existsHitU_succ x m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz (ap1 s O))))
        flag_rw = ax_eqCongR condFork (ap2 test x (ap1 s m)) (ap1 s O) zz
        reduce : Deriv (eqF (ap2 condFork zz (ap1 s O)) (ap1 s O))
        reduce = ruleTrans (condFork_true_nc zz O) (axFst (ap1 s O) (existsHitU x m))
    in compI (compI flag_rw
                (prependEqLeft (existsHitU x (ap1 s m)) condTm (ap2 condFork zz (ap1 s O)) base_eq))
             (appendEqRight (existsHitU x (ap1 s m)) (ap2 condFork zz (ap1 s O)) (ap1 s O) reduce)

  -- test (x, s m) = O (miss)  =>  existsHitU x (s m) = existsHitU x m .
  existsHitU_miss :
    (x m : Term) ->
    Deriv (imp (eqF (ap2 test x (ap1 s m)) O)
               (eqF (existsHitU x (ap1 s m)) (existsHitU x m)))
  existsHitU_miss x m =
    let hyp : Formula
        hyp = eqF (ap2 test x (ap1 s m)) O
        zz : Term
        zz = ap2 pi (ap1 s O) (existsHitU x m)
        condTm : Term
        condTm = ap2 condFork zz (ap2 test x (ap1 s m))
        base_eq : Deriv (eqF (existsHitU x (ap1 s m)) condTm)
        base_eq = existsHitU_succ x m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz O)))
        flag_rw = ax_eqCongR condFork (ap2 test x (ap1 s m)) O zz
        reduce : Deriv (eqF (ap2 condFork zz O) (existsHitU x m))
        reduce = ruleTrans (condFork_false zz) (axSnd (ap1 s O) (existsHitU x m))
    in compI (compI flag_rw
                (prependEqLeft (existsHitU x (ap1 s m)) condTm (ap2 condFork zz O) base_eq))
             (appendEqRight (existsHitU x (ap1 s m)) (ap2 condFork zz O) (existsHitU x m) reduce)

  ----------------------------------------------------------------------
  -- SECTION 3.  existsHitU_settles -- one witness forces the indicator to 1,
  -- with the abstract closed subject  x  carried as a spectator.

  existsHitU_settles :
    (x B p0 : Term) -> Closed x -> Closed B -> Closed p0 ->
    Deriv (eqF (ap2 test x p0) (ap1 s O)) ->
    Deriv (imp (leq p0 B) (eqF (existsHitU x B) (ap1 s O)))
  existsHitU_settles x B p0 clX clB clP0 hp0 = finalCoerced
    where
      Inv : Term -> Formula
      Inv r = imp (leq p0 r) (eqF (ap2 existsHitURec x r) (ap1 s O))

      n0 : Term
      n0 = var zero
      sn : Term
      sn = ap1 s n0

      ----------------------------------------------------------------
      -- base.
      baseReal : Deriv (Inv O)
      baseReal =
        let leqO_eq : Deriv (imp (leq p0 O) (eqF p0 O))
            leqO_eq = prependEqLeft p0 (ap2 sub p0 O) O (ruleSym (T_sub_O p0))
            e_testp0O : Deriv (imp (leq p0 O) (eqF (ap2 test x p0) (ap2 test x O)))
            e_testp0O = compI leqO_eq (ax_eqCongR test p0 O x)
            e_testO : Deriv (imp (leq p0 O) (eqF (ap2 test x O) (ap1 s O)))
            e_testO = bComb (compI e_testp0O
                       (ax_eqTrans (ap2 test x p0) (ap2 test x O) (ap1 s O)))
                       (liftP (leq p0 O) hp0)
        in compI e_testO
             (prependEqLeft (ap2 existsHitURec x O) (ap2 test x O) (ap1 s O) (existsHitU_at_O x))

      base : Deriv (substF zero O (Inv n0))
      base = closeCoe clX zero O
               (\ X -> imp (leq (substT zero O p0) O)
                          (eqF (ap2 existsHitURec X O) (ap1 s O)))
               (closeCoe clP0 zero O
                  (\ P -> imp (leq P O)
                             (eqF (ap2 existsHitURec x O) (ap1 s O)))
                  baseReal)

      ----------------------------------------------------------------
      -- step.
      Cn : Formula
      Cn = eqF (existsHitU x n0) (ap1 s O)
      Csn : Formula
      Csn = eqF (existsHitU x sn) (ap1 s O)
      phi1 : Formula
      phi1 = imp (leq p0 n0) Cn
      phi2 : Formula
      phi2 = leq p0 sn

      -- h2:  test (x, s n) /= O  =>  existsHitU x (s n) = 1  (no IH).
      h2 : Deriv (imp (neg (eqF (ap2 test x sn) O)) (imp phi1 (imp phi2 Csn)))
      h2 =
        let csn_neg : Deriv (imp (neg (eqF (ap2 test x sn) O)) Csn)
            csn_neg = compI (le_one_neq_zero (ap2 test x sn) (test_le_one x sn))
                            (existsHitU_fires x n0)
            kk : Deriv (imp Csn (imp phi1 (imp phi2 Csn)))
            kk = compI (axK Csn phi2) (axK (imp phi2 Csn) phi1)
        in compI csn_neg kk

      -- h1:  test (x, s n) = O  =>  recover  leq p0 n  (p0 /= s n) and use the IH.
      h1 : Deriv (imp (eqF (ap2 test x sn) O) (imp phi1 (imp phi2 Csn)))
      h1 =
        let h0 : Formula
            h0 = eqF (ap2 test x sn) O
            e_neq : Deriv (imp h0 (neg (eqF p0 sn)))
            e_neq =
              let phib : Formula
                  phib = eqF p0 sn
                  d1 : Deriv (imp h0 (imp phib (eqF (ap2 test x p0) (ap2 test x sn))))
                  d1 = liftP h0 (ax_eqCongR test p0 sn x)
                  d_h0 : Deriv (imp h0 (imp phib (eqF (ap2 test x sn) O)))
                  d_h0 = mapUnder1 h0 (axK h0 phib) (identImp h0)
                  d2 : Deriv (imp h0 (imp phib (eqF (ap2 test x p0) O)))
                  d2 = trans2 h0 phib (ap2 test x p0) (ap2 test x sn) O d1 d_h0
                  hp0Two : Deriv (imp h0 (imp phib (eqF (ap2 test x p0) (ap1 s O))))
                  hp0Two = liftP h0 (liftP phib hp0)
                  d3 : Deriv (imp h0 (imp phib (eqF (ap1 s O) O)))
                  d3 = bCombTwo
                         (mapUnder2 h0 phib
                            (ax_eqTrans (ap2 test x p0) (ap1 s O) O) hp0Two)
                         d2
                  contra : Deriv (imp h0 (imp phib falseF))
                  contra = mapUnder2 h0 phib
                             (negToImpFalse (eqF (ap1 s O) O) ax_succ_nonzero) d3
              in mapUnder1 h0 (impFalseToNeg_imp phib) contra
            e_leqn : Deriv (imp h0 (imp phi2 (leq p0 n0)))
            e_leqn = compI e_neq (le_succ_neq_curry p0 n0)
            d_leqn3 : Deriv (imp h0 (imp phi1 (imp phi2 (leq p0 n0))))
            d_leqn3 = mapUnder1 h0 (axK (imp phi2 (leq p0 n0)) phi1) e_leqn
            phi1Three : Deriv (imp h0 (imp phi1 (imp phi2 phi1)))
            phi1Three = liftP h0 (axK phi1 phi2)
            d_Cn : Deriv (imp h0 (imp phi1 (imp phi2 Cn)))
            d_Cn = bCombThree phi1Three d_leqn3
            e_csn : Deriv (imp h0 (imp Cn Csn))
            e_csn =
              let hh : Deriv (imp h0 (eqF (existsHitU x sn) (existsHitU x n0)))
                  hh = existsHitU_miss x n0
                  hhTwo : Deriv (imp h0 (imp Cn (eqF (existsHitU x sn) (existsHitU x n0))))
                  hhTwo = mapUnder1 h0
                           (axK (eqF (existsHitU x sn) (existsHitU x n0)) Cn) hh
                  cnTwo : Deriv (imp h0 (imp Cn (eqF (existsHitU x n0) (ap1 s O))))
                  cnTwo = liftP h0 (identImp Cn)
              in trans2 h0 Cn (existsHitU x sn) (existsHitU x n0) (ap1 s O)
                   hhTwo cnTwo
            e_csn3 : Deriv (imp h0 (imp phi1 (imp phi2 (imp Cn Csn))))
            e_csn3 = mapUnder1 h0
                       (compI (axK (imp Cn Csn) phi2)
                              (axK (imp phi2 (imp Cn Csn)) phi1)) e_csn
        in bCombThree e_csn3 d_Cn

      stepReal : Deriv (imp phi1 (imp phi2 Csn))
      stepReal = byCases (eqF (ap2 test x sn) O) (imp phi1 (imp phi2 Csn)) h1 h2

      step : Deriv (imp (Inv n0) (substF zero sn (Inv n0)))
      step = closeCoe clX zero sn
               (\ X -> imp (Inv n0)
                  (imp (leq (substT zero sn p0) sn)
                       (eqF (ap2 existsHitURec X sn) (ap1 s O))))
               (closeCoe clP0 zero sn
                  (\ P -> imp (Inv n0)
                     (imp (leq P sn) (eqF (ap2 existsHitURec x sn) (ap1 s O))))
                  stepReal)

      ind : Deriv (Inv n0)
      ind = ruleIndNat zero {P = Inv n0} base step

      finalSubst : Deriv (substF zero B (Inv n0))
      finalSubst = ruleInst zero B ind

      final1 : Deriv (imp (leq p0 B)
                          (eqF (ap2 existsHitURec (substT zero B x) B) (ap1 s O)))
      final1 =
        eqSubst
          (\ P -> Deriv (imp (leq P B)
                             (eqF (ap2 existsHitURec (substT zero B x) B) (ap1 s O))))
          (Closed.closedAt clP0 zero B) finalSubst

      finalCoerced : Deriv (imp (leq p0 B) (eqF (ap2 existsHitURec x B) (ap1 s O)))
      finalCoerced =
        eqSubst
          (\ X -> Deriv (imp (leq p0 B) (eqF (ap2 existsHitURec X B) (ap1 s O))))
          (Closed.closedAt clX zero B) final1

  ----------------------------------------------------------------------
  -- SECTION 4.  compHit packaging:  compHit = C existsHitURec u constB : Fun1 .
  -- For a constant-bound function  constB : Fun1  with  ap1 constB y = B  (B the
  -- search bound), this is the genuine  Fun1  whose  codeFun1  sits in the atom
  --   P = codeFXeqY1 compHit z0 (s O) ,
  -- and  ap1 compHit x = existsHitU x B .

  compHitOf : Fun1 -> Fun1
  compHitOf constB = C existsHitURec u constB

  compHitOf_eq :
    (constB : Fun1) (B : Term) ->
    ((y : Term) -> Deriv (eqF (ap1 constB y) B)) ->
    (x : Term) -> Deriv (eqF (ap1 (compHitOf constB) x) (existsHitU x B))
  compHitOf_eq constB B constB_eq x =
    ruleTrans (ax_C existsHitURec u constB x)
      (ruleTrans (congL existsHitURec (ap1 constB x) (ax_u x))
                 (congR existsHitURec x (constB_eq x)))
