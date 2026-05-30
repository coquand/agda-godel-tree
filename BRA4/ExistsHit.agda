{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- BRA4.ExistsHit -- the bounded-existential indicator and its one-hit lemma,
-- the OBJECT kernel of the witnessed bounded-exists-introduction that
-- discharges  BRA4.ChaitinG1Hit.chaitin_G1_hit 's hypothesis  h  (CHAITIN-G1-
-- ATOM-CORRECTION.md).
--
-- For a decidable 0/1 per-index test  test : Fun1  (the recogniser at a FIXED
-- subject -- "does candidate j witness compressibility of this subject"), the
-- bounded-exists indicator
--   existsHit r  =  1   iff   some  j in 0..r  has  test j = 1
-- is a primitive-recursive  Fun2  built exactly like  SpikeChaitin.lastPosRec ,
-- but ACCUMULATING the flag  1  (the constant  s o ) instead of the matched
-- position.  Its evaluation:
--   existsHit O      = test O                                       (base)
--   existsHit (s n)  = condFork (pi 1 (existsHit n)) (test (s n))   (step)
-- i.e. "if  test (s n)  fires the indicator is 1; else keep  existsHit n ".
--
-- one-hit (existsHit_settles): a single witness  test p0 = 1  with  p0 <= B
-- forces  existsHit B = 1 .  Proof = ONE object  ruleIndNat , the merged
-- reachability invariant  Inv r = (leq p0 r) -> (existsHit r = 1) , at the
-- abstract Closed bound  B  -- the SAME shape as  SpikeChaitin.search_settles
-- (this module is its bridge-free, flag-accumulating sibling).

module BRA4.ExistsHit where

open import BRA4.Base
open import BRA4.Code   using ( falseF )
open import BRA4.PHP    using ( byCases )

open import BRA4.Counting
  using ( antisym_curry ; nonzero_ge_one_imp
        ; mapUnder1 ; mapUnder2 ; negToImpFalse ; impFalseToNeg_imp
        ; bCombThree )
open import BRA4.CountingObj
  using ( closeCoe ; trans2 ; identImp ; swapImp )

open import BRA3.Church          using ( pi ; sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchSubSucc   using ( T57sub ; T_sub_O )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.ChurchStrictTrich using ( strictTrich )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.Dispatch        using ( condFork ; condFork_false ; condFork_true_nc )
open import BRA3.Contrapositive  using ( axExFalso ; compI ; bComb ; bCombTwo ; liftP )

------------------------------------------------------------------------
-- SECTION 0.  Order lemmas (Carneiro imp-form), lifted verbatim from
-- SpikeChaitin.Search Section 2 (they reference only Counting/BRA3, not the
-- test) so that  existsHit_settles  is self-contained.

-- x <= s O  and  x /= O  imply  x = s O .
le_one_neq_zero :
  (x : Term) -> Deriv (leq x (ap1 s O)) ->
  Deriv (imp (neg (eqF x O)) (eqF x (ap1 s O)))
le_one_neq_zero x leX1 =
  compI (nonzero_ge_one_imp x) (mp (antisym_curry x (ap1 s O)) leX1)

-- leq (s a) (s b)  implies  leq a b .
unsucc_leq : (a b : Term) -> Deriv (imp (leq (ap1 s a) (ap1 s b)) (leq a b))
unsucc_leq a b =
  prependEqLeft (ap2 sub a b) (ap2 sub (ap1 s a) (ap1 s b)) O
    (ruleSym (ruleInst2 zero a (suc zero) b refl T57sub))

-- a /= b  and  a <= b  imply  s a <= b .
lt_from_le_neq_curry :
  (a b : Term) -> Deriv (imp (neg (eqF a b)) (imp (leq a b) (leq (ap1 s a) b)))
lt_from_le_neq_curry a b =
  let neg' : Formula
      neg' = neg (eqF a b)
      phiL : Formula
      phiL = leq a b
      phiR : Formula
      phiR = leq b a
      exf : Deriv (imp neg' (imp (eqF a b) falseF))
      exf = swapImp (axExFalso (eqF a b) falseF)
      acN : Deriv (imp neg' (imp phiL (imp phiR (eqF a b))))
      acN = liftP neg' (antisym_curry a b)
      kk : Deriv (imp (imp (eqF a b) falseF)
                      (imp phiL (imp phiR (imp (eqF a b) falseF))))
      kk = compI (axK (imp (eqF a b) falseF) phiR)
                 (axK (imp phiR (imp (eqF a b) falseF)) phiL)
      exfN : Deriv (imp neg' (imp phiL (imp phiR (imp (eqF a b) falseF))))
      exfN = mapUnder1 neg' kk exf
      F2 : Deriv (imp neg' (imp phiL (imp phiR falseF)))
      F2 = bCombThree exfN acN
      NL : Deriv (imp neg' (imp phiL (neg phiR)))
      NL = mapUnder2 neg' phiL (impFalseToNeg_imp phiR) F2
      ST : Deriv (imp (neg phiR) (leq (ap1 s a) b))
      ST = ruleInst2 zero b (suc zero) a refl strictTrich
  in mapUnder2 neg' phiL ST NL

-- a /= s n  and  a <= s n  imply  a <= n .
le_succ_neq_curry :
  (a n : Term) ->
  Deriv (imp (neg (eqF a (ap1 s n))) (imp (leq a (ap1 s n)) (leq a n)))
le_succ_neq_curry a n =
  mapUnder2 (neg (eqF a (ap1 s n))) (leq a (ap1 s n))
    (unsucc_leq a n) (lt_from_le_neq_curry a (ap1 s n))

------------------------------------------------------------------------
-- SECTION 1.  The bounded-exists indicator, parametric in the test.

module Ind
  (test : Fun1)
  (test_le_one : (j : Term) -> Deriv (leq (ap1 test j) (ap1 s O)))
  where

  -- the constant  1  function:  ap1 oneConst x = s (o x) = s O .
  oneConst : Fun1
  oneConst = compose1U s o

  -- step: condFork (pi 1 prev) (test (s n)) .
  stepE : Fun2
  stepE = Fan (Fan (Lift1 oneConst) v pi)
              (Lift1 (compose1U test (compose1U s Snd)))
              condFork

  existsHitRec : Fun2
  existsHitRec = R (compose1U test o) stepE pi

  existsHit : Term -> Term
  existsHit r = ap2 existsHitRec O r

  -- stepE evaluation at a packaged input  pi x n  and accumulator  prev .
  stepE_eq :
    (x n prev : Term) ->
    Deriv (eqF (ap2 stepE (ap2 pi x n) prev)
               (ap2 condFork (ap2 pi (ap1 s O) prev) (ap1 test (ap1 s n))))
  stepE_eq x n prev =
    let pkg : Term
        pkg = ap2 pi x n
        ZP : Fun2
        ZP = Fan (Lift1 oneConst) v pi
        HF : Fun2
        HF = Lift1 (compose1U test (compose1U s Snd))

        e1 : Deriv (eqF (ap2 stepE pkg prev)
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

        hf_eq : Deriv (eqF (ap2 HF pkg prev) (ap1 test (ap1 s n)))
        hf_eq = ruleTrans (axLift (compose1U test (compose1U s Snd)) pkg prev)
                  (ruleTrans (axComp test (compose1U s Snd) pkg)
                    (cong1 test (ruleTrans (axComp s Snd pkg) (cong1 s (axSnd x n)))))
    in ruleTrans e1
         (ruleTrans (congL condFork (ap2 HF pkg prev) zp_eq)
                    (congR condFork (ap2 pi (ap1 s O) prev) hf_eq))

  existsHit_at_O : Deriv (eqF (existsHit O) (ap1 test O))
  existsHit_at_O =
    ruleTrans (ax_R_base (compose1U test o) stepE pi O)
              (ruleTrans (axComp test o O) (cong1 test (ax_o O)))

  existsHit_succ :
    (n : Term) ->
    Deriv (eqF (existsHit (ap1 s n))
               (ap2 condFork (ap2 pi (ap1 s O) (existsHit n)) (ap1 test (ap1 s n))))
  existsHit_succ n =
    ruleTrans (ax_R_step (compose1U test o) stepE pi O n)
              (stepE_eq O n (existsHit n))

  ----------------------------------------------------------------------
  -- SECTION 2.  The two condFork-reduction facts at a step.

  -- test (s m)  fires  =>  existsHit (s m) = 1  (condFork-true; no IH).
  existsHit_fires :
    (m : Term) ->
    Deriv (imp (eqF (ap1 test (ap1 s m)) (ap1 s O))
               (eqF (existsHit (ap1 s m)) (ap1 s O)))
  existsHit_fires m =
    let hyp : Formula
        hyp = eqF (ap1 test (ap1 s m)) (ap1 s O)
        zz : Term
        zz = ap2 pi (ap1 s O) (existsHit m)
        condTm : Term
        condTm = ap2 condFork zz (ap1 test (ap1 s m))
        base_eq : Deriv (eqF (existsHit (ap1 s m)) condTm)
        base_eq = existsHit_succ m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz (ap1 s O))))
        flag_rw = ax_eqCongR condFork (ap1 test (ap1 s m)) (ap1 s O) zz
        reduce : Deriv (eqF (ap2 condFork zz (ap1 s O)) (ap1 s O))
        reduce = ruleTrans (condFork_true_nc zz O) (axFst (ap1 s O) (existsHit m))
    in compI (compI flag_rw
                (prependEqLeft (existsHit (ap1 s m)) condTm (ap2 condFork zz (ap1 s O)) base_eq))
             (appendEqRight (existsHit (ap1 s m)) (ap2 condFork zz (ap1 s O)) (ap1 s O) reduce)

  -- test (s m) = O  (miss)  =>  existsHit (s m) = existsHit m .
  existsHit_miss :
    (m : Term) ->
    Deriv (imp (eqF (ap1 test (ap1 s m)) O)
               (eqF (existsHit (ap1 s m)) (existsHit m)))
  existsHit_miss m =
    let hyp : Formula
        hyp = eqF (ap1 test (ap1 s m)) O
        zz : Term
        zz = ap2 pi (ap1 s O) (existsHit m)
        condTm : Term
        condTm = ap2 condFork zz (ap1 test (ap1 s m))
        base_eq : Deriv (eqF (existsHit (ap1 s m)) condTm)
        base_eq = existsHit_succ m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz O)))
        flag_rw = ax_eqCongR condFork (ap1 test (ap1 s m)) O zz
        reduce : Deriv (eqF (ap2 condFork zz O) (existsHit m))
        reduce = ruleTrans (condFork_false zz) (axSnd (ap1 s O) (existsHit m))
    in compI (compI flag_rw
                (prependEqLeft (existsHit (ap1 s m)) condTm (ap2 condFork zz O) base_eq))
             (appendEqRight (existsHit (ap1 s m)) (ap2 condFork zz O) (existsHit m) reduce)

  ----------------------------------------------------------------------
  -- SECTION 3.  existsHit_settles -- one witness forces the indicator to 1.

  existsHit_settles :
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (eqF (ap1 test p0) (ap1 s O)) ->
    Deriv (imp (leq p0 B) (eqF (existsHit B) (ap1 s O)))
  existsHit_settles B p0 clB clP0 hp0 = finalCoerced
    where
      Inv : Term -> Formula
      Inv r = imp (leq p0 r) (eqF (ap2 existsHitRec O r) (ap1 s O))

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
            e_testp0O : Deriv (imp (leq p0 O) (eqF (ap1 test p0) (ap1 test O)))
            e_testp0O = compI leqO_eq (ax_eqCong1 test p0 O)
            e_testO : Deriv (imp (leq p0 O) (eqF (ap1 test O) (ap1 s O)))
            e_testO = bComb (compI e_testp0O
                       (ax_eqTrans (ap1 test p0) (ap1 test O) (ap1 s O)))
                       (liftP (leq p0 O) hp0)
        in compI e_testO
             (prependEqLeft (ap2 existsHitRec O O) (ap1 test O) (ap1 s O) existsHit_at_O)

      base : Deriv (substF zero O (Inv n0))
      base = closeCoe clP0 zero O
               (\ X -> imp (leq X O) (eqF (ap2 existsHitRec O O) (ap1 s O)))
               baseReal

      ----------------------------------------------------------------
      -- step.
      Cn : Formula
      Cn = eqF (existsHit n0) (ap1 s O)
      Csn : Formula
      Csn = eqF (existsHit sn) (ap1 s O)
      phi1 : Formula
      phi1 = imp (leq p0 n0) Cn
      phi2 : Formula
      phi2 = leq p0 sn

      -- h2:  test (s n) /= O  =>  existsHit (s n) = 1  (no IH).
      h2 : Deriv (imp (neg (eqF (ap1 test sn) O)) (imp phi1 (imp phi2 Csn)))
      h2 =
        let csn_neg : Deriv (imp (neg (eqF (ap1 test sn) O)) Csn)
            csn_neg = compI (le_one_neq_zero (ap1 test sn) (test_le_one sn))
                            (existsHit_fires n0)
            kk : Deriv (imp Csn (imp phi1 (imp phi2 Csn)))
            kk = compI (axK Csn phi2) (axK (imp phi2 Csn) phi1)
        in compI csn_neg kk

      -- h1:  test (s n) = O  =>  recover  leq p0 n  (p0 /= s n) and use the IH.
      h1 : Deriv (imp (eqF (ap1 test sn) O) (imp phi1 (imp phi2 Csn)))
      h1 =
        let h0 : Formula
            h0 = eqF (ap1 test sn) O
            e_neq : Deriv (imp h0 (neg (eqF p0 sn)))
            e_neq =
              let phib : Formula
                  phib = eqF p0 sn
                  d1 : Deriv (imp h0 (imp phib (eqF (ap1 test p0) (ap1 test sn))))
                  d1 = liftP h0 (ax_eqCong1 test p0 sn)
                  d_h0 : Deriv (imp h0 (imp phib (eqF (ap1 test sn) O)))
                  d_h0 = mapUnder1 h0 (axK h0 phib) (identImp h0)
                  d2 : Deriv (imp h0 (imp phib (eqF (ap1 test p0) O)))
                  d2 = trans2 h0 phib (ap1 test p0) (ap1 test sn) O d1 d_h0
                  hp0Two : Deriv (imp h0 (imp phib (eqF (ap1 test p0) (ap1 s O))))
                  hp0Two = liftP h0 (liftP phib hp0)
                  d3 : Deriv (imp h0 (imp phib (eqF (ap1 s O) O)))
                  d3 = bCombTwo
                         (mapUnder2 h0 phib
                            (ax_eqTrans (ap1 test p0) (ap1 s O) O) hp0Two)
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
              let hh : Deriv (imp h0 (eqF (existsHit sn) (existsHit n0)))
                  hh = existsHit_miss n0
                  hhTwo : Deriv (imp h0 (imp Cn (eqF (existsHit sn) (existsHit n0))))
                  hhTwo = mapUnder1 h0
                           (axK (eqF (existsHit sn) (existsHit n0)) Cn) hh
                  cnTwo : Deriv (imp h0 (imp Cn (eqF (existsHit n0) (ap1 s O))))
                  cnTwo = liftP h0 (identImp Cn)
              in trans2 h0 Cn (existsHit sn) (existsHit n0) (ap1 s O)
                   hhTwo cnTwo
            e_csn3 : Deriv (imp h0 (imp phi1 (imp phi2 (imp Cn Csn))))
            e_csn3 = mapUnder1 h0
                       (compI (axK (imp Cn Csn) phi2)
                              (axK (imp phi2 (imp Cn Csn)) phi1)) e_csn
        in bCombThree e_csn3 d_Cn

      stepReal : Deriv (imp phi1 (imp phi2 Csn))
      stepReal = byCases (eqF (ap1 test sn) O) (imp phi1 (imp phi2 Csn)) h1 h2

      step : Deriv (imp (Inv n0) (substF zero sn (Inv n0)))
      step = closeCoe clP0 zero sn
               (\ X -> imp (Inv n0)
                  (imp (leq X sn) (eqF (ap2 existsHitRec O sn) (ap1 s O))))
               stepReal

      ind : Deriv (Inv n0)
      ind = ruleIndNat zero {P = Inv n0} base step

      finalSubst : Deriv (substF zero B (Inv n0))
      finalSubst = ruleInst zero B ind

      finalCoerced : Deriv (imp (leq p0 B) (eqF (ap2 existsHitRec O B) (ap1 s O)))
      finalCoerced =
        eqSubst
          (\ X -> Deriv (imp (leq X B) (eqF (ap2 existsHitRec O B) (ap1 s O))))
          (Closed.closedAt clP0 zero B) finalSubst
