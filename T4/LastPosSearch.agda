{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.LastPosSearch -- the reusable find-(last)-hit bounded search kernel,
-- parametric ONLY in a 0/1 indicator  hit : Fun1  (no out / enum / bridge).
--
-- This is T4.SpikeChaitin's search machinery (SS1, SS3, SS4) extracted into a
-- standalone module: the  condFork -based  lastPosRec  recursor and its
-- correctness  search_settles  (a single witness  hit p0 = 1  with  p0 <= B
-- forces  hit (lastpos B) = 1).  SpikeChaitin folded this together with the
-- KR-A definability layer (out / enum / atomForm / bridge); the standard-route
-- (evalU) Chaitin construction needs the SAME search but with a DIFFERENT,
-- concrete recogniser  hit := hitK L (out_L L)  (T4.KRecog), so we factor the
-- search out.  The proof body is verbatim SpikeChaitin's; the only changes are
--   * the module parameters are  (hit : Fun1)(hit_le_one)  alone, and
--   * the two order lemmas  le_one_neq_zero / le_succ_neq_curry  are IMPORTED
--     from T4.ExistsHit (SpikeChaitin re-proved them locally).
--
--   ap2 lastPosRec x O      = O
--   ap2 lastPosRec x (s n)  = condFork (pi (s n) prev) (hit (s n))    (prev = ap2 lastPosRec x n)
-- "if  hit (s n)  fires, record the new top index  s n ; else keep prev".
-- The first argument  x  is unused (only  Snd pkg = n  matters); fix  x := O .

module T4.LastPosSearch where

open import T4.Base
open import T4.Code   using ( falseF )
open import T4.PHP    using ( byCases )

open import T4.Counting
  using ( mapUnder1 ; mapUnder2 ; negToImpFalse ; impFalseToNeg_imp
        ; bCombThree ; under1_trans )
open import T4.CountingObj
  using ( closeCoe ; trans2 ; identImp )

-- The two Section-2 order lemmas (imp-form) are subject-independent: import
-- them rather than re-prove (SpikeChaitin predates the ExistsHit factoring).
open import T4.ExistsHit       using ( le_one_neq_zero ; le_succ_neq_curry )

open import BRA3.Church          using ( pi ; sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchSubSucc   using ( T_sub_O )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.Dispatch        using ( condFork ; condFork_false ; condFork_true_nc )
open import BRA3.Contrapositive  using ( compI ; bComb ; bCombTwo ; liftP )

------------------------------------------------------------------------
-- The search, parametric in the 0/1 indicator  hit .

module LP
  (hit : Fun1)
  (hit_le_one : (j : Term) -> Deriv (leq (ap1 hit j) (ap1 s O)))
  where

  ------------------------------------------------------------------------
  -- SECTION 1.  The find-(last)-hit search recursor.

  stepH : Fun2
  stepH = Fan (Fan (Lift1 (compose1U s Snd)) v pi)
              (Lift1 (compose1U hit (compose1U s Snd)))
              condFork

  lastPosRec : Fun2
  lastPosRec = R o stepH pi

  lastpos : Term -> Term
  lastpos r = ap2 lastPosRec O r

  -- stepH evaluation at a packaged input  pi x n  and accumulator  prev .
  stepH_eq :
    (x n prev : Term) ->
    Deriv (eqF (ap2 stepH (ap2 pi x n) prev)
               (ap2 condFork (ap2 pi (ap1 s n) prev) (ap1 hit (ap1 s n))))
  stepH_eq x n prev =
    let pkg : Term
        pkg = ap2 pi x n
        ZP : Fun2
        ZP = Fan (Lift1 (compose1U s Snd)) v pi
        HF : Fun2
        HF = Lift1 (compose1U hit (compose1U s Snd))

        e1 : Deriv (eqF (ap2 stepH pkg prev)
                        (ap2 condFork (ap2 ZP pkg prev) (ap2 HF pkg prev)))
        e1 = axFan ZP HF condFork pkg prev

        zfan : Deriv (eqF (ap2 ZP pkg prev)
                          (ap2 pi (ap2 (Lift1 (compose1U s Snd)) pkg prev)
                                  (ap2 v pkg prev)))
        zfan = axFan (Lift1 (compose1U s Snd)) v pi pkg prev

        zleft : Deriv (eqF (ap2 (Lift1 (compose1U s Snd)) pkg prev) (ap1 s n))
        zleft = ruleTrans (axLift (compose1U s Snd) pkg prev)
                  (ruleTrans (axComp s Snd pkg) (cong1 s (axSnd x n)))

        zright : Deriv (eqF (ap2 v pkg prev) prev)
        zright = ax_v pkg prev

        zp_eq : Deriv (eqF (ap2 ZP pkg prev) (ap2 pi (ap1 s n) prev))
        zp_eq = ruleTrans zfan
                  (ruleTrans (congL pi (ap2 v pkg prev) zleft)
                             (congR pi (ap1 s n) zright))

        hf_eq : Deriv (eqF (ap2 HF pkg prev) (ap1 hit (ap1 s n)))
        hf_eq = ruleTrans (axLift (compose1U hit (compose1U s Snd)) pkg prev)
                  (ruleTrans (axComp hit (compose1U s Snd) pkg)
                    (cong1 hit (ruleTrans (axComp s Snd pkg) (cong1 s (axSnd x n)))))
    in ruleTrans e1
         (ruleTrans (congL condFork (ap2 HF pkg prev) zp_eq)
                    (congR condFork (ap2 pi (ap1 s n) prev) hf_eq))

  lastpos_at_O : (x : Term) -> Deriv (eqF (ap2 lastPosRec x O) O)
  lastpos_at_O x = ruleTrans (ax_R_base o stepH pi x) (ax_o x)

  lastpos_succ :
    (x n : Term) ->
    Deriv (eqF (ap2 lastPosRec x (ap1 s n))
               (ap2 condFork (ap2 pi (ap1 s n) (ap2 lastPosRec x n))
                             (ap1 hit (ap1 s n))))
  lastpos_succ x n =
    ruleTrans (ax_R_step o stepH pi x n)
              (stepH_eq x n (ap2 lastPosRec x n))

  ------------------------------------------------------------------------
  -- SECTION 2.  The two condFork-reduction facts at a step.

  -- if  hit (s m)  fires (= s O),  lastpos (s m) = s m , so it is a match.
  hitfires :
    (m : Term) ->
    Deriv (imp (eqF (ap1 hit (ap1 s m)) (ap1 s O))
               (eqF (ap1 hit (lastpos (ap1 s m))) (ap1 s O)))
  hitfires m =
    let hyp : Formula
        hyp = eqF (ap1 hit (ap1 s m)) (ap1 s O)
        zz : Term
        zz = ap2 pi (ap1 s m) (lastpos m)
        condTm : Term
        condTm = ap2 condFork zz (ap1 hit (ap1 s m))
        base_eq : Deriv (eqF (lastpos (ap1 s m)) condTm)
        base_eq = lastpos_succ O m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz (ap1 s O))))
        flag_rw = ax_eqCongR condFork (ap1 hit (ap1 s m)) (ap1 s O) zz
        reduce : Deriv (eqF (ap2 condFork zz (ap1 s O)) (ap1 s m))
        reduce = ruleTrans (condFork_true_nc zz O) (axFst (ap1 s m) (lastpos m))
        e_lp : Deriv (imp hyp (eqF (lastpos (ap1 s m)) (ap1 s m)))
        e_lp = compI (compI flag_rw
                  (prependEqLeft (lastpos (ap1 s m)) condTm (ap2 condFork zz (ap1 s O)) base_eq))
                  (appendEqRight (lastpos (ap1 s m)) (ap2 condFork zz (ap1 s O)) (ap1 s m) reduce)
        e_hitlp : Deriv (imp hyp (eqF (ap1 hit (lastpos (ap1 s m))) (ap1 hit (ap1 s m))))
        e_hitlp = compI e_lp (ax_eqCong1 hit (lastpos (ap1 s m)) (ap1 s m))
    in under1_trans e_hitlp (identImp hyp)

  -- if  hit (s m) = O ,  lastpos (s m) = lastpos m  (keep the old position).
  lastpos_miss :
    (m : Term) ->
    Deriv (imp (eqF (ap1 hit (ap1 s m)) O)
               (eqF (lastpos (ap1 s m)) (lastpos m)))
  lastpos_miss m =
    let hyp : Formula
        hyp = eqF (ap1 hit (ap1 s m)) O
        zz : Term
        zz = ap2 pi (ap1 s m) (lastpos m)
        condTm : Term
        condTm = ap2 condFork zz (ap1 hit (ap1 s m))
        base_eq : Deriv (eqF (lastpos (ap1 s m)) condTm)
        base_eq = lastpos_succ O m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz O)))
        flag_rw = ax_eqCongR condFork (ap1 hit (ap1 s m)) O zz
        reduce : Deriv (eqF (ap2 condFork zz O) (lastpos m))
        reduce = ruleTrans (condFork_false zz) (axSnd (ap1 s m) (lastpos m))
    in compI (compI flag_rw
         (prependEqLeft (lastpos (ap1 s m)) condTm (ap2 condFork zz O) base_eq))
         (appendEqRight (lastpos (ap1 s m)) (ap2 condFork zz O) (lastpos m) reduce)

  ------------------------------------------------------------------------
  -- SECTION 3.  search_settles -- the MERGED reachability + match-validity
  -- invariant.  ONE object  ruleIndNat , open in the range variable, at the
  -- abstract Closed Bin  B  (closeCoe on the witness position  p0 ).

  search_settles :
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (eqF (ap1 hit p0) (ap1 s O)) ->
    Deriv (imp (leq p0 B) (eqF (ap1 hit (lastpos B)) (ap1 s O)))
  search_settles B p0 clB clP0 hp0 = finalCoerced
    where
      Inv : Term -> Formula
      Inv r = imp (leq p0 r) (eqF (ap1 hit (ap2 lastPosRec O r)) (ap1 s O))

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
            e_hitp0O : Deriv (imp (leq p0 O) (eqF (ap1 hit p0) (ap1 hit O)))
            e_hitp0O = compI leqO_eq (ax_eqCong1 hit p0 O)
            e_hitO : Deriv (imp (leq p0 O) (eqF (ap1 hit O) (ap1 s O)))
            e_hitO = bComb (compI e_hitp0O
                       (ax_eqTrans (ap1 hit p0) (ap1 hit O) (ap1 s O)))
                       (liftP (leq p0 O) hp0)
            lp0_eq : Deriv (eqF (ap1 hit (ap2 lastPosRec O O)) (ap1 hit O))
            lp0_eq = cong1 hit (lastpos_at_O O)
        in compI e_hitO
             (prependEqLeft (ap1 hit (ap2 lastPosRec O O)) (ap1 hit O) (ap1 s O) lp0_eq)

      base : Deriv (substF zero O (Inv n0))
      base = closeCoe clP0 zero O
               (\ X -> imp (leq X O) (eqF (ap1 hit (ap2 lastPosRec O O)) (ap1 s O)))
               baseReal

      ----------------------------------------------------------------
      -- step.
      Cn : Formula
      Cn = eqF (ap1 hit (lastpos n0)) (ap1 s O)
      Csn : Formula
      Csn = eqF (ap1 hit (lastpos sn)) (ap1 s O)
      phi1 : Formula
      phi1 = imp (leq p0 n0) Cn
      phi2 : Formula
      phi2 = leq p0 sn

      -- h2:  hit (s n) /= O  =>  the new top index is the match (no IH needed).
      h2 : Deriv (imp (neg (eqF (ap1 hit sn) O)) (imp phi1 (imp phi2 Csn)))
      h2 =
        let csn_neg : Deriv (imp (neg (eqF (ap1 hit sn) O)) Csn)
            csn_neg = compI (le_one_neq_zero (ap1 hit sn) (hit_le_one sn))
                            (hitfires n0)
            kk : Deriv (imp Csn (imp phi1 (imp phi2 Csn)))
            kk = compI (axK Csn phi2) (axK (imp phi2 Csn) phi1)
        in compI csn_neg kk

      -- h1:  hit (s n) = O  =>  recover  leq p0 n  (p0 /= s n) and use the IH.
      h1 : Deriv (imp (eqF (ap1 hit sn) O) (imp phi1 (imp phi2 Csn)))
      h1 =
        let h0 : Formula
            h0 = eqF (ap1 hit sn) O
            e_neq : Deriv (imp h0 (neg (eqF p0 sn)))
            e_neq =
              let phib : Formula
                  phib = eqF p0 sn
                  d1 : Deriv (imp h0 (imp phib (eqF (ap1 hit p0) (ap1 hit sn))))
                  d1 = liftP h0 (ax_eqCong1 hit p0 sn)
                  d_h0 : Deriv (imp h0 (imp phib (eqF (ap1 hit sn) O)))
                  d_h0 = mapUnder1 h0 (axK h0 phib) (identImp h0)
                  d2 : Deriv (imp h0 (imp phib (eqF (ap1 hit p0) O)))
                  d2 = trans2 h0 phib (ap1 hit p0) (ap1 hit sn) O d1 d_h0
                  hp0Two : Deriv (imp h0 (imp phib (eqF (ap1 hit p0) (ap1 s O))))
                  hp0Two = liftP h0 (liftP phib hp0)
                  d3 : Deriv (imp h0 (imp phib (eqF (ap1 s O) O)))
                  d3 = bCombTwo
                         (mapUnder2 h0 phib
                            (ax_eqTrans (ap1 hit p0) (ap1 s O) O) hp0Two)
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
              let hh : Deriv (imp h0 (eqF (ap1 hit (lastpos sn)) (ap1 hit (lastpos n0))))
                  hh = compI (lastpos_miss n0)
                             (ax_eqCong1 hit (lastpos sn) (lastpos n0))
                  hhTwo : Deriv (imp h0 (imp Cn (eqF (ap1 hit (lastpos sn)) (ap1 hit (lastpos n0)))))
                  hhTwo = mapUnder1 h0
                           (axK (eqF (ap1 hit (lastpos sn)) (ap1 hit (lastpos n0))) Cn) hh
                  cnTwo : Deriv (imp h0 (imp Cn (eqF (ap1 hit (lastpos n0)) (ap1 s O))))
                  cnTwo = liftP h0 (identImp Cn)
              in trans2 h0 Cn (ap1 hit (lastpos sn)) (ap1 hit (lastpos n0)) (ap1 s O)
                   hhTwo cnTwo
            e_csn3 : Deriv (imp h0 (imp phi1 (imp phi2 (imp Cn Csn))))
            e_csn3 = mapUnder1 h0
                       (compI (axK (imp Cn Csn) phi2)
                              (axK (imp phi2 (imp Cn Csn)) phi1)) e_csn
        in bCombThree e_csn3 d_Cn

      stepReal : Deriv (imp phi1 (imp phi2 Csn))
      stepReal = byCases (eqF (ap1 hit sn) O) (imp phi1 (imp phi2 Csn)) h1 h2

      step : Deriv (imp (Inv n0) (substF zero sn (Inv n0)))
      step = closeCoe clP0 zero sn
               (\ X -> imp (Inv n0)
                  (imp (leq X sn) (eqF (ap1 hit (ap2 lastPosRec O sn)) (ap1 s O))))
               stepReal

      ind : Deriv (Inv n0)
      ind = ruleIndNat zero {P = Inv n0} base step

      finalSubst : Deriv (substF zero B (Inv n0))
      finalSubst = ruleInst zero B ind

      finalCoerced : Deriv (imp (leq p0 B) (eqF (ap1 hit (ap2 lastPosRec O B)) (ap1 s O)))
      finalCoerced =
        eqSubst
          (\ X -> Deriv (imp (leq X B) (eqF (ap1 hit (ap2 lastPosRec O B)) (ap1 s O))))
          (Closed.closedAt clP0 zero B) finalSubst
