{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.FirstHit -- the LEAST-NUMBER lemma for a decidable 0/1 predicate, as a
-- STANDALONE lemma (no K, no thmT, no interpreter).
--
-- For  p : Fun1  with  p <= 1 , and a witness  B  with  p B = s O  (the property
-- "p x = s O" holds at B), there is a FIRST  w1  (= g (s B)) with  p w1 = s O  and
-- p x = O  for all  x < w1 .
--
-- The search recursor (Coquand's clean form -- no found-flag; the condFork flag is
-- p (g n) itself, 0/1 by the hypothesis):
--   g O      = O
--   g (s n)  = if p (g n) = s O then g n  (freeze) else s n  (advance)
--            = condFork (pi (g n) (s n)) (p (g n))
--
-- Invariants (each ONE ruleIndNat on n, byCases on p (g n) <= 1):
--   compInv n : p (g n) = O  ->  g n = n        (frontier when current isn't a hit)
--   firstness x n : leq (s x) (g n)  ->  p x = O     (carried per-x: no object forall)

module BRA4.FirstHit where

open import BRA4.Base

open import BRA3.Church          using ( pi ; sub ; predecessor ; T_p_S_v0 ; T_p_O )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchSubSucc   using ( T_sub_O )
open import BRA3.ChurchT80       using ( exFalsoFromSO )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.PairAlgebra     using ( axFst ; axSnd ; compose1U ; compose1U_eq
                                       ; Fan ; Lift1 ; Lift2 ; axFan ; axLift ; axLift2
                                       ; axComp )
open import BRA3.Dispatch        using ( condFork ; condFork_true_nc ; condFork_false )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive  using ( compI ; liftP ; bComb ; bCombTwo ; identP ; axExFalso )
open import BRA4.Counting        using ( mapUnder1 ; mapUnder2 ; bCombThree )
open import BRA4.CountingObj      using ( trans2 )
open import BRA4.ExistsHit       using ( le_one_neq_zero ; lt_from_le_neq_curry ; unsucc_leq )
open import BRA4.PHP             using ( byCases )

module Search
  (p : Fun1)
  (p_le_one : (r : Term) -> Deriv (leq (ap1 p r) (ap1 s O)))
  where

  ----------------------------------------------------------------------
  -- SECTION 1.  The search recursor.

  -- ap2 gStep (pi x n) prev = condFork (pi prev (s n)) (p prev)
  gStep : Fun2
  gStep = Fan (Fan v (Lift1 (compose1U s Snd)) pi) (Lift2 p) condFork

  gRec : Fun2
  gRec = R o gStep pi

  g : Term -> Term
  g r = ap2 gRec O r

  g_at_O : Deriv (eqF (g O) O)
  g_at_O = ruleTrans (ax_R_base o gStep pi O) (ax_o O)

  gStep_eq :
    (x n prev : Term) ->
    Deriv (eqF (ap2 gStep (ap2 pi x n) prev)
               (ap2 condFork (ap2 pi prev (ap1 s n)) (ap1 p prev)))
  gStep_eq x n prev =
    let pkg : Term
        pkg = ap2 pi x n
        ZP : Fun2
        ZP = Fan v (Lift1 (compose1U s Snd)) pi
        e1 : Deriv (eqF (ap2 gStep pkg prev)
                        (ap2 condFork (ap2 ZP pkg prev) (ap2 (Lift2 p) pkg prev)))
        e1 = axFan ZP (Lift2 p) condFork pkg prev
        zfan : Deriv (eqF (ap2 ZP pkg prev)
                          (ap2 pi (ap2 v pkg prev)
                                  (ap2 (Lift1 (compose1U s Snd)) pkg prev)))
        zfan = axFan v (Lift1 (compose1U s Snd)) pi pkg prev
        zleft : Deriv (eqF (ap2 v pkg prev) prev)
        zleft = ax_v pkg prev
        zright : Deriv (eqF (ap2 (Lift1 (compose1U s Snd)) pkg prev) (ap1 s n))
        zright = ruleTrans (axLift (compose1U s Snd) pkg prev)
                   (ruleTrans (axComp s Snd pkg) (cong1 s (axSnd x n)))
        zp_eq : Deriv (eqF (ap2 ZP pkg prev) (ap2 pi prev (ap1 s n)))
        zp_eq = ruleTrans zfan
                  (ruleTrans (congL pi (ap2 (Lift1 (compose1U s Snd)) pkg prev) zleft)
                             (congR pi prev zright))
        flag_eq : Deriv (eqF (ap2 (Lift2 p) pkg prev) (ap1 p prev))
        flag_eq = axLift2 p pkg prev
    in ruleTrans e1
         (ruleTrans (congL condFork (ap2 (Lift2 p) pkg prev) zp_eq)
                    (congR condFork (ap2 pi prev (ap1 s n)) flag_eq))

  g_at_succ :
    (n : Term) ->
    Deriv (eqF (g (ap1 s n))
               (ap2 condFork (ap2 pi (g n) (ap1 s n)) (ap1 p (g n))))
  g_at_succ n =
    ruleTrans (ax_R_step o gStep pi O n) (gStep_eq O n (g n))

  ----------------------------------------------------------------------
  -- SECTION 2.  Companion:  p (g n) = O  ->  g n = n .

  compInvObj : Deriv (imp (eqF (ap1 p (g (var zero))) O) (eqF (g (var zero)) (var zero)))
  compInvObj = ruleIndNat zero {P = Inv} base step
    where
      n0 : Term
      n0 = var zero
      Inv : Formula
      Inv = imp (eqF (ap1 p (g n0)) O) (eqF (g n0) n0)

      base : Deriv (imp (eqF (ap1 p (g O)) O) (eqF (g O) O))
      base = liftP (eqF (ap1 p (g O)) O) g_at_O

      -- GOAL = Inv (s n0)
      sn : Term
      sn = ap1 s n0
      hsn : Formula
      hsn = eqF (ap1 p (g sn)) O
      goalEq : Formula
      goalEq = eqF (g sn) sn
      zz : Term
      zz = ap2 pi (g n0) sn

      -- miss:  p (g n0) = O  =>  g (s n0) = s n0  (condFork_false).
      eMiss : Deriv (imp (eqF (ap1 p (g n0)) O) goalEq)
      eMiss =
        let flagRw : Deriv (imp (eqF (ap1 p (g n0)) O)
                        (eqF (ap2 condFork zz (ap1 p (g n0))) (ap2 condFork zz O)))
            flagRw = ax_eqCongR condFork (ap1 p (g n0)) O zz
            reduceF : Deriv (eqF (ap2 condFork zz O) sn)
            reduceF = ruleTrans (condFork_false zz) (axSnd (g n0) sn)
        in compI (compI flagRw
              (prependEqLeft (g sn) (ap2 condFork zz (ap1 p (g n0))) (ap2 condFork zz O)
                             (g_at_succ n0)))
              (appendEqRight (g sn) (ap2 condFork zz O) sn reduceF)

      h_miss : Deriv (imp (eqF (ap1 p (g n0)) O) (imp hsn goalEq))
      h_miss = mapUnder1 (eqF (ap1 p (g n0)) O) (axK goalEq hsn) eMiss

      -- hit:  p (g n0) /= O  =>  g (s n0) = g n0 ; then hsn contradicts.
      eHit : Deriv (imp (neg (eqF (ap1 p (g n0)) O)) (eqF (g sn) (g n0)))
      eHit =
        let eHitChain : Deriv (imp (eqF (ap1 p (g n0)) (ap1 s O)) (eqF (g sn) (g n0)))
            eHitChain =
              let flagRw' : Deriv (imp (eqF (ap1 p (g n0)) (ap1 s O))
                              (eqF (ap2 condFork zz (ap1 p (g n0))) (ap2 condFork zz (ap1 s O))))
                  flagRw' = ax_eqCongR condFork (ap1 p (g n0)) (ap1 s O) zz
                  reduceT : Deriv (eqF (ap2 condFork zz (ap1 s O)) (g n0))
                  reduceT = ruleTrans (condFork_true_nc zz O) (axFst (g n0) sn)
              in compI (compI flagRw'
                    (prependEqLeft (g sn) (ap2 condFork zz (ap1 p (g n0)))
                                   (ap2 condFork zz (ap1 s O)) (g_at_succ n0)))
                    (appendEqRight (g sn) (ap2 condFork zz (ap1 s O)) (g n0) reduceT)
        in compI (le_one_neq_zero (ap1 p (g n0)) (p_le_one (g n0))) eHitChain

      d1 : Deriv (imp (neg (eqF (ap1 p (g n0)) O)) (eqF (ap1 p (g sn)) (ap1 p (g n0))))
      d1 = compI eHit (ax_eqCong1 p (g sn) (g n0))

      d_pgnO : Deriv (imp (neg (eqF (ap1 p (g n0)) O)) (imp hsn (eqF (ap1 p (g n0)) O)))
      d_pgnO = compI d1 (ax_eqTrans (ap1 p (g sn)) (ap1 p (g n0)) O)

      h_hit : Deriv (imp (neg (eqF (ap1 p (g n0)) O)) (imp hsn goalEq))
      h_hit =
        let nh : Formula
            nh = neg (eqF (ap1 p (g n0)) O)
            e2 : Deriv (imp nh (imp hsn (imp nh goalEq)))
            e2 = mapUnder2 nh hsn (axExFalso (eqF (ap1 p (g n0)) O) goalEq) d_pgnO
            e3 : Deriv (imp nh (imp hsn nh))
            e3 = axK nh hsn
        in bCombTwo e2 e3

      step : Deriv (imp Inv (imp hsn goalEq))
      step = liftP Inv (byCases (eqF (ap1 p (g n0)) O) (imp hsn goalEq) h_miss h_hit)

  compInv : (n : Term) -> Deriv (imp (eqF (ap1 p (g n)) O) (eqF (g n) n))
  compInv n = ruleInst zero n compInvObj

  ----------------------------------------------------------------------
  -- SECTION 3.  Freeze / advance step lemmas, and small helpers.

  -- advance: p (g n) = O  =>  g (s n) = s n .
  gSuccMiss : (n : Term) -> Deriv (imp (eqF (ap1 p (g n)) O) (eqF (g (ap1 s n)) (ap1 s n)))
  gSuccMiss n =
    let zzn : Term
        zzn = ap2 pi (g n) (ap1 s n)
        flagRw : Deriv (imp (eqF (ap1 p (g n)) O)
                  (eqF (ap2 condFork zzn (ap1 p (g n))) (ap2 condFork zzn O)))
        flagRw = ax_eqCongR condFork (ap1 p (g n)) O zzn
        reduceF : Deriv (eqF (ap2 condFork zzn O) (ap1 s n))
        reduceF = ruleTrans (condFork_false zzn) (axSnd (g n) (ap1 s n))
    in compI (compI flagRw
          (prependEqLeft (g (ap1 s n)) (ap2 condFork zzn (ap1 p (g n))) (ap2 condFork zzn O)
                         (g_at_succ n)))
          (appendEqRight (g (ap1 s n)) (ap2 condFork zzn O) (ap1 s n) reduceF)

  -- freeze: p (g n) /= O  =>  g (s n) = g n .
  gSuccHit : (n : Term) -> Deriv (imp (neg (eqF (ap1 p (g n)) O)) (eqF (g (ap1 s n)) (g n)))
  gSuccHit n =
    let zzn : Term
        zzn = ap2 pi (g n) (ap1 s n)
        chain : Deriv (imp (eqF (ap1 p (g n)) (ap1 s O)) (eqF (g (ap1 s n)) (g n)))
        chain =
          let flagRw' : Deriv (imp (eqF (ap1 p (g n)) (ap1 s O))
                          (eqF (ap2 condFork zzn (ap1 p (g n))) (ap2 condFork zzn (ap1 s O))))
              flagRw' = ax_eqCongR condFork (ap1 p (g n)) (ap1 s O) zzn
              reduceT : Deriv (eqF (ap2 condFork zzn (ap1 s O)) (g n))
              reduceT = ruleTrans (condFork_true_nc zzn O) (axFst (g n) (ap1 s n))
          in compI (compI flagRw'
                (prependEqLeft (g (ap1 s n)) (ap2 condFork zzn (ap1 p (g n)))
                               (ap2 condFork zzn (ap1 s O)) (g_at_succ n)))
                (appendEqRight (g (ap1 s n)) (ap2 condFork zzn (ap1 s O)) (g n) reduceT)
    in compI (le_one_neq_zero (ap1 p (g n)) (p_le_one (g n))) chain

  eqSymImp : (a b : Term) -> Deriv (imp (eqF a b) (eqF b a))
  eqSymImp a b = bComb (ax_eqTrans a b a) (liftP (eqF a b) (axRefl a))

  -- s x = O  is absurd:  ex falso quodlibet.
  sx_efq : (x : Term) (Q : Formula) -> Deriv (imp (eqF (ap1 s x) O) Q)
  sx_efq x Q =
    let A : Formula
        A = eqF (ap1 s x) O
        d_xO : Deriv (imp A (eqF x O))
        d_xO = compI (ax_eqCong1 predecessor (ap1 s x) O)
                 (compI (prependEqLeft x (ap1 predecessor (ap1 s x)) (ap1 predecessor O)
                           (ruleSym (ruleInst zero x T_p_S_v0)))
                        (appendEqRight x (ap1 predecessor O) O T_p_O))
        d3 : Deriv (imp A (eqF (ap1 s x) (ap1 s O)))
        d3 = compI d_xO (ax_eqCong1 s x O)
        step_a : Deriv (imp A (imp A (eqF (ap1 s O) O)))
        step_a = compI d3 (ax_eqTrans (ap1 s x) (ap1 s O) O)
        d_sOO : Deriv (imp A (eqF (ap1 s O) O))
        d_sOO = bComb step_a (identP A)
    in compI d_sOO (exFalsoFromSO Q)

  ----------------------------------------------------------------------
  -- SECTION 4.  Firstness:  leq (s x) (g n)  =>  p x = O   (per-x; ind on n).

  firstnessU :
    Deriv (imp (leq (ap1 s (var zero)) (g (var (suc zero)))) (eqF (ap1 p (var zero)) O))
  firstnessU = ruleIndNat (suc zero) {P = Inv} base step
    where
      x0 : Term
      x0 = var zero
      n0 : Term
      n0 = var (suc zero)
      Inv : Formula
      Inv = imp (leq (ap1 s x0) (g n0)) (eqF (ap1 p x0) O)
      H : Formula
      H = leq (ap1 s x0) (g (ap1 s n0))
      goal : Formula
      goal = eqF (ap1 p x0) O

      ------------------------------------------------------------------
      -- base:  leq (s x0) (g O) -> p x0 = O  (g O = O, so hyp is absurd).
      base : Deriv (imp (leq (ap1 s x0) (g O)) goal)
      base =
        let hyp_to_leqO : Deriv (imp (leq (ap1 s x0) (g O)) (leq (ap1 s x0) O))
            hyp_to_leqO =
              prependEqLeft (ap2 sub (ap1 s x0) O) (ap2 sub (ap1 s x0) (g O)) O
                (ruleSym (congR sub (ap1 s x0) g_at_O))
            leqO_to_sxO : Deriv (imp (leq (ap1 s x0) O) (eqF (ap1 s x0) O))
            leqO_to_sxO =
              prependEqLeft (ap1 s x0) (ap2 sub (ap1 s x0) O) O (ruleSym (T_sub_O (ap1 s x0)))
        in compI hyp_to_leqO (compI leqO_to_sxO (sx_efq x0 goal))

      ------------------------------------------------------------------
      -- step.
      mz : Formula
      mz = eqF (ap1 p (g n0)) O
      nx : Formula
      nx = neg (eqF x0 n0)

      -- HIT case:  p (g n0) /= O .  g (s n0) = g n0 ; rewrite H to leq (s x0) (g n0); use Inv.
      stepHit : Deriv (imp (neg mz) (imp Inv (imp H goal)))
      stepHit =
        let nh : Formula
            nh = neg mz
            e_sub : Deriv (imp nh (eqF (ap2 sub (ap1 s x0) (g (ap1 s n0)))
                                       (ap2 sub (ap1 s x0) (g n0))))
            e_sub = compI (gSuccHit n0) (ax_eqCongR sub (g (ap1 s n0)) (g n0) (ap1 s x0))
            H_to_leq : Deriv (imp nh (imp H (leq (ap1 s x0) (g n0))))
            H_to_leq = compI e_sub
              (ax_eqTrans (ap2 sub (ap1 s x0) (g (ap1 s n0))) (ap2 sub (ap1 s x0) (g n0)) O)
            e1 : Deriv (imp nh (imp Inv (imp H (leq (ap1 s x0) (g n0)))))
            e1 = mapUnder1 nh (axK (imp H (leq (ap1 s x0) (g n0))) Inv) H_to_leq
            e_inv : Deriv (imp nh (imp Inv (imp H Inv)))
            e_inv = liftP nh (axK Inv H)
        in bCombThree e_inv e1

      -- MISS case:  p (g n0) = O .  g (s n0) = s n0 ; H -> leq x0 n0 ; byCases x0 = n0.
      H_to_leqxn : Deriv (imp mz (imp H (leq x0 n0)))
      H_to_leqxn =
        let e_sub : Deriv (imp mz (eqF (ap2 sub (ap1 s x0) (g (ap1 s n0)))
                                       (ap2 sub (ap1 s x0) (ap1 s n0))))
            e_sub = compI (gSuccMiss n0) (ax_eqCongR sub (g (ap1 s n0)) (ap1 s n0) (ap1 s x0))
            H_to_leqssn : Deriv (imp mz (imp H (leq (ap1 s x0) (ap1 s n0))))
            H_to_leqssn = compI e_sub
              (ax_eqTrans (ap2 sub (ap1 s x0) (g (ap1 s n0))) (ap2 sub (ap1 s x0) (ap1 s n0)) O)
        in mapUnder2 mz H (unsucc_leq x0 n0) H_to_leqssn

      -- eq:  x0 = n0 .  p x0 = p n0 = p (g n0) = O .
      eqCase : Deriv (imp (eqF x0 n0) (imp mz (imp Inv (imp H goal))))
      eqCase =
        let d_pn0_O : Deriv (imp mz (eqF (ap1 p n0) O))
            d_pn0_O = bComb (compI (compI (compInv n0) (ax_eqCong1 p (g n0) n0))
                                   (ax_eqTrans (ap1 p (g n0)) (ap1 p n0) O))
                            (identP mz)
            arg1 : Deriv (imp (eqF x0 n0) (imp mz (eqF (ap1 p x0) (ap1 p n0))))
            arg1 = mapUnder1 (eqF x0 n0) (axK (eqF (ap1 p x0) (ap1 p n0)) mz)
                     (ax_eqCong1 p x0 n0)
            arg2 : Deriv (imp (eqF x0 n0) (imp mz (eqF (ap1 p n0) O)))
            arg2 = liftP (eqF x0 n0) d_pn0_O
            d_px0_O : Deriv (imp (eqF x0 n0) (imp mz goal))
            d_px0_O = trans2 (eqF x0 n0) mz (ap1 p x0) (ap1 p n0) O arg1 arg2
            inj : Deriv (imp goal (imp Inv (imp H goal)))
            inj = mapUnder1 goal (axK (imp H goal) Inv) (axK goal H)
        in mapUnder2 (eqF x0 n0) mz inj d_px0_O

      -- Carneiro-MP at telescope depth 4 (Frege/axS, simulated deduction theorem).
      bCombFour : {Q1 Q2 Q3 Q4 Q5 Rr : Formula} ->
        Deriv (imp Q1 (imp Q2 (imp Q3 (imp Q4 (imp Q5 Rr))))) ->
        Deriv (imp Q1 (imp Q2 (imp Q3 (imp Q4 Q5)))) ->
        Deriv (imp Q1 (imp Q2 (imp Q3 (imp Q4 Rr))))
      bCombFour {Q1} {Q2} {Q3} {Q4} {Q5} {Rr} D1 D2 =
        bCombThree (bCombThree (liftP Q1 (liftP Q2 (liftP Q3 (axS Q4 Q5 Rr)))) D1) D2

      -- neq:  x0 /= n0 .  Under the context (nx, mz, Inv, H) prove  p x0 = O  by the
      -- chain   leq x0 n0  ->  leq (s x0) n0  ->  leq (s x0) (g n0)  ->  p x0 = O ,
      -- each step a single Carneiro-MP (bCombFour).
      neqCase : Deriv (imp nx (imp mz (imp Inv (imp H goal))))
      neqCase =
        let f1 : Deriv (imp nx (imp mz (imp Inv (imp H (leq x0 n0)))))
            f1 = liftP nx (mapUnder1 mz (axK (imp H (leq x0 n0)) Inv) H_to_leqxn)
            C12 : Formula
            C12 = imp (leq x0 n0) (leq (ap1 s x0) n0)
            ak12 : Deriv (imp C12 (imp mz (imp Inv (imp H C12))))
            ak12 = mapUnder1 C12 (axK (imp Inv (imp H C12)) mz)
                     (mapUnder1 C12 (axK (imp H C12) Inv) (axK C12 H))
            f12 : Deriv (imp nx (imp mz (imp Inv (imp H C12))))
            f12 = mapUnder1 nx ak12 (lt_from_le_neq_curry x0 n0)
            f2 : Deriv (imp nx (imp mz (imp Inv (imp H (leq (ap1 s x0) n0)))))
            f2 = bCombFour f12 f1
            C23 : Formula
            C23 = imp (leq (ap1 s x0) n0) (leq (ap1 s x0) (g n0))
            impl23mz : Deriv (imp mz C23)
            impl23mz = compI (compI (compI (compInv n0) (eqSymImp (g n0) n0))
                                      (ax_eqCongR sub n0 (g n0) (ap1 s x0)))
                               (ax_eqTrans (ap2 sub (ap1 s x0) n0) (ap2 sub (ap1 s x0) (g n0)) O)
            ak23 : Deriv (imp C23 (imp Inv (imp H C23)))
            ak23 = mapUnder1 C23 (axK (imp H C23) Inv) (axK C23 H)
            f23 : Deriv (imp nx (imp mz (imp Inv (imp H C23))))
            f23 = liftP nx (mapUnder1 mz ak23 impl23mz)
            f3 : Deriv (imp nx (imp mz (imp Inv (imp H (leq (ap1 s x0) (g n0))))))
            f3 = bCombFour f23 f2
            fInv : Deriv (imp nx (imp mz (imp Inv (imp H Inv))))
            fInv = liftP nx (liftP mz (axK Inv H))
        in bCombFour fInv f3

      stepMiss : Deriv (imp mz (imp Inv (imp H goal)))
      stepMiss = byCases (eqF x0 n0) (imp mz (imp Inv (imp H goal))) eqCase neqCase

      step : Deriv (imp Inv (imp H goal))
      step = byCases mz (imp Inv (imp H goal)) stepMiss stepHit

  ----------------------------------------------------------------------
  -- SECTION 5.  The least-number lemma (w1 := g (s B)).

  -- firstness instantiated:  x < g (s B)  =>  p x = O .
  least_first :
    (B x : Term) -> Deriv (imp (leq (ap1 s x) (g (ap1 s B))) (eqF (ap1 p x) O))
  least_first B x = ruleInst2 0 x 1 (ap1 s B) refl firstnessU

  -- the recorded position g (s B) is a genuine hit:  p (g (s B)) = s O .
  least_hit :
    (B : Term) -> Deriv (eqF (ap1 p B) (ap1 s O)) ->
    Deriv (eqF (ap1 p (g (ap1 s B))) (ap1 s O))
  least_hit B witness =
    let missCase : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (ap1 p (g (ap1 s B))) (ap1 s O)))
        missCase =
          let d_gBB : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (g B) B))
              d_gBB = compInv B
              d_pBeq : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (ap1 p (g B)) (ap1 p B)))
              d_pBeq = compI d_gBB (ax_eqCong1 p (g B) B)
              d_pBO : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (ap1 p B) O))
              d_pBO = bComb (compI d_pBeq (ax_eqTrans (ap1 p (g B)) (ap1 p B) O))
                            (identP (eqF (ap1 p (g B)) O))
              e_sOO : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (ap1 s O) O))
              e_sOO = compI d_pBO
                        (prependEqLeft (ap1 s O) (ap1 p B) O (ruleSym witness))
          in compI e_sOO (exFalsoFromSO (eqF (ap1 p (g (ap1 s B))) (ap1 s O)))
        hitCase : Deriv (imp (neg (eqF (ap1 p (g B)) O)) (eqF (ap1 p (g (ap1 s B))) (ap1 s O)))
        hitCase =
          let d_eq : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                              (eqF (ap1 p (g (ap1 s B))) (ap1 p (g B))))
              d_eq = compI (gSuccHit B) (ax_eqCong1 p (g (ap1 s B)) (g B))
              d_sO : Deriv (imp (neg (eqF (ap1 p (g B)) O)) (eqF (ap1 p (g B)) (ap1 s O)))
              d_sO = le_one_neq_zero (ap1 p (g B)) (p_le_one (g B))
              d_eqSym : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                                 (eqF (ap1 p (g B)) (ap1 p (g (ap1 s B)))))
              d_eqSym = compI d_eq (eqSymImp (ap1 p (g (ap1 s B))) (ap1 p (g B)))
              t1 : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                            (imp (eqF (ap1 p (g B)) (ap1 s O))
                                 (eqF (ap1 p (g (ap1 s B))) (ap1 s O))))
              t1 = compI d_eqSym
                     (ax_eqTrans (ap1 p (g B)) (ap1 p (g (ap1 s B))) (ap1 s O))
          in bComb t1 d_sO
    in byCases (eqF (ap1 p (g B)) O) (eqF (ap1 p (g (ap1 s B))) (ap1 s O)) missCase hitCase

  ----------------------------------------------------------------------
  -- SECTION 6.  THE LEAST-NUMBER LEMMA, packaged.
  --
  -- For a 0/1 predicate p (p_le_one is the standing module hypothesis), from a
  -- witness  p B = s O  there is a FIRST  w1  with  p w1 = s O  and  p x = O  for
  -- all  x < w1 .   (w1 = g (s B).)

  record LeastNumber (B : Term) : Set where
    constructor mkLeast
    field
      w1     : Term
      isHit  : Deriv (eqF (ap1 p w1) (ap1 s O))
      isFirst : (x : Term) -> Deriv (imp (leq (ap1 s x) w1) (eqF (ap1 p x) O))

  leastNumber : (B : Term) -> Deriv (eqF (ap1 p B) (ap1 s O)) -> LeastNumber B
  leastNumber B witness =
    mkLeast (g (ap1 s B)) (least_hit B witness) (least_first B)
