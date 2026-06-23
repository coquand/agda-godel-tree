{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TauRowBase -- the Cantor antidiagonal ROW-BASE bound
--
--   tauRowBase : tau (pred (nu x)) <= x          (x at/above its row base)
--
-- and its corollaries
--
--   predNuLe : pred (nu x) <= x
--   fstLe    : Fst x <= x
--
-- Proof of tauRowBase: ruleIndNat on x with the sigma-encoded row-membership
-- invariant
--
--   Inv(x) = sigma (sub (tau (pred (nu x))) x)
--                  (sub (s x) (tau (nu x)))  =  O
--
-- i.e.  tau (pred (nu x)) <= x  AND  s x <= tau (nu x)   (full row membership).
-- The step Inv(x) => Inv(s x) splits on  tau(s r) <= s x  (r = pred(nu x)):
--   - new base  (s x = tau(s r))   : T109 gives  nu(s x) = s(nu x)
--   - in row    (s(s x) <= tau(s r)): T108 gives  nu(s x) = nu x
--
-- No native object conjunction: the two coupled bounds are carried as a single
-- sigma being O, split with sigmaZeroL/R.  No holes / postulates.

module T4.TauRowBase where

open import T4.Base

open import BRA3.Church        using ( sub ; tau ; sigma ; predecessor
                                     ; T35 ; T90 ; T91 ; T_p_S_v0 )
open import BRA3.ChurchSubSucc using ( T_sub_O ; T57sub )
open import BRA3.ChurchLeq     using ( leq ; T76 )
open import BRA3.ChurchT78     using ( T78 )
open import BRA3.ChurchT81     using ( T81 )
open import BRA3.ChurchMu      using ( mu ; T100 )
open import BRA3.ChurchNu      using ( nuFn ; T107 )
open import BRA3.ChurchT108    using ( T108 )
open import BRA3.ChurchT109    using ( T109 )
open import BRA3.ChurchStrictTrich using ( strictTrich )
open import BRA3.ChurchT117    using ( Fst ; Fst_closed )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.RuleInst2     using ( ruleInst2 )
open import BRA3.Contrapositive using ( liftP ; bComb ; bCombTwo ; identP )
open import BRA3.Logic         using ( impTrans ; eqSymImp )
open import BRA3.ChurchCM      using ( caseElim )

open import T4.SigmaZeroN      using ( sigmaZeroL ; sigmaZeroR )
open import T4.LoopReaches     using ( sigma_at_O_univ )
open import T4.LeqMono         using ( leq_trans ; leq_sigma_right )
open import T4.LeqPiLeft       using ( leq_tau )
open import T4.Counting        using ( antisym_curry ; mapUnder2 )
open import T4.DescSnd         using ( nuGe2 ; posNeqO ; succForm )
open import T4.ChaitinG1Arith  using ( sub_le_arg1 )
open import T4.Thm12.ImpHelpers using ( impEqTrans )

------------------------------------------------------------------------
-- Two-hypothesis equational helpers (carry P1, P2).

private
  lift2 : (P1 P2 : Formula) {Q : Formula} -> Deriv Q ->
          Deriv (imp P1 (imp P2 Q))
  lift2 P1 P2 d = liftP P1 (liftP P2 d)

  trans2 : (P1 P2 : Formula) (a b c : Term) ->
           Deriv (imp P1 (imp P2 (eqF a b))) ->
           Deriv (imp P1 (imp P2 (eqF b c))) ->
           Deriv (imp P1 (imp P2 (eqF a c)))
  trans2 P1 P2 a b c eqAB eqBC =
    let axEqT_lifted :
          Deriv (imp P1 (imp P2 (imp (eqF b a) (imp (eqF b c) (eqF a c)))))
        axEqT_lifted = liftP P1 (liftP P2 (ax_eqTrans b a c))
        eqBA : Deriv (imp P1 (imp P2 (eqF b a)))
        eqBA = bCombTwo (liftP P1 (liftP P2 (eqSymImp a b))) eqAB
        step1 : Deriv (imp P1 (imp P2 (imp (eqF b c) (eqF a c))))
        step1 = bCombTwo axEqT_lifted eqBA
    in bCombTwo step1 eqBC

  sym2 : (P1 P2 : Formula) (a b : Term) ->
         Deriv (imp P1 (imp P2 (eqF a b))) ->
         Deriv (imp P1 (imp P2 (eqF b a)))
  sym2 P1 P2 a b d = mapUnder2 P1 P2 (eqSymImp a b) d

  congone2 : (P1 P2 : Formula) (f : Fun1) (a b : Term) ->
            Deriv (imp P1 (imp P2 (eqF a b))) ->
            Deriv (imp P1 (imp P2 (eqF (ap1 f a) (ap1 f b))))
  congone2 P1 P2 f a b d = mapUnder2 P1 P2 (ax_eqCong1 f a b) d

  congL2 : (P1 P2 : Formula) (g : Fun2) (a b c : Term) ->
           Deriv (imp P1 (imp P2 (eqF a b))) ->
           Deriv (imp P1 (imp P2 (eqF (ap2 g a c) (ap2 g b c))))
  congL2 P1 P2 g a b c d = mapUnder2 P1 P2 (ax_eqCongL g a b c) d

  congR2 : (P1 P2 : Formula) (g : Fun2) (a b c : Term) ->
           Deriv (imp P1 (imp P2 (eqF a b))) ->
           Deriv (imp P1 (imp P2 (eqF (ap2 g c a) (ap2 g c b))))
  congR2 P1 P2 g a b c d = mapUnder2 P1 P2 (ax_eqCongR g a b c) d

  -- sigma A B = O  from  A = O  and  B = O  (unconditional).
  sigmaBothZero : (a b : Term) ->
    Deriv (eqF a O) -> Deriv (eqF b O) -> Deriv (eqF (ap2 sigma a b) O)
  sigmaBothZero a b pa pb =
    ruleTrans (congL sigma b pa)
              (ruleTrans (congR sigma O pb) (sigma_at_O_univ O))

------------------------------------------------------------------------
-- nu x >= 1, universal.

private
  -- leq O (s O).
  leqO_sO : Deriv (leq O (ap1 s O))
  leqO_sO = ruleInst 0 (ap1 s O) T76

  nuGe1_univ : Deriv (leq (ap1 s O) (ap1 nuFn (var 0)))
  nuGe1_univ = ruleIndNat 0 {P = Pform} base step
    where
      Pform : Formula
      Pform = leq (ap1 s O) (ap1 nuFn (var 0))

      -- nu O = s O.
      nuO_eq : Deriv (eqF (ap1 nuFn O) (ap1 s O))
      nuO_eq = ruleTrans (ruleInst 0 O T107) (ruleInst 0 O T100)

      base : Deriv (leq (ap1 s O) (ap1 nuFn O))
      base = ruleTrans (congR sub (ap1 s O) nuO_eq) (sub_self (ap1 s O))

      -- leq (s O) (s (var 0)).
      sOleSsx : Deriv (leq (ap1 s O) (ap1 s (var 0)))
      sOleSsx = mp (ruleInst2 0 O 1 (var 0) refl T78) T76

      -- leq (s O) (s (s O)).
      sOleSsO : Deriv (leq (ap1 s O) (ap1 s (ap1 s O)))
      sOleSsO = mp (ruleInst2 0 O 1 (ap1 s O) refl T78) leqO_sO

      Q : Formula
      Q = leq (ap1 s O) (ap1 nuFn (ap1 s (var 0)))

      Qderiv : Deriv Q
      Qderiv =
        leq_trans (ap1 s O) (ap1 s (ap1 s O)) (ap1 nuFn (ap1 s (var 0)))
          sOleSsO
          (nuGe2 (ap1 s (var 0)) sOleSsx)

      step : Deriv (imp Pform Q)
      step = mp (axK Q Pform) Qderiv

------------------------------------------------------------------------
-- The invariant and its instances.

private
  InvAt : Term -> Formula
  InvAt t =
    eqF (ap2 sigma
              (ap2 sub (ap1 tau (ap1 predecessor (ap1 nuFn t))) t)
              (ap2 sub (ap1 s t) (ap1 tau (ap1 nuFn t))))
        O

  -- Object variable = x.
  x : Term
  x = var 0

  nuX   : Term
  nuX   = ap1 nuFn x
  rr    : Term
  rr    = ap1 predecessor nuX
  tauR  : Term
  tauR  = ap1 tau rr
  sx    : Term
  sx    = ap1 s x
  ssx   : Term
  ssx   = ap1 s sx
  nuSX  : Term
  nuSX  = ap1 nuFn sx
  rSX   : Term
  rSX   = ap1 predecessor nuSX
  tauRSX : Term
  tauRSX = ap1 tau rSX
  tauNuX : Term
  tauNuX = ap1 tau nuX
  tauNuSX : Term
  tauNuSX = ap1 tau nuSX
  tauSr : Term
  tauSr = ap1 tau (ap1 s rr)

  Inv : Formula
  Inv = InvAt x

  Goal : Formula
  Goal = InvAt sx

  -- bodies of Inv at x.
  B1 : Term
  B1 = ap2 sub tauR x
  B2 : Term
  B2 = ap2 sub sx tauNuX

  H1imp : Deriv (imp Inv (leq tauR x))
  H1imp = sigmaZeroL B1 B2

  H2imp : Deriv (imp Inv (leq sx tauNuX))
  H2imp = sigmaZeroR B1 B2

  -- nu x >= 1, nu x = s r.
  nuPos : Deriv (leq (ap1 s O) nuX)
  nuPos = nuGe1_univ

  nuX_eq : Deriv (eqF nuX (ap1 s rr))
  nuX_eq = succForm nuX (posNeqO nuX nuPos)

  pred_sr : Deriv (eqF (ap1 predecessor (ap1 s rr)) rr)
  pred_sr = ruleInst 0 rr T_p_S_v0

  -- tau (nu x) = tau (s r).
  tauNuX_eq_tauSr : Deriv (eqF tauNuX tauSr)
  tauNuX_eq_tauSr = cong1 tau nuX_eq

  -- The case-split proposition  X = (tau (s r) <= s x).
  Xprop : Formula
  Xprop = leq tauSr sx

  NX : Formula
  NX = neg Xprop

  -- Output goal bodies (Inv at s x).
  B1' : Term
  B1' = ap2 sub tauRSX sx
  B2' : Term
  B2' = ap2 sub ssx tauNuSX

------------------------------------------------------------------------
-- New-base branch :  Xprop = (tau(s r) <= s x)  holds.

private
  newBaseBranch : Deriv (imp Xprop (imp Inv Goal))
  newBaseBranch =
    let -- H2 rewritten to tau(s r) under Inv.
        e_h2 : Deriv (eqF (ap2 sub sx tauSr) (ap2 sub sx tauNuX))
        e_h2 = congR sub sx (ruleSym tauNuX_eq_tauSr)

        H2'imp : Deriv (imp Inv (leq sx tauSr))
        H2'imp = impEqTrans (ap2 sub sx tauSr) (ap2 sub sx tauNuX) O
                            (liftP Inv e_h2) H2imp

        -- s x = tau(s r) under (Xprop, Inv) via antisymmetry.
        H2primeU : Deriv (imp Xprop (imp Inv (leq sx tauSr)))
        H2primeU = liftP Xprop H2'imp

        XpropU : Deriv (imp Xprop (imp Inv Xprop))
        XpropU = axK Xprop Inv

        antisymU :
          Deriv (imp Xprop (imp Inv (imp (leq sx tauSr)
                                          (imp (leq tauSr sx) (eqF sx tauSr)))))
        antisymU = lift2 Xprop Inv (antisym_curry sx tauSr)

        sxEqTauSr : Deriv (imp Xprop (imp Inv (eqF sx tauSr)))
        sxEqTauSr = bCombTwo (bCombTwo antisymU H2primeU) XpropU

        -- T109 : tau(s r) = s x  =>  nu(s x) = s(nu x).
        T109_inst :
          Deriv (imp (eqF tauSr sx) (eqF nuSX (ap1 s nuX)))
        T109_inst = ruleInst 1 (ap1 s rr) T109

        tauSrEqSx : Deriv (imp Xprop (imp Inv (eqF tauSr sx)))
        tauSrEqSx = sym2 Xprop Inv sx tauSr sxEqTauSr

        nuSX_eq_snuX : Deriv (imp Xprop (imp Inv (eqF nuSX (ap1 s nuX))))
        nuSX_eq_snuX = bCombTwo (lift2 Xprop Inv T109_inst) tauSrEqSx

        nuSX_eq_ssr : Deriv (imp Xprop (imp Inv (eqF nuSX (ap1 s (ap1 s rr)))))
        nuSX_eq_ssr =
          trans2 Xprop Inv nuSX (ap1 s nuX) (ap1 s (ap1 s rr))
            nuSX_eq_snuX
            (lift2 Xprop Inv (cong1 s nuX_eq))

        rSX_eq_sr : Deriv (imp Xprop (imp Inv (eqF rSX (ap1 s rr))))
        rSX_eq_sr =
          trans2 Xprop Inv rSX (ap1 predecessor (ap1 s (ap1 s rr))) (ap1 s rr)
            (congone2 Xprop Inv predecessor nuSX (ap1 s (ap1 s rr)) nuSX_eq_ssr)
            (lift2 Xprop Inv (ruleInst 0 (ap1 s rr) T_p_S_v0))

        tauRSX_eq_tauSr : Deriv (imp Xprop (imp Inv (eqF tauRSX tauSr)))
        tauRSX_eq_tauSr = congone2 Xprop Inv tau rSX (ap1 s rr) rSX_eq_sr

        tauRSX_eq_sx : Deriv (imp Xprop (imp Inv (eqF tauRSX sx)))
        tauRSX_eq_sx =
          trans2 Xprop Inv tauRSX tauSr sx
            tauRSX_eq_tauSr
            (sym2 Xprop Inv sx tauSr sxEqTauSr)

        -- conjunct 1 : tau(pred(nu(s x))) <= s x.
        conj1 : Deriv (imp Xprop (imp Inv (eqF B1' O)))
        conj1 =
          trans2 Xprop Inv (ap2 sub tauRSX sx) (ap2 sub sx sx) O
            (congL2 Xprop Inv sub tauRSX sx sx tauRSX_eq_sx)
            (lift2 Xprop Inv (sub_self sx))

        -- conjunct 2 : s(s x) <= tau(nu(s x)).
        SIGsmall : Term
        SIGsmall = ap2 sigma (ap1 s rr) (ap1 tau (ap1 s rr))
        SIG : Term
        SIG = ap2 sigma (ap1 s (ap1 s rr)) (ap1 tau (ap1 s rr))
        AA : Term
        AA = ap1 s tauSr   -- s (tau (s r))

        L0 : Deriv (leq (ap1 tau (ap1 s rr)) SIGsmall)
        L0 = leq_sigma_right (ap1 s rr) (ap1 tau (ap1 s rr))

        L1 : Deriv (leq AA (ap1 s SIGsmall))
        L1 = mp (ruleInst2 0 (ap1 tau (ap1 s rr)) 1 SIGsmall refl T78) L0

        e35 : Deriv (eqF SIG (ap1 s SIGsmall))
        e35 = ruleInst2 0 (ap1 s rr) 1 (ap1 tau (ap1 s rr)) refl T35

        L2 : Deriv (leq AA SIG)
        L2 = ruleTrans (ruleSym (congR sub AA (ruleSym e35))) L1

        ssx_eq : Deriv (imp Xprop (imp Inv (eqF ssx AA)))
        ssx_eq = congone2 Xprop Inv s sx tauSr sxEqTauSr

        tauNuSX_eqC : Deriv (imp Xprop (imp Inv (eqF tauNuSX SIG)))
        tauNuSX_eqC =
          trans2 Xprop Inv tauNuSX (ap1 tau (ap1 s (ap1 s rr))) SIG
            (congone2 Xprop Inv tau nuSX (ap1 s (ap1 s rr)) nuSX_eq_ssr)
            (lift2 Xprop Inv (T91 (ap1 s rr)))

        conj2 : Deriv (imp Xprop (imp Inv (eqF B2' O)))
        conj2 =
          trans2 Xprop Inv (ap2 sub ssx tauNuSX) (ap2 sub AA tauNuSX) O
            (congL2 Xprop Inv sub ssx AA tauNuSX ssx_eq)
            (trans2 Xprop Inv (ap2 sub AA tauNuSX) (ap2 sub AA SIG) O
              (congR2 Xprop Inv sub tauNuSX SIG AA tauNuSX_eqC)
              (lift2 Xprop Inv L2))

    in trans2 Xprop Inv (ap2 sigma B1' B2') (ap2 sigma O B2') O
         (congL2 Xprop Inv sigma B1' O B2' conj1)
         (trans2 Xprop Inv (ap2 sigma O B2') (ap2 sigma O O) O
           (congR2 Xprop Inv sigma B2' O O conj2)
           (lift2 Xprop Inv (sigma_at_O_univ O)))

------------------------------------------------------------------------
-- In-row branch :  neg Xprop  holds, so  s(s x) <= tau(s r).

private
  inRowBranch : Deriv (imp NX (imp Inv Goal))
  inRowBranch =
    let -- s(s x) <= tau(s r)  from  neg(tau(s r) <= s x).
        strictTrich_inst : Deriv (imp NX (leq ssx tauSr))
        strictTrich_inst = ruleInst2 0 tauSr 1 sx refl strictTrich

        inRowFact : Deriv (imp NX (imp Inv (leq ssx tauSr)))
        inRowFact = impTrans strictTrich_inst (axK (leq ssx tauSr) Inv)

        -- T108 : tau r <= x  ->  s(s x) <= tau(s r)  ->  nu(s x) = nu x.
        T108_inst :
          Deriv (imp (leq tauR x)
                     (imp (leq ssx tauSr) (eqF nuSX nuX)))
        T108_inst = ruleInst 1 rr T108

        H1u : Deriv (imp NX (imp Inv (leq tauR x)))
        H1u = liftP NX H1imp

        nuSXeqNuX : Deriv (imp NX (imp Inv (eqF nuSX nuX)))
        nuSXeqNuX =
          bCombTwo (bCombTwo (lift2 NX Inv T108_inst) H1u) inRowFact

        nuSX_eq_sr : Deriv (imp NX (imp Inv (eqF nuSX (ap1 s rr))))
        nuSX_eq_sr =
          trans2 NX Inv nuSX nuX (ap1 s rr)
            nuSXeqNuX (lift2 NX Inv nuX_eq)

        rSX_eq_r : Deriv (imp NX (imp Inv (eqF rSX rr)))
        rSX_eq_r =
          trans2 NX Inv rSX (ap1 predecessor (ap1 s rr)) rr
            (congone2 NX Inv predecessor nuSX (ap1 s rr) nuSX_eq_sr)
            (lift2 NX Inv pred_sr)

        tauRSX_eq_tauR : Deriv (imp NX (imp Inv (eqF tauRSX tauR)))
        tauRSX_eq_tauR = congone2 NX Inv tau rSX rr rSX_eq_r

        -- conjunct 1 : tau r <= x <= s x.
        T81_at : Deriv (imp (leq tauR x) (leq tauR sx))
        T81_at = ruleInst 1 x (ruleInst 0 tauR T81)

        leqTauR_sx_imp : Deriv (imp Inv (leq tauR sx))
        leqTauR_sx_imp = impTrans H1imp T81_at

        conj1 : Deriv (imp NX (imp Inv (eqF B1' O)))
        conj1 =
          trans2 NX Inv (ap2 sub tauRSX sx) (ap2 sub tauR sx) O
            (congL2 NX Inv sub tauRSX tauR sx tauRSX_eq_tauR)
            (liftP NX leqTauR_sx_imp)

        -- conjunct 2 : s(s x) <= tau(nu(s x)) = tau(s r).
        tauNuSX_eq_tauSr : Deriv (imp NX (imp Inv (eqF tauNuSX tauSr)))
        tauNuSX_eq_tauSr = congone2 NX Inv tau nuSX (ap1 s rr) nuSX_eq_sr

        conj2 : Deriv (imp NX (imp Inv (eqF B2' O)))
        conj2 =
          trans2 NX Inv (ap2 sub ssx tauNuSX) (ap2 sub ssx tauSr) O
            (congR2 NX Inv sub tauNuSX tauSr ssx tauNuSX_eq_tauSr)
            inRowFact

    in trans2 NX Inv (ap2 sigma B1' B2') (ap2 sigma O B2') O
         (congL2 NX Inv sigma B1' O B2' conj1)
         (trans2 NX Inv (ap2 sigma O B2') (ap2 sigma O O) O
           (congR2 NX Inv sigma B2' O O conj2)
           (lift2 NX Inv (sigma_at_O_univ O)))

------------------------------------------------------------------------
-- Inv, universal, by ruleIndNat.

private
  Inv_univ : Deriv (InvAt (var 0))
  Inv_univ = ruleIndNat 0 {P = InvAt (var 0)} baseInv stepInv
    where
      -- Base  x = O.
      nuO_eq : Deriv (eqF (ap1 nuFn O) (ap1 s O))
      nuO_eq = ruleTrans (ruleInst 0 O T107) (ruleInst 0 O T100)

      predNuO_eq : Deriv (eqF (ap1 predecessor (ap1 nuFn O)) O)
      predNuO_eq = ruleTrans (cong1 predecessor nuO_eq) (ruleInst 0 O T_p_S_v0)

      tauPredNuO_eq : Deriv (eqF (ap1 tau (ap1 predecessor (ap1 nuFn O))) O)
      tauPredNuO_eq = ruleTrans (cong1 tau predNuO_eq) T90

      b1o : Deriv (eqF (ap2 sub (ap1 tau (ap1 predecessor (ap1 nuFn O))) O) O)
      b1o = ruleTrans (T_sub_O (ap1 tau (ap1 predecessor (ap1 nuFn O))))
                      tauPredNuO_eq

      tauSO : Deriv (eqF (ap1 tau (ap1 s O)) (ap1 s O))
      tauSO = ruleTrans (T91 O)
                (ruleTrans (congR sigma (ap1 s O) T90) (sigma_at_O_univ (ap1 s O)))

      tauNuO_eq : Deriv (eqF (ap1 tau (ap1 nuFn O)) (ap1 s O))
      tauNuO_eq = ruleTrans (cong1 tau nuO_eq) tauSO

      b2o : Deriv (eqF (ap2 sub (ap1 s O) (ap1 tau (ap1 nuFn O))) O)
      b2o = ruleTrans (congR sub (ap1 s O) tauNuO_eq) (sub_self (ap1 s O))

      baseInv : Deriv (InvAt O)
      baseInv = sigmaBothZero
                  (ap2 sub (ap1 tau (ap1 predecessor (ap1 nuFn O))) O)
                  (ap2 sub (ap1 s O) (ap1 tau (ap1 nuFn O)))
                  b1o b2o

      -- Step.
      stepInv : Deriv (imp (InvAt (var 0))
                           (substF 0 (ap1 s (var 0)) (InvAt (var 0))))
      stepInv =
        caseElim {X = Xprop} {Y = neg Xprop} {Rf = imp Inv Goal}
          (identP (neg Xprop))
          newBaseBranch
          inRowBranch

------------------------------------------------------------------------
-- tauRowBase and corollaries.

tauRowBase : (t : Term) ->
  Deriv (leq (ap1 tau (ap1 predecessor (ap1 nuFn t))) t)
tauRowBase t =
  mp (sigmaZeroL (ap2 sub (ap1 tau (ap1 predecessor (ap1 nuFn t))) t)
                 (ap2 sub (ap1 s t) (ap1 tau (ap1 nuFn t))))
     (ruleInst 0 t Inv_univ)

predNuLe : (t : Term) -> Deriv (leq (ap1 predecessor (ap1 nuFn t)) t)
predNuLe t =
  leq_trans (ap1 predecessor (ap1 nuFn t))
            (ap1 tau (ap1 predecessor (ap1 nuFn t)))
            t
            (leq_tau (ap1 predecessor (ap1 nuFn t)))
            (tauRowBase t)

fstLe : (t : Term) -> Deriv (leq (ap1 Fst t) t)
fstLe t =
  let pNu : Term
      pNu = ap1 predecessor (ap1 nuFn t)
      fstLePredNu : Deriv (leq (ap1 Fst t) pNu)
      fstLePredNu =
        ruleTrans (congL sub pNu (Fst_closed t))
                  (sub_le_arg1 pNu (ap1 Snd t))
  in leq_trans (ap1 Fst t) pNu t fstLePredNu (predNuLe t)
