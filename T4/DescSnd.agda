{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DescSnd -- the Cantor VALUE-DESCENT lemma (route a):
--   descSnd : x >= 1  ->  leq (s (Snd x)) x       (Snd x < x)
-- NO surjective pairing, NO eta -- pure nu/mu/sub arithmetic.  Discharges
-- FoldRec.lookup_eq_fold's value-bound  leq child (pred d)  for opaque codes.

module T4.DescSnd where

open import T4.Base

open import BRA3.Church      using ( sub ; tau ; predecessor ; sigma
                                   ; T91 ; T_sub_S_v01 ; T_p_S_v0 )
open import BRA3.ChurchLeq   using ( leq ; T76 )
open import BRA3.ChurchT116  using ( Snd ; Snd_closed )
open import BRA3.ChurchNu    using ( nuFn )
open import BRA3.ChurchT78   using ( T78 )
open import BRA3.ChurchPredMono using ( predMono )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.ChurchSubSucc using ( T_sub_O )
open import BRA3.ChurchMu     using ( mu ; T99 ; T100 )
open import BRA3.ChurchEta1   using ( eta1 ; ssub ; T97 )
open import BRA3.ChurchAlpha  using ( alpha ; T30 )
open import BRA3.ChurchSsubClosedFull using ( ssubClosed )
open import BRA3.ChurchNu     using ( T107 )
open import BRA3.ChurchT84    using ( T84 )
open import BRA3.Church       using ( T33 ; T34 ; T90 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.RuleInst2   using ( ruleInst2 )
open import BRA3.RuleInst3   using ( ruleInst3 )
open import BRA3.Classical   using ( axContrapos )
open import BRA3.Logic       using ( impTrans ; appendEqRight )
open import T4.LeqMono       using ( leq_trans ; leq_sigma_left )
open import T4.ChaitinG1Arith using ( sub_le_arg1 )
open import T4.Counting       using ( reassembly )
open import T4.SndDescent     using ( muStep )

------------------------------------------------------------------------
-- posNeqO :  leq (s O) c  ->  c != O .

posNeqO : (c : Term) -> Deriv (leq (ap1 s O) c) -> Deriv (neg (eqF c O))
posNeqO c hpos =
  let H : Formula
      H = eqF c O
      Q : Formula
      Q = eqF (ap1 s O) O
      X : Term
      X = ap2 sub (ap1 s O) c
      -- (c = O) -> (sub (s O) c = sub (s O) O)
      congStep : Deriv (imp H (eqF X (ap2 sub (ap1 s O) O)))
      congStep = ax_eqCongR sub c O (ap1 s O)
      -- (sub (s O) c = sub (s O) O) -> (sub (s O) c = s O)
      toS : Deriv (imp (eqF X (ap2 sub (ap1 s O) O)) (eqF X (ap1 s O)))
      toS = appendEqRight X (ap2 sub (ap1 s O) O) (ap1 s O) (T_sub_O (ap1 s O))
      -- (sub (s O) c = s O) -> (s O = O)   [using hpos : X = O]
      etr : Deriv (imp (eqF X (ap1 s O)) (imp (eqF X O) Q))
      etr = ax_eqTrans X (ap1 s O) O
      toQ : Deriv (imp (eqF X (ap1 s O)) Q)
      toQ = mp (mp (axS (eqF X (ap1 s O)) (eqF X O) Q) etr)
               (mp (axK (eqF X O) (eqF X (ap1 s O))) hpos)
      impHQ : Deriv (imp H Q)
      impHQ = impTrans congStep (impTrans toS toQ)
  in mp (mp (axContrapos H Q) impHQ) ax_succ_nonzero

------------------------------------------------------------------------
-- predNonzeroSuccForm :  c != O  ->  c = s (pred c) .

succForm : (c : Term) -> Deriv (neg (eqF c O)) -> Deriv (eqF c (ap1 s (ap1 predecessor c)))
succForm c cNeq = ruleSym (mp (ruleInst 0 c L_sp) cNeq)

------------------------------------------------------------------------
-- subStrict :  a >= 1 -> c >= 1 -> s (sub a c) <= a .
-- Route: c = s(pred c); sub a c = pred(sub a (pred c)) = pred w, w <= a;
--   pred w <= pred a (predMono); s(pred w) <= s(pred a) (T78) = a (L_sp).

subStrict : (a c : Term) ->
  Deriv (leq (ap1 s O) a) -> Deriv (leq (ap1 s O) c) ->
  Deriv (leq (ap1 s (ap2 sub a c)) a)
subStrict a c apos cpos =
  let pc : Term
      pc = ap1 predecessor c
      w : Term
      w = ap2 sub a pc
      cEq : Deriv (eqF c (ap1 s pc))
      cEq = succForm c (posNeqO c cpos)
      -- sub a c = sub a (s pc) = pred(sub a pc) = pred w
      subEq : Deriv (eqF (ap2 sub a c) (ap1 predecessor w))
      subEq = ruleTrans (congR sub a cEq) (ruleInst2 0 a 1 pc refl T_sub_S_v01)
      wLeA : Deriv (leq w a)
      wLeA = sub_le_arg1 a pc
      predLe : Deriv (leq (ap1 predecessor w) (ap1 predecessor a))
      predLe = mp (ruleInst2 0 w 1 a refl predMono) wLeA
      sPredLe : Deriv (leq (ap1 s (ap1 predecessor w)) (ap1 s (ap1 predecessor a)))
      sPredLe = mp (ruleInst2 0 (ap1 predecessor w) 1 (ap1 predecessor a) refl T78) predLe
      saEq : Deriv (eqF (ap1 s (ap1 predecessor a)) a)
      saEq = mp (ruleInst 0 a L_sp) (posNeqO a apos)
      -- s(pred w) <= a
      goalLe : Deriv (leq (ap1 s (ap1 predecessor w)) a)
      goalLe = ruleTrans (congR sub (ap1 s (ap1 predecessor w)) (ruleSym saEq)) sPredLe
  in ruleTrans (congL sub a (cong1 s subEq)) goalLe

------------------------------------------------------------------------
-- tauGe1 :  k >= 1 -> tau k >= 1 .   tau k = sigma (s pk)(tau pk) >= s pk >= 1.

tauGe1 : (k : Term) -> Deriv (leq (ap1 s O) k) -> Deriv (leq (ap1 s O) (ap1 tau k))
tauGe1 k kpos =
  let pk : Term
      pk = ap1 predecessor k
      kEq : Deriv (eqF k (ap1 s pk))
      kEq = succForm k (posNeqO k kpos)
      tauEq : Deriv (eqF (ap1 tau k) (ap2 sigma (ap1 s pk) (ap1 tau pk)))
      tauEq = ruleTrans (cong1 tau kEq) (T91 pk)
      lsl : Deriv (leq (ap1 s pk) (ap2 sigma (ap1 s pk) (ap1 tau pk)))
      lsl = leq_sigma_left (ap1 s pk) (ap1 tau pk)
      leqOpk : Deriv (leq O pk)
      leqOpk = ruleInst 0 pk T76
      sOlespk : Deriv (leq (ap1 s O) (ap1 s pk))
      sOlespk = mp (ruleInst2 0 O 1 pk refl T78) leqOpk
      step : Deriv (leq (ap1 s O) (ap2 sigma (ap1 s pk) (ap1 tau pk)))
      step = leq_trans (ap1 s O) (ap1 s pk) (ap2 sigma (ap1 s pk) (ap1 tau pk)) sOlespk lsl
  in ruleTrans (congR sub (ap1 s O) tauEq) step

------------------------------------------------------------------------
-- predNuGe1 :  nu x >= 2 -> pred (nu x) >= 1 .   (predMono + pred(s(s O)) = s O)

predNuGe1 : (x : Term) ->
  Deriv (leq (ap1 s (ap1 s O)) (ap1 nuFn x)) ->
  Deriv (leq (ap1 s O) (ap1 predecessor (ap1 nuFn x)))
predNuGe1 x nuge2 =
  let pm : Deriv (leq (ap1 predecessor (ap1 s (ap1 s O)))
                      (ap1 predecessor (ap1 nuFn x)))
      pm = mp (ruleInst2 0 (ap1 s (ap1 s O)) 1 (ap1 nuFn x) refl predMono) nuge2
      predSSO : Deriv (eqF (ap1 predecessor (ap1 s (ap1 s O))) (ap1 s O))
      predSSO = ruleInst 0 (ap1 s O) T_p_S_v0
  in ruleTrans (congL sub (ap1 predecessor (ap1 nuFn x)) (ruleSym predSSO)) pm

------------------------------------------------------------------------
-- descSnd_from :  the strict descent GIVEN nu x >= 2 (the residual lemma).
--   Snd x = sub x (tau (pred (nu x))) ; tau(pred(nu x)) >= 1 ; subStrict.

descSnd_from : (x : Term) ->
  Deriv (leq (ap1 s O) x) ->
  Deriv (leq (ap1 s (ap1 s O)) (ap1 nuFn x)) ->
  Deriv (leq (ap1 s (ap1 Snd x)) x)
descSnd_from x xpos nuge2 =
  let c : Term
      c = ap1 tau (ap1 predecessor (ap1 nuFn x))
      cpos : Deriv (leq (ap1 s O) c)
      cpos = tauGe1 (ap1 predecessor (ap1 nuFn x)) (predNuGe1 x nuge2)
      ss : Deriv (leq (ap1 s (ap2 sub x c)) x)
      ss = subStrict x c xpos cpos
  in ruleTrans (congL sub x (cong1 s (Snd_closed x))) ss

------------------------------------------------------------------------
-- muMonoGap :  leq (mu x n) (mu x (sigma n k))   (induction on the gap k;
-- pure successor structure + muStep, no classical case split).

muMonoGap_univ :
  Deriv (leq (ap2 mu (var 2) (var 1))
             (ap2 mu (var 2) (ap2 sigma (var 1) (var 0))))
muMonoGap_univ = ruleIndNat 0 {P = Pform} base stepImp
  where
    A0 : Term
    A0 = ap2 mu (var 2) (var 1)
    Pform : Formula
    Pform = leq A0 (ap2 mu (var 2) (ap2 sigma (var 1) (var 0)))

    B0 : Term
    B0 = ap2 mu (var 2) (ap2 sigma (var 1) O)
    base : Deriv (leq A0 B0)
    base = ruleTrans (congR sub A0 (congR mu (var 2) (T33 (var 1)))) (sub_self A0)

    Bk : Term
    Bk = ap2 mu (var 2) (ap2 sigma (var 1) (var 0))
    Bsk : Term
    Bsk = ap2 mu (var 2) (ap2 sigma (var 1) (ap1 s (var 0)))
    leqBkBsk : Deriv (leq Bk Bsk)
    leqBkBsk =
      ruleTrans
        (congR sub Bk (congR mu (var 2) (ruleInst2 0 (var 1) 1 (var 0) refl T34)))
        (muStep (var 2) (ap2 sigma (var 1) (var 0)))
    -- imp (leq A0 Bk) (leq A0 Bsk) from leqBkBsk, via T84 instantiated at the
    -- CONCRETE A0/Bk/Bsk using fresh vars 5,6,7 (so substT reduces).
    stepImp : Deriv (imp Pform (leq A0 Bsk))
    stepImp =
      let A : Formula
          A = leq A0 Bk
          B : Formula
          B = leq Bk Bsk
          C : Formula
          C = leq A0 Bsk
          t84r : Deriv (imp (leq (var 5) (var 6))
                            (imp (leq (var 6) (var 7)) (leq (var 5) (var 7))))
          t84r = ruleInst 2 (var 7) (ruleInst 1 (var 6) (ruleInst 0 (var 5) T84))
          t84c : Deriv (imp A (imp B C))
          t84c = ruleInst 7 Bsk (ruleInst 6 Bk (ruleInst 5 A0 t84r))
      in mp (mp (axS A B C) t84c) (mp (axK B A) leqBkBsk)

-- NOTE: the generic instantiation  muMonoGap x n k  from muMonoGap_univ needs
-- freshABC / substT_above_max bridging (the leq_trans pattern) to avoid
-- capturing var0/var1/var2 inside abstract x/n/k.  Parked; see report.

------------------------------------------------------------------------
-- muX3 :  x >= 1  ->  mu x 3 = s (s O) .   (eta1 x 2 = alpha x = s O ; mu x 2 = s O.)

muX3 : (x : Term) -> Deriv (leq (ap1 s O) x) ->
       Deriv (eqF (ap2 mu x (ap1 s (ap1 s (ap1 s O)))) (ap1 s (ap1 s O)))
muX3 x xpos =
  let -- mu x 3 = sigma (eta1 x 2) (mu x 2)   [T99 at v1 := s(s O)]
      e99 : Deriv (eqF (ap2 mu x (ap1 s (ap1 s (ap1 s O))))
                       (ap2 sigma (ap2 eta1 x (ap1 s (ap1 s O))) (ap2 mu x (ap1 s (ap1 s O)))))
      e99 = ruleInst2 0 x 1 (ap1 s (ap1 s O)) refl T99
      -- mu x 2 = s O   [T100]
      e100 : Deriv (eqF (ap2 mu x (ap1 s (ap1 s O))) (ap1 s O))
      e100 = ruleInst 0 x T100
      -- eta1 x 2 = alpha (ssub x (s O))   [T97 at v1 := s O]
      e97 : Deriv (eqF (ap2 eta1 x (ap1 s (ap1 s O))) (ap1 alpha (ap2 ssub x (ap1 s O))))
      e97 = ruleInst2 0 x 1 (ap1 s O) refl T97
      -- ssub x (s O) = sub (s x) (tau (s O))   [ssubClosed]
      eClosed : Deriv (eqF (ap2 ssub x (ap1 s O)) (ap2 sub (ap1 s x) (ap1 tau (ap1 s O))))
      eClosed = ruleInst2 0 x 1 (ap1 s O) refl ssubClosed
      -- tau (s O) = s O :  tau (s O) = sigma (s O)(tau O) = sigma (s O) O = s O
      tauSO : Deriv (eqF (ap1 tau (ap1 s O)) (ap1 s O))
      tauSO = ruleTrans (T91 O)
                (ruleTrans (congR sigma (ap1 s O) T90) (T33 (ap1 s O)))
      -- sub (s x)(tau (s O)) = sub (s x)(s O) = pred(sub (s x) O) = pred (s x) = x
      eSub : Deriv (eqF (ap2 sub (ap1 s x) (ap1 tau (ap1 s O))) x)
      eSub = ruleTrans (congR sub (ap1 s x) tauSO)
               (ruleTrans (ruleInst2 0 (ap1 s x) 1 O refl T_sub_S_v01)
                 (ruleTrans (cong1 predecessor (T_sub_O (ap1 s x)))
                            (ruleInst 0 x T_p_S_v0)))
      -- ssub x (s O) = x
      ssubX : Deriv (eqF (ap2 ssub x (ap1 s O)) x)
      ssubX = ruleTrans eClosed eSub
      -- alpha x = s O   (x >= 1 = s(pred x), T30)
      aEq : Deriv (eqF (ap1 alpha x) (ap1 s O))
      aEq = ruleTrans (cong1 alpha (succForm x (posNeqO x xpos)))
                      (ruleInst 0 (ap1 predecessor x) T30)
      -- eta1 x 2 = s O
      eta2 : Deriv (eqF (ap2 eta1 x (ap1 s (ap1 s O))) (ap1 s O))
      eta2 = ruleTrans e97 (ruleTrans (cong1 alpha ssubX) aEq)
      -- sigma (s O)(s O) = s (s O)
      sigSO : Deriv (eqF (ap2 sigma (ap1 s O) (ap1 s O)) (ap1 s (ap1 s O)))
      sigSO = ruleTrans (ruleInst2 0 (ap1 s O) 1 O refl T34)
                        (cong1 s (T33 (ap1 s O)))
  in ruleTrans e99
       (ruleTrans (congL sigma (ap2 mu x (ap1 s (ap1 s O))) eta2)
         (ruleTrans (congR sigma (ap1 s O) e100) sigSO))

------------------------------------------------------------------------
-- leq3ssx :  x >= 1  ->  leq 3 (s (s x)) .   (s(s x) = s(s(s(pred x))) >= 3.)

leq3ssx : (x : Term) -> Deriv (leq (ap1 s O) x) ->
          Deriv (leq (ap1 s (ap1 s (ap1 s O))) (ap1 s (ap1 s x)))
leq3ssx x xpos =
  let px : Term
      px = ap1 predecessor x
      l0 : Deriv (leq O px)
      l0 = ruleInst 0 px T76
      l1 : Deriv (leq (ap1 s O) (ap1 s px))
      l1 = mp (ruleInst2 0 O 1 px refl T78) l0
      l2 : Deriv (leq (ap1 s (ap1 s O)) (ap1 s (ap1 s px)))
      l2 = mp (ruleInst2 0 (ap1 s O) 1 (ap1 s px) refl T78) l1
      l3 : Deriv (leq (ap1 s (ap1 s (ap1 s O))) (ap1 s (ap1 s (ap1 s px))))
      l3 = mp (ruleInst2 0 (ap1 s (ap1 s O)) 1 (ap1 s (ap1 s px)) refl T78) l2
      -- s(s x) = s(s(s px))   (x = s px)
      ssxEq : Deriv (eqF (ap1 s (ap1 s x)) (ap1 s (ap1 s (ap1 s px))))
      ssxEq = cong1 s (cong1 s (succForm x (posNeqO x xpos)))
  in ruleTrans (congR sub (ap1 s (ap1 s (ap1 s O))) ssxEq) l3

------------------------------------------------------------------------
-- nuGe2 :  x >= 1  ->  nu x >= 2 .
--   nu x = mu x (s(s x)) ;  mu x 3 = 2 ;  mu x 3 <= mu x (s(s x)) (muMonoGap).

nuGe2 : (x : Term) -> Deriv (leq (ap1 s O) x) ->
        Deriv (leq (ap1 s (ap1 s O)) (ap1 nuFn x))
nuGe2 x xpos =
  let three : Term
      three = ap1 s (ap1 s (ap1 s O))
      ssx : Term
      ssx = ap1 s (ap1 s x)
      -- mu x 3 = 2, so leq 2 (mu x 3)
      muEq : Deriv (eqF (ap2 mu x three) (ap1 s (ap1 s O)))
      muEq = muX3 x xpos
      leq2mu3 : Deriv (leq (ap1 s (ap1 s O)) (ap2 mu x three))
      leq2mu3 = ruleTrans (congR sub (ap1 s (ap1 s O)) muEq)
                          (sub_self (ap1 s (ap1 s O)))
      -- leq 3 (s(s x)) ; muMonoGap gives leq (mu x 3)(mu x (sigma 3 (...)))?
      -- Instead: leq (mu x 3)(mu x (s(s x))) -- need gap form.  Use muMonoGap with
      -- n=3, k chosen so sigma 3 k = s(s x).  Simpler: build leq (mu x 3)(mu x (s(s x)))
      -- directly from muMonoGap_univ specialised? We use the GENERAL monotonicity below.
      -- mu monotone: from leq 3 (s(s x)) we want leq (mu x 3)(mu x (s(s x))).
      gap : Term
      gap = ap2 sub ssx three
      -- sigma 3 gap = s(s x)   (since 3 <= s(s x):  3 + (ssx - 3) = ssx)
      l3 : Deriv (leq three ssx)
      l3 = leq3ssx x xpos
      -- mmg : leq (mu x 3)(mu x (sigma 3 gap))
      mmg : Deriv (leq (ap2 mu x three) (ap2 mu x (ap2 sigma three gap)))
      mmg = ruleInst3 0 gap 1 three 2 x refl refl refl muMonoGap_univ
      -- sigma 3 gap = sigma three (sub ssx three) = ssx   (k + (n - ... )) -- via T_addsub
      sigGapEq : Deriv (eqF ssx (ap2 sigma three gap))
      sigGapEq = ruleSym (reassembly ssx three l3)
      muGap2ssx : Deriv (leq (ap2 mu x three) (ap2 mu x ssx))
      muGap2ssx =
        ruleTrans (congR sub (ap2 mu x three) (congR mu x sigGapEq)) mmg
      -- nu x = mu x (s(s x))
      nuEq : Deriv (eqF (ap1 nuFn x) (ap2 mu x ssx))
      nuEq = ruleInst 0 x T107
      leq2nu : Deriv (leq (ap1 s (ap1 s O)) (ap2 mu x ssx))
      leq2nu = leq_trans (ap1 s (ap1 s O)) (ap2 mu x three) (ap2 mu x ssx) leq2mu3 muGap2ssx
  in ruleTrans (congR sub (ap1 s (ap1 s O)) nuEq) leq2nu

------------------------------------------------------------------------
-- descSnd :  x >= 1  ->  Snd x < x .   (the headline; unconditional.)

descSnd : (x : Term) -> Deriv (leq (ap1 s O) x) ->
          Deriv (leq (ap1 s (ap1 Snd x)) x)
descSnd x xpos = descSnd_from x xpos (nuGe2 x xpos)
