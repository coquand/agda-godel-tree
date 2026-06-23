{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedSized -- the STRICT validity predicate over the SIZE-PREFIXED coding
-- (T4.DerCodeS), as a sized FoldRec fold (T4.SizedFold.szRunF), checking:
--   (1) tag validity (dtag in 0..4, else reject),
--   (2) child validity (recursive),
--   (3) ONE-SIDED size consistency  sub (canonical) (dsize p) = O , i.e.
--       leq (canonical) (dsize p)  -- exactly what  descSz  needs (no eqTest,
--       no antisymmetry; canonical = s(sigma(dsize l)(dsize r)) binary /
--       s(dsize arg) unary).
--
-- Defining equations on BUILT nodes (the size check passes via  sub_self ):
--   wfRedSized (szDerZe)       = O
--   wfRedSized (szDerSu d)     = sigma O (wfRedSized d)
--   wfRedSized (szDerAd d1 d2) = sigma O (sigma (wfRedSized d1) (wfRedSized d2))
--   wfRedSized (szDerRO d)     = sigma O (wfRedSized d)
--   wfRedSized (szDerRS d1 d2) = sigma O (sigma (wfRedSized d1) (wfRedSized d2))
--
-- The node cell reuses the DerSrc cascade (nIdx = Fst body = dtag for sized
-- codes) + the sized harness lemmas.  (THIS FILE: cells + leaf + su; the ad/rO/
-- rS equations and the OPAQUE extraction lemmas follow.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedSized where

open import T4.Base

open import T4.DerCodeS
  using ( szDerZe ; szDerSu ; szDerAd ; szDerRO ; szDerRS ; dsize )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.SizedFold
  using ( szRunF ; szPkg ; Pout ; sz_unfold ; sz_rc ; sz_lookup ; sz_leq_b ; sz_self )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt ; get_newK )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church      using ( pi ; sigma ; sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import T4.LeqMono using ( leq_trans ; leq_pi_right )
open import T4.LeqPiLeft using ( leq_pi_left )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Index Fun1s and the cells.

dszSelf : Fun1                          -- dsize p  = Fst (get_newK pkg)
dszSelf = compose1U Fst get_newK

argIdx : Fun1                           -- pArg     = Snd (get_rc)
argIdx = compose1U Snd get_rc
dszArg : Fun1
dszArg = compose1U Fst argIdx
dszL : Fun1
dszL = compose1U Fst lIdx
dszR : Fun1
dszR = compose1U Fst rIdx

chkU : Fun1                             -- sub (s (dsize pArg)) (dsize p)
chkU = C sub (compose1U s dszArg) dszSelf
chkB : Fun1                             -- sub (s (sigma (dsize l)(dsize r))) (dsize p)
chkB = C sub (compose1U s (C sigma dszL dszR)) dszSelf

unaryCell : Fun1
unaryCell = C sigma chkU (lookupAt argIdx)
binaryCell : Fun1
binaryCell = C sigma chkB (C sigma (lookupAt lIdx) (lookupAt rIdx))

rejectCell : Fun1
rejectCell = constN 1

------------------------------------------------------------------------
-- SECTION 2.  The 5-way dtag cascade and  wfRedSized .

wfRestRS : Fun1
wfRestRS = C condFork (C pi binaryCell rejectCell) (testEq 4)
wfRestRO : Fun1
wfRestRO = C condFork (C pi unaryCell wfRestRS) (testEq 3)
wfRestAd : Fun1
wfRestAd = C condFork (C pi binaryCell wfRestRO) (testEq 2)
wfRestSu : Fun1
wfRestSu = C condFork (C pi unaryCell wfRestAd) (testEq 1)
wfStep : Fun1
wfStep = C condFork (C pi Z wfRestSu) (testEq 0)

wfRedSized : Fun1
wfRedSized = szRunF wfStep

------------------------------------------------------------------------
-- neq witnesses (tag k vs 0 ; the others come from DerSrc).

w10 : NatNeqWitness 1 0
w10 = decideNatNeq 1 0 (\ ())
w20 : NatNeqWitness 2 0
w20 = decideNatNeq 2 0 (\ ())
w30 : NatNeqWitness 3 0
w30 = decideNatNeq 3 0 (\ ())
w40 : NatNeqWitness 4 0
w40 = decideNatNeq 4 0 (\ ())

------------------------------------------------------------------------
-- SECTION 3.  Leaf:  wfRedSized (szDerZe) = O .

wfRedSized_Ze : Deriv (eqF (ap1 wfRedSized szDerZe) O)
wfRedSized_Ze =
  let A : Term
      A = O
      b : Term
      b = ap2 Pair dgZe O
      pkg : Term
      pkg = szPkg wfStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgZe)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc wfStep A b)) (axFst dgZe O))
      cell_fires : Deriv (eqF (ap1 wfStep pkg) (ap1 Z pkg))
      cell_fires = fork_true_to_fst Z wfRestSu (testEq 0) pkg
                     (testEq_fire 0 pkg nieq)
  in ruleTrans (sz_unfold wfStep A b) (ruleTrans cell_fires (axZ pkg))

------------------------------------------------------------------------
-- SECTION 4.  su:  wfRedSized (szDerSu d) = sigma O (wfRedSized d) .

wfRedSized_Su : (d : Term) ->
  Deriv (eqF (ap1 wfRedSized (szDerSu d)) (ap2 sigma O (ap1 wfRedSized d)))
wfRedSized_Su d =
  let A : Term
      A = dsize d
      b : Term
      b = ap2 Pair dgSu d
      pkg : Term
      pkg = szPkg wfStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgSu)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc wfStep A b)) (axFst dgSu d))
      -- cascade : skip tag 0, fire tag 1 -> unaryCell.
      cell_fires : Deriv (eqF (ap1 wfStep pkg) (ap1 unaryCell pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) pkg
                     (testEq_skip 1 0 pkg w10 nieq))
                  (fork_true_to_fst unaryCell wfRestAd (testEq 1) pkg
                     (testEq_fire 1 pkg nieq))
      -- argIdx pkg = d  (the child).
      argIdx_eq : Deriv (eqF (ap1 argIdx pkg) d)
      argIdx_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                    (ruleTrans (cong1 Snd (sz_rc wfStep A b)) (axSnd dgSu d))
      dszArg_eq : Deriv (eqF (ap1 dszArg pkg) (dsize d))
      dszArg_eq = ruleTrans (compose1U_eq Fst argIdx pkg) (cong1 Fst argIdx_eq)
      -- size check  sub (s (dsize d)) (dsize p)  collapses to O (sub_self).
      chkU_O : Deriv (eqF (ap1 chkU pkg) O)
      chkU_O =
        ruleTrans (ax_C sub (compose1U s dszArg) dszSelf pkg)
          (ruleTrans (congL sub (ap1 dszSelf pkg)
                       (ruleTrans (compose1U_eq s dszArg pkg) (cong1 s dszArg_eq)))
            (ruleTrans (congR sub (ap1 s (dsize d)) (sz_self wfStep A b))
                       (sub_self (ap1 s (dsize d)))))
      -- child validity recovered.
      leq_d : Deriv (leq d (Pout A b))
      leq_d = leq_trans d b (Pout A b) (leq_pi_right dgSu d) (sz_leq_b A b)
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) pkg) (ap1 wfRedSized d))
      recArg = sz_lookup wfStep argIdx A b d argIdx_eq leq_d
      cell_val : Deriv (eqF (ap1 unaryCell pkg) (ap2 sigma O (ap1 wfRedSized d)))
      cell_val =
        ruleTrans (ax_C sigma chkU (lookupAt argIdx) pkg)
          (ruleTrans (congL sigma (ap1 (lookupAt argIdx) pkg) chkU_O)
                     (congR sigma O recArg))
  in ruleTrans (sz_unfold wfStep A b) (ruleTrans cell_fires cell_val)

------------------------------------------------------------------------
-- SECTION 5.  Shared cell-value helpers (generic in the tag  dgX ).

unaryCellVal : (dgX d : Term) ->
  Deriv (eqF (ap1 unaryCell (szPkg wfStep (dsize d) (ap2 Pair dgX d)))
             (ap2 sigma O (ap1 wfRedSized d)))
unaryCellVal dgX d =
  let A : Term
      A = dsize d
      b : Term
      b = ap2 Pair dgX d
      pkg : Term
      pkg = szPkg wfStep A b
      argIdx_eq : Deriv (eqF (ap1 argIdx pkg) d)
      argIdx_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                    (ruleTrans (cong1 Snd (sz_rc wfStep A b)) (axSnd dgX d))
      dszArg_eq : Deriv (eqF (ap1 dszArg pkg) (dsize d))
      dszArg_eq = ruleTrans (compose1U_eq Fst argIdx pkg) (cong1 Fst argIdx_eq)
      chkU_O : Deriv (eqF (ap1 chkU pkg) O)
      chkU_O =
        ruleTrans (ax_C sub (compose1U s dszArg) dszSelf pkg)
          (ruleTrans (congL sub (ap1 dszSelf pkg)
                       (ruleTrans (compose1U_eq s dszArg pkg) (cong1 s dszArg_eq)))
            (ruleTrans (congR sub (ap1 s (dsize d)) (sz_self wfStep A b))
                       (sub_self (ap1 s (dsize d)))))
      leq_d : Deriv (leq d (Pout A b))
      leq_d = leq_trans d b (Pout A b) (leq_pi_right dgX d) (sz_leq_b A b)
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) pkg) (ap1 wfRedSized d))
      recArg = sz_lookup wfStep argIdx A b d argIdx_eq leq_d
  in ruleTrans (ax_C sigma chkU (lookupAt argIdx) pkg)
       (ruleTrans (congL sigma (ap1 (lookupAt argIdx) pkg) chkU_O)
                  (congR sigma O recArg))

binaryCellVal : (dgX d1 d2 : Term) ->
  Deriv (eqF (ap1 binaryCell
               (szPkg wfStep (ap2 sigma (dsize d1) (dsize d2))
                 (ap2 Pair dgX (ap2 Pair d1 d2))))
             (ap2 sigma O (ap2 sigma (ap1 wfRedSized d1) (ap1 wfRedSized d2))))
binaryCellVal dgX d1 d2 =
  let A : Term
      A = ap2 sigma (dsize d1) (dsize d2)
      b : Term
      b = ap2 Pair dgX (ap2 Pair d1 d2)
      pkg : Term
      pkg = szPkg wfStep A b
      sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) pkg) (ap2 Pair d1 d2))
      sndArg_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                    (ruleTrans (cong1 Snd (sz_rc wfStep A b)) (axSnd dgX (ap2 Pair d1 d2)))
      lIdx_eq : Deriv (eqF (ap1 lIdx pkg) d1)
      lIdx_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) pkg)
                  (ruleTrans (cong1 Fst sndArg_eq) (axFst d1 d2))
      rIdx_eq : Deriv (eqF (ap1 rIdx pkg) d2)
      rIdx_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) pkg)
                  (ruleTrans (cong1 Snd sndArg_eq) (axSnd d1 d2))
      dszL_eq : Deriv (eqF (ap1 dszL pkg) (dsize d1))
      dszL_eq = ruleTrans (compose1U_eq Fst lIdx pkg) (cong1 Fst lIdx_eq)
      dszR_eq : Deriv (eqF (ap1 dszR pkg) (dsize d2))
      dszR_eq = ruleTrans (compose1U_eq Fst rIdx pkg) (cong1 Fst rIdx_eq)
      firstEq : Deriv (eqF (ap1 (compose1U s (C sigma dszL dszR)) pkg) (ap1 s A))
      firstEq = ruleTrans (compose1U_eq s (C sigma dszL dszR) pkg)
                  (cong1 s (ruleTrans (ax_C sigma dszL dszR pkg)
                             (ruleTrans (congL sigma (ap1 dszR pkg) dszL_eq)
                                        (congR sigma (dsize d1) dszR_eq))))
      chkB_O : Deriv (eqF (ap1 chkB pkg) O)
      chkB_O =
        ruleTrans (ax_C sub (compose1U s (C sigma dszL dszR)) dszSelf pkg)
          (ruleTrans (congL sub (ap1 dszSelf pkg) firstEq)
            (ruleTrans (congR sub (ap1 s A) (sz_self wfStep A b))
                       (sub_self (ap1 s A))))
      leq_d1 : Deriv (leq d1 (Pout A b))
      leq_d1 = leq_trans d1 (ap2 Pair d1 d2) (Pout A b) (leq_pi_left d1 d2)
                 (leq_trans (ap2 Pair d1 d2) b (Pout A b)
                    (leq_pi_right dgX (ap2 Pair d1 d2)) (sz_leq_b A b))
      leq_d2 : Deriv (leq d2 (Pout A b))
      leq_d2 = leq_trans d2 (ap2 Pair d1 d2) (Pout A b) (leq_pi_right d1 d2)
                 (leq_trans (ap2 Pair d1 d2) b (Pout A b)
                    (leq_pi_right dgX (ap2 Pair d1 d2)) (sz_leq_b A b))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) pkg) (ap1 wfRedSized d1))
      recL = sz_lookup wfStep lIdx A b d1 lIdx_eq leq_d1
      recR : Deriv (eqF (ap1 (lookupAt rIdx) pkg) (ap1 wfRedSized d2))
      recR = sz_lookup wfStep rIdx A b d2 rIdx_eq leq_d2
  in ruleTrans (ax_C sigma chkB (C sigma (lookupAt lIdx) (lookupAt rIdx)) pkg)
       (ruleTrans (congL sigma (ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) pkg) chkB_O)
         (congR sigma O
           (ruleTrans (ax_C sigma (lookupAt lIdx) (lookupAt rIdx) pkg)
             (ruleTrans (congL sigma (ap1 (lookupAt rIdx) pkg) recL)
                        (congR sigma (ap1 wfRedSized d1) recR)))))

------------------------------------------------------------------------
-- SECTION 6.  ad / rO / rS  defining equations.

wfRedSized_Ad : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRedSized (szDerAd d1 d2))
             (ap2 sigma O (ap2 sigma (ap1 wfRedSized d1) (ap1 wfRedSized d2))))
wfRedSized_Ad d1 d2 =
  let A : Term
      A = ap2 sigma (dsize d1) (dsize d2)
      b : Term
      b = ap2 Pair dgAd (ap2 Pair d1 d2)
      pkg : Term
      pkg = szPkg wfStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgAd)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc wfStep A b)) (axFst dgAd (ap2 Pair d1 d2)))
      cell_fires : Deriv (eqF (ap1 wfStep pkg) (ap1 binaryCell pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) pkg
                     (testEq_skip 2 0 pkg w20 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) pkg
                        (testEq_skip 2 1 pkg w21 nieq))
                     (fork_true_to_fst binaryCell wfRestRO (testEq 2) pkg
                        (testEq_fire 2 pkg nieq)))
  in ruleTrans (sz_unfold wfStep A b)
       (ruleTrans cell_fires (binaryCellVal dgAd d1 d2))

wfRedSized_RO : (d : Term) ->
  Deriv (eqF (ap1 wfRedSized (szDerRO d)) (ap2 sigma O (ap1 wfRedSized d)))
wfRedSized_RO d =
  let A : Term
      A = dsize d
      b : Term
      b = ap2 Pair dgRO d
      pkg : Term
      pkg = szPkg wfStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgRO)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc wfStep A b)) (axFst dgRO d))
      cell_fires : Deriv (eqF (ap1 wfStep pkg) (ap1 unaryCell pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) pkg
                     (testEq_skip 3 0 pkg w30 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) pkg
                        (testEq_skip 3 1 pkg w31 nieq))
            (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) pkg
                          (testEq_skip 3 2 pkg w32 nieq))
                       (fork_true_to_fst unaryCell wfRestRS (testEq 3) pkg
                          (testEq_fire 3 pkg nieq))))
  in ruleTrans (sz_unfold wfStep A b)
       (ruleTrans cell_fires (unaryCellVal dgRO d))

wfRedSized_RS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRedSized (szDerRS d1 d2))
             (ap2 sigma O (ap2 sigma (ap1 wfRedSized d1) (ap1 wfRedSized d2))))
wfRedSized_RS d1 d2 =
  let A : Term
      A = ap2 sigma (dsize d1) (dsize d2)
      b : Term
      b = ap2 Pair dgRS (ap2 Pair d1 d2)
      pkg : Term
      pkg = szPkg wfStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgRS)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc wfStep A b)) (axFst dgRS (ap2 Pair d1 d2)))
      cell_fires : Deriv (eqF (ap1 wfStep pkg) (ap1 binaryCell pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) pkg
                     (testEq_skip 4 0 pkg w40 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) pkg
                        (testEq_skip 4 1 pkg w41 nieq))
            (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) pkg
                          (testEq_skip 4 2 pkg w42 nieq))
              (ruleTrans (fork_false_to_snd unaryCell wfRestRS (testEq 3) pkg
                            (testEq_skip 4 3 pkg w43 nieq))
                         (fork_true_to_fst binaryCell rejectCell (testEq 4) pkg
                            (testEq_fire 4 pkg nieq)))))
  in ruleTrans (sz_unfold wfStep A b)
       (ruleTrans cell_fires (binaryCellVal dgRS d1 d2))
