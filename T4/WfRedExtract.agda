{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedExtract -- the EXTRACTION lemmas for the opaque cov-lift: from
-- wfRedSized(p)=O (p OPAQUE) recover the validity of the children and the
-- size-consistency the descent needs.  This is "local recovery inside the
-- verifier" (Thierry 2026-06-22): the size-prefix already won the GLOBAL
-- induction measure (dsize child < dsize p); here we only unfold the verifier
-- at an opaque code and project the conjunction.
--
-- Mechanism: foldOpaque (T4.SizedPres, eta-free unfold at p != O) puts
--   wfRedSized p = wfStep (opkg p) ;  the cascade dispatches on
--   nIdx(opkg p) = dtag p ;  the sigma-conjunction inverts via SigmaZeroN.
--
-- THIS FILE: the opaque-unfold harness (opUnfold / op_rc / op_nIdx / ...) and
-- the SIZE-CHECK extraction for the su case (Thierry's last bullet):
--   wfRedSized p = O  /\  dtag p = tagSu  ==>  leq (s (dsize (pArg p))) (dsize p)
-- which is exactly the  descSzU  input for covMeasure(dsize).  (The ad/rO/rS
-- size checks and the child-validity extractions follow the same pattern;
-- the child ones additionally use lookup_op + descSnd for the value bound.)
--
-- p != O is taken as a hypothesis here (discharged separately from the tag).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedExtract where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg ; pL ; pR ; dsize )
open import T4.DerCode  using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfStep ; unaryCell ; binaryCell ; chkU ; chkB
        ; dszSelf ; dszArg ; dszL ; dszR ; argIdx
        ; wfRestSu ; wfRestAd ; wfRestRO ; wfRestRS ; rejectCell ; w20 ; w30 ; w40 ; w10 )
open import T4.SizedFold using ( szRunF )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( get_newK ; get_newK_at_pi ; lookupAt )
open import T4.SizedPres using ( foldOpaque ; succForm )
open import T4.CoVSpec using ( cov_spec )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church      using ( pi ; sigma ; sub ; predecessor )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.PairAlgebra using ( Post ; axPost ; compose1U ; compose1U_eq )
open import T4.SigmaZeroN using ( sigmaZeroL ; sigmaZeroR )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.DescSnd  using ( descSnd )
open import T4.SndDescent using ( sndLe )
open import T4.TauRowBase using ( fstLe )
open import T4.Counting using ( nonzero_ge_one )
open import T4.TreeCovInd using ( leq_s_s_cancel )
open import T4.LeqMono using ( leq_trans )

------------------------------------------------------------------------
-- SECTION 1.  The opaque recovery package and the harness lemmas.

prevS : Term -> Term
prevS p = ap1 Snd (ap2 (cov_spec Z (Post wfStep pi)) O (ap1 predecessor p))

opkg : Term -> Term
opkg p = ap2 pi (ap1 predecessor p) (prevS p)

-- opUnfold :  wfRedSized p  unfolds (eta-free) to  wfStep (opkg p)  at p != O.
opUnfold : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) (ap1 wfStep (opkg p)))
opUnfold p ne =
  ruleTrans (foldOpaque Z (Post wfStep pi) p ne)
            (axPost wfStep pi (ap1 predecessor p) (prevS p))

-- get_newK (opkg p) = p  (via get_newK_at_pi + succForm).
op_newK : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 get_newK (opkg p)) p)
op_newK p ne =
  ruleTrans (get_newK_at_pi (ap1 predecessor p) (prevS p)) (succForm p ne)

-- get_rc (opkg p) = Snd p .
op_rc : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 get_rc (opkg p)) (ap1 Snd p))
op_rc p ne =
  ruleTrans (compose1U_eq Snd get_newK (opkg p)) (cong1 Snd (op_newK p ne))

-- nIdx (opkg p) = dtag p .
op_nIdx : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 nIdx (opkg p)) (dtag p))
op_nIdx p ne =
  ruleTrans (compose1U_eq Fst get_rc (opkg p)) (cong1 Fst (op_rc p ne))

-- argIdx (opkg p) = pArg p .
op_argIdx : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 argIdx (opkg p)) (pArg p))
op_argIdx p ne =
  ruleTrans (compose1U_eq Snd get_rc (opkg p)) (cong1 Snd (op_rc p ne))

-- dszSelf (opkg p) = dsize p .
op_dszSelf : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 dszSelf (opkg p)) (dsize p))
op_dszSelf p ne =
  ruleTrans (compose1U_eq Fst get_newK (opkg p)) (cong1 Fst (op_newK p ne))

-- dszArg (opkg p) = dsize (pArg p) .
op_dszArg : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 dszArg (opkg p)) (dsize (pArg p)))
op_dszArg p ne =
  ruleTrans (compose1U_eq Fst argIdx (opkg p)) (cong1 Fst (op_argIdx p ne))

-- binary-node harness:  lIdx (opkg p) = pL p , rIdx = pR p , and their sizes.
op_pL : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 lIdx (opkg p)) (pL p))
op_pL p ne =
  ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) (opkg p))
            (cong1 Fst (op_argIdx p ne))
op_pR : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 rIdx (opkg p)) (pR p))
op_pR p ne =
  ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) (opkg p))
            (cong1 Snd (op_argIdx p ne))
op_dszL : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 dszL (opkg p)) (dsize (pL p)))
op_dszL p ne = ruleTrans (compose1U_eq Fst lIdx (opkg p)) (cong1 Fst (op_pL p ne))
op_dszR : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 dszR (opkg p)) (dsize (pR p)))
op_dszR p ne = ruleTrans (compose1U_eq Fst rIdx (opkg p)) (cong1 Fst (op_pR p ne))

------------------------------------------------------------------------
-- SECTION 2.  Size-check extraction, factored by arity.
-- Given the cascade has fired the matching cell, invert the sigma-conjunction
-- (FIRST conjunct) and read the size-check term -- gives the  descSz  input.

unaryFromCell : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p))) ->
  Deriv (leq (ap1 s (dsize (pArg p))) (dsize p))
unaryFromCell p ne hwf cf =
  let opk : Term
      opk = opkg p
      sigmaEqO : Deriv (eqF (ap2 sigma (ap1 chkU opk) (ap1 (lookupAt argIdx) opk)) O)
      sigmaEqO = ruleTrans (ruleSym
                   (ruleTrans (opUnfold p ne)
                     (ruleTrans cf (ax_C sigma chkU (lookupAt argIdx) opk)))) hwf
      chkU_O : Deriv (eqF (ap1 chkU opk) O)
      chkU_O = mp (sigmaZeroL (ap1 chkU opk) (ap1 (lookupAt argIdx) opk)) sigmaEqO
      chkU_eq : Deriv (eqF (ap1 chkU opk)
                           (ap2 sub (ap1 s (dsize (pArg p))) (dsize p)))
      chkU_eq =
        ruleTrans (ax_C sub (compose1U s dszArg) dszSelf opk)
          (ruleTrans (congL sub (ap1 dszSelf opk)
                       (ruleTrans (compose1U_eq s dszArg opk) (cong1 s (op_dszArg p ne))))
                     (congR sub (ap1 s (dsize (pArg p))) (op_dszSelf p ne)))
  in ruleTrans (ruleSym chkU_eq) chkU_O

binaryFromCell : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (leq (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))) (dsize p))
binaryFromCell p ne hwf cf =
  let opk : Term
      opk = opkg p
      sigmaEqO : Deriv (eqF (ap2 sigma (ap1 chkB opk)
                              (ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)) O)
      sigmaEqO = ruleTrans (ruleSym
                   (ruleTrans (opUnfold p ne)
                     (ruleTrans cf (ax_C sigma chkB
                                     (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)))) hwf
      chkB_O : Deriv (eqF (ap1 chkB opk) O)
      chkB_O = mp (sigmaZeroL (ap1 chkB opk)
                    (ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)) sigmaEqO
      firstEq : Deriv (eqF (ap1 (compose1U s (C sigma dszL dszR)) opk)
                           (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))))
      firstEq = ruleTrans (compose1U_eq s (C sigma dszL dszR) opk)
                  (cong1 s (ruleTrans (ax_C sigma dszL dszR opk)
                             (ruleTrans (congL sigma (ap1 dszR opk) (op_dszL p ne))
                                        (congR sigma (dsize (pL p)) (op_dszR p ne)))))
      chkB_eq : Deriv (eqF (ap1 chkB opk)
                  (ap2 sub (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))) (dsize p)))
      chkB_eq =
        ruleTrans (ax_C sub (compose1U s (C sigma dszL dszR)) dszSelf opk)
          (ruleTrans (congL sub (ap1 dszSelf opk) firstEq)
                     (congR sub (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p))))
                            (op_dszSelf p ne)))
  in ruleTrans (ruleSym chkB_eq) chkB_O

------------------------------------------------------------------------
-- SECTION 3.  The four size-check extractions (cascade per tag).

extractSizeCheck_Su : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (leq (ap1 s (dsize (pArg p))) (dsize p))
extractSizeCheck_Su p ne htag hwf =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgSu)
      nieq = ruleTrans (op_nIdx p ne) htag
  in unaryFromCell p ne hwf
       (ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                     (testEq_skip 1 0 opk w10 nieq))
                  (fork_true_to_fst unaryCell wfRestAd (testEq 1) opk
                     (testEq_fire 1 opk nieq)))

extractSizeCheck_Ad : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (leq (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))) (dsize p))
extractSizeCheck_Ad p ne htag hwf =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
      nieq = ruleTrans (op_nIdx p ne) htag
  in binaryFromCell p ne hwf
       (ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                     (testEq_skip 2 0 opk w20 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                        (testEq_skip 2 1 opk w21 nieq))
                     (fork_true_to_fst binaryCell wfRestRO (testEq 2) opk
                        (testEq_fire 2 opk nieq))))

extractSizeCheck_RO : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (leq (ap1 s (dsize (pArg p))) (dsize p))
extractSizeCheck_RO p ne htag hwf =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRO)
      nieq = ruleTrans (op_nIdx p ne) htag
  in unaryFromCell p ne hwf
       (ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                     (testEq_skip 3 0 opk w30 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                        (testEq_skip 3 1 opk w31 nieq))
            (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) opk
                          (testEq_skip 3 2 opk w32 nieq))
                       (fork_true_to_fst unaryCell wfRestRS (testEq 3) opk
                          (testEq_fire 3 opk nieq)))))

extractSizeCheck_RS : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (leq (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))) (dsize p))
extractSizeCheck_RS p ne htag hwf =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRS)
      nieq = ruleTrans (op_nIdx p ne) htag
  in binaryFromCell p ne hwf
       (ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                     (testEq_skip 4 0 opk w40 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                        (testEq_skip 4 1 opk w41 nieq))
            (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) opk
                          (testEq_skip 4 2 opk w42 nieq))
              (ruleTrans (fork_false_to_snd unaryCell wfRestRS (testEq 3) opk
                            (testEq_skip 4 3 opk w43 nieq))
                         (fork_true_to_fst binaryCell rejectCell (testEq 4) opk
                            (testEq_fire 4 opk nieq))))))

------------------------------------------------------------------------
-- SECTION 4.  Child-validity extraction.
-- The size-prefix already won the GLOBAL descent; here we only recover the
-- folded child value (local), bounded by  predecessor p  (the lookup_op value
-- bound) via the FREE  Snd-descent  sndLe + descSnd .  This works for the UNARY
-- child (pArg = Snd (Snd p)) and the binary RIGHT child (pR = Snd (pArg p)).
-- The binary LEFT child (pL = Fst (pArg p)) additionally needs
--   fstLe : leq (Fst x) x
-- which is NOT yet in the codebase (Snd x = sub x c is free; Fst is nu-based --
-- see T4.SndDescent's notes).  So the dAd/dRS LEFT-child extraction is BLOCKED
-- on  fstLe  (a finite nu-arithmetic lemma), and is the one remaining gap.

-- value bound:  pArg p <= predecessor p   (Snd-descent, free).
argValueBound : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (leq (pArg p) (ap1 predecessor p))
argValueBound p ne =
  let pos : Deriv (leq (ap1 s O) p)
      pos = nonzero_ge_one p ne
      dscS : Deriv (leq (ap1 s (ap1 Snd p)) (ap1 s (ap1 predecessor p)))
      dscS = ruleTrans (congR sub (ap1 s (ap1 Snd p)) (succForm p ne))
                       (descSnd p pos)
      sndLeP : Deriv (leq (ap1 Snd p) (ap1 predecessor p))
      sndLeP = leq_s_s_cancel (ap1 Snd p) (ap1 predecessor p) dscS
  in leq_trans (pArg p) (ap1 Snd p) (ap1 predecessor p) (sndLe (ap1 Snd p)) sndLeP

-- given the cascade fired the unary cell, recover  wfRedSized (pArg p) = O .
childFromCellU : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p))) ->
  Deriv (eqF (ap1 wfRedSized (pArg p)) O)
childFromCellU p ne hwf cf =
  let opk : Term
      opk = opkg p
      sigmaEqO : Deriv (eqF (ap2 sigma (ap1 chkU opk) (ap1 (lookupAt argIdx) opk)) O)
      sigmaEqO = ruleTrans (ruleSym
                   (ruleTrans (opUnfold p ne)
                     (ruleTrans cf (ax_C sigma chkU (lookupAt argIdx) opk)))) hwf
      argO : Deriv (eqF (ap1 (lookupAt argIdx) opk) O)
      argO = mp (sigmaZeroR (ap1 chkU opk) (ap1 (lookupAt argIdx) opk)) sigmaEqO
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) opk) (ap1 wfRedSized (pArg p)))
      recArg = lookup_op Z wfStep argIdx (ap1 predecessor p) (pArg p)
                 (op_argIdx p ne) (argValueBound p ne)
  in ruleTrans (ruleSym recArg) argO

extractChild_Su : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfRedSized (pArg p)) O)
extractChild_Su p ne htag hwf =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgSu)
      nieq = ruleTrans (op_nIdx p ne) htag
  in childFromCellU p ne hwf
       (ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                     (testEq_skip 1 0 opk w10 nieq))
                  (fork_true_to_fst unaryCell wfRestAd (testEq 1) opk
                     (testEq_fire 1 opk nieq)))

extractChild_RO : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfRedSized (pArg p)) O)
extractChild_RO p ne htag hwf =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRO)
      nieq = ruleTrans (op_nIdx p ne) htag
  in childFromCellU p ne hwf
       (ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                     (testEq_skip 3 0 opk w30 nieq))
          (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                        (testEq_skip 3 1 opk w31 nieq))
            (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) opk
                          (testEq_skip 3 2 opk w32 nieq))
                       (fork_true_to_fst unaryCell wfRestRS (testEq 3) opk
                          (testEq_fire 3 opk nieq)))))

------------------------------------------------------------------------
-- SECTION 5.  Binary child-validity extraction (LEFT + RIGHT).
-- LEFT child  pL p = Fst (pArg p)  now bounded via  fstLe (the Cantor row-base
-- lemma, T4.TauRowBase) :  pL p <= pArg p <= predecessor p .  RIGHT child
-- pR p = Snd (pArg p)  via the free Snd-descent  sndLe + argValueBound .

-- value bound:  pL p <= predecessor p .
pLValueBound : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (leq (pL p) (ap1 predecessor p))
pLValueBound p ne =
  leq_trans (pL p) (pArg p) (ap1 predecessor p)
    (fstLe (pArg p)) (argValueBound p ne)

-- value bound:  pR p <= predecessor p .
pRValueBound : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (leq (pR p) (ap1 predecessor p))
pRValueBound p ne =
  leq_trans (pR p) (pArg p) (ap1 predecessor p)
    (sndLe (pArg p)) (argValueBound p ne)

-- the inner sigma  sigma (lookupAt lIdx)(lookupAt rIdx) = O  from the binary
-- cell (SECOND conjunct of binaryCell, via sigmaZeroR + ax_C).
binChildSigmaO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (eqF (ap2 sigma (ap1 (lookupAt lIdx) (opkg p))
                        (ap1 (lookupAt rIdx) (opkg p))) O)
binChildSigmaO p ne hwf cf =
  let opk : Term
      opk = opkg p
      sigmaEqO : Deriv (eqF (ap2 sigma (ap1 chkB opk)
                              (ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)) O)
      sigmaEqO = ruleTrans (ruleSym
                   (ruleTrans (opUnfold p ne)
                     (ruleTrans cf (ax_C sigma chkB
                                     (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)))) hwf
      innerEqO : Deriv (eqF (ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk) O)
      innerEqO = mp (sigmaZeroR (ap1 chkB opk)
                      (ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)) sigmaEqO
  in ruleTrans (ruleSym (ax_C sigma (lookupAt lIdx) (lookupAt rIdx) opk)) innerEqO

-- recover  wfRedSized (pL p) = O  from a fired binary cell.
childFromCellL : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (eqF (ap1 wfRedSized (pL p)) O)
childFromCellL p ne hwf cf =
  let opk : Term
      opk = opkg p
      lO : Deriv (eqF (ap1 (lookupAt lIdx) opk) O)
      lO = mp (sigmaZeroL (ap1 (lookupAt lIdx) opk) (ap1 (lookupAt rIdx) opk))
              (binChildSigmaO p ne hwf cf)
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 wfRedSized (pL p)))
      recL = lookup_op Z wfStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
  in ruleTrans (ruleSym recL) lO

-- recover  wfRedSized (pR p) = O  from a fired binary cell.
childFromCellR : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (eqF (ap1 wfRedSized (pR p)) O)
childFromCellR p ne hwf cf =
  let opk : Term
      opk = opkg p
      rO : Deriv (eqF (ap1 (lookupAt rIdx) opk) O)
      rO = mp (sigmaZeroR (ap1 (lookupAt lIdx) opk) (ap1 (lookupAt rIdx) opk))
              (binChildSigmaO p ne hwf cf)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 wfRedSized (pR p)))
      recR = lookup_op Z wfStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
  in ruleTrans (ruleSym recR) rO

-- the binary-cell firing for the Ad / RS tags (shared by size-check + children).
binCellAd : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p)))
binCellAd p ne htag =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
      nieq = ruleTrans (op_nIdx p ne) htag
  in ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                  (testEq_skip 2 0 opk w20 nieq))
       (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                     (testEq_skip 2 1 opk w21 nieq))
                  (fork_true_to_fst binaryCell wfRestRO (testEq 2) opk
                     (testEq_fire 2 opk nieq)))

binCellRS : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p)))
binCellRS p ne htag =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRS)
      nieq = ruleTrans (op_nIdx p ne) htag
  in ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                  (testEq_skip 4 0 opk w40 nieq))
       (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                     (testEq_skip 4 1 opk w41 nieq))
         (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) opk
                       (testEq_skip 4 2 opk w42 nieq))
           (ruleTrans (fork_false_to_snd unaryCell wfRestRS (testEq 3) opk
                         (testEq_skip 4 3 opk w43 nieq))
                      (fork_true_to_fst binaryCell rejectCell (testEq 4) opk
                         (testEq_fire 4 opk nieq)))))

extractChild_Ad_L : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfRedSized (pL p)) O)
extractChild_Ad_L p ne htag hwf = childFromCellL p ne hwf (binCellAd p ne htag)

extractChild_Ad_R : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfRedSized (pR p)) O)
extractChild_Ad_R p ne htag hwf = childFromCellR p ne hwf (binCellAd p ne htag)

extractChild_RS_L : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfRedSized (pL p)) O)
extractChild_RS_L p ne htag hwf = childFromCellL p ne hwf (binCellRS p ne htag)

extractChild_RS_R : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 wfRedSized p) O) ->
  Deriv (eqF (ap1 wfRedSized (pR p)) O)
extractChild_RS_R p ne htag hwf = childFromCellR p ne hwf (binCellRS p ne htag)
