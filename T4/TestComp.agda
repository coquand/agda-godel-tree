{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.TestComp -- the COMPRESSIBILITY RECOGNISER test_comp : Fun2 (recogniser
-- plan C.2, CHAITIN-G1-ATOM-CORRECTION.md / NEXT-SESSION-CHAITIN-G1-RECOGNISER.md
-- Part B.1).  It is the per-index test of the bounded-exists indicator
-- compHit_L = IndU.existsHitU test_comp (T4.ExistsHitU):
--
--   test_comp(x, j) = isEqForm(thmT(enum j))                 -- head tag = tag_eq
--                   . szLeq(lhsOf(thmT(enum j)))             -- LHS code-size <= L'
--                   . eqInd(rhsOf(thmT(enum j)), num x) .    -- RHS value-slot = num x
--
-- EXTRACTION, NEVER CONSTRUCTION (the load-bearing invariant).  The test READS
-- thmT(enum j) -- a closed code -- via the shipped Fst/Snd projectors:
--   * head    = Fst (thmT(enum j))              compared to  natCode tag_eq ;
--   * lhsOf    = Fst (Snd (thmT(enum j)))        its code-SIZE checked by szLeq ;
--   * rhsOf    = Snd (Snd (thmT(enum j)))        compared to  num x  by eqInd .
-- The subject  x  enters ONLY as  num x  (Nelson Name x); the PROGRAM is whatever
-- lhsOf decodes to and is NEVER decoded/coded/run -- only its code-size matters.
-- So NO codeTermF (no object syntax-coder for arbitrary programs): the existential
-- over programs lives inside the formula, discharged on dPos by Sigma_1-completeness
-- (thm13) with the search machine as witness.  This is the corrected (extraction)
-- route; the naive "build <p = num x> from p" reading is a mis-modelling.
--
-- The three 0/1 factors are AND-ed by the condFork idiom  andInd  (the same
-- 0/1 dispatch as T4.ExistsHit's step; NO multiplication monotonicity needed).
-- enum : Fun1 (proof enumerator, concrete in C.5) and szLeq : Fun1 (the
-- code-size-<=-L' indicator, concrete in C.5 with dLen) are MODULE PARAMETERS;
-- this isolates the genuinely-deferred infrastructure (enum, dLen) as clean
-- hypotheses fed to  test_comp_fires .
--
-- Deliverables:
--   test_comp_le_one : (x j) -> leq (test_comp x j) 1                 -- IndU's test_le_one
--   test_comp_fires  : (x j lhs) ->                                   -- C.3's witness firing
--       thmT(enum j) = <tag_eq, <lhs, num x>>  ->  szLeq lhs = 1  ->  test_comp x j = 1

module T4.TestComp where

open import T4.Base
open import T4.Tags    using ( tag_eq )
open import T4.ThmT    using ( thmT )
open import T4.Num     using ( num )
open import T4.PHP     using ( byCases ; indLt )
open import T4.Counting
  using ( eqInd ; eqInd_le_one ; leq_of_left_zero_imp )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )

open import BRA3.Church          using ( pi ; sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchSubSucc   using ( T_sub_O )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; sub_succ_self )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive  using ( compI )
open import T4.ExistsHit       using ( le_one_neq_zero )

------------------------------------------------------------------------
-- SECTION 0.  Generic 0/1 helpers (subject- and recogniser-independent).

-- eqInd at equal arguments fires:  eqInd a a = 1 .
--   eqInd a a = sub (indLt a (s a)) (indLt a a) ;
--   indLt a (s a) = sub (s O) (sub (s a) (s a)) = sub (s O) O = s O  [sub_self, T_sub_O] ;
--   indLt a a     = sub (s O) (sub (s a) a)     = sub (s O) (s O) = O [sub_succ_self, sub_self] ;
--   eqInd a a     = sub (s O) O = s O .
eqInd_at_eq : (a : Term) -> Deriv (eqF (eqInd a a) (ap1 s O))
eqInd_at_eq a =
  let e_hi : Deriv (eqF (indLt a (ap1 s a)) (ap1 s O))
      e_hi = ruleTrans (congR sub (ap1 s O) (sub_self (ap1 s a))) (T_sub_O (ap1 s O))
      e_lo : Deriv (eqF (indLt a a) O)
      e_lo = ruleTrans (congR sub (ap1 s O) (sub_succ_self a)) (sub_self (ap1 s O))
  in ruleTrans (congL sub (indLt a a) e_hi)
       (ruleTrans (congR sub (ap1 s O) e_lo) (T_sub_O (ap1 s O)))

-- leq congruence on the subject (left argument).
leqLeftCong :
  (c c' d : Term) -> Deriv (eqF c c') -> Deriv (leq c' d) -> Deriv (leq c d)
leqLeftCong c c' d e lcd =
  mp (prependEqLeft (ap2 sub c d) (ap2 sub c' d) O (congL sub d e)) lcd

-- the 0/1 conjunction:  andInd a b = condFork (pi b O) a , i.e.
--   a /= 0  =>  andInd a b = Fst (pi b O) = b ;
--   a  = 0  =>  andInd a b = Snd (pi b O) = O .
andInd : Term -> Term -> Term
andInd a b = ap2 condFork (ap2 pi b O) a

-- a = 1 and b = 1  =>  andInd a b = 1 .
andInd_fires :
  (a b : Term) ->
  Deriv (eqF a (ap1 s O)) -> Deriv (eqF b (ap1 s O)) ->
  Deriv (eqF (andInd a b) (ap1 s O))
andInd_fires a b ha hb =
  ruleTrans (congR condFork (ap2 pi b O) ha)
    (ruleTrans (condFork_true_nc (ap2 pi b O) O)
      (ruleTrans (axFst b O) hb))

-- a <= 1 and b <= 1  =>  andInd a b <= 1 .
andInd_le_one :
  (a b : Term) ->
  Deriv (leq a (ap1 s O)) -> Deriv (leq b (ap1 s O)) ->
  Deriv (leq (andInd a b) (ap1 s O))
andInd_le_one a b la1 lb1 =
  byCases (eqF a O) (leq (andInd a b) (ap1 s O)) h_eq h_neq
  where
    -- a = O  =>  andInd a b = O  <=  1 .
    cf_O : Deriv (eqF (ap2 condFork (ap2 pi b O) O) O)
    cf_O = ruleTrans (condFork_false (ap2 pi b O)) (axSnd b O)
    e_andO : Deriv (imp (eqF a O) (eqF (andInd a b) O))
    e_andO = compI (ax_eqCongR condFork a O (ap2 pi b O))
                   (appendEqRight (andInd a b) (ap2 condFork (ap2 pi b O) O) O cf_O)
    h_eq : Deriv (imp (eqF a O) (leq (andInd a b) (ap1 s O)))
    h_eq = compI e_andO (leq_of_left_zero_imp (andInd a b) (ap1 s O))
    -- a /= O (with a <= 1) => a = 1 => andInd a b = b <= 1 .
    cfOne : Deriv (eqF (ap2 condFork (ap2 pi b O) (ap1 s O)) b)
    cfOne = ruleTrans (condFork_true_nc (ap2 pi b O) O) (axFst b O)
    e_andb : Deriv (imp (neg (eqF a O)) (eqF (andInd a b) b))
    e_andb = compI (le_one_neq_zero a la1)
                   (compI (ax_eqCongR condFork a (ap1 s O) (ap2 pi b O))
                          (appendEqRight (andInd a b) (ap2 condFork (ap2 pi b O) (ap1 s O)) b cfOne))
    leqFromEq : Deriv (imp (eqF (andInd a b) b) (leq (andInd a b) (ap1 s O)))
    leqFromEq = compI (ax_eqCongL sub (andInd a b) b (ap1 s O))
                      (appendEqRight (ap2 sub (andInd a b) (ap1 s O)) (ap2 sub b (ap1 s O)) O lb1)
    h_neq : Deriv (imp (neg (eqF a O)) (leq (andInd a b) (ap1 s O)))
    h_neq = compI e_andb leqFromEq

------------------------------------------------------------------------
-- SECTION 1.  The recogniser test_comp, parametric in  enum  and  szLeq .

module Rec
  (enum  : Fun1)                                          -- proof enumerator (length-lex; C.5)
  (szLeq : Fun1)                                          -- code-size-<=-L' indicator (C.5/dLen)
  (szLeq_le_one : (c : Term) -> Deriv (leq (ap1 szLeq c) (ap1 s O)))
  where

  -- meta abbreviations (the READS: projections of thmT(enum j)).
  Wj : Term -> Term
  Wj j = ap1 thmT (ap1 enum j)
  headEq : Term -> Term
  headEq j = eqInd (ap1 Fst (Wj j)) (natCode tag_eq)
  szOk : Term -> Term
  szOk j = ap1 szLeq (ap1 Fst (ap1 Snd (Wj j)))
  rhsOf : Term -> Term
  rhsOf j = ap1 Snd (ap1 Snd (Wj j))
  valEq : Term -> Term -> Term
  valEq x j = eqInd (rhsOf j) (ap1 num x)

  ----------------------------------------------------------------------
  -- The Fun2 combinators.

  -- andInd as a Fun2:  ap2 andIndF p q = andInd p q = condFork (pi q O) p .
  andIndF : Fun2
  andIndF = Fan (Fan v (Lift1 o) pi) Const condFork

  andIndF_eq :
    (p q : Term) -> Deriv (eqF (ap2 andIndF p q) (andInd p q))
  andIndF_eq p q =
    let inner_left : Deriv (eqF (ap2 (Fan v (Lift1 o) pi) p q) (ap2 pi q O))
        inner_left = ruleTrans (axFan v (Lift1 o) pi p q)
                       (ruleTrans (congL pi (ap2 (Lift1 o) p q) (ax_v p q))
                                  (congR pi q (ruleTrans (axLift o p q) (ax_o p))))
    in ruleTrans (axFan (Fan v (Lift1 o) pi) Const condFork p q)
         (ruleTrans (congL condFork (ap2 Const p q) inner_left)
                    (congR condFork (ap2 pi q O) (axConst p q)))

  Wf : Fun1
  Wf = compose1U thmT enum
  Wf_eq : (j : Term) -> Deriv (eqF (ap1 Wf j) (Wj j))
  Wf_eq j = axComp thmT enum j

  HEADfun : Fun1
  HEADfun = compose1U Fst Wf
  HEADfun_eq : (j : Term) -> Deriv (eqF (ap1 HEADfun j) (ap1 Fst (Wj j)))
  HEADfun_eq j = ruleTrans (axComp Fst Wf j) (cong1 Fst (Wf_eq j))

  LHSfun : Fun1
  LHSfun = compose1U Fst (compose1U Snd Wf)
  LHSfun_eq : (j : Term) -> Deriv (eqF (ap1 LHSfun j) (ap1 Fst (ap1 Snd (Wj j))))
  LHSfun_eq j =
    ruleTrans (axComp Fst (compose1U Snd Wf) j)
      (cong1 Fst (ruleTrans (axComp Snd Wf j) (cong1 Snd (Wf_eq j))))

  RHSfun : Fun1
  RHSfun = compose1U Snd (compose1U Snd Wf)
  RHSfun_eq : (j : Term) -> Deriv (eqF (ap1 RHSfun j) (rhsOf j))
  RHSfun_eq j =
    ruleTrans (axComp Snd (compose1U Snd Wf) j)
      (cong1 Snd (ruleTrans (axComp Snd Wf j) (cong1 Snd (Wf_eq j))))

  headEqF : Fun1
  headEqF = C eqIndF HEADfun (constN tag_eq)
  headEqF_eq : (j : Term) -> Deriv (eqF (ap1 headEqF j) (headEq j))
  headEqF_eq j =
    ruleTrans (ax_C eqIndF HEADfun (constN tag_eq) j)
      (ruleTrans (congL eqIndF (ap1 (constN tag_eq) j) (HEADfun_eq j))
        (ruleTrans (congR eqIndF (ap1 Fst (Wj j)) (constN_eq tag_eq j))
                   (eqIndF_eq (ap1 Fst (Wj j)) (natCode tag_eq))))

  szOkF : Fun1
  szOkF = compose1U szLeq LHSfun
  szOkF_eq : (j : Term) -> Deriv (eqF (ap1 szOkF j) (szOk j))
  szOkF_eq j = ruleTrans (axComp szLeq LHSfun j) (cong1 szLeq (LHSfun_eq j))

  headSzF : Fun1
  headSzF = C andIndF headEqF szOkF
  headSzF_eq : (j : Term) -> Deriv (eqF (ap1 headSzF j) (andInd (headEq j) (szOk j)))
  headSzF_eq j =
    ruleTrans (ax_C andIndF headEqF szOkF j)
      (ruleTrans (congL andIndF (ap1 szOkF j) (headEqF_eq j))
        (ruleTrans (congR andIndF (headEq j) (szOkF_eq j))
                   (andIndF_eq (headEq j) (szOk j))))

  HSpart : Fun2
  HSpart = Lift2 headSzF
  HSpart_eq : (x j : Term) -> Deriv (eqF (ap2 HSpart x j) (andInd (headEq j) (szOk j)))
  HSpart_eq x j = ruleTrans (axLift2 headSzF x j) (headSzF_eq j)

  VEpart : Fun2
  VEpart = Fan (Lift2 RHSfun) (Lift1 num) eqIndF
  VEpart_eq : (x j : Term) -> Deriv (eqF (ap2 VEpart x j) (valEq x j))
  VEpart_eq x j =
    ruleTrans (axFan (Lift2 RHSfun) (Lift1 num) eqIndF x j)
      (ruleTrans (congL eqIndF (ap2 (Lift1 num) x j)
                    (ruleTrans (axLift2 RHSfun x j) (RHSfun_eq j)))
        (ruleTrans (congR eqIndF (rhsOf j) (axLift num x j))
                   (eqIndF_eq (rhsOf j) (ap1 num x))))

  test_comp : Fun2
  test_comp = Fan HSpart VEpart andIndF

  -- the single reduction: test_comp reads to the nested AND of the three indicators.
  test_comp_eq :
    (x j : Term) ->
    Deriv (eqF (ap2 test_comp x j) (andInd (andInd (headEq j) (szOk j)) (valEq x j)))
  test_comp_eq x j =
    ruleTrans (axFan HSpart VEpart andIndF x j)
      (ruleTrans (congL andIndF (ap2 VEpart x j) (HSpart_eq x j))
        (ruleTrans (congR andIndF (andInd (headEq j) (szOk j)) (VEpart_eq x j))
                   (andIndF_eq (andInd (headEq j) (szOk j)) (valEq x j))))

  ----------------------------------------------------------------------
  -- SECTION 2.  test_comp is 0/1, and it fires at a matched witness.

  test_comp_le_one :
    (x j : Term) -> Deriv (leq (ap2 test_comp x j) (ap1 s O))
  test_comp_le_one x j =
    leqLeftCong (ap2 test_comp x j)
      (andInd (andInd (headEq j) (szOk j)) (valEq x j)) (ap1 s O)
      (test_comp_eq x j)
      (andInd_le_one (andInd (headEq j) (szOk j)) (valEq x j)
        (andInd_le_one (headEq j) (szOk j)
          (eqInd_le_one (ap1 Fst (Wj j)) (natCode tag_eq))
          (szLeq_le_one (ap1 Fst (ap1 Snd (Wj j)))))
        (eqInd_le_one (rhsOf j) (ap1 num x)))

  -- C.3's witness firing: a matched proof at index  j  whose thmT decodes to the
  -- equation  <lhs = num x>  with  lhs  short ( szLeq lhs = 1 ) makes test fire.
  test_comp_fires :
    (x j lhs : Term) ->
    Deriv (eqF (Wj j) (ap2 Pair (natCode tag_eq) (ap2 Pair lhs (ap1 num x)))) ->
    Deriv (eqF (ap1 szLeq lhs) (ap1 s O)) ->
    Deriv (eqF (ap2 test_comp x j) (ap1 s O))
  test_comp_fires x j lhs hit szFires =
    let -- read off the three slots from the matched code.
        e_head : Deriv (eqF (ap1 Fst (Wj j)) (natCode tag_eq))
        e_head = ruleTrans (cong1 Fst hit) (axFst (natCode tag_eq) (ap2 Pair lhs (ap1 num x)))
        e_snd : Deriv (eqF (ap1 Snd (Wj j)) (ap2 Pair lhs (ap1 num x)))
        e_snd = ruleTrans (cong1 Snd hit) (axSnd (natCode tag_eq) (ap2 Pair lhs (ap1 num x)))
        e_lhs : Deriv (eqF (ap1 Fst (ap1 Snd (Wj j))) lhs)
        e_lhs = ruleTrans (cong1 Fst e_snd) (axFst lhs (ap1 num x))
        e_rhs : Deriv (eqF (rhsOf j) (ap1 num x))
        e_rhs = ruleTrans (cong1 Snd e_snd) (axSnd lhs (ap1 num x))

        -- the three factors fire.
        headEq_fires : Deriv (eqF (headEq j) (ap1 s O))
        headEq_fires =
          ruleTrans (ruleSym (eqIndF_eq (ap1 Fst (Wj j)) (natCode tag_eq)))
            (ruleTrans (congL eqIndF (natCode tag_eq) e_head)
              (ruleTrans (eqIndF_eq (natCode tag_eq) (natCode tag_eq))
                         (eqInd_at_eq (natCode tag_eq))))
        szOk_fires : Deriv (eqF (szOk j) (ap1 s O))
        szOk_fires = ruleTrans (cong1 szLeq e_lhs) szFires
        valEq_fires : Deriv (eqF (valEq x j) (ap1 s O))
        valEq_fires =
          ruleTrans (ruleSym (eqIndF_eq (rhsOf j) (ap1 num x)))
            (ruleTrans (congL eqIndF (ap1 num x) e_rhs)
              (ruleTrans (eqIndF_eq (ap1 num x) (ap1 num x))
                         (eqInd_at_eq (ap1 num x))))
    in ruleTrans (test_comp_eq x j)
         (andInd_fires (andInd (headEq j) (szOk j)) (valEq x j)
           (andInd_fires (headEq j) (szOk j) headEq_fires szOk_fires)
           valEq_fires)
