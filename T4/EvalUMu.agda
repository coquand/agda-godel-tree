{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EvalUMu -- Phase E4 core: the mu-loop simulation, ABSTRACT and
-- EQUATIONAL.  This is the standard-route analog of T4.LastPosSearch's
-- search_settles, but at the evalU level: it shows that evalU, run on the code
-- mcodeMu gc of the mu-program  mu n. [gc(n) = 0] , reaches the return-config
-- holding the first hit position  k0 , using ONLY the shipped mu-loop reduction
-- equations  stepU_at_evMu / stepU_at_rtMstep / stepU_at_rtMbase  (T4.EvalUStep)
-- chained over an abstract per-position evaluation of the predicate.
--
-- WHY ABSTRACT.  The diagonal predicate gc reads  thmT  (it is the search for an
-- incompressibility proof).  Establishing "evalU runs g_L" by the STRUCTURAL
-- meta-induction  runs1  (T4.EvalUCorrect, the pure-fragment evalU_correct)
-- would recurse over gc's whole syntax tree -- i.e. over thmT -- so that the
-- proof's well-formedness/feasibility would hinge on Agda's evaluation strategy
-- (whether the astronomical structural step-count is forced).  The MATHEMATICS
-- never mentions such a computation: it argues equationally that the interpreter
-- SIMULATES the program, halting (for SOME fuel) with its output.  So here the
-- predicate's per-position behaviour is an ABSTRACT hypothesis
--   predReaches : (k)(K) -> Reaches (cfgEV gc (num k) K) (cfgRT (predVal k) K)
-- (interpreter correctness for the predicate, supplied as a black box -- a
-- legitimate universal instantiation), and gc / predVal / predPre stay opaque.
-- The conclusion's fuel  N = steps ...  is built from predReaches' (symbolic)
-- step counts by reach_trans -- never a concrete numeral, never forced.  Nothing
-- depends on what Agda reduces.
--
-- The witness is the FIRST-hit data (the mu convention: halt when the predicate
-- value is  O ; continue on  s _ ):
--   dHalt  : predVal k0 = O                  -- the predicate hits (=0) at k0
--   dBelow : i < k0 => predVal i = s (predPre i)   -- strictly nonzero below k0
-- exactly the search-settling antecedent, here as the least witness.

module T4.EvalUMu where

open import T4.Base
open import T4.Tags using ( tag_C )
open import T4.EvalU
  using ( mcode1 ; mcodeMu ; cfgEV ; cfgRT ; cfgHALT ; kons ; konEmpty
        ; frmM ; frmC1 ; frmApp2 ; tagRT )
open import T4.EvalUStep
  using ( stepU ; stepU_at_evMu ; stepU_at_rtMbase ; stepU_at_rtMstep
        ; stepU_at_rtEmpty ; stepU_at_evC_code ; stepU_at_rtC1
        ; stepU_at_rtApp2 ; stepU_at_evU )
open import T4.EvalUEval
  using ( evalU ; evalU_unfold ; initF ; initF_eq ; readout ; readout_halt )
open import T4.EvalUCorrect
  using ( Reaches ; mkReach ; steps ; runs ; reach_step1 ; reach_trans
        ; EvalsTo ; mkEvalsTo ; fuel ; ev )

open import BRA3.Church         using ( pi )
open import BRA3.CourseOfValues using ( iter )

------------------------------------------------------------------------
-- SECTION 0.  Meta helpers: the "advance start, shrink gap" addition  padd
-- (so the loop recursion is definitional), and a meta strict-order  Lt .

padd : Nat -> Nat -> Nat
padd j zero    = j
padd j (suc g) = padd (suc j) g

-- padd (suc j) g = suc (padd j g)   (by induction on g)
paddShift : (j g : Nat) -> Eq (padd (suc j) g) (suc (padd j g))
paddShift j zero    = refl
paddShift j (suc g) = paddShift (suc j) g

paddZero : (n : Nat) -> Eq (padd zero n) n
paddZero zero    = refl
paddZero (suc n) = eqTrans (paddShift zero n) (eqCong suc (paddZero n))

data Lt : Nat -> Nat -> Set where
  ltZ : (n : Nat) -> Lt zero (suc n)
  ltS : (m n : Nat) -> Lt m n -> Lt (suc m) (suc n)

------------------------------------------------------------------------
-- The mu-loop, abstract in the predicate.

module Mu
  (gc      : Term)
  (predVal : Nat -> Term)
  (predPre : Nat -> Term)
  (predReaches : (k : Nat) (K : Term) ->
                 Reaches (cfgEV gc (natCode k) K) (cfgRT (predVal k) K))
  where

  -- congruence on the value slot of a cfgRT config.
  cfgRTcong : (val val' K : Term) -> Deriv (eqF val val') ->
              Deriv (eqF (cfgRT val K) (cfgRT val' K))
  cfgRTcong val val' K e = congR pi (natCode tagRT) (congL pi K e)

  ----------------------------------------------------------------------
  -- SECTION 1.  loop -- run the mu-loop from position  j , reaching the first
  -- hit  padd j g .  Gap-induction on  g  (all  padd  steps definitional).

  loop : (j g : Nat) (K : Term) ->
    Deriv (eqF (predVal (padd j g)) O) ->
    ((i : Nat) -> Lt i g ->
       Deriv (eqF (predVal (padd j i)) (ap1 s (predPre (padd j i))))) ->
    Reaches (cfgEV gc (natCode j) (kons (frmM gc (natCode j)) K))
            (cfgRT (natCode (padd j g)) K)
  loop j zero K dHalt dBelow =
    -- predVal (padd j 0) = predVal j = O : evaluate gc at j, then Mbase.
    let frameK : Term
        frameK = kons (frmM gc (natCode j)) K
        pr : Reaches (cfgEV gc (natCode j) frameK) (cfgRT (predVal j) frameK)
        pr = predReaches j frameK
        eStep : Deriv (eqF (ap1 stepU (cfgRT (predVal j) frameK)) (cfgRT (natCode j) K))
        eStep = ruleTrans (cong1 stepU (cfgRTcong (predVal j) O frameK dHalt))
                          (stepU_at_rtMbase gc (natCode j) K)
    in reach_trans pr (reach_step1 eStep)
  loop j (suc g) K dHalt dBelow =
    -- predVal j = s w : evaluate gc at j, Mstep to j+1, recurse.
    let frameK : Term
        frameK = kons (frmM gc (natCode j)) K
        pr : Reaches (cfgEV gc (natCode j) frameK) (cfgRT (predVal j) frameK)
        pr = predReaches j frameK
        w : Term
        w = predPre (padd j zero)
        dSj : Deriv (eqF (predVal j) (ap1 s w))
        dSj = dBelow zero (ltZ g)
        eStep : Deriv (eqF (ap1 stepU (cfgRT (predVal j) frameK))
                           (cfgEV gc (ap1 s (natCode j))
                                  (kons (frmM gc (ap1 s (natCode j))) K)))
        eStep = ruleTrans (cong1 stepU (cfgRTcong (predVal j) (ap1 s w) frameK dSj))
                          (stepU_at_rtMstep w gc (natCode j) K)
        dHalt' : Deriv (eqF (predVal (padd (suc j) g)) O)
        dHalt' = dHalt
        dBelow' : (i : Nat) -> Lt i g ->
                  Deriv (eqF (predVal (padd (suc j) i))
                             (ap1 s (predPre (padd (suc j) i))))
        dBelow' i lt = dBelow (suc i) (ltS i g lt)
        ih : Reaches (cfgEV gc (natCode (suc j)) (kons (frmM gc (natCode (suc j))) K))
                     (cfgRT (natCode (padd (suc j) g)) K)
        ih = loop (suc j) g K dHalt' dBelow'
    in reach_trans pr (reach_trans (reach_step1 eStep) ih)

  ----------------------------------------------------------------------
  -- SECTION 2.  muReaches -- the mu-program, started on input  a , reaches the
  -- first-hit return-config  cfgRT k0 K .  evMu starts the search at 0;  loop
  -- runs it; paddZero converts  padd 0 k0  to  k0 .

  muReaches : (a : Nat) (k0 : Nat) (K : Term) ->
    Deriv (eqF (predVal k0) O) ->
    ((i : Nat) -> Lt i k0 ->
       Deriv (eqF (predVal i) (ap1 s (predPre i)))) ->
    Reaches (cfgEV (mcodeMu gc) (natCode a) K) (cfgRT (natCode k0) K)
  muReaches a k0 K dHalt dBelow =
    let start : Reaches (cfgEV (mcodeMu gc) (natCode a) K)
                        (cfgEV gc O (kons (frmM gc O) K))
        start = reach_step1 (stepU_at_evMu gc (natCode a) K)
        dHalt' : Deriv (eqF (predVal (padd zero k0)) O)
        dHalt' = eqSubst (\ n -> Deriv (eqF (predVal n) O)) (eqSym (paddZero k0)) dHalt
        dBelow' : (i : Nat) -> Lt i k0 ->
                  Deriv (eqF (predVal (padd zero i)) (ap1 s (predPre (padd zero i))))
        dBelow' i lt =
          eqSubst (\ n -> Deriv (eqF (predVal n) (ap1 s (predPre n))))
                   (eqSym (paddZero i)) (dBelow i lt)
        lp : Reaches (cfgEV gc (natCode zero) (kons (frmM gc (natCode zero)) K))
                     (cfgRT (natCode (padd zero k0)) K)
        lp = loop zero k0 K dHalt' dBelow'
        whole : Reaches (cfgEV (mcodeMu gc) (natCode a) K)
                        (cfgRT (natCode (padd zero k0)) K)
        whole = reach_trans start lp
    in eqSubst (\ n -> Reaches (cfgEV (mcodeMu gc) (natCode a) K) (cfgRT (natCode n) K))
                (paddZero k0) whole

  ----------------------------------------------------------------------
  -- SECTION 3.  muEvalU -- the existential halting fact for the WHOLE machine
  -- (kont empty): evalU (mcodeMu gc) (num N) = s (num k0)  for the symbolic fuel
  -- N = steps ... .  This is the EvalsTo black box (the "exists n" of the math),
  -- with the fuel symbolic.  Identical assembly to evalU_correct_num, but driven
  -- by the mu-loop (muReaches), not by the pure-fragment structural runs1.

  muEvalU : (k0 : Nat) ->
    Deriv (eqF (predVal k0) O) ->
    ((i : Nat) -> Lt i k0 ->
       Deriv (eqF (predVal i) (ap1 s (predPre i)))) ->
    EvalsTo (mcodeMu gc) (ap1 s (natCode k0))
  muEvalU k0 dHalt dBelow =
    let halt : Reaches (cfgEV (mcodeMu gc) O konEmpty) (cfgHALT (natCode k0))
        halt = reach_trans (muReaches zero k0 konEmpty dHalt dBelow)
                           (reach_step1 (stepU_at_rtEmpty (natCode k0)))
        N : Nat
        N = steps halt
        e : Deriv (eqF (ap2 (iter stepU) (cfgEV (mcodeMu gc) O konEmpty) (natCode N))
                       (cfgHALT (natCode k0)))
        e = runs halt
        u1 = evalU_unfold (mcodeMu gc) (natCode N)
        iterEq = congL (iter stepU) (natCode N) (initF_eq (mcodeMu gc))
        chain = ruleTrans iterEq e
        final = ruleTrans u1
                  (ruleTrans (cong1 readout chain) (readout_halt (natCode k0)))
    in mkEvalsTo N final

  ----------------------------------------------------------------------
  -- SECTION 4.  The diagonal program  g_L = out_L o (mu-search) , and its
  -- full evalU halting fact (the SUBJECT z0, not the mu position k0).
  --
  -- g_L is the composition  compose1U out_L (mu gc) = C (Lift1 out_L) (mu gc) u
  -- at the CODE level (the mu-child is NOT a pure Fun1, so we build the code
  -- directly):  gLCodeOf gCode = pi tag_C (pi gCode (pi (mcodeMu gc) (mcode1 u)))
  -- where  gCode = mcode2 (Lift1 out_L)  is the Fun2 code for "apply out_L to the
  -- first component".  out_L's own evaluation is supplied as an ABSTRACT BLACK BOX
  --   outLReaches : (K) -> Reaches (cfgEV gCode <k0,O> K) (cfgRT (num z0) K)
  -- (= out_L k0 = z0; out_L reads thmT, so -- like predReaches -- it stays opaque,
  -- a legitimate universal instantiation).  The C-evaluation plumbing
  -- (code-level evC + rtC1 + u-eval + rtApp2) is deterministic; the mu-loop part
  -- is  muReaches  (kont-parametric, runs UNDER the frmC1 frame).

  gLCodeOf : Term -> Term
  gLCodeOf gCode =
    ap2 pi (natCode tag_C) (ap2 pi gCode (ap2 pi (mcodeMu gc) (mcode1 u)))

  gLReaches :
    (gCode : Term) (k0 z0 : Nat) ->
    Deriv (eqF (predVal k0) O) ->
    ((i : Nat) -> Lt i k0 ->
       Deriv (eqF (predVal i) (ap1 s (predPre i)))) ->
    ((K : Term) ->
       Reaches (cfgEV gCode (ap2 pi (natCode k0) O) K) (cfgRT (natCode z0) K)) ->
    (K : Term) ->
    Reaches (cfgEV (gLCodeOf gCode) O K) (cfgRT (natCode z0) K)
  gLReaches gCode k0 z0 dHalt dBelow outLReaches K =
    let h1Code : Term
        h1Code = mcodeMu gc
        h2Code : Term
        h2Code = mcode1 u
        kC1 : Term
        kC1 = kons (frmC1 gCode h2Code O) K
        kAp2 : Term
        kAp2 = kons (frmApp2 gCode (natCode k0)) K
        s1 : Reaches (cfgEV (gLCodeOf gCode) O K) (cfgEV h1Code O kC1)
        s1 = reach_step1 (stepU_at_evC_code gCode h1Code h2Code O K)
        s2 : Reaches (cfgEV h1Code O kC1) (cfgRT (natCode k0) kC1)
        s2 = muReaches zero k0 kC1 dHalt dBelow
        s3 : Reaches (cfgRT (natCode k0) kC1) (cfgEV h2Code O kAp2)
        s3 = reach_step1 (stepU_at_rtC1 (natCode k0) gCode h2Code O K)
        s4 : Reaches (cfgEV h2Code O kAp2) (cfgRT O kAp2)
        s4 = reach_step1 (stepU_at_evU O kAp2)
        s5 : Reaches (cfgRT O kAp2) (cfgEV gCode (ap2 pi (natCode k0) O) K)
        s5 = reach_step1 (stepU_at_rtApp2 O gCode (natCode k0) K)
        s6 : Reaches (cfgEV gCode (ap2 pi (natCode k0) O) K) (cfgRT (natCode z0) K)
        s6 = outLReaches K
    in reach_trans s1 (reach_trans s2 (reach_trans s3
         (reach_trans s4 (reach_trans s5 s6))))

  -- The full diagonal halting fact (kont empty): evalU(⌜g_L⌝, num N) = s (num z0)
  -- for the symbolic fuel  N = steps ... .  THIS is the honest  dEval  (subject z0).
  gLEvalU :
    (gCode : Term) (k0 z0 : Nat) ->
    Deriv (eqF (predVal k0) O) ->
    ((i : Nat) -> Lt i k0 ->
       Deriv (eqF (predVal i) (ap1 s (predPre i)))) ->
    ((K : Term) ->
       Reaches (cfgEV gCode (ap2 pi (natCode k0) O) K) (cfgRT (natCode z0) K)) ->
    EvalsTo (gLCodeOf gCode) (ap1 s (natCode z0))
  gLEvalU gCode k0 z0 dHalt dBelow outLReaches =
    let halt : Reaches (cfgEV (gLCodeOf gCode) O konEmpty) (cfgHALT (natCode z0))
        halt = reach_trans (gLReaches gCode k0 z0 dHalt dBelow outLReaches konEmpty)
                           (reach_step1 (stepU_at_rtEmpty (natCode z0)))
        N : Nat
        N = steps halt
        e : Deriv (eqF (ap2 (iter stepU) (cfgEV (gLCodeOf gCode) O konEmpty) (natCode N))
                       (cfgHALT (natCode z0)))
        e = runs halt
        u1 = evalU_unfold (gLCodeOf gCode) (natCode N)
        iterEq = congL (iter stepU) (natCode N) (initF_eq (gLCodeOf gCode))
        chain = ruleTrans iterEq e
        final = ruleTrans u1
                  (ruleTrans (cong1 readout chain) (readout_halt (natCode z0)))
    in mkEvalsTo N final
