{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SpikeChaitin -- Gate KR-1 spike: Chaitin's barrier (Kritchman-Raz Eq 1)
-- as  chaitin_thm , with the KR-A definability layer ABSTRACTED and the ONE
-- genuinely-new lemma -- Stage 1, search-correctness -- built CONCRETELY.
--
-- Methodology = SpikeD / SpikeB / SpikeC: the KR-A deliverables ( hit / out /
-- enum / the  isIncomprProof -soundness  bridge / the Stage-2  compress_canonical
-- result / the D1 necessitations) are module/argument PARAMETERS; only the
-- search assembly is built here.  This certifies Gate KR-1's structure end to
-- end modulo the KR-A definability layer, exactly as SpikeD certified Gate KR-2
-- modulo  barrier / advance .
--
-- THE NEW CONTENT (Stage 1).  CountingObj already ships an OUTPUT-extracting
-- object  ruleIndNat  (csumObj idx N N = s N).  What is new for Chaitin is that
-- the extracted output is a WITNESS-DRIVEN SEARCH RESULT: a bounded find-(last)
-- search over the range  0..B  whose value is forced to be a VALID match by a
-- supplied witness  pi  at a position  p0 <= B  (= the  (FIT)  premise of
-- SPIKE-KR-B).  The search is the condFork-based  lastPosRec ; its correctness
-- is the merged  search_settles  invariant -- ONE object  ruleIndNat , open in
-- the range variable, instantiated at the abstract Closed Bin  B  (closeCoe on
-- the witness position  p0 ).  See  CHAITIN-SEARCH-DESIGN.md .
--
-- NON-VACUITY (cf. SpikeD's INV-guard).  The conclusion is  imp (leq p0 B) ... ;
-- it is discharged ONLY by the supplied witness  (hit p0 = sO , leq p0 B) .  The
-- search genuinely fires on  pi .
--
-- yhat = ap1 chaitinSearch B  stays SYMBOLIC -- never evaluated to a numeral
-- (the exp trap; symbolic staging is the only escape, SPIKE-KR-B 4).

module T4.SpikeChaitin where

open import T4.Base
open import T4.Code   using ( codeFormula ; codeFalse ; falseF )
open import T4.Tags   using ( tag_imp ; tag_mp )
open import T4.ThmT   using ( thmT )
open import T4.PHP    using ( byCases )
open import T4.Thm12.EncodedMp using ( encoded_mp )

open import T4.Counting
  using ( antisym_curry ; nonzero_ge_one_imp
        ; mapUnder1 ; mapUnder2 ; negToImpFalse ; impFalseToNeg_imp
        ; bCombThree ; under1_trans )
open import T4.CountingObj
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
-- The abstracted KR-A definability layer (parameters of the whole spike).
--
--   hit  j  in {O, s O} :  "candidate j is an incompressibility proof"
--   out  j           :  the SUBJECT named by candidate j  (= K's output slot)
--   enum j           :  the proof-code at position j  (Bin length-lex enum)
--   atomForm t       :  the open DefWit-atom  (so  Incompressible t = neg (atomForm t))
--
-- bridge  = isIncomprProof-soundness:  a firing match at  j  means  thmT  reads
-- enum j  as a code of  Incompressible(out j) = neg (atomForm (out j)) .
-- hit_le_one  = hit is a 0/1 indicator (it is a bounded Sigma_0 search).

module Search
  (hit out enum : Fun1)
  (atomForm : Term -> Formula)
  (hit_le_one : (j : Term) -> Deriv (leq (ap1 hit j) (ap1 s O)))
  (bridge : (j : Term) ->
            Deriv (imp (eqF (ap1 hit j) (ap1 s O))
                       (eqF (ap1 thmT (ap1 enum j))
                            (codeFormula (neg (atomForm (ap1 out j)))))))
  where

  ------------------------------------------------------------------------
  -- SECTION 1.  The find-(last)-hit search recursor.
  --
  --   ap2 lastPosRec x O      = O
  --   ap2 lastPosRec x (s n)  = condFork (pi (s n) prev) (hit (s n))
  -- where  prev = ap2 lastPosRec x n .  I.e. "if  hit (s n)  fires, record the
  -- new top index  s n ; else keep the previous recorded position."  The first
  -- argument  x  is unused (only  Snd pkg = n  matters); fix  x := O .

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

        -- top-level Fan unfold.
        e1 : Deriv (eqF (ap2 stepH pkg prev)
                        (ap2 condFork (ap2 ZP pkg prev) (ap2 HF pkg prev)))
        e1 = axFan ZP HF condFork pkg prev

        -- ZP pkg prev = pi (s n) prev.
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

        -- HF pkg prev = hit (s n).
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
  -- SECTION 2.  Small order lemmas (Carneiro imp-form, from shipped Counting).

  -- x <= s O  and  x /= O  imply  x = s O .
  le_one_neq_zero :
    (x : Term) -> Deriv (leq x (ap1 s O)) ->
    Deriv (imp (neg (eqF x O)) (eqF x (ap1 s O)))
  le_one_neq_zero x leX1 =
    compI (nonzero_ge_one_imp x) (mp (antisym_curry x (ap1 s O)) leX1)

  -- neg (leq p0 n)  and  leq p0 (s n)  imply  p0 = s n .
  boundary :
    (p0 n : Term) ->
    Deriv (imp (neg (leq p0 n)) (imp (leq p0 (ap1 s n)) (eqF p0 (ap1 s n))))
  boundary p0 n =
    let strict : Deriv (imp (neg (leq p0 n)) (leq (ap1 s n) p0))
        strict = ruleInst2 zero p0 (suc zero) n refl strictTrich
        anti : Deriv (imp (leq p0 (ap1 s n)) (imp (leq (ap1 s n) p0) (eqF p0 (ap1 s n))))
        anti = antisym_curry p0 (ap1 s n)
    in compI strict (swapImp anti)

  -- reverse successor monotonicity:  leq (s a) (s b)  implies  leq a b
  -- (leq a b = eqF (sub a b) O, and  sub (s a) (s b) = sub a b  by T57sub).
  unsucc_leq : (a b : Term) -> Deriv (imp (leq (ap1 s a) (ap1 s b)) (leq a b))
  unsucc_leq a b =
    prependEqLeft (ap2 sub a b) (ap2 sub (ap1 s a) (ap1 s b)) O
      (ruleSym (ruleInst2 zero a (suc zero) b refl T57sub))

  -- a /= b  and  a <= b  imply  s a <= b   (fully curried, neq as antecedent).
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
  -- SECTION 3.  The two condFork-reduction facts at a step.

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
        condTm : Term                                    -- condFork zz (hit (s m))
        condTm = ap2 condFork zz (ap1 hit (ap1 s m))
        base_eq : Deriv (eqF (lastpos (ap1 s m)) condTm)
        base_eq = lastpos_succ O m
        flag_rw : Deriv (imp hyp (eqF condTm (ap2 condFork zz (ap1 s O))))
        flag_rw = ax_eqCongR condFork (ap1 hit (ap1 s m)) (ap1 s O) zz
        reduce : Deriv (eqF (ap2 condFork zz (ap1 s O)) (ap1 s m))
        reduce = ruleTrans (condFork_true_nc zz O) (axFst (ap1 s m) (lastpos m))
        -- lastpos (s m) = s m  under hyp.
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
  -- SECTION 4.  search_settles -- the MERGED reachability + match-validity
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
            -- hit O = s O  under  leq p0 O .
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
      phi1 : Formula                                          -- the IH
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
            -- e_neq:  under h0,  p0 /= s n .
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
            -- e_csn:  under h0, Cn => Csn  (lastpos (s n) = lastpos n).
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

  ------------------------------------------------------------------------
  -- SECTION 5.  chaitinSearch as a Fun1 + the Stage-1 conclusion.

  -- chaitinSearch B = out (lastpos B) :  the SUBJECT of the (last) matched
  -- proof-code in the range  0..B .  yhat = ap1 chaitinSearch B  stays SYMBOLIC.
  chaitinSearch : Fun1
  chaitinSearch = compose1U out (C lastPosRec o u)

  chaitinSearch_eq :
    (B : Term) -> Deriv (eqF (ap1 chaitinSearch B) (ap1 out (ap2 lastPosRec O B)))
  chaitinSearch_eq B =
    let inner : Deriv (eqF (ap1 (C lastPosRec o u) B) (ap2 lastPosRec O B))
        inner = ruleTrans (ax_C lastPosRec o u B)
                  (ruleTrans (congL lastPosRec (ap1 u B) (ax_o B))
                             (congR lastPosRec O (ax_u B)))
    in ruleTrans (axComp out (C lastPosRec o u) B) (cong1 out inner)

  -- Stage 1 conclusion:  thmT proves  Incompressible(yhat) = neg (atomForm yhat) ,
  -- via the concrete proof-code  enum (lastpos B) .  Non-vacuous: driven by the
  -- supplied witness  (hp0 , leqp0B) .
  search_concludes :
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (leq p0 B) ->
    Deriv (eqF (ap1 hit p0) (ap1 s O)) ->
    Deriv (eqF (ap1 thmT (ap1 enum (ap2 lastPosRec O B)))
               (codeFormula (neg (atomForm (ap1 out (ap2 lastPosRec O B))))))
  search_concludes B p0 clB clP0 leqp0B hp0 =
    mp (bridge (ap2 lastPosRec O B))
       (mp (search_settles B p0 clB clP0 hp0) leqp0B)

  ------------------------------------------------------------------------
  -- SECTION 6.  chaitin_thm  (Stages 2-3; Stage 3 concrete = a con_inj variant,
  -- Stage 2 + the D1 necessitation abstracted as parameters).

  ConSchema : Formula
  ConSchema = neg (eqF (ap1 thmT (var zero)) codeFalse)

  cimp : Term -> Term -> Term
  cimp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

  cmp : Term -> Term -> Term
  cmp pImp pA = ap2 Pair (natCode tag_mp) (ap2 Pair pImp pA)

  -- chaitin_thm  (KR Eq 1, the Chaitin barrier), in BRA's witnessed form.
  -- yhat = ap1 out (ap2 lastPosRec O B) = ap1 chaitinSearch B  (chaitinSearch_eq),
  -- kept SYMBOLIC.  The  (FIT)  premise  leq p0 B  is SPIKE-KR-B 6's mandatory
  -- correction; the match witness  hp0  drives the search (non-vacuity).
  chaitin_thm :
    Deriv ConSchema ->
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (leq p0 B) ->                                   -- (FIT): pi sits at p0 <= B
    Deriv (eqF (ap1 hit p0) (ap1 s O)) ->                 -- pi is a match (the witness)
    (cPos cExF : Term) ->
    -- Stage 2 (KR-A compress_canonical + D1):  thmT proves the DefWit atom of yhat.
    Deriv (eqF (ap1 thmT cPos)
               (codeFormula (atomForm (ap1 out (ap2 lastPosRec O B))))) ->
    -- D1 necessitation (shipped):  thmT proves  atom -> (neg atom -> 0=1) .
    Deriv (eqF (ap1 thmT cExF)
               (cimp (codeFormula (atomForm (ap1 out (ap2 lastPosRec O B))))
                     (cimp (codeFormula (neg (atomForm (ap1 out (ap2 lastPosRec O B)))))
                           codeFalse))) ->
    Deriv falseF
  chaitin_thm con B p0 clB clP0 leqp0B hp0 cPos cExF dPos dExF =
    let yhat : Term
        yhat = ap1 out (ap2 lastPosRec O B)
        codeX : Term
        codeX = codeFormula (atomForm yhat)
        codeNegX : Term
        codeNegX = codeFormula (neg (atomForm yhat))
        w1 : Term
        w1 = ap1 enum (ap2 lastPosRec O B)
        -- Stage 1 (concrete):  thmT proves  neg (atomForm yhat)  via  w1 .
        dNeg : Deriv (eqF (ap1 thmT w1) codeNegX)
        dNeg = search_concludes B p0 clB clP0 leqp0B hp0
        -- Stage 3:  two  encoded_mp  give  thmT proves codeFalse .
        mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos)) (cimp codeNegX codeFalse))
        mp1 = encoded_mp cExF cPos codeX (cimp codeNegX codeFalse) dExF dPos
        mp2 : Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) w1)) codeFalse)
        mp2 = encoded_mp (cmp cExF cPos) w1 codeNegX codeFalse mp1 dNeg
        finalProof : Term
        finalProof = cmp (cmp cExF cPos) w1
        con_inst : Deriv (neg (eqF (ap1 thmT finalProof) codeFalse))
        con_inst = ruleInst zero finalProof con
    in mp (mp (axExFalso (eqF (ap1 thmT finalProof) codeFalse) falseF) mp2) con_inst

  -- SECTION 7.  chaitin_inconsistency  (the Con-FREE Chaitin-Goedel I target,
  -- chaitin-G1-statement.tex Thm 1 / NEXT-SESSION-CHAITIN-G1-FRESH.md SS0, SS2.2).
  --
  -- This is  chaitin_thm  MINUS the final Con step: it returns the constructed
  -- inconsistency proof  mp2 : thmT (f z x) = codeFalse  outright, with
  --   f z x := cmp (cmp cExF cPos) w1     (w1 = enum at the settled position),
  -- so it never consumes  con  / never forms  con_inst  + the final  mp .  The
  -- (FIT) premise  leq p0 B  is a HYPOTHESIS (Solovay/exp-total, elements.pdf SS18;
  -- discharged for free in BRA), never proved here.  The match witness  hp0
  -- drives the search (non-vacuity).  Identical Stage-1/2/3 body as chaitin_thm
  -- up to  mp2 ; chaitin_thm = this  +  axExFalso/con_inst/mp  (the corollary).
  chaitin_inconsistency :
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (leq p0 B) ->                                   -- (FIT): pi sits at p0 <= B
    Deriv (eqF (ap1 hit p0) (ap1 s O)) ->                 -- pi is a match (the witness)
    (cPos cExF : Term) ->
    -- Stage 2 (KR-A compress_canonical + D1):  thmT proves the DefWit atom of yhat.
    Deriv (eqF (ap1 thmT cPos)
               (codeFormula (atomForm (ap1 out (ap2 lastPosRec O B))))) ->
    -- D1 necessitation (shipped):  thmT proves  atom -> (neg atom -> 0=1) .
    Deriv (eqF (ap1 thmT cExF)
               (cimp (codeFormula (atomForm (ap1 out (ap2 lastPosRec O B))))
                     (cimp (codeFormula (neg (atomForm (ap1 out (ap2 lastPosRec O B)))))
                           codeFalse))) ->
    -- the constructed proof of  0=1  (= thmT (f z x) = code(0=1)).
    Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) (ap1 enum (ap2 lastPosRec O B))))
               codeFalse)
  chaitin_inconsistency B p0 clB clP0 leqp0B hp0 cPos cExF dPos dExF =
    let yhat : Term
        yhat = ap1 out (ap2 lastPosRec O B)
        codeX : Term
        codeX = codeFormula (atomForm yhat)
        codeNegX : Term
        codeNegX = codeFormula (neg (atomForm yhat))
        w1 : Term
        w1 = ap1 enum (ap2 lastPosRec O B)
        -- Stage 1 (concrete):  thmT proves  neg (atomForm yhat)  via  w1 .
        dNeg : Deriv (eqF (ap1 thmT w1) codeNegX)
        dNeg = search_concludes B p0 clB clP0 leqp0B hp0
        -- Stage 3:  two  encoded_mp  give  thmT proves codeFalse  (= mp2).
        mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos)) (cimp codeNegX codeFalse))
        mp1 = encoded_mp cExF cPos codeX (cimp codeNegX codeFalse) dExF dPos
        mp2 : Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) w1)) codeFalse)
        mp2 = encoded_mp (cmp cExF cPos) w1 codeNegX codeFalse mp1 dNeg
    in mp2
