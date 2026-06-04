{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.ChaitinG1Witness -- the witnessed bounded-exists-introduction (recogniser
-- plan C.3, CHAITIN-G1-ATOM-CORRECTION.md / NEXT-SESSION-CHAITIN-G1-RECOGNISER.md
-- Part B.3).  This discharges  T4.ChaitinG1Hit.chaitin_G1_hit 's hypothesis
--   h : Deriv (eqF (ap1 compHit z0) (s O))         -- "z0 is L-compressible"
-- by ASSEMBLING the recogniser (T4.TestComp) with the object one-hit kernel
-- (T4.ExistsHitU) at the witness  (g, Df) :
--   * the bounded-search indicator  compHit = C existsHitURec u constB : Fun1 ;
--   * the witness fires the per-index test  test_comp z0 j_g = 1  (TestComp.test_comp_fires),
--     where the matched proof  Df = thm12 search  has  thmT(Df) = <search(num L) = num z0>
--     (the SHIPPED thm13_singulary -- the only place the program enters, witness-side);
--   * the witness lies in range  j_g <= B  (the FIT premise);
--   * the one-hit lemma  existsHitU_settles  lifts these to  existsHitU z0 B = 1 .
--
-- This is the ENCODED witnessed-exists-introduction: NOT a necessitation of a
-- codeFormula (no codeFormula on the subject), NOT encoded_and -- just the object
-- fact  compHit z0 = 1  (the bounded search evaluates to 1 at the witness), which
-- chaitin_G1_hit then internalises ONCE via thm13_singulary at f := compHit.
--
-- The genuinely-deferred infrastructure (C.5) is isolated as CLEAN hypotheses:
-- the proof enumerator  enum  and code-size indicator  szLeq  (module parameters);
-- the self-naming  h0 : search(L) = z0  (definitional), the enum-points-at-Df fact
-- enum_at_jg (C.5: enum lists Df at j_g), the in-budget  szFires  (= dLen, |g|<=L),
-- and the in-range  inRange : j_g <= B  (= FIT).  NO logical content is deferred:
-- each is a length-lex/Bin bookkeeping fact about the concrete enumerator and L.

module T4.ChaitinG1Witness where

open import T4.Base
open import T4.Tags            using ( tag_eq ; tag_ap1 )
open import T4.ThmT            using ( thmT )
open import T4.Num             using ( num )
open import T4.Code            using ( codeFun1 ; codeFalse )
open import T4.DefWit          using ( cNeg )
open import T4.ConInj          using ( cmp )
open import T4.Thm12.All       using ( thm12 ; fst )
open import T4.Thm12.Thm13     using ( codeFXeqY1 ; thm13_singulary )
open import T4.EncodedProp     using ( exfProof )
open import T4.ChaitinG1Hit    using ( chaitin_G1_hit )
open import T4.ChaitinG1Neg    using ( hitNeg ; dNeg_from_hitNeg )
open import T4.ChaitinG1Out    using ( out )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; constTermFun1 ; constTermFun1_eq )

open import BRA3.ChurchLeq       using ( leq )

import T4.ExistsHitU
import T4.TestComp

------------------------------------------------------------------------
-- The assembly, parametric in the recogniser infrastructure (enum, szLeq).

module W
  (enum  : Fun1)
  (szLeq : Fun1)
  (szLeq_le_one : (c : Term) -> Deriv (leq (ap1 szLeq c) (ap1 s O)))
  where

  open T4.TestComp.Rec enum szLeq szLeq_le_one
    using ( test_comp ; test_comp_le_one ; test_comp_fires ; Wj )
  open T4.ExistsHitU.IndU test_comp test_comp_le_one
    using ( existsHitU ; existsHitU_settles ; compHitOf ; compHitOf_eq )

  ----------------------------------------------------------------------
  -- C.3 core: h from a matched, in-range, in-budget witness.

  h_from_witness :
    (constB : Fun1) (B z0 j_g lhs : Term) ->
    Closed z0 -> Closed B -> Closed j_g ->
    ((y : Term) -> Deriv (eqF (ap1 constB y) B)) ->
    Deriv (eqF (Wj j_g) (ap2 Pair (natCode tag_eq) (ap2 Pair lhs (ap1 num z0)))) ->
    Deriv (eqF (ap1 szLeq lhs) (ap1 s O)) ->
    Deriv (leq j_g B) ->
    Deriv (eqF (ap1 (compHitOf constB) z0) (ap1 s O))
  h_from_witness constB B z0 j_g lhs clZ0 clB clJg constB_eq hit szFires inRange =
    let fires : Deriv (eqF (ap2 test_comp z0 j_g) (ap1 s O))
        fires = test_comp_fires z0 j_g lhs hit szFires
        settled : Deriv (eqF (existsHitU z0 B) (ap1 s O))
        settled = mp (existsHitU_settles z0 B j_g clZ0 clB clJg fires) inRange
    in ruleTrans (compHitOf_eq constB B constB_eq z0) settled

  ----------------------------------------------------------------------
  -- C.3, grounded in thm13: the witness IS the search program  g = search(L) ;
  -- the matched code is built by the SHIPPED thm13_singulary, exhibiting the
  -- codeFXeqY1 shape  <tag_eq, <lhs, num z0>>  with  lhs = <ap1, <code search, num L>>
  -- (the LHS = code of  search(num L) ;  szLeq lhs = 1  is exactly  dLen, |g| <= L).
  -- The only program-mention is here, on the WITNESS side (thm13), never as a
  -- target the test constructs (the extraction invariant).

  h_from_thm13 :
    (constB : Fun1) (B z0 j_g L : Term) (search : Fun1) ->
    Closed z0 -> Closed B -> Closed j_g ->
    ((y : Term) -> Deriv (eqF (ap1 constB y) B)) ->
    -- self-naming: the search returns z0 at L (definitional; chaitinSearch_eq in C.5).
    Deriv (eqF (ap1 search L) z0) ->
    -- enum lists the canonical Sigma_1 proof Df = (fst (thm12 search)) L at index j_g.
    Deriv (eqF (ap1 enum j_g) (ap1 (fst (thm12 search)) L)) ->
    -- dLen: the code of  search(num L)  is short (<= L'); the szLeq indicator fires.
    Deriv (eqF (ap1 szLeq (ap2 Pair (natCode tag_ap1)
                              (ap2 Pair (codeFun1 search) (ap1 num L)))) (ap1 s O)) ->
    -- FIT: the witness sits at a search position <= B.
    Deriv (leq j_g B) ->
    Deriv (eqF (ap1 (compHitOf constB) z0) (ap1 s O))
  h_from_thm13 constB B z0 j_g L search clZ0 clB clJg constB_eq h0 enum_at_jg szFires inRange =
    let lhs : Term
        lhs = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 search) (ap1 num L))
        -- thmT(enum j_g) = thmT(Df) = codeFXeqY1 search L z0 = <tag_eq, <lhs, num z0>>.
        hit : Deriv (eqF (Wj j_g)
                         (ap2 Pair (natCode tag_eq) (ap2 Pair lhs (ap1 num z0))))
        hit = ruleTrans (cong1 thmT enum_at_jg) (thm13_singulary search L z0 h0)
    in h_from_witness constB B z0 j_g lhs clZ0 clB clJg constB_eq hit szFires inRange

  ----------------------------------------------------------------------
  -- Capstone: the fully-wired Con-free barrier.  Given the witness (=> h) and the
  -- recogniser output dNeg (C.4), chaitin_G1_hit assembles  thmT(f) = codeFalse .

  chaitin_G1_barrier :
    (constB : Fun1) (B z0 j_g L : Term) (search : Fun1) (w0 : Term) ->
    Closed z0 -> Closed B -> Closed j_g ->
    ((y : Term) -> Deriv (eqF (ap1 constB y) B)) ->
    Deriv (eqF (ap1 search L) z0) ->
    Deriv (eqF (ap1 enum j_g) (ap1 (fst (thm12 search)) L)) ->
    Deriv (eqF (ap1 szLeq (ap2 Pair (natCode tag_ap1)
                              (ap2 Pair (codeFun1 search) (ap1 num L)))) (ap1 s O)) ->
    Deriv (leq j_g B) ->
    -- dNeg: the incompressibility recogniser output (C.4); N = cNeg P, manifest.
    Deriv (eqF (ap1 thmT w0)
               (cNeg (codeFXeqY1 (compHitOf constB) z0 (ap1 s O)))) ->
    Deriv (eqF (ap1 thmT
                 (cmp (cmp (exfProof (codeFXeqY1 (compHitOf constB) z0 (ap1 s O)) codeFalse)
                           (ap1 (fst (thm12 (compHitOf constB))) z0))
                      w0))
               codeFalse)
  chaitin_G1_barrier constB B z0 j_g L search w0 clZ0 clB clJg constB_eq h0 enum_at_jg szFires inRange dNeg =
    chaitin_G1_hit (compHitOf constB) z0 w0
      (h_from_thm13 constB B z0 j_g L search clZ0 clB clJg constB_eq h0 enum_at_jg szFires inRange)
      dNeg

  ----------------------------------------------------------------------
  -- C.5 wiring: the barrier from a FIRING recogniser (C.4) instead of an
  -- explicit dNeg.  The subject is read off the matched proof, z0 := out w0;
  -- the search's incompressibility recogniser hitNeg (T4.ChaitinG1Neg) firing
  -- at w0  (hitNeg (compHitOf constB) out w0 = 1, which the lastPos settling of
  -- C.5 produces)  delivers dNeg via dNeg_from_hitNeg (= eqInd_sound, no
  -- thmT_at_sb).  This connects C.4 to C.3 end-to-end: a settled match + the
  -- (still-abstract) h-side / FIT hypotheses ==> thmT(f) = codeFalse, Con-free.
  --
  -- Remaining for the CLOSED barrier (C.5 infra, isolated as hypotheses here):
  -- the lastPos settling producing the firing  hf  (SpikeChaitin.search_settles);
  -- enum/pairEnum (enum_at_jg); szLeq (szFires = dLen); FIT/B (inRange); constB;
  -- the self-referential  h0 : search L = out w0  (g's output is the subject of
  -- the proof it found); pin a polynomial rho and L, z0.

  chaitin_G1_from_firing :
    (out constB : Fun1) (B j_g L : Term) (search : Fun1) (w0 : Term) ->
    Closed (ap1 out w0) -> Closed B -> Closed j_g ->
    ((y : Term) -> Deriv (eqF (ap1 constB y) B)) ->
    -- the search's output is the subject of the found incompressibility proof.
    Deriv (eqF (ap1 search L) (ap1 out w0)) ->
    Deriv (eqF (ap1 enum j_g) (ap1 (fst (thm12 search)) L)) ->
    Deriv (eqF (ap1 szLeq (ap2 Pair (natCode tag_ap1)
                              (ap2 Pair (codeFun1 search) (ap1 num L)))) (ap1 s O)) ->
    Deriv (leq j_g B) ->
    -- the recogniser FIRES at w0 (the lastPos settling of C.5).
    Deriv (eqF (ap1 (hitNeg (compHitOf constB) out) w0) (ap1 s O)) ->
    Deriv (eqF (ap1 thmT
                 (cmp (cmp (exfProof (codeFXeqY1 (compHitOf constB) (ap1 out w0) (ap1 s O)) codeFalse)
                           (ap1 (fst (thm12 (compHitOf constB))) (ap1 out w0)))
                      w0))
               codeFalse)
  chaitin_G1_from_firing out constB B j_g L search w0 clZ0 clB clJg constB_eq h0 enum_at_jg szFires inRange hf =
    chaitin_G1_barrier constB B (ap1 out w0) j_g L search w0 clZ0 clB clJg constB_eq h0 enum_at_jg szFires inRange
      (dNeg_from_hitNeg (compHitOf constB) out w0 hf)

  ----------------------------------------------------------------------
  -- C.5, concretised: the projector and the constant-B function pinned.
  --   out      := T4.ChaitinG1Out.out  (decode o Snd.Snd.Fst.Snd.Snd o thmT),
  --   constB   := constTermFun1 B         (the constant-B Fun1; needs NoVar B).
  -- This discharges the  out  and  constB / constB_eq  parameters of
  -- chaitin_G1_from_firing, leaving the genuine search infrastructure (C.5 bulk)
  -- as hypotheses:  the settled firing  hf , the self-referential
  -- h0 : search L = out w0 , the enumerator fact  enum_at_jg , the budget
  -- szFires (= dLen) and the in-range  inRange  (= FIT).  z0 := out w0 throughout.

  chaitin_G1_closed :
    (B j_g L : Term) (search : Fun1) (w0 : Term) ->
    NoVar B ->
    Closed (ap1 out w0) -> Closed B -> Closed j_g ->
    Deriv (eqF (ap1 search L) (ap1 out w0)) ->
    Deriv (eqF (ap1 enum j_g) (ap1 (fst (thm12 search)) L)) ->
    Deriv (eqF (ap1 szLeq (ap2 Pair (natCode tag_ap1)
                              (ap2 Pair (codeFun1 search) (ap1 num L)))) (ap1 s O)) ->
    Deriv (leq j_g B) ->
    Deriv (eqF (ap1 (hitNeg (compHitOf (constTermFun1 B)) out) w0) (ap1 s O)) ->
    Deriv (eqF (ap1 thmT
                 (cmp (cmp (exfProof (codeFXeqY1 (compHitOf (constTermFun1 B)) (ap1 out w0) (ap1 s O)) codeFalse)
                           (ap1 (fst (thm12 (compHitOf (constTermFun1 B)))) (ap1 out w0)))
                      w0))
               codeFalse)
  chaitin_G1_closed B j_g L search w0 nvB clZ0 clB clJg h0 enum_at_jg szFires inRange hf =
    chaitin_G1_from_firing out (constTermFun1 B) B j_g L search w0 clZ0 clB clJg
      (\ y -> constTermFun1_eq B nvB y) h0 enum_at_jg szFires inRange hf
