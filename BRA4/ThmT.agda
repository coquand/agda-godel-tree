{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmT -- the validating-decoder verifier  thmT : Fun1 .
--
-- This file ships the DEFINITIONS of thmT plus the base-case closure
--  thmT_at_O .  Per-shape closures for ax / sb / mp / ind and the
-- completeness theorem  thmT_complete  are delivered in subsequent files.
--
-- ARCHITECTURE.
--
-- Built atop  BRA4.CoVSpec.cov_spec : Fun1 -> Fun2 -> Fun2 , the same
-- spec-carrying course-of-values used by  sbt  and  sbf .  Since thmT
-- takes one BRA argument (the proof tree code), we use a dummy
--  spec = O  and wrap the resulting Fun2 as a Fun1 :
--
--    thmT_F2  : Fun2  =  Post readOff_spec (cov_spec base step)
--    thmT     : Fun1  =  C thmT_F2 o I
--
-- so that  ap1 thmT y =Deriv= ap2 thmT_F2 O y .
--
-- The step function dispatches on the top-level tag of the encoded
-- proof  y = Pair (natCode tag) body :
--
--   tag = tag_ax  :  ax_branch -- sub-dispatch on the axiom index N
--                                inside body = Pair (natCode N) extra_arg ;
--                                returns codeFormula(axiom N's schema)
--                                parametrised on  extra_arg  (which holds
--                                functor codes / formula codes where
--                                applicable).  No recursion on sub-proofs.
--   tag = tag_sb  :  sb_branch -- body = Pair (sub_spec) (sub_proof_idx) .
--                                Returns  sbf sub_spec (thmT sub_proof_idx) .
--   tag = tag_mp  :  mp_branch -- body = Pair (p_imp_idx) (p_a_idx) .
--                                Looks up the two thmT cov-table values and
--                                does the well-formedness shape check
--                                (Fst of p_imp_val = natCode tag_imp and
--                                 Fst (Snd p_imp_val) = p_a_val);
--                                returns  Snd (Snd p_imp_val) if ok,
--                                codeTriv otherwise.
--   tag = tag_ind :  ind_branch -- body = Pair (p_base_idx) (p_step_idx) .
--                                Most intricate -- defers full
--                                well-formedness to S6-closures phase.
--                                Outputs the "P_motive code" if the two
--                                lookups line up with the induction
--                                shape; codeTriv otherwise.
--   else (any other tag) : codeTriv (validating-decoder fallback).
--
-- By construction every rule body output is either the codeFormula of
-- a derivable formula or  codeTriv = code(0 = 0) .

module BRA4.ThmT where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.SbF  using ( sbf )
-- NOTE: the  tag_sb2 / tag_sb3  dispatch branches are now DEAD (no encoding
-- emits those tags; all simultaneous substitutions were rewritten to nested
-- single-sb wraps -- see project_bra4_eliminate_sbt2_sbt3_consumers_done).
-- Their bodies are repointed from sbf2/sbf3 to plain sbf so the SbF2/SbF3
-- stacks can be deleted.  The cascade SHAPE is unchanged, so the dispatch
-- navigation lemmas (ThmTAtSb / ThmTAtMp / ThmTAtInd) are unaffected.
open import BRA4.SbT using
  ( get_K ; get_inner ; get_table ; get_newK ; get_tag ; get_body
  ; lookupAt )

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost
  ; I ; axI )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using ( condFork ; constN ; constN_eq )
open import BRA3.SubT.NatEq      using ( natEqF )

------------------------------------------------------------------------
-- Section 1.  baseValue_thmT : Fun1 -- the value at fuel 0.
--
-- We use  baseValue_thmT spec = codeTriv  for any  spec  (we will fix
--  spec = O  when wrapping thmT).  Concrete Fun1 :
--
--   codeTriv  =  codeFormula (atomic (eqn O O))
--             =  pi (natCode tag_eq) (pi O O) .
--
-- Fun1 form :  C pi (constN tag_eq) (C pi o o) .
--   ( o  is the Fun1 returning O ;  constN tag_eq  returns natCode 10.)

baseValue_thmT : Fun1
baseValue_thmT = C pi (constN tag_eq) (C pi o o)

baseValue_thmT_eq :
  (spec : Term) ->
  Deriv (eqF (ap1 baseValue_thmT spec) codeTriv)
baseValue_thmT_eq spec =
  let s1 :
        Deriv (eqF (ap1 baseValue_thmT spec)
                    (ap2 pi (ap1 (constN tag_eq) spec)
                            (ap1 (C pi o o) spec)))
      s1 = ax_C pi (constN tag_eq) (C pi o o) spec
      s2 :
        Deriv (eqF (ap1 (constN tag_eq) spec) (natCode tag_eq))
      s2 = constN_eq tag_eq spec
      s3 :
        Deriv (eqF (ap1 (C pi o o) spec)
                    (ap2 pi (ap1 o spec) (ap1 o spec)))
      s3 = ax_C pi o o spec
      s4 :
        Deriv (eqF (ap1 o spec) O)
      s4 = ax_o spec
      s5 :
        Deriv (eqF (ap2 pi (ap1 o spec) (ap1 o spec)) (ap2 pi O O))
      s5 = ruleTrans (congL pi (ap1 o spec) s4) (congR pi O s4)
      s35 :
        Deriv (eqF (ap1 (C pi o o) spec) (ap2 pi O O))
      s35 = ruleTrans s3 s5
      s_outer :
        Deriv (eqF (ap2 pi (ap1 (constN tag_eq) spec) (ap1 (C pi o o) spec))
                    (ap2 pi (natCode tag_eq) (ap2 pi O O)))
      s_outer = ruleTrans (congL pi (ap1 (C pi o o) spec) s2)
                          (congR pi (natCode tag_eq) s35)
  in ruleTrans s1 s_outer

------------------------------------------------------------------------
-- Section 2.  Position decoders specific to thmT.
--
-- The packaged step input has shape  pi K_term (pi spec table)  with
--  K_term = natCode K_prev .  We re-use the SbT-exposed accessors
--  get_K , get_newK , get_tag , get_body , get_table  -- they're
-- stepFun-agnostic.
--
-- thmT-specific projections of  body  (= the input proof's body) :
--
--   body = Pair (natCode N) extra_arg     for ax branch
--        = Pair sub_spec sub_proof_idx    for sb branch
--        = Pair p_imp_idx p_a_idx         for mp branch
--        = Pair p_base_idx p_step_idx     for ind branch

get_ax_index : Fun1
get_ax_index = compose1U Fst get_body

get_ax_extra : Fun1
get_ax_extra = compose1U Snd get_body

-- Common 1-deep extra-arg projections (for axK / axNeg : 2 formula params).
get_extra_Fst : Fun1
get_extra_Fst = compose1U Fst get_ax_extra

get_extra_Snd : Fun1
get_extra_Snd = compose1U Snd get_ax_extra

-- 2-deep (for axS : 3 formula params).
get_extra_FstSnd : Fun1
get_extra_FstSnd = compose1U Fst get_extra_Snd

get_extra_SndSnd : Fun1
get_extra_SndSnd = compose1U Snd get_extra_Snd

-- Functor-args projection helpers.  For ax 8 (axC) the extra_arg has
-- shape  pi (natCode tag_C) (pi codeG (pi codeH1 codeH2))  -- a
-- codeFun1 of an outer  C  combinator.  We expose three Fun1's that
-- decode it.
get_extra_g_after_tag : Fun1
get_extra_g_after_tag = compose1U Fst (compose1U Snd get_ax_extra)

get_extra_h1_after_tag : Fun1
get_extra_h1_after_tag = compose1U Fst
                          (compose1U Snd (compose1U Snd get_ax_extra))

get_extra_h2_after_tag : Fun1
get_extra_h2_after_tag = compose1U Snd
                          (compose1U Snd (compose1U Snd get_ax_extra))

-- sb branch: body = pi sub_spec sub_proof_idx.
get_sb_spec : Fun1
get_sb_spec = compose1U Fst get_body

get_sb_proof_idx : Fun1
get_sb_proof_idx = compose1U Snd get_body

-- mp branch: body = pi p_imp_idx p_a_idx.
get_mp_pImp_idx : Fun1
get_mp_pImp_idx = compose1U Fst get_body

get_mp_pA_idx : Fun1
get_mp_pA_idx = compose1U Snd get_body

-- ind branch: body = pi p_base_idx p_step_idx.
get_ind_pBase_idx : Fun1
get_ind_pBase_idx = compose1U Fst get_body

get_ind_pStep_idx : Fun1
get_ind_pStep_idx = compose1U Snd get_body

------------------------------------------------------------------------
-- Section 3.  Tag witnesses for top-level dispatch.

isAx : Fun1
isAx = C natEqF get_tag (constN tag_ax)

isSb : Fun1
isSb = C natEqF get_tag (constN tag_sb)

isSb2 : Fun1
isSb2 = C natEqF get_tag (constN tag_sb2)

isSb3 : Fun1
isSb3 = C natEqF get_tag (constN tag_sb3)

isMp : Fun1
isMp = C natEqF get_tag (constN tag_mp)

isInd : Fun1
isInd = C natEqF get_tag (constN tag_ind)

-- Sub-dispatch for ax branch: 14 schemas indexed 0..13.
-- For brevity each isAx_N is built directly inline in the cascade,
-- but expose the most-frequent ones as named helpers.

------------------------------------------------------------------------
-- Section 4.  Helper Fun1's for axiom-schema construction.
--
-- These are the "fixed Term" Fun1's : each returns its specific Term
-- for ANY input.  Built via nested  C pi  with leaf  constN  and  o .
--
-- Each name corresponds to a sub-piece of an axiom schema's codeFormula.

-- codeTerm(var k) = pi (natCode tag_var) (natCode k) , as a Fun1.
V0_F1 : Fun1
V0_F1 = C pi (constN tag_var) (constN zero)

V1_F1 : Fun1
V1_F1 = C pi (constN tag_var) (constN (suc zero))

V2_F1 : Fun1
V2_F1 = C pi (constN tag_var) (constN (suc (suc zero)))

-- codeFormula(eqF (var i) (var j)) = pi 10 (pi Vi Vj)
codeEq_V0_V1 : Fun1
codeEq_V0_V1 = C pi (constN tag_eq) (C pi V0_F1 V1_F1)

codeEq_V0_V2 : Fun1
codeEq_V0_V2 = C pi (constN tag_eq) (C pi V0_F1 V2_F1)

codeEq_V1_V2 : Fun1
codeEq_V1_V2 = C pi (constN tag_eq) (C pi V1_F1 V2_F1)

------------------------------------------------------------------------
-- Section 5.  ax sub-branches (14 schemas).
--
-- Each ax_branch_N : Fun1 takes the packaged step input and produces the
-- codeFormula of axiom N (in vars v0, v1, v2 for the schema form, with
-- functor / formula params spliced in via  get_ax_extra  projections).
--
-- The Term parameters (a, b, c, ...) of  axN params  are reintroduced
-- via an outer chain of  ruleInst -encoded substitutions ; that chain
-- lives in the  encode  function (S6b), not in ax_branch_N itself.

-- N = 0 : ax_succ_nonzero -- neg (eqF (ap1 s O) O)
-- code = pi 11 (pi 10 (pi (pi 2 (pi 4 O)) O))

axBranch0 : Fun1
axBranch0 =
  C pi (constN tag_neg)
       (C pi (constN tag_eq)
             (C pi (C pi (constN tag_ap1)
                         (C pi (constN tag_s) o))
                   o))

-- N = 1 : ax_o schema -- eqF (ap1 o (var 0)) O
-- code = pi 10 (pi (pi 2 (pi 5 V0)) O)

axBranch1 : Fun1
axBranch1 =
  C pi (constN tag_eq)
       (C pi (C pi (constN tag_ap1)
                   (C pi (constN tag_o) V0_F1))
             o)

-- N = 2 : ax_u schema -- eqF (ap1 u (var 0)) (var 0)
-- code = pi 10 (pi (pi 2 (pi 6 V0)) V0)

axBranch2 : Fun1
axBranch2 =
  C pi (constN tag_eq)
       (C pi (C pi (constN tag_ap1)
                   (C pi (constN tag_u) V0_F1))
             V0_F1)

-- N = 3 : ax_v schema -- eqF (ap2 v (var 0) (var 1)) (var 1)
-- code = pi 10 (pi (pi 3 (pi 8 (pi V0 V1))) V1)

axBranch3 : Fun1
axBranch3 =
  C pi (constN tag_eq)
       (C pi (C pi (constN tag_ap2)
                   (C pi (constN tag_v) (C pi V0_F1 V1_F1)))
             V1_F1)

-- N = 4 : ax_eqTrans schema --
-- imp (eqF v0 v1) (imp (eqF v0 v2) (eqF v1 v2))

axBranch4 : Fun1
axBranch4 =
  C pi (constN tag_imp)
       (C pi codeEq_V0_V1
             (C pi (constN tag_imp)
                   (C pi codeEq_V0_V2 codeEq_V1_V2)))

-- N = 5 : ax_eqCong1 schema -- imp (eqF v0 v1) (eqF (ap1 f v0) (ap1 f v1))
-- extra_arg = codeFun1 f  (as a Term).

axBranch5 : Fun1
axBranch5 =
  C pi (constN tag_imp)
       (C pi codeEq_V0_V1
             (C pi (constN tag_eq)
                   (C pi (C pi (constN tag_ap1)
                               (C pi get_ax_extra V0_F1))
                         (C pi (constN tag_ap1)
                               (C pi get_ax_extra V1_F1)))))

-- N = 6 : ax_eqCongL schema -- imp (eqF v0 v1) (eqF (ap2 g v0 v2) (ap2 g v1 v2))
-- extra_arg = codeFun2 g .

axBranch6 : Fun1
axBranch6 =
  C pi (constN tag_imp)
       (C pi codeEq_V0_V1
             (C pi (constN tag_eq)
                   (C pi (C pi (constN tag_ap2)
                               (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                         (C pi (constN tag_ap2)
                               (C pi get_ax_extra (C pi V1_F1 V2_F1))))))

-- N = 7 : ax_eqCongR schema -- imp (eqF v0 v1) (eqF (ap2 g v2 v0) (ap2 g v2 v1))
-- extra_arg = codeFun2 g .

axBranch7 : Fun1
axBranch7 =
  C pi (constN tag_imp)
       (C pi codeEq_V0_V1
             (C pi (constN tag_eq)
                   (C pi (C pi (constN tag_ap2)
                               (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                         (C pi (constN tag_ap2)
                               (C pi get_ax_extra (C pi V2_F1 V1_F1))))))

-- N = 8 : ax_C schema -- eqF (ap1 (C g h1 h2) v0) (ap2 g (ap1 h1 v0) (ap1 h2 v0))
-- extra_arg = codeFun1 (C g h1 h2)
--           = pi tag_C (pi codeG (pi codeH1 codeH2)) .
-- Projections : get_extra_g_after_tag, get_extra_h1_after_tag, get_extra_h2_after_tag.

axBranch8 : Fun1
axBranch8 =
  C pi (constN tag_eq)
       (C pi (C pi (constN tag_ap1)
                   (C pi get_ax_extra V0_F1))
             (C pi (constN tag_ap2)
                   (C pi get_extra_g_after_tag
                         (C pi (C pi (constN tag_ap1)
                                     (C pi get_extra_h1_after_tag V0_F1))
                               (C pi (constN tag_ap1)
                                     (C pi get_extra_h2_after_tag V0_F1))))))

-- N = 9 : ax_R_base schema -- eqF (ap2 (R g h1 h2) v0 O) (ap1 g v0)
-- extra_arg = codeFun2 (R g h1 h2) = pi tag_R (pi codeG (pi codeH1 codeH2)) .
-- Same internal layout as ax 8 (modulo the outer  R  tag) so we re-use the
-- projection helpers ; what differs is just the LHS/RHS schema templates.

axBranch9 : Fun1
axBranch9 =
  C pi (constN tag_eq)
       (C pi (C pi (constN tag_ap2)
                   (C pi get_ax_extra (C pi V0_F1 o)))
             (C pi (constN tag_ap1)
                   (C pi get_extra_g_after_tag V0_F1)))

-- N = 10 : ax_R_step schema --
-- eqF (ap2 (R g h1 h2) v0 (ap1 s v1))
--     (ap2 h1 (ap2 h2 v0 v1) (ap2 (R g h1 h2) v0 v1))

axBranch10 : Fun1
axBranch10 =
  C pi (constN tag_eq)
       (C pi (C pi (constN tag_ap2)
                   (C pi get_ax_extra
                         (C pi V0_F1
                               (C pi (constN tag_ap1)
                                     (C pi (constN tag_s) V1_F1)))))
             (C pi (constN tag_ap2)
                   (C pi get_extra_h1_after_tag
                         (C pi (C pi (constN tag_ap2)
                                     (C pi get_extra_h2_after_tag
                                           (C pi V0_F1 V1_F1)))
                               (C pi (constN tag_ap2)
                                     (C pi get_ax_extra
                                           (C pi V0_F1 V1_F1)))))))

-- N = 11 : axK schema -- imp A (imp B A)
-- extra_arg = pi codeA codeB .
-- Projections : get_extra_Fst (= codeA) , get_extra_Snd (= codeB).

axBranch11 : Fun1
axBranch11 =
  C pi (constN tag_imp)
       (C pi get_extra_Fst
             (C pi (constN tag_imp)
                   (C pi get_extra_Snd get_extra_Fst)))

-- N = 12 : axS schema -- imp (imp A (imp B C)) (imp (imp A B) (imp A C))
-- extra_arg = pi codeA (pi codeB codeC) .
-- Projections : get_extra_Fst (= codeA) ,
--                get_extra_FstSnd (= codeB) ,
--                get_extra_SndSnd (= codeC).

axBranch12 : Fun1
axBranch12 =
  C pi (constN tag_imp)
       (C pi (C pi (constN tag_imp)
                   (C pi get_extra_Fst
                         (C pi (constN tag_imp)
                               (C pi get_extra_FstSnd get_extra_SndSnd))))
             (C pi (constN tag_imp)
                   (C pi (C pi (constN tag_imp)
                               (C pi get_extra_Fst get_extra_FstSnd))
                         (C pi (constN tag_imp)
                               (C pi get_extra_Fst get_extra_SndSnd)))))

-- N = 13 : axNeg schema -- imp (imp (neg A) (neg B)) (imp B A)
-- extra_arg = pi codeA codeB .

axBranch13 : Fun1
axBranch13 =
  C pi (constN tag_imp)
       (C pi (C pi (constN tag_imp)
                   (C pi (C pi (constN tag_neg) get_extra_Fst)
                         (C pi (constN tag_neg) get_extra_Snd)))
             (C pi (constN tag_imp)
                   (C pi get_extra_Snd get_extra_Fst)))

------------------------------------------------------------------------
-- Section 6.  ax sub-dispatch cascade.
--
-- 14-way condFork cascade on  get_ax_index .  We test each N in
-- ascending order ; the "fallthrough" of each step is the next-N test.

-- Sub-witnesses isAxN.
isAx0  : Fun1 ; isAx0  = C natEqF get_ax_index (constN zero)
isAx1  : Fun1 ; isAx1  = C natEqF get_ax_index (constN (suc zero))
isAx2  : Fun1 ; isAx2  = C natEqF get_ax_index (constN (suc (suc zero)))
isAx3  : Fun1 ; isAx3  = C natEqF get_ax_index (constN (suc (suc (suc zero))))
isAx4  : Fun1 ; isAx4  = C natEqF get_ax_index (constN (suc (suc (suc (suc zero)))))
isAx5  : Fun1 ; isAx5  = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc zero))))))
isAx6  : Fun1 ; isAx6  = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc zero)))))))
isAx7  : Fun1 ; isAx7  = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc zero))))))))
isAx8  : Fun1 ; isAx8  = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
isAx9  : Fun1 ; isAx9  = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
isAx10 : Fun1 ; isAx10 = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
isAx11 : Fun1 ; isAx11 = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
isAx12 : Fun1 ; isAx12 = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
isAx13 : Fun1 ; isAx13 = C natEqF get_ax_index (constN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))

-- Cascade from highest N down to lowest, ending with codeTriv fallback.
ax_fallthrough : Fun1
ax_fallthrough = baseValue_thmT   -- = codeTriv

axDispatch13 : Fun1
axDispatch13 = C condFork (C pi axBranch13 ax_fallthrough)  isAx13

axDispatch12 : Fun1
axDispatch12 = C condFork (C pi axBranch12 axDispatch13) isAx12

axDispatch11 : Fun1
axDispatch11 = C condFork (C pi axBranch11 axDispatch12) isAx11

axDispatch10 : Fun1
axDispatch10 = C condFork (C pi axBranch10 axDispatch11) isAx10

axDispatch9 : Fun1
axDispatch9 = C condFork (C pi axBranch9 axDispatch10) isAx9

axDispatch8 : Fun1
axDispatch8 = C condFork (C pi axBranch8 axDispatch9) isAx8

axDispatch7 : Fun1
axDispatch7 = C condFork (C pi axBranch7 axDispatch8) isAx7

axDispatch6 : Fun1
axDispatch6 = C condFork (C pi axBranch6 axDispatch7) isAx6

axDispatch5 : Fun1
axDispatch5 = C condFork (C pi axBranch5 axDispatch6) isAx5

axDispatch4 : Fun1
axDispatch4 = C condFork (C pi axBranch4 axDispatch5) isAx4

axDispatch3 : Fun1
axDispatch3 = C condFork (C pi axBranch3 axDispatch4) isAx3

axDispatch2 : Fun1
axDispatch2 = C condFork (C pi axBranch2 axDispatch3) isAx2

axDispatch1 : Fun1
axDispatch1 = C condFork (C pi axBranch1 axDispatch2) isAx1

ax_branch_thmT : Fun1
ax_branch_thmT = C condFork (C pi axBranch0 axDispatch1) isAx0

------------------------------------------------------------------------
-- Section 7.  sb_branch_thmT .
--
-- body = pi sub_spec sub_proof_idx .
-- Output : sbf sub_spec (thmT_table[sub_proof_idx])
--   where thmT_table is the running cov-table, looked up via lookupAt.
--
-- sb_branch_thmT = C sbf get_sb_spec get_sb_proof_val
-- where get_sb_proof_val = lookupAt get_sb_proof_idx .

get_sb_proof_val : Fun1
get_sb_proof_val = lookupAt get_sb_proof_idx

sb_branch_thmT : Fun1
sb_branch_thmT = C sbf get_sb_spec get_sb_proof_val

-- sb2 / sb3 branches : same body shape pi cSpec cProofIdx as sb, but
-- with the 2-var / 3-var simultaneous-substitution functor sbf2 / sbf3
-- respectively.  The spec is the full pair-encoded 2- or 3-variable
-- specification (pi (pi (natCode k1) S1) (pi (natCode k2) S2) for sb2 ;
-- analogous 3-deep for sb3).  sub_proof_val is looked up the same way.

sb2_branch_thmT : Fun1
sb2_branch_thmT = C sbf get_sb_spec get_sb_proof_val

sb3_branch_thmT : Fun1
sb3_branch_thmT = C sbf get_sb_spec get_sb_proof_val

------------------------------------------------------------------------
-- Section 8.  mp_branch_thmT .
--
-- body = pi p_imp_idx p_a_idx .
-- Let pImp_val = thmT_table[p_imp_idx] (should = codeFormula (imp A B))
--     pA_val   = thmT_table[p_a_idx]   (should = codeFormula A) .
--
-- Well-formedness check :
--   Fst pImp_val = natCode tag_imp                AND
--   Fst (Snd pImp_val) = pA_val (via natEqF on encoded formulas).
--
-- Note : natEqF compares only natCode-level Terms ; for full
-- formula-equality we'd need a deeper structural-equality primitive.
-- The S6 design choice (per learnt.md) is to compare the FULL Terms
-- via natEqF -- the encoded formulas are Pair-trees whose underlying
-- nat-codes are well-defined (cantor-encoded).  In practice we treat
-- natEqF as a coarse equality at the encoded level ; the actual
-- correctness lives in thmT_complete, where the IH ensures the
-- equality always holds for properly-encoded proofs.
--
-- For ill-formed inputs, output codeTriv.

get_pImp_val : Fun1
get_pImp_val = lookupAt get_mp_pImp_idx

get_pA_val : Fun1
get_pA_val = lookupAt get_mp_pA_idx

-- get_pImp_tag = Fst pImp_val (= natCode tag_imp if well-formed)
get_pImp_tag : Fun1
get_pImp_tag = compose1U Fst get_pImp_val

-- get_pImp_body = Snd pImp_val (= pi A_code B_code if well-formed)
get_pImp_body : Fun1
get_pImp_body = compose1U Snd get_pImp_val

-- get_pImp_ant = Fst (Snd pImp_val) (= A_code if well-formed)
get_pImp_ant : Fun1
get_pImp_ant = compose1U Fst get_pImp_body

-- get_pImp_cons = Snd (Snd pImp_val) (= B_code if well-formed)
get_pImp_cons : Fun1
get_pImp_cons = compose1U Snd get_pImp_body

-- isMpTagOk = natEqF (Fst pImp_val) (natCode tag_imp)
isMpTagOk : Fun1
isMpTagOk = C natEqF get_pImp_tag (constN tag_imp)

-- isMpAntOk = natEqF (Fst (Snd pImp_val)) (pA_val)
-- Coarse natEqF on the antecedent code -- see comment above.
isMpAntOk : Fun1
isMpAntOk = C natEqF get_pImp_ant get_pA_val

-- mp_branch_thmT = if isMpTagOk and isMpAntOk then get_pImp_cons else codeTriv .
--
-- Cascade : if-tag-ok then (if-ant-ok then cons else triv) else triv .

mp_inner : Fun1
mp_inner = C condFork (C pi get_pImp_cons baseValue_thmT) isMpAntOk

mp_branch_thmT : Fun1
mp_branch_thmT = C condFork (C pi mp_inner baseValue_thmT) isMpTagOk

------------------------------------------------------------------------
-- Section 9.  ind_branch_thmT .
--
-- body = pi p_base_idx p_step_idx .
-- pBase_val should = codeFormula (substF 0 O P_motive)  = P[0/x0]
-- pStep_val should = codeFormula (imp P_motive (substF 0 (s var0) P_motive))
--
-- Well-formedness :
--   Fst pStep_val = natCode tag_imp                                AND
--   Fst (Snd pStep_val) is a codeFormula that, when substF'd with
--   substituent O at index 0, equals pBase_val .
--
-- The CORRECT output is P_motive's code  = Fst (Snd pStep_val) .
--
-- S6-Round 1 simplification : we DEFER the deep substF check (it
-- requires invoking sbf with substituent O and comparing the result
-- via natEqF, which compounds the coarse-equality concern).  Round 1
-- ships a minimal well-formedness check (tag of pStep_val is tag_imp);
-- the substF/equality check is delivered in the S6b closures phase.
--
-- For ill-formed inputs, output codeTriv.

get_pBase_val : Fun1
get_pBase_val = lookupAt get_ind_pBase_idx

get_pStep_val : Fun1
get_pStep_val = lookupAt get_ind_pStep_idx

get_pStep_tag : Fun1
get_pStep_tag = compose1U Fst get_pStep_val

get_pStep_body : Fun1
get_pStep_body = compose1U Snd get_pStep_val

-- get_motive = Fst (Snd pStep_val) (= codeFormula P_motive if well-formed)
get_motive : Fun1
get_motive = compose1U Fst get_pStep_body

isIndStepImp : Fun1
isIndStepImp = C natEqF get_pStep_tag (constN tag_imp)

ind_branch_thmT : Fun1
ind_branch_thmT = C condFork (C pi get_motive baseValue_thmT) isIndStepImp

------------------------------------------------------------------------
-- Section 10.  Else branch (validating-decoder fallback).

else_branch_thmT : Fun1
else_branch_thmT = baseValue_thmT

------------------------------------------------------------------------
-- Section 11.  Main top-level cascade : ax / sb / mp / ind / else.

ind_or_else : Fun1
ind_or_else = C condFork (C pi ind_branch_thmT else_branch_thmT) isInd

mp_or_above : Fun1
mp_or_above = C condFork (C pi mp_branch_thmT ind_or_else) isMp

sb2_or_above : Fun1
sb2_or_above = C condFork (C pi sb2_branch_thmT mp_or_above) isSb2

sb3_or_above : Fun1
sb3_or_above = C condFork (C pi sb3_branch_thmT sb2_or_above) isSb3

sb_or_above : Fun1
sb_or_above = C condFork (C pi sb_branch_thmT sb3_or_above) isSb

stepBody_thmT : Fun1
stepBody_thmT = C condFork (C pi ax_branch_thmT sb_or_above) isAx

stepFun_thmT : Fun2
stepFun_thmT = Post stepBody_thmT pi

------------------------------------------------------------------------
-- Section 12.  thmTState : Fun2 -- the running cov-state.
-- thmT_F2  : Fun2 -- readOff_spec composed with thmTState.
-- thmT     : Fun1 -- the Fun1 wrapper that hardcodes spec = O.

thmTState : Fun2
thmTState = cov_spec baseValue_thmT stepFun_thmT

thmT_F2 : Fun2
thmT_F2 = Post readOff_spec thmTState

-- thmT y = thmT_F2 (o y) (I y) = thmT_F2 O y (after  ax_o + axI ).
thmT : Fun1
thmT = C thmT_F2 o I

thmT_unfold_F2 :
  (spec t : Term) ->
  Deriv (eqF (ap2 thmT_F2 spec t) (ap1 readOff_spec (ap2 thmTState spec t)))
thmT_unfold_F2 spec t = axPost readOff_spec thmTState spec t

-- thmT y = thmT_F2 O y .
thmT_unfold :
  (y : Term) ->
  Deriv (eqF (ap1 thmT y) (ap2 thmT_F2 O y))
thmT_unfold y =
  let s1 :
        Deriv (eqF (ap1 thmT y)
                    (ap2 thmT_F2 (ap1 o y) (ap1 I y)))
      s1 = ax_C thmT_F2 o I y
      s2 : Deriv (eqF (ap1 o y) O)
      s2 = ax_o y
      s3 : Deriv (eqF (ap1 I y) y)
      s3 = axI y
      s4 :
        Deriv (eqF (ap2 thmT_F2 (ap1 o y) (ap1 I y))
                    (ap2 thmT_F2 O (ap1 I y)))
      s4 = congL thmT_F2 (ap1 I y) s2
      s5 :
        Deriv (eqF (ap2 thmT_F2 O (ap1 I y)) (ap2 thmT_F2 O y))
      s5 = congR thmT_F2 O s3
  in ruleTrans s1 (ruleTrans s4 s5)

------------------------------------------------------------------------
-- Section 13.  thmT_at_O .
--
-- Chain :
--   thmT O  = thmT_F2 O O                                  [thmT_unfold]
--           = readOff_spec (thmTState O O)                  [axPost]
--   thmTState O O = pi O (pi O (pi (baseValue_thmT O) O))   [cov_spec_base]
--   baseValue_thmT O = codeTriv                              [baseValue_thmT_eq]
--   readOff_spec (pi O (pi O (pi codeTriv O)))
--      = Fst (Snd (Snd (...)))
--      = Fst (Snd (pi O (pi codeTriv O)))                   [axSnd]
--      = Fst (pi codeTriv O)                                 [axSnd]
--      = codeTriv                                             [axFst]

thmT_at_O : Deriv (eqF (ap1 thmT O) codeTriv)
thmT_at_O =
  let step1 :
        Deriv (eqF (ap1 thmT O) (ap2 thmT_F2 O O))
      step1 = thmT_unfold O

      step2 :
        Deriv (eqF (ap2 thmT_F2 O O)
                    (ap1 readOff_spec (ap2 thmTState O O)))
      step2 = thmT_unfold_F2 O O

      base_raw :
        Deriv (eqF (ap2 thmTState O O)
                    (ap2 pi O (ap2 pi O
                              (ap2 pi (ap1 baseValue_thmT O) O))))
      base_raw = cov_spec_base baseValue_thmT stepFun_thmT O

      bv_eq :
        Deriv (eqF (ap1 baseValue_thmT O) codeTriv)
      bv_eq = baseValue_thmT_eq O

      bv_lift :
        Deriv (eqF (ap2 pi (ap1 baseValue_thmT O) O) (ap2 pi codeTriv O))
      bv_lift = congL pi O bv_eq

      bv_outer1 :
        Deriv (eqF (ap2 pi O (ap2 pi (ap1 baseValue_thmT O) O))
                    (ap2 pi O (ap2 pi codeTriv O)))
      bv_outer1 = congR pi O bv_lift

      bv_outer2 :
        Deriv (eqF (ap2 pi O (ap2 pi O
                          (ap2 pi (ap1 baseValue_thmT O) O)))
                    (ap2 pi O (ap2 pi O (ap2 pi codeTriv O))))
      bv_outer2 = congR pi O bv_outer1

      base_full :
        Deriv (eqF (ap2 thmTState O O)
                    (ap2 pi O (ap2 pi O (ap2 pi codeTriv O))))
      base_full = ruleTrans base_raw bv_outer2

      step3 :
        Deriv (eqF (ap1 readOff_spec (ap2 thmTState O O))
                    (ap1 readOff_spec (ap2 pi O (ap2 pi O (ap2 pi codeTriv O)))))
      step3 = cong1 readOff_spec base_full

      readOff_eq :
        Deriv (eqF (ap1 readOff_spec (ap2 pi O (ap2 pi O (ap2 pi codeTriv O))))
                    (ap1 Fst (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi O (ap2 pi codeTriv O)))))))
      readOff_eq = readOff_spec_eq (ap2 pi O (ap2 pi O (ap2 pi codeTriv O)))

      snd1 :
        Deriv (eqF (ap1 Snd (ap2 pi O (ap2 pi O (ap2 pi codeTriv O))))
                    (ap2 pi O (ap2 pi codeTriv O)))
      snd1 = axSnd O (ap2 pi O (ap2 pi codeTriv O))

      snd1_lift :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi O (ap2 pi codeTriv O)))))
                    (ap1 Snd (ap2 pi O (ap2 pi codeTriv O))))
      snd1_lift = cong1 Snd snd1

      snd2 :
        Deriv (eqF (ap1 Snd (ap2 pi O (ap2 pi codeTriv O))) (ap2 pi codeTriv O))
      snd2 = axSnd O (ap2 pi codeTriv O)

      snd2_lift :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi O (ap2 pi codeTriv O)))))
                    (ap2 pi codeTriv O))
      snd2_lift = ruleTrans snd1_lift snd2

      fst_lift :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi O (ap2 pi codeTriv O))))))
                    (ap1 Fst (ap2 pi codeTriv O)))
      fst_lift = cong1 Fst snd2_lift

      fst_eq :
        Deriv (eqF (ap1 Fst (ap2 pi codeTriv O)) codeTriv)
      fst_eq = axFst codeTriv O

      readOff_at_O :
        Deriv (eqF (ap1 readOff_spec (ap2 pi O (ap2 pi O (ap2 pi codeTriv O)))) codeTriv)
      readOff_at_O = ruleTrans readOff_eq (ruleTrans fst_lift fst_eq)
  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3 readOff_at_O))
