{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbF3 -- the substitution functor   sbf3 : Fun2  on coded Formulas.
--
-- Parallel to  BRA4.SbT.sbt  on coded Terms.  Built atop the SAME
-- spec-carrying course-of-values  BRA4.CoVSpec.cov_spec  but with a
-- DIFFERENT step function  stepFun_sbf3  that dispatches on Formula
-- constructor tags (tag_eq / tag_neg / tag_imp) instead of Term tags
-- (tag_var / tag_ap1 / tag_ap2).
--
-- Critically, the  tag_eq  (atomic) branch invokes  sbt  DIRECTLY as a
-- Fun2 sub-combinator -- it does NOT look up the sub-positions ca, cb
-- in the  sbf3 cov-table, because those sub-positions are coded TERMS
-- and the  sbf3 cov-table only holds values of   sbf3  on prior formula
-- inputs.  The other two branches use the standard  lookupAt  pattern
-- against the  sbf3 cov-table (sub-positions are coded formulas).
--
-- Per  [[feedback-bra4-sbt-sbf-separate]] ,  sbt  and   sbf3  are kept
-- SEPARATE Fun2 functors with separate step functions; the existing
--  stepFun_sbt  in  BRA4/SbT.agda  is FROZEN.

module BRA4.SbF3 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.SbT3          using ( sbt3 ; get_K ; get_inner ; get_spec
                                     ; get_table ; get_newK ; get_tag ; get_body
                                     ; lookupAt )

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using ( condFork ; constN )
open import BRA3.SubT.NatEq      using ( natEqF )

------------------------------------------------------------------------
-- baseValue_sbf3 : the value at fuel 0.
--
-- We choose  baseValue_sbf3 = o  (constant O), the validating-decoder
-- fallback.  At fuel 0 the input is  O  and there is no meaningful
-- substitution to perform.

baseValue_sbf3 : Fun1
baseValue_sbf3 = o

baseValue_sbf3_eq :
  (spec : Term) ->
  Deriv (eqF (ap1 baseValue_sbf3 spec) O)
baseValue_sbf3_eq spec = ax_o spec

------------------------------------------------------------------------
-- Position-extraction Fun1's specific to sbf.
--
-- The packaged input has shape  pi K_term inner  with  K_term = natCode K
-- and  inner = pi spec table_K .  The standard accessors  get_K ,
--  get_spec ,  get_body ,  get_table , etc. are re-exported from
--  BRA4.SbT3  (they're not stepFun-specific).
--
-- For  sbf3 we add three branch-specific position decoders:
--
--   * atomic (tag_eq): body = pi ca cb.
--       get_ca_atom = Fst body, get_cb_atom = Snd body.
--   * neg (tag_neg):    body = cP directly (NOT wrapped in pi).
--       Use get_body as the index.
--   * imp (tag_imp):    body = pi cP cQ.
--       get_cP_imp = Fst body, get_cQ_imp = Snd body.

get_ca_atom : Fun1
get_ca_atom = compose1U Fst get_body

get_cb_atom : Fun1
get_cb_atom = compose1U Snd get_body

get_cP_imp : Fun1
get_cP_imp = compose1U Fst get_body

get_cQ_imp : Fun1
get_cQ_imp = compose1U Snd get_body

------------------------------------------------------------------------
-- Dispatch witnesses.

isEq : Fun1
isEq = C natEqF get_tag (constN tag_eq)

isNeg : Fun1
isNeg = C natEqF get_tag (constN tag_neg)

isImp : Fun1
isImp = C natEqF get_tag (constN tag_imp)

------------------------------------------------------------------------
-- Branch bodies.
--
-- atomic_branch_sbf3 :
--   pi (natCode tag_eq) (pi (sbt spec ca) (sbt spec cb))
--   sbt-on-Term sub-positions via direct combinator wrapping.

atomic_branch_sbf3 : Fun1
atomic_branch_sbf3 =
  C pi (constN tag_eq)
       (C pi (C sbt3 get_spec get_ca_atom)
             (C sbt3 get_spec get_cb_atom))

-- neg_branch_sbf3 :
--   pi (natCode tag_neg) (lookupAt get_body)
--   sub-position is a formula, so use the  sbf3 cov-table.

neg_branch_sbf3 : Fun1
neg_branch_sbf3 =
  C pi (constN tag_neg) (lookupAt get_body)

-- imp_branch_sbf3 :
--   pi (natCode tag_imp) (pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp))

imp_branch_sbf3 : Fun1
imp_branch_sbf3 =
  C pi (constN tag_imp)
       (C pi (lookupAt get_cP_imp) (lookupAt get_cQ_imp))

-- else_branch_sbf3 : validating-decoder fallback.

else_branch_sbf3 : Fun1
else_branch_sbf3 = o

------------------------------------------------------------------------
-- Cascade: dispatch atomic -> neg -> imp -> else.

imp_or_else : Fun1
imp_or_else = C condFork (C pi imp_branch_sbf3 else_branch_sbf3) isImp

neg_or_above : Fun1
neg_or_above = C condFork (C pi neg_branch_sbf3 imp_or_else) isNeg

stepBody_sbf3 : Fun1
stepBody_sbf3 = C condFork (C pi atomic_branch_sbf3 neg_or_above) isEq

stepFun_sbf3 : Fun2
stepFun_sbf3 = Post stepBody_sbf3 pi

------------------------------------------------------------------------
-- The full  sbf3 via cov_spec.

sbf3State : Fun2
sbf3State = cov_spec baseValue_sbf3 stepFun_sbf3

sbf3 : Fun2
sbf3 = Post readOff_spec sbf3State

sbf3_unfold :
  (spec t : Term) ->
  Deriv (eqF (ap2  sbf3 spec t) (ap1 readOff_spec (ap2 sbf3State spec t)))
sbf3_unfold spec t = axPost readOff_spec sbf3State spec t

------------------------------------------------------------------------
-- sbf3_at_O :  ap2  sbf3 spec O =Deriv= O .
--
-- Mirrors  BRA4.SbT.sbt_at_O .

sbf3_at_O :
  (spec : Term) ->
  Deriv (eqF (ap2  sbf3 spec O) O)
sbf3_at_O spec =
  let step1 :
        Deriv (eqF (ap2  sbf3 spec O)
                    (ap1 readOff_spec (ap2 sbf3State spec O)))
      step1 = sbf3_unfold spec O

      base_raw :
        Deriv (eqF (ap2 sbf3State spec O)
                    (ap2 pi O (ap2 pi spec
                              (ap2 pi (ap1 baseValue_sbf3 spec) O))))
      base_raw = cov_spec_base baseValue_sbf3 stepFun_sbf3 spec

      bv_eq :
        Deriv (eqF (ap1 baseValue_sbf3 spec) O)
      bv_eq = baseValue_sbf3_eq spec

      bv_lift :
        Deriv (eqF (ap2 pi (ap1 baseValue_sbf3 spec) O) (ap2 pi O O))
      bv_lift = congL pi O bv_eq

      bv_outer1 :
        Deriv (eqF (ap2 pi spec (ap2 pi (ap1 baseValue_sbf3 spec) O))
                    (ap2 pi spec (ap2 pi O O)))
      bv_outer1 = congR pi spec bv_lift

      bv_outer2 :
        Deriv (eqF (ap2 pi O (ap2 pi spec
                          (ap2 pi (ap1 baseValue_sbf3 spec) O)))
                    (ap2 pi O (ap2 pi spec (ap2 pi O O))))
      bv_outer2 = congR pi O bv_outer1

      base_full :
        Deriv (eqF (ap2 sbf3State spec O)
                    (ap2 pi O (ap2 pi spec (ap2 pi O O))))
      base_full = ruleTrans base_raw bv_outer2

      step3 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbf3State spec O))
                    (ap1 readOff_spec (ap2 pi O (ap2 pi spec (ap2 pi O O)))))
      step3 = cong1 readOff_spec base_full

      readOff_eq :
        Deriv (eqF (ap1 readOff_spec (ap2 pi O (ap2 pi spec (ap2 pi O O))))
                    (ap1 Fst (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O)))))))
      readOff_eq = readOff_spec_eq (ap2 pi O (ap2 pi spec (ap2 pi O O)))

      snd1 :
        Deriv (eqF (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O))))
                    (ap2 pi spec (ap2 pi O O)))
      snd1 = axSnd O (ap2 pi spec (ap2 pi O O))

      snd1_lift :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O)))))
                    (ap1 Snd (ap2 pi spec (ap2 pi O O))))
      snd1_lift = cong1 Snd snd1

      snd2 :
        Deriv (eqF (ap1 Snd (ap2 pi spec (ap2 pi O O))) (ap2 pi O O))
      snd2 = axSnd spec (ap2 pi O O)

      snd2_lift :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O)))))
                    (ap2 pi O O))
      snd2_lift = ruleTrans snd1_lift snd2

      fst_lift :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O))))))
                    (ap1 Fst (ap2 pi O O)))
      fst_lift = cong1 Fst snd2_lift

      fst_eq :
        Deriv (eqF (ap1 Fst (ap2 pi O O)) O)
      fst_eq = axFst O O

      readOff_at_O :
        Deriv (eqF (ap1 readOff_spec (ap2 pi O (ap2 pi spec (ap2 pi O O)))) O)
      readOff_at_O = ruleTrans readOff_eq (ruleTrans fst_lift fst_eq)
  in ruleTrans step1 (ruleTrans step3 readOff_at_O)
