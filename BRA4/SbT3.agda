{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbT3 -- the 3-variable simultaneous substitution functor
--  sbt3 : Fun2  on coded Terms.
--
-- ======================================================================
-- DESIGN.
-- ======================================================================
--
-- Parallel to BRA4.SbT2.sbt2, but the "spec" arg encodes THREE
-- substitutions simultaneously :
--
--   spec3 = pi (pi (natCode k1) S1)
--              (pi (pi (natCode k2) S2)
--                  (pi (natCode k3) S3))
--
-- with  k1 /= k2 , k1 /= k3 , k2 /= k3 .  At each var-i position in the
-- input,  sbt3  plops the matching  S_j  (if  i = k_j ) or preserves the
-- var (otherwise).
--
-- Mirrors  ruleInst3  (BRA3.RuleInst3) at the encoded level :  for
-- distinct k1, k2, k3 , there is no variable-capture issue because the
-- substitutions are applied SIMULTANEOUSLY in one cascade.
--
-- ======================================================================
-- SCOPE OF THIS FILE (proof-of-concept).
-- ======================================================================
--
-- 1.  baseValue_sbt3 , stepFun_sbt3 (full multi-var dispatch).
-- 2.  sbt3 : Fun2  via cov_spec .
-- 3.  sbt3_at_O .
--
-- The contract closures
--   sbt3_at_var_match_1 , sbt3_at_var_match_2 , sbt3_at_var_nomatch ,
--   sbt3_at_ap1 , sbt3_at_ap2
-- live in subsequent BRA4.SbT3AtVar / BRA4.SbT3AtAp .

module BRA4.SbT3 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec

open import BRA3.Church          using ( pi ; sub )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using ( condFork ; constN )
open import BRA3.SubT.NatEq      using ( natEqF )

------------------------------------------------------------------------
-- baseValue_sbt3 : the value at fuel 0  (= the empty/leaf input  O ).
-- Same as sbt's: substT_multi O = O .

baseValue_sbt3 : Fun1
baseValue_sbt3 = o

baseValue_sbt3_eq :
  (spec : Term) ->
  Deriv (eqF (ap1 baseValue_sbt3 spec) O)
baseValue_sbt3_eq spec = ax_o spec

------------------------------------------------------------------------
-- Position accessors (Fun1) for the packaged input  pi K_term inner
-- where  inner = pi spec2 table  and  spec2 = pi (pi (natCode k1) S1)
--                                                (pi (natCode k2) S2) .

get_K : Fun1
get_K = Fst

get_inner : Fun1
get_inner = Snd

get_spec : Fun1
get_spec = compose1U Fst get_inner          -- Fst inner = spec2

get_table : Fun1
get_table = compose1U Snd get_inner          -- Snd inner = table

-- spec3 = pi spec_left spec_right  where
--   spec_left  = pi (natCode k1) S1
--   spec_right = pi spec_mid_left spec_mid_right
--   spec_mid_left  = pi (natCode k2) S2
--   spec_mid_right = pi (natCode k3) S3

get_spec_left : Fun1
get_spec_left = compose1U Fst get_spec

get_spec_right : Fun1
get_spec_right = compose1U Snd get_spec

get_spec_mid_left : Fun1
get_spec_mid_left = compose1U Fst get_spec_right

get_spec_mid_right : Fun1
get_spec_mid_right = compose1U Snd get_spec_right

get_spec1Fst : Fun1
get_spec1Fst = compose1U Fst get_spec_left      -- natCode k1

get_spec1Snd : Fun1
get_spec1Snd = compose1U Snd get_spec_left      -- S1

get_spec2Fst : Fun1
get_spec2Fst = compose1U Fst get_spec_mid_left  -- natCode k2

get_spec2Snd : Fun1
get_spec2Snd = compose1U Snd get_spec_mid_left  -- S2

get_spec3Fst : Fun1
get_spec3Fst = compose1U Fst get_spec_mid_right -- natCode k3

get_spec3Snd : Fun1
get_spec3Snd = compose1U Snd get_spec_mid_right -- S3

get_newK : Fun1
get_newK = compose1U s get_K                  -- s K_term = newK

get_tag : Fun1
get_tag = compose1U Fst get_newK             -- Fst newK = tag

get_body : Fun1
get_body = compose1U Snd get_newK            -- Snd newK = body

------------------------------------------------------------------------
-- Dispatch witnesses (Fun1, value sO when matching).

isVar : Fun1
isVar = C natEqF get_tag (constN tag_var)

isAp1 : Fun1
isAp1 = C natEqF get_tag (constN tag_ap1)

isAp2 : Fun1
isAp2 = C natEqF get_tag (constN tag_ap2)

------------------------------------------------------------------------
-- Var branch (the 3-variable dispatch, the heart of sbt3).
--   body should be  natCode m  (the var index of the input).
--   Cascade:
--     if  natEq m k1 :  return  S1  (= get_spec1Snd).
--     else if  natEq m k2 :  return  S2 .
--     else if  natEq m k3 :  return  S3 .
--     else :  preserve var ( = get_newK , the input as-is).

isVarMatch1 : Fun1
isVarMatch1 = C natEqF get_body get_spec1Fst

isVarMatch2 : Fun1
isVarMatch2 = C natEqF get_body get_spec2Fst

isVarMatch3 : Fun1
isVarMatch3 = C natEqF get_body get_spec3Fst

-- Innermost condFork (level-3): match against k3 vs preserve.
var_branch_match3 : Fun1
var_branch_match3 =
  C condFork (C pi get_spec3Snd get_newK) isVarMatch3

-- Middle condFork (level-2): match against k2 vs go to level-3.
var_branch_match2 : Fun1
var_branch_match2 =
  C condFork (C pi get_spec2Snd var_branch_match3) isVarMatch2

-- Outer condFork (level-1): match against k1 vs go to level-2.
var_branch : Fun1
var_branch =
  C condFork (C pi get_spec1Snd var_branch_match2) isVarMatch1

------------------------------------------------------------------------
-- Lookup helper (same as sbt).

lookupAt : Fun1 -> Fun1
lookupAt idx_F1 =
  compose1U Fst
    (C (iter Snd)
      get_table
      (C sub get_K idx_F1))

------------------------------------------------------------------------
-- Ap1 / Ap2 branches (identical to sbt's — recurse with same spec via
-- table lookup; no dependence on spec format).

get_bodyFst_ap1 : Fun1
get_bodyFst_ap1 = compose1U Fst get_body

get_ct_ap1 : Fun1
get_ct_ap1 = compose1U Snd get_body

get_val_ct_ap1 : Fun1
get_val_ct_ap1 = lookupAt get_ct_ap1

ap1_branch : Fun1
ap1_branch =
  C pi (constN tag_ap1)
       (C pi get_bodyFst_ap1 get_val_ct_ap1)

get_bodyFst_ap2 : Fun1
get_bodyFst_ap2 = compose1U Fst get_body

get_ab_ap2 : Fun1
get_ab_ap2 = compose1U Snd get_body

get_ca_ap2 : Fun1
get_ca_ap2 = compose1U Fst get_ab_ap2

get_cb_ap2 : Fun1
get_cb_ap2 = compose1U Snd get_ab_ap2

get_val_ca : Fun1
get_val_ca = lookupAt get_ca_ap2

get_val_cb : Fun1
get_val_cb = lookupAt get_cb_ap2

ap2_branch : Fun1
ap2_branch =
  C pi (constN tag_ap2)
       (C pi get_bodyFst_ap2
             (C pi get_val_ca get_val_cb))

------------------------------------------------------------------------
-- Else branch : validating-decoder fallback (same as sbt).

else_branch : Fun1
else_branch = o

------------------------------------------------------------------------
-- Cascade :  condFork  isVar (var, condFork isAp1 (ap1, condFork isAp2
--                                                     (ap2, else))) .

ap2_or_else : Fun1
ap2_or_else = C condFork (C pi ap2_branch else_branch) isAp2

ap1_or_above : Fun1
ap1_or_above = C condFork (C pi ap1_branch ap2_or_else) isAp1

stepBody_sbt3 : Fun1
stepBody_sbt3 = C condFork (C pi var_branch ap1_or_above) isVar

stepFun_sbt3 : Fun2
stepFun_sbt3 = Post stepBody_sbt3 pi

------------------------------------------------------------------------
-- The full sbt3 via cov_spec .

sbt3State : Fun2
sbt3State = cov_spec baseValue_sbt3 stepFun_sbt3

sbt3 : Fun2
sbt3 = Post readOff_spec sbt3State

sbt3_unfold :
  (spec t : Term) ->
  Deriv (eqF (ap2 sbt3 spec t) (ap1 readOff_spec (ap2 sbt3State spec t)))
sbt3_unfold spec t = axPost readOff_spec sbt3State spec t

------------------------------------------------------------------------
-- sbt3_at_O :  ap2 sbt3 spec O =Deriv= O .  (Same proof shape as sbt_at_O .)

sbt3_at_O :
  (spec : Term) ->
  Deriv (eqF (ap2 sbt3 spec O) O)
sbt3_at_O spec =
  let
    step1 :
      Deriv (eqF (ap2 sbt3 spec O)
                  (ap1 readOff_spec (ap2 sbt3State spec O)))
    step1 = sbt3_unfold spec O

    base_raw :
      Deriv (eqF (ap2 sbt3State spec O)
                  (ap2 pi O (ap2 pi spec
                            (ap2 pi (ap1 baseValue_sbt3 spec) O))))
    base_raw = cov_spec_base baseValue_sbt3 stepFun_sbt3 spec

    bv_eq :
      Deriv (eqF (ap1 baseValue_sbt3 spec) O)
    bv_eq = baseValue_sbt3_eq spec

    bv_lift :
      Deriv (eqF (ap2 pi (ap1 baseValue_sbt3 spec) O) (ap2 pi O O))
    bv_lift = congL pi O bv_eq

    bv_outer1 :
      Deriv (eqF (ap2 pi spec (ap2 pi (ap1 baseValue_sbt3 spec) O))
                  (ap2 pi spec (ap2 pi O O)))
    bv_outer1 = congR pi spec bv_lift

    bv_outer2 :
      Deriv (eqF (ap2 pi O (ap2 pi spec
                        (ap2 pi (ap1 baseValue_sbt3 spec) O)))
                  (ap2 pi O (ap2 pi spec (ap2 pi O O))))
    bv_outer2 = congR pi O bv_outer1

    base_full :
      Deriv (eqF (ap2 sbt3State spec O)
                  (ap2 pi O (ap2 pi spec (ap2 pi O O))))
    base_full = ruleTrans base_raw bv_outer2

    step3 :
      Deriv (eqF (ap1 readOff_spec (ap2 sbt3State spec O))
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

------------------------------------------------------------------------
-- TODO (fresh session) : the contract closures
--
--   sbt3_at_var_match_1 :
--     (k1 k2 : Nat) (S1 S2 : Term) ->
--     Deriv (eqF (ap2 sbt3 (ap2 pi (ap2 pi (natCode k1) S1)
--                                  (ap2 pi (natCode k2) S2))
--                           (ap2 pi (natCode tag_var) (natCode k1))) S1)
--
--   sbt3_at_var_match_2 :
--     (k1 k2 : Nat) (S1 S2 : Term) -> Eq (natEq k1 k2) false ->
--     Deriv (eqF (ap2 sbt3 (ap2 pi (ap2 pi (natCode k1) S1)
--                                  (ap2 pi (natCode k2) S2))
--                           (ap2 pi (natCode tag_var) (natCode k2))) S2)
--
--   sbt3_at_var_nomatch :
--     (k1 k2 m : Nat) (S1 S2 : Term) ->
--     Eq (natEq k1 m) false -> Eq (natEq k2 m) false ->
--     Deriv (eqF (ap2 sbt3 (ap2 pi (ap2 pi (natCode k1) S1)
--                                  (ap2 pi (natCode k2) S2))
--                           (ap2 pi (natCode tag_var) (natCode m)))
--                 (ap2 pi (natCode tag_var) (natCode m)))
--
--   sbt3_at_ap1 / sbt3_at_ap2 :  recurse with same spec2 .
--
-- These follow the patterns of BRA4.SbtAtVar / BRA4.SbtAtAp .
