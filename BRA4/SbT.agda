{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbT -- the substitution functor  sbt : Fun2  on coded Terms.
--
-- ======================================================================
-- DESIGN.
-- ======================================================================
--
-- Built atop  BRA4.CoVSpec.cov_spec : Fun1 -> Fun2 -> Fun2 , the
-- spec-carrying course-of-values recursion.  At fuel = K (a meta-Nat),
-- the recursion produces:
--
--   state_K = ap2 pi (natCode K) (ap2 pi spec table_K)
--
-- with  table_K = [val_K, val_{K-1}, ..., val_0] .
--
-- The user-facing  sbt : Fun2  is then:
--
--   sbt = Post readOff_spec (cov_spec baseValue_sbt stepFun_sbt)
--
-- where  readOff_spec  extracts the newest table value  val_K  and
--  stepFun_sbt  is the step function that computes  val_{K+1}  by
-- decoding  s(natCode K)  via Cantor-Fst/Snd , dispatching on tag, and
-- (for ap1/ap2) looking up sub-position values from the prior table.
--
-- ======================================================================
-- WHAT THIS FILE SHIPS THIS SESSION (S1).
-- ======================================================================
--
-- 1. The real  stepFun_sbt : Fun2  -- full tag dispatch (var / ap1 / ap2
--    / else) with real bodies including table-lookup machinery.
--
-- 2.  sbt : Fun2  built atop  cov_spec  with the full machinery.
--
-- 3.  sbt_at_O :  ap2 sbt spec O =Deriv= O .
--
-- The closure equations  sbt_at_var_match / sbt_at_var_nomatch /
--  sbt_at_ap1 / sbt_at_ap2  require fuel > 0 unfoldings of  cov_spec
-- and corresponding stability/lookup lemmas.  Those live in subsequent
-- sessions (S2-S5) per the multi-session plan in
--  BRA4/NEXT-SESSION-S2.md  and friends.

module BRA4.SbT where

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
-- baseValue_sbt : the value at fuel 0 (= the empty/leaf input  O ).
--
-- For substitution,  substT k t O = O  always.  So  val_0 = O ,
-- realised by  baseValue_sbt = o .

baseValue_sbt : Fun1
baseValue_sbt = o

baseValue_sbt_eq :
  (spec : Term) ->
  Deriv (eqF (ap1 baseValue_sbt spec) O)
baseValue_sbt_eq spec = ax_o spec

------------------------------------------------------------------------
-- stepFun_sbt : Fun2  -- the step function.
--
-- Receives  (K_term, inner)  where  K_term = natCode K_prev  and
--  inner = pi spec table_{K_prev} .
--
-- Computes  val_{K_prev+1}  by decoding  s(K_term)  via Cantor-Fst/Snd:
--
--   tag = Fst (s K_term)
--   body = Snd (s K_term)
--
--   if tag = tag_var :  body = natCode m .
--      if m = Fst spec :  val = Snd spec   (var-match: plant the substituent)
--      else :              val = s K_term  (var-nomatch: input as-is)
--
--   if tag = tag_ap1 :  body = pi (codeFun1 f) ct .
--      val = pi (natCode tag_ap1) (pi (Fst body) (lookup_at_table ct))
--      where lookup_at_table c = Fst (iter Snd table (K_prev - c)) .
--
--   if tag = tag_ap2 :  body = pi (codeFun2 g) (pi ca cb) .
--      val = pi (natCode tag_ap2) (pi (Fst body)
--               (pi (lookup_at_table ca) (lookup_at_table cb)))
--
--   else :  val = O  (validating-decoder fallback per
--           [[feedback-thmt-validating-decoder-invariant]]).
--
-- Implementation: a Fun1  stepBody_sbt : Fun1  that takes the packaged
--  pi K_term inner  and returns  val .  Wrap as  Post stepBody_sbt pi .

-- Helpers as Fun1's of the packaged input  pi K_term inner .  These
-- are exposed (not private) because BRA4/SbtAtVar.agda + BRA4/SbtAtAp.agda
-- need to refer to them to prove the SbContract closure equations.

get_K : Fun1
get_K = Fst

get_inner : Fun1
get_inner = Snd

get_spec : Fun1
get_spec = compose1U Fst get_inner          -- Fst inner = spec

get_table : Fun1
get_table = compose1U Snd get_inner          -- Snd inner = table

get_specFst : Fun1
get_specFst = compose1U Fst get_spec         -- Fst spec = k (var index)

get_specSnd : Fun1
get_specSnd = compose1U Snd get_spec         -- Snd spec = S (substituent)

get_newK : Fun1
get_newK = compose1U s get_K                  -- s K_term = newK

get_tag : Fun1
get_tag = compose1U Fst get_newK             -- Fst newK = tag

get_body : Fun1
get_body = compose1U Snd get_newK            -- Snd newK = body

-- Dispatch witnesses (Fun1, value sO when matching).

isVar : Fun1
isVar = C natEqF get_tag (constN tag_var)

isAp1 : Fun1
isAp1 = C natEqF get_tag (constN tag_ap1)

isAp2 : Fun1
isAp2 = C natEqF get_tag (constN tag_ap2)

-- Var branch: body should be natCode m; compare with specFst (= k).
-- If equal -> Snd spec (= S).  Else -> newK (the input as-is).

isVarMatch : Fun1
isVarMatch = C natEqF get_body get_specFst

var_branch : Fun1
var_branch = C condFork (C pi get_specSnd get_newK) isVarMatch
-- condFork (Pair true_val false_val) witness:
--   = Fst (Pair true false) = true_val      if witness = sO (match)
--   = Snd (Pair true false) = false_val     if witness = O  (nomatch)
-- true_val = get_specSnd = Snd spec = S
-- false_val = get_newK   = s K_term = the input encoding

-- Lookup helper: given an "index Fun1" idx_F1 producing  c : Term ,
-- compute the table value at position (K_prev - c) :
--   Fst (iter Snd table (K_prev - c)) .

lookupAt : Fun1 -> Fun1
lookupAt idx_F1 =
  compose1U Fst
    (C (iter Snd)
      get_table
      (C sub get_K idx_F1))

-- Ap1 branch: body = pi (codeFun1 f) ct.
--   get_bodyFst_ap1 = codeFun1 f.
--   get_ct_ap1      = ct.
--   val_ct = lookupAt get_ct_ap1.
--   result = pi (natCode tag_ap1) (pi (codeFun1 f) val_ct).

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

-- Ap2 branch: body = pi (codeFun2 g) (pi ca cb).
--   get_bodyFst_ap2 = codeFun2 g.
--   get_ab          = pi ca cb.
--   get_ca, get_cb  = Fst / Snd of ab.
--   val_a, val_b    = lookups.
--   result = pi (natCode tag_ap2) (pi (codeFun2 g) (pi val_a val_b)).

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

-- Else branch: validating-decoder fallback.

else_branch : Fun1
else_branch = o

-- Cascade: condFork  isVar (var, condFork isAp1 (ap1, condFork isAp2 (ap2, else))) .

ap2_or_else : Fun1
ap2_or_else = C condFork (C pi ap2_branch else_branch) isAp2

ap1_or_above : Fun1
ap1_or_above = C condFork (C pi ap1_branch ap2_or_else) isAp1

stepBody_sbt : Fun1
stepBody_sbt = C condFork (C pi var_branch ap1_or_above) isVar

stepFun_sbt : Fun2
stepFun_sbt = Post stepBody_sbt pi

------------------------------------------------------------------------
-- The full sbt via cov_spec.
--
--   sbt spec t  =  readOff_spec (cov_spec baseValue_sbt stepFun_sbt spec t)
--
-- which at  t = O  reduces to  baseValue_sbt spec = O .

sbtState : Fun2
sbtState = cov_spec baseValue_sbt stepFun_sbt

sbt : Fun2
sbt = Post readOff_spec sbtState

sbt_unfold :
  (spec t : Term) ->
  Deriv (eqF (ap2 sbt spec t) (ap1 readOff_spec (ap2 sbtState spec t)))
sbt_unfold spec t = axPost readOff_spec sbtState spec t

------------------------------------------------------------------------
-- sbt_at_O :  ap2 sbt spec O =Deriv= O .
--
-- Chain:
--   sbt spec O = readOff_spec (sbtState spec O)            [sbt_unfold]
--   sbtState spec O = pi O (pi spec (pi O O))              [cov_spec_base + baseValue_sbt=o]
--   readOff_spec (pi O (pi spec (pi O O)))
--      = Fst (Snd (Snd (pi O (pi spec (pi O O)))))         [readOff_spec_eq]
--      = Fst (Snd (pi spec (pi O O)))                       [axSnd]
--      = Fst (pi O O)                                        [axSnd]
--      = O                                                    [axFst]

sbt_at_O :
  (spec : Term) ->
  Deriv (eqF (ap2 sbt spec O) O)
sbt_at_O spec =
  let -- Step 1: sbt_unfold.
      step1 :
        Deriv (eqF (ap2 sbt spec O)
                    (ap1 readOff_spec (ap2 sbtState spec O)))
      step1 = sbt_unfold spec O

      -- Step 2: cov_spec_base + baseValue_sbt_eq spec.
      base_raw :
        Deriv (eqF (ap2 sbtState spec O)
                    (ap2 pi O (ap2 pi spec
                              (ap2 pi (ap1 baseValue_sbt spec) O))))
      base_raw = cov_spec_base baseValue_sbt stepFun_sbt spec

      bv_eq :
        Deriv (eqF (ap1 baseValue_sbt spec) O)
      bv_eq = baseValue_sbt_eq spec

      bv_lift :
        Deriv (eqF (ap2 pi (ap1 baseValue_sbt spec) O) (ap2 pi O O))
      bv_lift = congL pi O bv_eq

      bv_outer1 :
        Deriv (eqF (ap2 pi spec (ap2 pi (ap1 baseValue_sbt spec) O))
                    (ap2 pi spec (ap2 pi O O)))
      bv_outer1 = congR pi spec bv_lift

      bv_outer2 :
        Deriv (eqF (ap2 pi O (ap2 pi spec
                          (ap2 pi (ap1 baseValue_sbt spec) O)))
                    (ap2 pi O (ap2 pi spec (ap2 pi O O))))
      bv_outer2 = congR pi O bv_outer1

      base_full :
        Deriv (eqF (ap2 sbtState spec O)
                    (ap2 pi O (ap2 pi spec (ap2 pi O O))))
      base_full = ruleTrans base_raw bv_outer2

      -- Step 3: lift through readOff_spec.
      step3 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbtState spec O))
                    (ap1 readOff_spec (ap2 pi O (ap2 pi spec (ap2 pi O O)))))
      step3 = cong1 readOff_spec base_full

      -- Step 4: unfold readOff_spec.
      readOff_eq :
        Deriv (eqF (ap1 readOff_spec (ap2 pi O (ap2 pi spec (ap2 pi O O))))
                    (ap1 Fst (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O)))))))
      readOff_eq = readOff_spec_eq (ap2 pi O (ap2 pi spec (ap2 pi O O)))

      -- Step 5: Snd (pi O ...) = pi spec (pi O O).
      snd1 :
        Deriv (eqF (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O))))
                    (ap2 pi spec (ap2 pi O O)))
      snd1 = axSnd O (ap2 pi spec (ap2 pi O O))

      snd1_lift :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O)))))
                    (ap1 Snd (ap2 pi spec (ap2 pi O O))))
      snd1_lift = cong1 Snd snd1

      -- Step 6: Snd (pi spec (pi O O)) = pi O O.
      snd2 :
        Deriv (eqF (ap1 Snd (ap2 pi spec (ap2 pi O O))) (ap2 pi O O))
      snd2 = axSnd spec (ap2 pi O O)

      snd2_lift :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi O O)))))
                    (ap2 pi O O))
      snd2_lift = ruleTrans snd1_lift snd2

      -- Step 7: Fst (Snd (Snd ...)) = Fst (pi O O) = O.
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
-- TODO (S2..S5): the remaining four closure equations of  SbContract sbt :
--
--   sbt_at_var_match   :  ap2 sbt (pi (natCode k) S) (pi (natCode tag_var) (natCode k)) = S
--   sbt_at_var_nomatch :  Eq (natEq k m) false ->
--                          ap2 sbt (pi (natCode k) S) (pi (natCode tag_var) (natCode m))
--                          = pi (natCode tag_var) (natCode m)
--   sbt_at_ap1         :  ap2 sbt spec (pi (natCode tag_ap1) (pi (codeFun1 f) ct))
--                          = pi (natCode tag_ap1) (pi (codeFun1 f) (ap2 sbt spec ct))
--   sbt_at_ap2         :  ap2 sbt spec (pi (natCode tag_ap2) (pi (codeFun2 g) (pi ca cb)))
--                          = pi (natCode tag_ap2) (pi (codeFun2 g)
--                               (pi (ap2 sbt spec ca) (ap2 sbt spec cb)))
--
-- These all require running  cov_spec  at non-zero fuel and using the
-- stability/lookup machinery to be built in BRA4/StabilityNatFuel.agda (S2)
-- and BRA4/SbtAtPair.agda (S3).  See BRA4/NEXT-SESSION-S2.md.
