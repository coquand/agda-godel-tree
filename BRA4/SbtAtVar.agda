{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbtAtVar -- discharge of the SbContract sbt closures at the two
-- var-shape inputs:
--
--   sbt_at_var_match :
--     ap2 sbt (ap2 Pair (natCode k) S)
--             (ap2 Pair (natCode tag_var) (natCode k))     =  S
--
--   sbt_at_var_nomatch :
--     Eq (natEq k m) false ->
--     ap2 sbt (ap2 Pair (natCode k) S)
--             (ap2 Pair (natCode tag_var) (natCode m))     =  Pair (natCode tag_var) (natCode m)
--
-- Both proofs follow the same skeleton:
--
--   1.  sbt_unfold      :  sbt spec t = readOff_spec (sbtState spec t)
--   2.  readOff_at_pi_natCode  :  reduce sbtState ... (pi (natCode 1) (natCode m))
--                                  to  stateMeta (cantor 1 m) .
--   3.  cantor_var_succ_decomp :  cantor 1 m = suc (cantorVarPred m)  (meta-Nat).
--   4.  readOff_stateMeta_succ_via_natCode :  ... = stepFun_sbt (natCode K_pred) (Snd ...).
--   5.  Unfold  stepFun_sbt = Post stepBody_sbt pi  and dispatch through
--       isVar (tag = tag_var via tagOf_cantor)  +  isVarMatch (body = natCode k
--       compared with Fst spec = natCode k).  Both natEqF tests resolve via
--       natEq_eq (match) or natEq_neq (nomatch).
--   6.  Take Fst-of-pair (match) or Snd-of-pair (nomatch) of the var_branch
--       to obtain  S  (match) or  s (natCode K_pred) = natCode (cantor 1 m)  (nomatch),
--       the latter bridged back to  pi (natCode tag_var) (natCode m) via pi_natCode.

module BRA4.SbtAtVar where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.SbT
open import BRA4.StabilityNatFuel

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( Closed ; closed_O ; closed_natCode ; closed_ap1 ; closed_ap2
  ; condFork ; condFork_true_nc ; condFork_false
  ; constN ; constN_eq
  ; tagOf_cantor ; bodyOf_cantor )
open import BRA3.Numerals        using ( pi_natCode )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq ; natEq_neq_gt )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; gtW ; ltW ; natEqF_at_neq ; decideNatNeq ; Not )
open import BRA3.RuleInst2       using
  ( natEq-refl ; true_neq_false )
open import BRA3.Code.Tag        using
  ( cantor ; cantor_compute ; tauN ; addN )

------------------------------------------------------------------------
-- Meta-Nat decomposition:  cantor 1 m  =  suc (cantorVarPred m) .
--
-- Direct from  cantor_compute 1 m  (Agda definitionally reduces
-- addN 1 m -> suc m  and  tauN (suc m) -> suc (addN m (tauN m))  and
-- addN (suc X) m -> suc (addN X m)).

cantorVarPred : Nat -> Nat
cantorVarPred m = addN (addN m (tauN m)) m

cantor_var_succ_decomp :
  (m : Nat) -> Eq (cantor (suc zero) m) (suc (cantorVarPred m))
cantor_var_succ_decomp m = cantor_compute (suc zero) m

------------------------------------------------------------------------
-- Section A.  Stepwise unfolding of the dispatch helpers at a packaged
-- input  pi A Y  (where A is intended to be  natCode K_pred  and Y is
-- intended to be  Snd state ).
--
-- Each helper has a Fun1 = compose1U ... shape; we give its closed-form
-- on the packaged input via compose1U_eq + axFst/axSnd.

private
  -- Conveniences.

  base : Fun1
  base = baseValue_sbt

  step : Fun2
  step = stepFun_sbt

  -- ap1 get_K (pi A Y) = A.
  get_K_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_K (ap2 pi A Y)) A)
  get_K_at_pi A Y = axFst A Y

  -- ap1 get_inner (pi A Y) = Y.
  get_inner_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_inner (ap2 pi A Y)) Y)
  get_inner_at_pi A Y = axSnd A Y

  -- ap1 get_newK (pi A Y) = ap1 s A.
  get_newK_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_newK (ap2 pi A Y)) (ap1 s A))
  get_newK_at_pi A Y =
    let -- get_newK = compose1U s get_K.
        step1 :
          Deriv (eqF (ap1 get_newK (ap2 pi A Y))
                      (ap1 s (ap1 get_K (ap2 pi A Y))))
        step1 = compose1U_eq s get_K (ap2 pi A Y)
    in ruleTrans step1 (cong1 s (get_K_at_pi A Y))

  -- ap1 get_tag (pi A Y) = ap1 Fst (ap1 s A).
  get_tag_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_tag (ap2 pi A Y)) (ap1 Fst (ap1 s A)))
  get_tag_at_pi A Y =
    let step1 :
          Deriv (eqF (ap1 get_tag (ap2 pi A Y))
                      (ap1 Fst (ap1 get_newK (ap2 pi A Y))))
        step1 = compose1U_eq Fst get_newK (ap2 pi A Y)
    in ruleTrans step1 (cong1 Fst (get_newK_at_pi A Y))

  -- ap1 get_body (pi A Y) = ap1 Snd (ap1 s A).
  get_body_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_body (ap2 pi A Y)) (ap1 Snd (ap1 s A)))
  get_body_at_pi A Y =
    let step1 :
          Deriv (eqF (ap1 get_body (ap2 pi A Y))
                      (ap1 Snd (ap1 get_newK (ap2 pi A Y))))
        step1 = compose1U_eq Snd get_newK (ap2 pi A Y)
    in ruleTrans step1 (cong1 Snd (get_newK_at_pi A Y))

  -- ap1 get_spec (pi A Y) = ap1 Fst Y.
  get_spec_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_spec (ap2 pi A Y)) (ap1 Fst Y))
  get_spec_at_pi A Y =
    let step1 :
          Deriv (eqF (ap1 get_spec (ap2 pi A Y))
                      (ap1 Fst (ap1 get_inner (ap2 pi A Y))))
        step1 = compose1U_eq Fst get_inner (ap2 pi A Y)
    in ruleTrans step1 (cong1 Fst (get_inner_at_pi A Y))

  -- ap1 get_specFst (pi A Y) = ap1 Fst (ap1 Fst Y).
  get_specFst_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_specFst (ap2 pi A Y)) (ap1 Fst (ap1 Fst Y)))
  get_specFst_at_pi A Y =
    let step1 :
          Deriv (eqF (ap1 get_specFst (ap2 pi A Y))
                      (ap1 Fst (ap1 get_spec (ap2 pi A Y))))
        step1 = compose1U_eq Fst get_spec (ap2 pi A Y)
    in ruleTrans step1 (cong1 Fst (get_spec_at_pi A Y))

  -- ap1 get_specSnd (pi A Y) = ap1 Snd (ap1 Fst Y).
  get_specSnd_at_pi :
    (A Y : Term) ->
    Deriv (eqF (ap1 get_specSnd (ap2 pi A Y)) (ap1 Snd (ap1 Fst Y)))
  get_specSnd_at_pi A Y =
    let step1 :
          Deriv (eqF (ap1 get_specSnd (ap2 pi A Y))
                      (ap1 Snd (ap1 get_spec (ap2 pi A Y))))
        step1 = compose1U_eq Snd get_spec (ap2 pi A Y)
    in ruleTrans step1 (cong1 Snd (get_spec_at_pi A Y))

------------------------------------------------------------------------
-- Section B.  Tag-dispatch at the packaged input  pi (natCode K_pred) Y
-- when  s (natCode K_pred) = natCode K  for  K = cantor 1 m  (the var case).
--
-- Under  Fst (Fst Y) = natCode k  hypothesis (i.e.,  Fst Y  has the
-- spec shape  pi (natCode k) S ), and using  tagOf_cantor 1 m ,
-- isVar input fires as  sO  and  isVarMatch input fires as  sO  iff
--  m = k .  natEq_eq / natEq_neq_gt complete the test.

-- The full sbt_at_var_match closure is the cleanest path; we inline the
-- entire chain.  Where  fstSnd_stateMeta  +  axFst  give us  Fst (Fst Y)
-- = natCode k  for  Y = Snd (stateMeta K_pred) .

private
  -- Convenience: the "spec" expression.
  specT : (k : Nat) (S : Term) -> Term
  specT k S = ap2 pi (natCode k) S

  -- ap1 stepBody_sbt input = condFork (C pi var_branch ap1_or_above input) (isVar input).
  stepBody_sbt_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 stepBody_sbt input)
                (ap2 condFork
                  (ap1 (C pi var_branch ap1_or_above) input)
                  (ap1 isVar input)))
  stepBody_sbt_unfold input =
    ax_C condFork (C pi var_branch ap1_or_above) isVar input

  -- ap1 (C pi var_branch ap1_or_above) input = pi (var_branch input) (ap1_or_above input).
  pi_var_ap1_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
  pi_var_ap1_unfold input = ax_C pi var_branch ap1_or_above input

  -- ap1 var_branch input = condFork (C pi get_specSnd get_newK input) (isVarMatch input).
  var_branch_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 var_branch input)
                (ap2 condFork
                  (ap1 (C pi get_specSnd get_newK) input)
                  (ap1 isVarMatch input)))
  var_branch_unfold input =
    ax_C condFork (C pi get_specSnd get_newK) isVarMatch input

  -- ap1 (C pi get_specSnd get_newK) input = pi (get_specSnd input) (get_newK input).
  pi_specSnd_newK_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 (C pi get_specSnd get_newK) input)
                (ap2 pi (ap1 get_specSnd input) (ap1 get_newK input)))
  pi_specSnd_newK_unfold input = ax_C pi get_specSnd get_newK input

  -- ap1 isVar input = ap2 natEqF (get_tag input) (natCode tag_var).
  isVar_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isVar input)
                (ap2 natEqF (ap1 get_tag input) (natCode tag_var)))
  isVar_unfold input =
    let s1 :
          Deriv (eqF (ap1 isVar input)
                      (ap2 natEqF (ap1 get_tag input) (ap1 (constN tag_var) input)))
        s1 = ax_C natEqF get_tag (constN tag_var) input

        s2 :
          Deriv (eqF (ap1 (constN tag_var) input) (natCode tag_var))
        s2 = constN_eq tag_var input
    in ruleTrans s1 (congR natEqF (ap1 get_tag input) s2)

  -- ap1 isVarMatch input = ap2 natEqF (get_body input) (get_specFst input).
  isVarMatch_unfold :
    (input : Term) ->
    Deriv (eqF (ap1 isVarMatch input)
                (ap2 natEqF (ap1 get_body input) (ap1 get_specFst input)))
  isVarMatch_unfold input =
    ax_C natEqF get_body get_specFst input

------------------------------------------------------------------------
-- The main closure equations.

private
  -- input at the dispatch level, after readOff_stateMeta_succ_via_natCode.
  -- Specifically: input = pi (natCode K_pred) (Snd (stateMeta base step spec K_pred))
  -- where  spec = specT k S  and  K_pred = cantorVarPred m .

  -- For sbt_at_var_match, m = k.

  -- Step (i): bridge  natCode (suc K_pred) = ap1 s (natCode K_pred)  is definitional.

  -- Step (ii): bridge  natCode (suc K_pred) = natCode (cantor 1 m)  via cantor_var_succ_decomp.

  natCode_succ_eq_cantor :
    (m : Nat) ->
    Eq (suc (cantorVarPred m)) (cantor (suc zero) m)
  natCode_succ_eq_cantor m = eqSym (cantor_var_succ_decomp m)

  natCode_bridge :
    (m : Nat) ->
    Deriv (eqF (ap1 s (natCode (cantorVarPred m)))
                (natCode (cantor (suc zero) m)))
  natCode_bridge m =
    eqSubst (\ z -> Deriv (eqF (ap1 s (natCode (cantorVarPred m)))
                                 (natCode z)))
             (natCode_succ_eq_cantor m)
             (axRefl (ap1 s (natCode (cantorVarPred m))))

  -- Combined:  ap1 Fst (ap1 s (natCode K_pred)) = natCode tag_var
  -- when  K_pred = cantorVarPred m .

  Fst_s_natCode_at_var :
    (m : Nat) ->
    Deriv (eqF (ap1 Fst (ap1 s (natCode (cantorVarPred m))))
                (natCode tag_var))
  Fst_s_natCode_at_var m =
    let bridge :
          Deriv (eqF (ap1 Fst (ap1 s (natCode (cantorVarPred m))))
                      (ap1 Fst (natCode (cantor (suc zero) m))))
        bridge = cong1 Fst (natCode_bridge m)

        tagEq :
          Deriv (eqF (ap1 Fst (natCode (cantor (suc zero) m)))
                      (natCode (suc zero)))
        tagEq = tagOf_cantor (suc zero) m
    in ruleTrans bridge tagEq

  -- Similarly:  ap1 Snd (ap1 s (natCode K_pred)) = natCode m .

  Snd_s_natCode_at_var :
    (m : Nat) ->
    Deriv (eqF (ap1 Snd (ap1 s (natCode (cantorVarPred m))))
                (natCode m))
  Snd_s_natCode_at_var m =
    let bridge :
          Deriv (eqF (ap1 Snd (ap1 s (natCode (cantorVarPred m))))
                      (ap1 Snd (natCode (cantor (suc zero) m))))
        bridge = cong1 Snd (natCode_bridge m)

        bodyEq :
          Deriv (eqF (ap1 Snd (natCode (cantor (suc zero) m)))
                      (natCode m))
        bodyEq = bodyOf_cantor (suc zero) m
    in ruleTrans bridge bodyEq

------------------------------------------------------------------------
-- Section C.  The stepFun_sbt firing lemma for sbt_at_var_match.
--
--   stepFun_sbt_at_var_match_core :
--     (k : Nat) (S Y : Term) ->
--     Deriv (eqF (ap1 Fst Y) (ap2 pi (natCode k) S)) ->
--     Deriv (eqF (ap2 stepFun_sbt (natCode (cantorVarPred k)) Y) S)
--
-- We assume:  Fst Y = pi (natCode k) S  (i.e., Y has the "Snd state"
-- shape with spec = pi (natCode k) S at the head).  We never need to know
-- Y's full shape -- only its  Fst .

stepFun_sbt_at_var_match_core :
  (k : Nat) (S Y : Term) ->
  Deriv (eqF (ap1 Fst Y) (ap2 pi (natCode k) S)) ->
  Deriv (eqF (ap2 stepFun_sbt (natCode (cantorVarPred k)) Y) S)
stepFun_sbt_at_var_match_core k S Y fstY_eq =
  let A : Term
      A = natCode (cantorVarPred k)

      input : Term
      input = ap2 pi A Y

      spec : Term
      spec = ap2 pi (natCode k) S

      ----------------------------------------------------------------
      -- Step 1: stepFun_sbt (A, Y) = stepBody_sbt (pi A Y).

      e1 :
        Deriv (eqF (ap2 stepFun_sbt A Y) (ap1 stepBody_sbt input))
      e1 = axPost stepBody_sbt pi A Y

      ----------------------------------------------------------------
      -- Step 2: stepBody_sbt input = condFork (C pi var ap1or input) (isVar input).

      e2 :
        Deriv (eqF (ap1 stepBody_sbt input)
                    (ap2 condFork
                      (ap1 (C pi var_branch ap1_or_above) input)
                      (ap1 isVar input)))
      e2 = stepBody_sbt_unfold input

      ----------------------------------------------------------------
      -- Step 3: isVar input = sO.
      --
      -- isVar input = natEqF (get_tag input) (natCode tag_var).
      -- get_tag input = Fst (s A) = Fst (s (natCode K_pred)) = natCode tag_var.

      e3a :
        Deriv (eqF (ap1 isVar input)
                    (ap2 natEqF (ap1 get_tag input) (natCode tag_var)))
      e3a = isVar_unfold input

      e3b :
        Deriv (eqF (ap1 get_tag input) (ap1 Fst (ap1 s A)))
      e3b = get_tag_at_pi A Y

      e3c :
        Deriv (eqF (ap1 Fst (ap1 s A)) (natCode tag_var))
      e3c = Fst_s_natCode_at_var k

      get_tag_value :
        Deriv (eqF (ap1 get_tag input) (natCode tag_var))
      get_tag_value = ruleTrans e3b e3c

      e3_natEq :
        Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_var))
                    (ap2 natEqF (natCode tag_var) (natCode tag_var)))
      e3_natEq = congL natEqF (natCode tag_var) get_tag_value

      e3_eq :
        Deriv (eqF (ap2 natEqF (natCode tag_var) (natCode tag_var)) (ap1 s O))
      e3_eq = natEq_eq tag_var

      e3_full :
        Deriv (eqF (ap1 isVar input) (ap1 s O))
      e3_full = ruleTrans e3a (ruleTrans e3_natEq e3_eq)

      ----------------------------------------------------------------
      -- Step 4: condFork (...) sO = Fst (...) = (C pi var ap1or) input = pi (var_branch input) (ap1_or_above input).
      -- Then Fst pi(...) = var_branch input.

      isVar_subst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi var_branch ap1_or_above) input)
                     (ap1 isVar input))
                    (ap2 condFork
                     (ap1 (C pi var_branch ap1_or_above) input)
                     (ap1 s O)))
      isVar_subst =
        congR condFork (ap1 (C pi var_branch ap1_or_above) input) e3_full

      condFork_to_Fst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi var_branch ap1_or_above) input) (ap1 s O))
                    (ap1 Fst (ap1 (C pi var_branch ap1_or_above) input)))
      condFork_to_Fst =
        condFork_true_nc (ap1 (C pi var_branch ap1_or_above) input) O

      pi_var_ap1_eq :
        Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                    (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
      pi_var_ap1_eq = pi_var_ap1_unfold input

      Fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
                    (ap1 var_branch input))
      Fst_pi = axFst (ap1 var_branch input) (ap1 ap1_or_above input)

      to_var_branch :
        Deriv (eqF (ap1 stepBody_sbt input) (ap1 var_branch input))
      to_var_branch =
        ruleTrans e2
          (ruleTrans isVar_subst
            (ruleTrans condFork_to_Fst
              (ruleTrans (cong1 Fst pi_var_ap1_eq) Fst_pi)))

      ----------------------------------------------------------------
      -- Step 5: var_branch input.
      --   var_branch = C condFork (C pi get_specSnd get_newK) isVarMatch.
      --   ax_C: var_branch input = condFork (pi (get_specSnd input) (get_newK input)) (isVarMatch input).

      e5a :
        Deriv (eqF (ap1 var_branch input)
                    (ap2 condFork
                      (ap1 (C pi get_specSnd get_newK) input)
                      (ap1 isVarMatch input)))
      e5a = var_branch_unfold input

      ----------------------------------------------------------------
      -- Step 6: isVarMatch input = sO.
      --   isVarMatch input = natEqF (get_body input) (get_specFst input).
      --   get_body input = Snd (s A) = Snd (s (natCode K_pred)) = natCode k.
      --   get_specFst input = Fst (Fst Y).  By  fstY_eq, Fst Y = pi (natCode k) S,
      --     so Fst (Fst Y) = Fst (pi (natCode k) S) = natCode k.

      e6_isVarMatch :
        Deriv (eqF (ap1 isVarMatch input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_specFst input)))
      e6_isVarMatch = isVarMatch_unfold input

      e6_body :
        Deriv (eqF (ap1 get_body input) (ap1 Snd (ap1 s A)))
      e6_body = get_body_at_pi A Y

      e6_body_natCode :
        Deriv (eqF (ap1 Snd (ap1 s A)) (natCode k))
      e6_body_natCode = Snd_s_natCode_at_var k

      e6_body_eq :
        Deriv (eqF (ap1 get_body input) (natCode k))
      e6_body_eq = ruleTrans e6_body e6_body_natCode

      e6_specFst :
        Deriv (eqF (ap1 get_specFst input) (ap1 Fst (ap1 Fst Y)))
      e6_specFst = get_specFst_at_pi A Y

      e6_FstFstY :
        Deriv (eqF (ap1 Fst (ap1 Fst Y))
                    (ap1 Fst (ap2 pi (natCode k) S)))
      e6_FstFstY = cong1 Fst fstY_eq

      e6_Fst_spec :
        Deriv (eqF (ap1 Fst (ap2 pi (natCode k) S)) (natCode k))
      e6_Fst_spec = axFst (natCode k) S

      e6_specFst_eq :
        Deriv (eqF (ap1 get_specFst input) (natCode k))
      e6_specFst_eq =
        ruleTrans e6_specFst (ruleTrans e6_FstFstY e6_Fst_spec)

      e6_natEq_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_specFst input))
                    (ap2 natEqF (natCode k) (natCode k)))
      e6_natEq_args =
        ruleTrans (congL natEqF (ap1 get_specFst input) e6_body_eq)
                   (congR natEqF (natCode k) e6_specFst_eq)

      e6_natEq_eq :
        Deriv (eqF (ap2 natEqF (natCode k) (natCode k)) (ap1 s O))
      e6_natEq_eq = natEq_eq k

      e6_full :
        Deriv (eqF (ap1 isVarMatch input) (ap1 s O))
      e6_full = ruleTrans e6_isVarMatch (ruleTrans e6_natEq_args e6_natEq_eq)

      ----------------------------------------------------------------
      -- Step 7: condFork (pi (get_specSnd input) (get_newK input)) sO
      --       = Fst (pi (get_specSnd input) (get_newK input))
      --       = get_specSnd input.

      e7_isVarMatch_subst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi get_specSnd get_newK) input)
                     (ap1 isVarMatch input))
                    (ap2 condFork
                     (ap1 (C pi get_specSnd get_newK) input)
                     (ap1 s O)))
      e7_isVarMatch_subst =
        congR condFork (ap1 (C pi get_specSnd get_newK) input) e6_full

      e7_condFork_to_Fst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi get_specSnd get_newK) input) (ap1 s O))
                    (ap1 Fst (ap1 (C pi get_specSnd get_newK) input)))
      e7_condFork_to_Fst =
        condFork_true_nc (ap1 (C pi get_specSnd get_newK) input) O

      e7_pi_eq :
        Deriv (eqF (ap1 (C pi get_specSnd get_newK) input)
                    (ap2 pi (ap1 get_specSnd input) (ap1 get_newK input)))
      e7_pi_eq = pi_specSnd_newK_unfold input

      e7_Fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap1 get_specSnd input) (ap1 get_newK input)))
                    (ap1 get_specSnd input))
      e7_Fst_pi = axFst (ap1 get_specSnd input) (ap1 get_newK input)

      e7_full :
        Deriv (eqF (ap1 var_branch input) (ap1 get_specSnd input))
      e7_full =
        ruleTrans e5a
          (ruleTrans e7_isVarMatch_subst
            (ruleTrans e7_condFork_to_Fst
              (ruleTrans (cong1 Fst e7_pi_eq) e7_Fst_pi)))

      ----------------------------------------------------------------
      -- Step 8: get_specSnd input = Snd (Fst Y) = Snd (pi (natCode k) S) = S.

      e8_specSnd :
        Deriv (eqF (ap1 get_specSnd input) (ap1 Snd (ap1 Fst Y)))
      e8_specSnd = get_specSnd_at_pi A Y

      e8_SndFstY :
        Deriv (eqF (ap1 Snd (ap1 Fst Y)) (ap1 Snd (ap2 pi (natCode k) S)))
      e8_SndFstY = cong1 Snd fstY_eq

      e8_Snd_spec :
        Deriv (eqF (ap1 Snd (ap2 pi (natCode k) S)) S)
      e8_Snd_spec = axSnd (natCode k) S

      e8_full :
        Deriv (eqF (ap1 get_specSnd input) S)
      e8_full = ruleTrans e8_specSnd (ruleTrans e8_SndFstY e8_Snd_spec)

  in ruleTrans e1
       (ruleTrans to_var_branch
         (ruleTrans e7_full e8_full))

------------------------------------------------------------------------
-- Section D.  The sbt_at_var_match closure equation of SbContract.
--
--   sbt_at_var_match :
--     (k : Nat) (S : Term) ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
--                  (ap2 Pair (natCode tag_var) (natCode k))) S)
--
-- (Pair = pi internally.)

sbt_at_var_match :
  (k : Nat) (S : Term) ->
  Deriv (eqF (ap2 sbt (ap2 pi (natCode k) S)
                       (ap2 pi (natCode tag_var) (natCode k))) S)
sbt_at_var_match k S =
  let spec : Term
      spec = ap2 pi (natCode k) S

      t : Term
      t = ap2 pi (natCode tag_var) (natCode k)

      base : Fun1
      base = baseValue_sbt

      step : Fun2
      step = stepFun_sbt

      K_pred : Nat
      K_pred = cantorVarPred k

      stateK : Term
      stateK = stateMeta base step spec K_pred

      Y : Term
      Y = ap1 Snd stateK

      ----------------------------------------------------------------
      -- Step 1: sbt_unfold.
      step1 :
        Deriv (eqF (ap2 sbt spec t) (ap1 readOff_spec (ap2 sbtState spec t)))
      step1 = sbt_unfold spec t

      ----------------------------------------------------------------
      -- Step 2: readOff_at_pi_natCode reduces sbtState ... t to stateMeta (cantor 1 k).
      step2 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbtState spec t))
                    (ap1 readOff_spec
                          (stateMeta base step spec
                            (cantor tag_var k))))
      step2 = readOff_at_pi_natCode base step spec tag_var k

      ----------------------------------------------------------------
      -- Step 3: rewrite cantor 1 k = suc K_pred (meta-Nat) via eqSubst on natCode_succ_eq_cantor.
      cantor_eq_succ : Eq (cantor (suc zero) k) (suc K_pred)
      cantor_eq_succ = cantor_var_succ_decomp k

      -- tag_var = suc zero, so cantor tag_var k = cantor (suc zero) k.

      step3 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k)))
                    (ap1 readOff_spec (stateMeta base step spec (suc K_pred))))
      step3 =
        eqSubst (\ z -> Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k)))
                                      (ap1 readOff_spec (stateMeta base step spec z))))
                 cantor_eq_succ
                 (axRefl (ap1 readOff_spec (stateMeta base step spec (cantor tag_var k))))

      ----------------------------------------------------------------
      -- Step 4: readOff_stateMeta_succ_via_natCode at K_pred.
      step4 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (suc K_pred)))
                    (ap2 step (natCode K_pred) Y))
      step4 = readOff_stateMeta_succ_via_natCode base step spec K_pred

      ----------------------------------------------------------------
      -- Step 5: Fst Y = spec.  Direct via fstSnd_stateMeta.
      fstY_eq : Deriv (eqF (ap1 Fst Y) spec)
      fstY_eq = fstSnd_stateMeta base step spec K_pred

      ----------------------------------------------------------------
      -- Step 6: apply the core firing lemma.
      step6 :
        Deriv (eqF (ap2 step (natCode K_pred) Y) S)
      step6 = stepFun_sbt_at_var_match_core k S Y fstY_eq

  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3
           (ruleTrans step4 step6)))

------------------------------------------------------------------------
-- Section E.  The nomatch case.
--
--   sbt_at_var_nomatch :
--     (k m : Nat) (S : Term) -> Eq (natEq k m) false ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
--                  (ap2 Pair (natCode tag_var) (natCode m)))
--                 (ap2 Pair (natCode tag_var) (natCode m)))
--
-- Same skeleton as sbt_at_var_match, but isVarMatch fires as O instead
-- of sO, so condFork picks the Snd branch (= get_newK input = ap1 s A
-- = natCode (cantor 1 m) = pi (natCode tag_var) (natCode m)).

------------------------------------------------------------------------
-- E.1  Bridge from  Eq (natEq k m) false  to  NatNeqWitness m k .

private
  natEqFalse_to_NotEq :
    (k m : Nat) -> Eq (natEq k m) false -> Not (Eq k m)
  natEqFalse_to_NotEq k m hyp eqKM =
    let trueEq : Eq (natEq k m) true
        trueEq = eqSubst (\ z -> Eq (natEq k z) true) eqKM (natEq-refl k)

        contradict : Eq true false
        contradict = eqTrans (eqSym trueEq) hyp
    in true_neq_false contradict

  natEqFalse_to_witness_flipped :
    (k m : Nat) -> Eq (natEq k m) false -> NatNeqWitness m k
  natEqFalse_to_witness_flipped k m hyp =
    let notEqKM : Not (Eq k m)
        notEqKM = natEqFalse_to_NotEq k m hyp

        notEqMK : Not (Eq m k)
        notEqMK eqMK = notEqKM (eqSym eqMK)
    in decideNatNeq m k notEqMK

------------------------------------------------------------------------
-- E.2  The core firing lemma for nomatch.
--
--   stepFun_sbt_at_var_nomatch_core :
--     (k m : Nat) (S Y : Term) ->
--     NatNeqWitness m k ->
--     Deriv (eqF (ap1 Fst Y) (ap2 pi (natCode k) S)) ->
--     Deriv (eqF (ap2 stepFun_sbt (natCode (cantorVarPred m)) Y)
--                 (ap1 s (natCode (cantorVarPred m))))
--
-- Note the result is  ap1 s (natCode K_pred)  -- bridged at the call site
-- to  natCode (cantor 1 m) = pi (natCode tag_var) (natCode m)  via pi_natCode.

stepFun_sbt_at_var_nomatch_core :
  (k m : Nat) (S Y : Term) ->
  NatNeqWitness m k ->
  Deriv (eqF (ap1 Fst Y) (ap2 pi (natCode k) S)) ->
  Deriv (eqF (ap2 stepFun_sbt (natCode (cantorVarPred m)) Y)
              (ap1 s (natCode (cantorVarPred m))))
stepFun_sbt_at_var_nomatch_core k m S Y witness fstY_eq =
  let A : Term
      A = natCode (cantorVarPred m)

      input : Term
      input = ap2 pi A Y

      ----------------------------------------------------------------
      -- Step 1: stepFun_sbt (A, Y) = stepBody_sbt (pi A Y).
      e1 : Deriv (eqF (ap2 stepFun_sbt A Y) (ap1 stepBody_sbt input))
      e1 = axPost stepBody_sbt pi A Y

      ----------------------------------------------------------------
      -- Step 2: stepBody_sbt unfold.
      e2 :
        Deriv (eqF (ap1 stepBody_sbt input)
                    (ap2 condFork
                      (ap1 (C pi var_branch ap1_or_above) input)
                      (ap1 isVar input)))
      e2 = stepBody_sbt_unfold input

      ----------------------------------------------------------------
      -- Step 3: isVar input = sO  (same as match case, but at index m).
      e3a :
        Deriv (eqF (ap1 isVar input)
                    (ap2 natEqF (ap1 get_tag input) (natCode tag_var)))
      e3a = isVar_unfold input

      e3b :
        Deriv (eqF (ap1 get_tag input) (ap1 Fst (ap1 s A)))
      e3b = get_tag_at_pi A Y

      e3c :
        Deriv (eqF (ap1 Fst (ap1 s A)) (natCode tag_var))
      e3c = Fst_s_natCode_at_var m

      get_tag_value :
        Deriv (eqF (ap1 get_tag input) (natCode tag_var))
      get_tag_value = ruleTrans e3b e3c

      e3_natEq :
        Deriv (eqF (ap2 natEqF (ap1 get_tag input) (natCode tag_var))
                    (ap2 natEqF (natCode tag_var) (natCode tag_var)))
      e3_natEq = congL natEqF (natCode tag_var) get_tag_value

      e3_eq :
        Deriv (eqF (ap2 natEqF (natCode tag_var) (natCode tag_var)) (ap1 s O))
      e3_eq = natEq_eq tag_var

      e3_full :
        Deriv (eqF (ap1 isVar input) (ap1 s O))
      e3_full = ruleTrans e3a (ruleTrans e3_natEq e3_eq)

      ----------------------------------------------------------------
      -- Step 4: condFork dispatches into var_branch input.
      isVar_subst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi var_branch ap1_or_above) input)
                     (ap1 isVar input))
                    (ap2 condFork
                     (ap1 (C pi var_branch ap1_or_above) input)
                     (ap1 s O)))
      isVar_subst =
        congR condFork (ap1 (C pi var_branch ap1_or_above) input) e3_full

      condFork_to_Fst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi var_branch ap1_or_above) input) (ap1 s O))
                    (ap1 Fst (ap1 (C pi var_branch ap1_or_above) input)))
      condFork_to_Fst =
        condFork_true_nc (ap1 (C pi var_branch ap1_or_above) input) O

      pi_var_ap1_eq :
        Deriv (eqF (ap1 (C pi var_branch ap1_or_above) input)
                    (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
      pi_var_ap1_eq = pi_var_ap1_unfold input

      Fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap1 var_branch input) (ap1 ap1_or_above input)))
                    (ap1 var_branch input))
      Fst_pi = axFst (ap1 var_branch input) (ap1 ap1_or_above input)

      to_var_branch :
        Deriv (eqF (ap1 stepBody_sbt input) (ap1 var_branch input))
      to_var_branch =
        ruleTrans e2
          (ruleTrans isVar_subst
            (ruleTrans condFork_to_Fst
              (ruleTrans (cong1 Fst pi_var_ap1_eq) Fst_pi)))

      ----------------------------------------------------------------
      -- Step 5: var_branch unfold.
      e5a :
        Deriv (eqF (ap1 var_branch input)
                    (ap2 condFork
                      (ap1 (C pi get_specSnd get_newK) input)
                      (ap1 isVarMatch input)))
      e5a = var_branch_unfold input

      ----------------------------------------------------------------
      -- Step 6: isVarMatch input = O.
      --   isVarMatch = natEqF get_body get_specFst.
      --   get_body input = natCode m, get_specFst input = natCode k.
      --   natEqF (natCode m) (natCode k) = O by natEqF_at_neq (m, k, witness).
      e6_isVarMatch :
        Deriv (eqF (ap1 isVarMatch input)
                    (ap2 natEqF (ap1 get_body input) (ap1 get_specFst input)))
      e6_isVarMatch = isVarMatch_unfold input

      e6_body :
        Deriv (eqF (ap1 get_body input) (ap1 Snd (ap1 s A)))
      e6_body = get_body_at_pi A Y

      e6_body_natCode :
        Deriv (eqF (ap1 Snd (ap1 s A)) (natCode m))
      e6_body_natCode = Snd_s_natCode_at_var m

      e6_body_eq :
        Deriv (eqF (ap1 get_body input) (natCode m))
      e6_body_eq = ruleTrans e6_body e6_body_natCode

      e6_specFst :
        Deriv (eqF (ap1 get_specFst input) (ap1 Fst (ap1 Fst Y)))
      e6_specFst = get_specFst_at_pi A Y

      e6_FstFstY :
        Deriv (eqF (ap1 Fst (ap1 Fst Y))
                    (ap1 Fst (ap2 pi (natCode k) S)))
      e6_FstFstY = cong1 Fst fstY_eq

      e6_Fst_spec :
        Deriv (eqF (ap1 Fst (ap2 pi (natCode k) S)) (natCode k))
      e6_Fst_spec = axFst (natCode k) S

      e6_specFst_eq :
        Deriv (eqF (ap1 get_specFst input) (natCode k))
      e6_specFst_eq =
        ruleTrans e6_specFst (ruleTrans e6_FstFstY e6_Fst_spec)

      e6_natEq_args :
        Deriv (eqF (ap2 natEqF (ap1 get_body input) (ap1 get_specFst input))
                    (ap2 natEqF (natCode m) (natCode k)))
      e6_natEq_args =
        ruleTrans (congL natEqF (ap1 get_specFst input) e6_body_eq)
                   (congR natEqF (natCode m) e6_specFst_eq)

      e6_natEq_O :
        Deriv (eqF (ap2 natEqF (natCode m) (natCode k)) O)
      e6_natEq_O = natEqF_at_neq m k witness

      e6_full :
        Deriv (eqF (ap1 isVarMatch input) O)
      e6_full = ruleTrans e6_isVarMatch (ruleTrans e6_natEq_args e6_natEq_O)

      ----------------------------------------------------------------
      -- Step 7: condFork (pi (get_specSnd input) (get_newK input)) O
      --       = Snd (pi (get_specSnd input) (get_newK input))
      --       = get_newK input.
      e7_isVarMatch_subst :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi get_specSnd get_newK) input)
                     (ap1 isVarMatch input))
                    (ap2 condFork
                     (ap1 (C pi get_specSnd get_newK) input)
                     O))
      e7_isVarMatch_subst =
        congR condFork (ap1 (C pi get_specSnd get_newK) input) e6_full

      e7_condFork_to_Snd :
        Deriv (eqF (ap2 condFork
                     (ap1 (C pi get_specSnd get_newK) input) O)
                    (ap1 Snd (ap1 (C pi get_specSnd get_newK) input)))
      e7_condFork_to_Snd =
        condFork_false (ap1 (C pi get_specSnd get_newK) input)

      e7_pi_eq :
        Deriv (eqF (ap1 (C pi get_specSnd get_newK) input)
                    (ap2 pi (ap1 get_specSnd input) (ap1 get_newK input)))
      e7_pi_eq = pi_specSnd_newK_unfold input

      e7_Snd_pi :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 get_specSnd input) (ap1 get_newK input)))
                    (ap1 get_newK input))
      e7_Snd_pi = axSnd (ap1 get_specSnd input) (ap1 get_newK input)

      e7_full :
        Deriv (eqF (ap1 var_branch input) (ap1 get_newK input))
      e7_full =
        ruleTrans e5a
          (ruleTrans e7_isVarMatch_subst
            (ruleTrans e7_condFork_to_Snd
              (ruleTrans (cong1 Snd e7_pi_eq) e7_Snd_pi)))

      ----------------------------------------------------------------
      -- Step 8: get_newK input = ap1 s A = ap1 s (natCode (cantorVarPred m)).
      e8_newK :
        Deriv (eqF (ap1 get_newK input) (ap1 s A))
      e8_newK = get_newK_at_pi A Y

  in ruleTrans e1
       (ruleTrans to_var_branch
         (ruleTrans e7_full e8_newK))

------------------------------------------------------------------------
-- E.3  sbt_at_var_nomatch closure equation.

sbt_at_var_nomatch :
  (k m : Nat) (S : Term) -> Eq (natEq k m) false ->
  Deriv (eqF (ap2 sbt (ap2 pi (natCode k) S)
                       (ap2 pi (natCode tag_var) (natCode m)))
              (ap2 pi (natCode tag_var) (natCode m)))
sbt_at_var_nomatch k m S hyp =
  let spec : Term
      spec = ap2 pi (natCode k) S

      t : Term
      t = ap2 pi (natCode tag_var) (natCode m)

      base : Fun1
      base = baseValue_sbt

      step : Fun2
      step = stepFun_sbt

      K_pred : Nat
      K_pred = cantorVarPred m

      stateK : Term
      stateK = stateMeta base step spec K_pred

      Y : Term
      Y = ap1 Snd stateK

      witness : NatNeqWitness m k
      witness = natEqFalse_to_witness_flipped k m hyp

      ----------------------------------------------------------------
      -- Step 1: sbt_unfold.
      step1 :
        Deriv (eqF (ap2 sbt spec t) (ap1 readOff_spec (ap2 sbtState spec t)))
      step1 = sbt_unfold spec t

      ----------------------------------------------------------------
      -- Step 2: readOff_at_pi_natCode at (tag_var, m).
      step2 :
        Deriv (eqF (ap1 readOff_spec (ap2 sbtState spec t))
                    (ap1 readOff_spec
                          (stateMeta base step spec (cantor tag_var m))))
      step2 = readOff_at_pi_natCode base step spec tag_var m

      ----------------------------------------------------------------
      -- Step 3: rewrite cantor 1 m = suc K_pred.
      cantor_eq_succ : Eq (cantor (suc zero) m) (suc K_pred)
      cantor_eq_succ = cantor_var_succ_decomp m

      step3 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var m)))
                    (ap1 readOff_spec (stateMeta base step spec (suc K_pred))))
      step3 =
        eqSubst (\ z -> Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (cantor tag_var m)))
                                      (ap1 readOff_spec (stateMeta base step spec z))))
                 cantor_eq_succ
                 (axRefl (ap1 readOff_spec (stateMeta base step spec (cantor tag_var m))))

      ----------------------------------------------------------------
      -- Step 4: readOff_stateMeta_succ_via_natCode.
      step4 :
        Deriv (eqF (ap1 readOff_spec (stateMeta base step spec (suc K_pred)))
                    (ap2 step (natCode K_pred) Y))
      step4 = readOff_stateMeta_succ_via_natCode base step spec K_pred

      ----------------------------------------------------------------
      -- Step 5: Fst Y = spec.
      fstY_eq : Deriv (eqF (ap1 Fst Y) spec)
      fstY_eq = fstSnd_stateMeta base step spec K_pred

      ----------------------------------------------------------------
      -- Step 6: core firing lemma.
      step6 :
        Deriv (eqF (ap2 step (natCode K_pred) Y)
                    (ap1 s (natCode K_pred)))
      step6 = stepFun_sbt_at_var_nomatch_core k m S Y witness fstY_eq

      ----------------------------------------------------------------
      -- Step 7: bridge  ap1 s (natCode K_pred) = natCode (cantor 1 m)
      --              = ap2 pi (natCode tag_var) (natCode m)  via pi_natCode (reversed).
      step7a :
        Deriv (eqF (ap1 s (natCode K_pred))
                    (natCode (cantor (suc zero) m)))
      step7a = natCode_bridge m

      step7b :
        Deriv (eqF (natCode (cantor (suc zero) m))
                    (ap2 pi (natCode (suc zero)) (natCode m)))
      step7b = ruleSym (pi_natCode (suc zero) m)

      -- tag_var = suc zero literally, so this is t.

  in ruleTrans step1
       (ruleTrans step2
         (ruleTrans step3
           (ruleTrans step4
             (ruleTrans step6
               (ruleTrans step7a step7b)))))
