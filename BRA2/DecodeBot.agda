{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DecodeBot
--
-- Reflection-threshold experiment.  Goal:
--
--   decode_bot :
--     (y : Term) -> IsValue y ->
--     Deriv (atomic (eqn (ap1 thmT y) (reify (codeFormula bot)))) ->
--     Deriv bot
--
-- This file delivers the reusable infrastructure piece -- the
-- "ineqLemma" framework, which converts any Deriv of a closed false
-- equation between value-shape Terms into Deriv bot.  ineqLemma is
-- the structural ingredient decode_bot would use in every leaf
-- (non-recursive-rule) case.
--
-- The main theorem decode_bot is NOT delivered.  See
-- BRA2/DECODE-BOT-REPORT.md for the diagnostic on why: the BRA2.Thm.ThmT
-- module wraps thmT in an abstract block (lines 137-10583), so thmT is
-- opaque outside the WithDispatch namespace.  The exported dispatch
-- lemmas (thmTDispAxI, thmTDispMp, ...) only give reductions for
-- inputs of the form  ap2 Pair (natCode (suc tag)) payT  at a known
-- tag.  No reduction is exported for  thmT O  or for  thmT (ap2 Pair a b)
-- when  a  is not a recognized tag.  decode_bot's value-base case
-- (y = O) and unrecognized-tag cases consequently cannot be discharged
-- without either embedding decode_bot inside the abstract block or
-- exporting additional thmT-evaluation lemmas.

module BRA2.DecodeBot where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.SubT using (treeEqRed)
open import BRA2.Th14SubTPushthrough using (treeEqRefl)
open import BRA2.GoedelII using (bot)

import BRA2.Thm.ThmT
open BRA2.Thm.ThmT using
  ( thmT ; thmT_O_eval ; thmT_pairO_eval ; thmT_sndProj_eval
  ; thmTDispAxI_param ; thmTDispAxRefl_param ; thmTDispAxFst_param
  ; thmTDispAxSnd_param ; thmTDispAxConst_param )
open import BRA2.Thm.TagCodes using
  (tagCode_axI ; tagCode_axRefl ; tagCode_axFst ; tagCode_axSnd ; tagCode_axConst)

----------------------------------------------------------------------
-- The "false equation -> Deriv bot" bridge.
--
-- ineqLemma packages the standard projection-via-TreeEq trick:
-- if t and u are value-shape Terms with treeEq t u = false (a
-- decidable, meta-level fact), then any Deriv of  t = u  collapses
-- to a Deriv of  bot = atomic (eqn O falseT) .
--
-- Construction:
--   1.  congR TreeEq t h               :  TreeEq t t = TreeEq t u
--   2.  treeEqRed t t                  :  TreeEq t t = boolCase (treeEq t t) O falseT
--                                       = O                                   (treeEqRefl t)
--   3.  treeEqRed t u                  :  TreeEq t u = boolCase (treeEq t u) O falseT
--                                       = falseT                              (neq)
--   4.  Chain ruleSym/ruleTrans yields :  O = falseT .

ineqLemma :
  (t u : Term) (vt : IsValue t) (vu : IsValue u) ->
  Eq (treeEq t u) false ->
  Deriv (atomic (eqn t u)) ->
  Deriv bot
ineqLemma t u vt vu neq h =
  let
    -- Step 1: TreeEq t t = TreeEq t u .
    s1 : Deriv (atomic (eqn (ap2 TreeEq t t) (ap2 TreeEq t u)))
    s1 = congR TreeEq t h

    -- Step 2: TreeEq t t = boolCase (treeEq t t) O falseT .
    s2raw : Deriv (atomic (eqn (ap2 TreeEq t t)
                                (boolCase (treeEq t t) O falseT)))
    s2raw = treeEqRed t vt t vt

    -- Reduce the meta-level boolCase by Eq.subst on  treeEq t t = true .
    s2 : Deriv (atomic (eqn (ap2 TreeEq t t) O))
    s2 = eqSubst
           (\ b -> Deriv (atomic (eqn (ap2 TreeEq t t)
                                       (boolCase b O falseT))))
           (treeEqRefl t vt)
           s2raw

    -- Step 3: TreeEq t u = boolCase (treeEq t u) O falseT
    --                    = falseT                       (since neq)
    s3raw : Deriv (atomic (eqn (ap2 TreeEq t u)
                                (boolCase (treeEq t u) O falseT)))
    s3raw = treeEqRed t vt u vu

    s3 : Deriv (atomic (eqn (ap2 TreeEq t u) falseT))
    s3 = eqSubst
           (\ b -> Deriv (atomic (eqn (ap2 TreeEq t u)
                                       (boolCase b O falseT))))
           neq
           s3raw

    -- Step 4: chain.
    chain1 : Deriv (atomic (eqn O (ap2 TreeEq t u)))
    chain1 = ruleTrans (ruleSym s2) s1
  in ruleTrans chain1 s3

----------------------------------------------------------------------
-- Sanity check: the codeFormula of bot is value-shape, and
-- meta-level treeEq distinguishes O from it (proof: refl).
-- These are the two static facts decode_bot's y=O case would need.

codeBot : Term
codeBot = reify (codeFormula bot)

codeBot_isValue : IsValue codeBot
codeBot_isValue = codeFormula_isValue bot

treeEq_O_codeBot_false : Eq (treeEq O codeBot) false
treeEq_O_codeBot_false = refl

----------------------------------------------------------------------
-- The y = O case of decode_bot.
--
-- thmT(O) reduces to O via thmT_O_eval (which lives inside the
-- BRA2.Thm.ThmT abstract block, applying axRecLf at the underlying
-- Rec primitive).  The hypothesis  thmT O = codeFormula bot  then
-- collapses via ineqLemma to Deriv bot.

decode_bot_O :
  Deriv (atomic (eqn (ap1 thmT O) (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_O h =
  let
    -- Replace  thmT O  by  O  using thmT_O_eval.
    h' : Deriv (atomic (eqn O codeBot))
    h' = ruleTrans (ruleSym thmT_O_eval) h
  in ineqLemma O codeBot valO codeBot_isValue treeEq_O_codeBot_false h'

----------------------------------------------------------------------
-- The y = Pair O b case of decode_bot.
--
-- thmT(Pair O b) reduces to O via thmT_pairO_eval (cascade falls
-- through all 42 levels and lands at fbBody = O).  Then ineqLemma
-- between O and codeFormula bot.

decode_bot_pairO :
  (b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair O b)) (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_pairO b h =
  let
    h' : Deriv (atomic (eqn O codeBot))
    h' = ruleTrans (ruleSym (thmT_pairO_eval b)) h
  in ineqLemma O codeBot valO codeBot_isValue treeEq_O_codeBot_false h'

----------------------------------------------------------------------
-- Representative tag-dispatch case: y = Pair tagCode_axI xT (= the
-- encoded form of "axI t" applied at xT = code t).
--
-- thmTDispAxI_param reduces  thmT (Pair tagCode_axI xT)  to
--   Pair (Pair tagAp1 (Pair (codeF1 I) xT)) xT
-- (the codeFormula of  atomic (eqn (ap1 I t) t) , in projective form).
--
-- That value-shape Pair has a Pair-headed Fst (= Pair tagAp1 ...),
-- whereas codeBot has Fst = O .  So treeEq is false at the outermost
-- Pair pattern (the  ap2 Pair _ _ vs O  case in BRA2.Term.treeEq),
-- and ineqLemma applies.
--
-- Pattern: every non-recursive axiom case follows this template.
-- Each tag X has a thmTDispX_param producing a Pair-shaped value
-- whose Fst is a Pair tag header (tagAp1 / tagAp2 / etc.); none can
-- coincide with codeBot's Fst = O.

decode_bot_axI :
  (xT : Term) -> IsValue xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI xT)) (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_axI xT vxT h =
  let
    -- thmT (Pair tagCode_axI xT) = Pair (Pair tagAp1 (Pair (codeF1 I) xT)) xT
    red = thmTDispAxI_param xT

    rhsT : Term
    rhsT = ap2 Pair (ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 I)) xT)) xT

    h' : Deriv (atomic (eqn rhsT codeBot))
    h' = ruleTrans (ruleSym red) h

    -- IsValue witness for the Pair output.  reify is identity, so all
    -- nested codes remain value-shape.
    rhsT_iv : IsValue rhsT
    rhsT_iv =
      valNd (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) xT)) xT
            (valNd (reify tagAp1) (ap2 Pair (reify (codeF1 I)) xT)
                   tagAp1_isValue
                   (valNd (reify (codeF1 I)) xT (codeF1_isValue I) vxT))
            vxT

    -- treeEq rhsT codeBot = false.  Outermost: Pair X Y vs Pair O Z,
    -- so treeEq = boolAnd (treeEq X O) (treeEq Y Z).  X is Pair-headed,
    -- so treeEq X O = false (per the Pair-vs-leaf clause of treeEq),
    -- short-circuiting via boolAnd.
    treeEq_rhsT_codeBot_false : Eq (treeEq rhsT codeBot) false
    treeEq_rhsT_codeBot_false = refl

  in ineqLemma rhsT codeBot rhsT_iv codeBot_isValue treeEq_rhsT_codeBot_false h'

----------------------------------------------------------------------
-- decode_bot_axRefl: y = Pair tagCode_axRefl xT.
--
-- Pattern test: a tag whose dispatch result has Fst = xT (the second
-- slot of the input).  Whether treeEq (Pair xT xT) codeBot = false
-- depends on the value-shape of xT, so the meta-level proof case-
-- splits on IsValue xT (rather than reducing definitionally as in
-- the axI case).

private
  -- (Pair xT xT) vs codeBot = (Pair O codeFalseT).  Outer Pair pattern
  -- gives boolAnd (treeEq xT O) (treeEq xT codeFalseT).  Either treeEq
  -- xT O = false (xT non-leaf) or treeEq xT codeFalseT = false (xT = O,
  -- codeFalseT non-leaf).  Either way boolAnd is false.
  treeEq_axReflRhs_codeBot_false :
    (xT : Term) -> IsValue xT ->
    Eq (treeEq (ap2 Pair xT xT) codeBot) false
  treeEq_axReflRhs_codeBot_false .O                 valO                = refl
  treeEq_axReflRhs_codeBot_false (ap2 Pair a b)    (valNd .a .b va vb)  = refl

decode_bot_axRefl :
  (xT : Term) -> IsValue xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axRefl xT)) (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_axRefl xT vxT h =
  let
    red = thmTDispAxRefl_param xT

    rhsT : Term
    rhsT = ap2 Pair xT xT

    h' : Deriv (atomic (eqn rhsT codeBot))
    h' = ruleTrans (ruleSym red) h

    rhsT_iv : IsValue rhsT
    rhsT_iv = valNd xT xT vxT vxT

  in ineqLemma rhsT codeBot rhsT_iv codeBot_isValue
       (treeEq_axReflRhs_codeBot_false xT vxT) h'

----------------------------------------------------------------------
-- decode_bot_axFst : y = Pair tagCode_axFst (Pair aT bT).
--
-- Multi-arg payload variant.  The dispatch result is a deeply-nested
-- Pair tagAp1 (Pair (codeF1 Fst) (Pair tagAp2 (Pair (codeF2 Pair) (Pair aT bT))))
-- paired with aT.  Outer Fst is Pair-headed, contradicting codeBot's O.

decode_bot_axFst :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axFst (ap2 Pair aT bT)))
                     (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_axFst aT bT vaT vbT h =
  let
    red = thmTDispAxFst_param aT bT

    rhsT : Term
    rhsT = ap2 Pair
             (ap2 Pair (reify tagAp1)
               (ap2 Pair (reify (codeF1 Fst))
                 (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 Pair))
                     (ap2 Pair aT bT)))))
             aT

    h' : Deriv (atomic (eqn rhsT codeBot))
    h' = ruleTrans (ruleSym red) h

    rhsT_iv : IsValue rhsT
    rhsT_iv =
      valNd _ aT
        (valNd _ _ tagAp1_isValue
          (valNd _ _ (codeF1_isValue Fst)
            (valNd _ _ tagAp2_isValue
              (valNd _ _ (codeF2_isValue Pair) (valNd aT bT vaT vbT)))))
        vaT

    treeEq_rhsT_codeBot_false : Eq (treeEq rhsT codeBot) false
    treeEq_rhsT_codeBot_false = refl

  in ineqLemma rhsT codeBot rhsT_iv codeBot_isValue
       treeEq_rhsT_codeBot_false h'

----------------------------------------------------------------------
-- decode_bot_axSnd : y = Pair tagCode_axSnd (Pair aT bT).
-- Mirror of decode_bot_axFst with bT in the result's Snd position.

decode_bot_axSnd :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axSnd (ap2 Pair aT bT)))
                     (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_axSnd aT bT vaT vbT h =
  let
    red = thmTDispAxSnd_param aT bT

    rhsT : Term
    rhsT = ap2 Pair
             (ap2 Pair (reify tagAp1)
               (ap2 Pair (reify (codeF1 Snd))
                 (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 Pair))
                     (ap2 Pair aT bT)))))
             bT

    h' : Deriv (atomic (eqn rhsT codeBot))
    h' = ruleTrans (ruleSym red) h

    rhsT_iv : IsValue rhsT
    rhsT_iv =
      valNd _ bT
        (valNd _ _ tagAp1_isValue
          (valNd _ _ (codeF1_isValue Snd)
            (valNd _ _ tagAp2_isValue
              (valNd _ _ (codeF2_isValue Pair) (valNd aT bT vaT vbT)))))
        vbT

    treeEq_rhsT_codeBot_false : Eq (treeEq rhsT codeBot) false
    treeEq_rhsT_codeBot_false = refl

  in ineqLemma rhsT codeBot rhsT_iv codeBot_isValue
       treeEq_rhsT_codeBot_false h'

----------------------------------------------------------------------
-- thmT_eval : the meta-level evaluator of  thmT  on value-shape
-- inputs.  Foundation for the generalised soundness theorem
-- decode_at -- and ultimately for the recursive cases of decode_bot.
--
-- For each value-shape Term y, thmT_eval produces a canonical
-- normalised value v : Term plus a Deriv-level proof that
-- thmT y = v.  Plus an IsValue witness for v (since v is built
-- from O / Pair only).
--
-- This is currently delivered as a collection of compositional
-- helpers, NOT as a single total function.  Reason: making it
-- total would require deep case-analysis on the dispatch tag
-- (40+ cases plus their payload-shape sub-cases).  See
-- DECODE-BOT-REPORT.md for the full effort breakdown.

EvalResult : Term -> Set
EvalResult y =
  Sigma Term (\ v ->
    Sigma (IsValue v) (\ _ ->
      Deriv (atomic (eqn (ap1 thmT y) v))))

evalValue : (y : Term) -> EvalResult y -> Term
evalValue y r = fst r

evalIsValue : (y : Term) (r : EvalResult y) -> IsValue (evalValue y r)
evalIsValue y r = fst (snd r)

evalEq : (y : Term) (r : EvalResult y) ->
         Deriv (atomic (eqn (ap1 thmT y) (evalValue y r)))
evalEq y r = snd (snd r)

----------------------------------------------------------------------
-- evalO : the leaf case.

eval_O : EvalResult O
eval_O = mkSigma O (mkSigma valO thmT_O_eval)

----------------------------------------------------------------------
-- eval_pairO : the "no top-level Pair tag" case.  Dispatch cascade
-- falls through; thmT y = O.

eval_pairO : (b : Term) -> EvalResult (ap2 Pair O b)
eval_pairO b = mkSigma O (mkSigma valO (thmT_pairO_eval b))

----------------------------------------------------------------------
-- eval_sndProj : the "Fst-of-Fst is Pair-shape" case (sndProj branch
-- of stepProto).
--
-- Given recursive evaluations of the inner Pair (Pair a11 a12) a3
-- and of b , produces an evaluation of the full input.
-- thmT y = Pair (eval-result-X) (eval-result-b) .

eval_sndProj :
  (a11 a12 a3 b : Term) ->
  (evX : EvalResult (ap2 Pair (ap2 Pair a11 a12) a3)) ->
  (evb : EvalResult b) ->
  EvalResult (ap2 Pair (ap2 Pair (ap2 Pair a11 a12) a3) b)
eval_sndProj a11 a12 a3 b evX evb =
  let
    X : Term
    X = ap2 Pair (ap2 Pair a11 a12) a3

    vX : Term
    vX = evalValue X evX

    vX_iv : IsValue vX
    vX_iv = evalIsValue X evX

    eqX : Deriv (atomic (eqn (ap1 thmT X) vX))
    eqX = evalEq X evX

    vb : Term
    vb = evalValue b evb

    vb_iv : IsValue vb
    vb_iv = evalIsValue b evb

    eqb : Deriv (atomic (eqn (ap1 thmT b) vb))
    eqb = evalEq b evb

    -- thmT y = Pair (thmT X) (thmT b) via the sndProj branch.
    raw : Deriv (atomic (eqn (ap1 thmT (ap2 Pair X b))
                              (ap2 Pair (ap1 thmT X) (ap1 thmT b))))
    raw = thmT_sndProj_eval a11 a12 a3 b

    -- Substitute thmT X = vX.
    s1 : Deriv (atomic (eqn (ap2 Pair (ap1 thmT X) (ap1 thmT b))
                             (ap2 Pair vX (ap1 thmT b))))
    s1 = congL Pair (ap1 thmT b) eqX

    -- Substitute thmT b = vb.
    s2 : Deriv (atomic (eqn (ap2 Pair vX (ap1 thmT b))
                             (ap2 Pair vX vb)))
    s2 = congR Pair vX eqb

    eqFinal : Deriv (atomic (eqn (ap1 thmT (ap2 Pair X b))
                                  (ap2 Pair vX vb)))
    eqFinal = ruleTrans raw (ruleTrans s1 s2)

    v : Term
    v = ap2 Pair vX vb

    v_iv : IsValue v
    v_iv = valNd vX vb vX_iv vb_iv

  in mkSigma v (mkSigma v_iv eqFinal)

----------------------------------------------------------------------
-- decode_bot_sndProj : the sndProj-branch case of decode_bot.
--
-- Given a recursive evaluation of the inner Pair (Pair a11 a12) a3
-- and of b , and a hypothesis that thmT y = codeBot, derive Deriv bot.
--
-- The sndProj-branch's thmT y is Pair vX vb where vX = thmT(inner)
-- and vb = thmT b.  For codeBot = Pair O codeFalseT, ineqLemma
-- discharges syntactically iff Pair vX vb != codeBot, which is
-- decidable from the structures of vX and vb.

decode_bot_sndProj_at_iv :
  (a11 a12 a3 b : Term) ->
  (evX : EvalResult (ap2 Pair (ap2 Pair a11 a12) a3)) ->
  (evb : EvalResult b) ->
  Eq (treeEq (ap2 Pair (evalValue _ evX) (evalValue _ evb)) codeBot) false ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair (ap2 Pair (ap2 Pair a11 a12) a3) b))
                     (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_sndProj_at_iv a11 a12 a3 b evX evb neq h =
  let
    ev = eval_sndProj a11 a12 a3 b evX evb
    v = evalValue _ ev
    v_iv = evalIsValue _ ev
    eq_thmTy_v = evalEq _ ev

    -- Hypothesis transports: thmT y = codeBot becomes v = codeBot.
    h' : Deriv (atomic (eqn v codeBot))
    h' = ruleTrans (ruleSym eq_thmTy_v) h

  in ineqLemma v codeBot v_iv codeBot_isValue neq h'

----------------------------------------------------------------------
-- Dispatch-case evaluators (eval_dispatch_X).
--
-- These handle the in-cascade tag dispatches.  Each is a thin wrapper
-- around the existing thmTDispX_param :  the dispatch lemma already
-- gives  thmT (Pair tagCode_X payload) = (specific Pair value) , so
-- the eval just packages the result with its IsValue witness.
--
-- These three (axI, axRefl, axFst) demonstrate the template; the 30
-- remaining axiom tags follow it unchanged.  ~ 30 LoC each.

eval_dispatch_axI :
  (xT : Term) -> IsValue xT ->
  EvalResult (ap2 Pair tagCode_axI xT)
eval_dispatch_axI xT vxT =
  let
    v : Term
    v = ap2 Pair (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 I)) xT)) xT
    v_iv : IsValue v
    v_iv = valNd _ xT
             (valNd _ _ tagAp1_isValue
                (valNd _ _ (codeF1_isValue I) vxT))
             vxT
  in mkSigma v (mkSigma v_iv (thmTDispAxI_param xT))

eval_dispatch_axRefl :
  (xT : Term) -> IsValue xT ->
  EvalResult (ap2 Pair tagCode_axRefl xT)
eval_dispatch_axRefl xT vxT =
  let
    v : Term
    v = ap2 Pair xT xT
    v_iv : IsValue v
    v_iv = valNd xT xT vxT vxT
  in mkSigma v (mkSigma v_iv (thmTDispAxRefl_param xT))

eval_dispatch_axFst :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  EvalResult (ap2 Pair tagCode_axFst (ap2 Pair aT bT))
eval_dispatch_axFst aT bT vaT vbT =
  let
    v : Term
    v = ap2 Pair
          (ap2 Pair (reify tagAp1)
            (ap2 Pair (reify (codeF1 Fst))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT)))))
          aT
    v_iv : IsValue v
    v_iv = valNd _ aT
             (valNd _ _ tagAp1_isValue
               (valNd _ _ (codeF1_isValue Fst)
                 (valNd _ _ tagAp2_isValue
                   (valNd _ _ (codeF2_isValue Pair) (valNd aT bT vaT vbT)))))
             vaT
  in mkSigma v (mkSigma v_iv (thmTDispAxFst_param aT bT))

----------------------------------------------------------------------
-- decode_bot_axConst : y = Pair tagCode_axConst (Pair aT bT).
-- Result has Pair (Pair tagAp2 ...) aT structure.

decode_bot_axConst :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axConst (ap2 Pair aT bT)))
                     (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_axConst aT bT vaT vbT h =
  let
    red = thmTDispAxConst_param aT bT

    rhsT : Term
    rhsT = ap2 Pair (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Const))
                                        (ap2 Pair aT bT))) aT

    h' : Deriv (atomic (eqn rhsT codeBot))
    h' = ruleTrans (ruleSym red) h

    rhsT_iv : IsValue rhsT
    rhsT_iv =
      valNd _ aT
        (valNd _ _ tagAp2_isValue
          (valNd _ _ (codeF2_isValue Const) (valNd aT bT vaT vbT)))
        vaT

    treeEq_rhsT_codeBot_false : Eq (treeEq rhsT codeBot) false
    treeEq_rhsT_codeBot_false = refl

  in ineqLemma rhsT codeBot rhsT_iv codeBot_isValue
       treeEq_rhsT_codeBot_false h'
