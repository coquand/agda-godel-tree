{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DecodeAt
--
-- Generalised soundness theorem for the encoded-derivation interpreter
-- thmT: invert "thmT y = code(P)" to extract "Deriv P" itself.
--
-- This is the natural extension of BRA2.DecodeBot from the specific
-- target codeBot to an arbitrary formula P.  Once decode_at is
-- delivered for the recursive tags (mp, ruleSym, ruleTrans, ruleInst,
-- ruleIndBT, ruleIndBT2), decode_bot follows trivially as a one-line
-- specialisation.
--
-- Architectural choice: decode_at is split into two complementary
-- lemmas per tag, decode_at_X_match and decode_at_X_nomatch.
--
--   * decode_at_X_match  : caller certifies meta-level that v = code(P)
--                          syntactically; we extract Deriv P from the
--                          axiom constructor (e.g. axI t).  Hypothesis
--                          unused.
--   * decode_at_X_nomatch : caller certifies meta-level that v differs
--                          from code(P); we collapse to Deriv bot via
--                          ineqLemma.
--
-- BRA's ex-falso is propositional (P -> not P imp Q), not equational
-- (eqn O falseT -> Q), so we cannot internally turn an arbitrary
-- mismatch into Deriv P.  The two-piece formulation is honest about
-- this: the consumer (decode_bot's recursive cases) only ever needs
-- Deriv bot for non-match anyway, since decode_bot's output type IS
-- Deriv bot.
--
-- For the axiom cases, this file delivers a working axI prototype that
-- pins down the architecture.  The remaining axiom cases follow the
-- same template; the recursive cases (mp, ruleSym, etc.) build on top.
--
-- ASCII only.  No postulates, no holes, no with-abstraction.

module BRA2.DecodeAt where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.GoedelII using (bot)
open import BRA2.DecodeBot using
  ( ineqLemma ; codeBot ; codeBot_isValue
  ; EvalResult ; evalValue ; evalIsValue ; evalEq
  ; eval_dispatch_axI ; eval_dispatch_axRefl
  ; eval_dispatch_axFst ; eval_dispatch_axSnd
  ; eval_dispatch_axConst )

import BRA2.Thm.ThmT
open BRA2.Thm.ThmT using
  ( thmT ; thmTDispAxI_param ; thmTDispAxRefl_param
  ; thmTDispAxFst_param ; thmTDispAxSnd_param ; thmTDispAxConst_param )
open import BRA2.Thm.TagCodes using
  ( tagCode_axI ; tagCode_axRefl
  ; tagCode_axFst ; tagCode_axSnd ; tagCode_axConst )

----------------------------------------------------------------------
-- The match-witness for axI.
--
-- Given xT (IsValue) and t (a term whose code is xT), the eval result
-- v = (Pair (Pair tagAp1 (Pair (codeF1 I) xT)) xT)  is syntactically
-- equal to codeFormula (atomic (eqn (ap1 I t) t)).  The match-witness
-- is just  refl  in that case.

axI_match_eq :
  (t : Term) ->
  Eq (codeFormula (atomic (eqn (ap1 I t) t)))
     (ap2 Pair (ap2 Pair tagAp1 (ap2 Pair (codeF1 I) (code t))) (code t))
axI_match_eq t = refl

----------------------------------------------------------------------
-- decode_at_axI_match : extract Deriv P when caller certifies match.
--
-- The caller has determined P = atomic (eqn (ap1 I t) t) for a known
-- t such that  code t = xT .  In that case codeFormula P syntactically
-- equals the value v that thmT produces for  Pair tagCode_axI xT , so
-- the hypothesis is non-contradictory and we just return  axI t .
--
-- Hypothesis is unused: axI t is unconditionally derivable.  The
-- hypothesis IS the witness that the match-claim was correctly typed.

decode_at_axI_match :
  (xT : Term) -> IsValue xT ->
  (t : Term) -> Eq (code t) xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI xT))
                     (codeFormula (atomic (eqn (ap1 I t) t))))) ->
  Deriv (atomic (eqn (ap1 I t) t))
decode_at_axI_match xT vxT t code_t_eq_xT _ = axI t

----------------------------------------------------------------------
-- decode_at_axI_nomatch : collapse the hypothesis to Deriv bot when
-- caller certifies meta-level mismatch.
--
-- The caller has determined that  treeEq v (codeFormula P) = false ,
-- i.e., P does NOT correspond syntactically to what  Pair tagCode_axI
-- xT  encodes.  Since v is value-shape and codeFormula P is value-
-- shape, ineqLemma converts the equational hypothesis to Deriv bot.

decode_at_axI_nomatch :
  (xT : Term) -> IsValue xT -> (P : Formula) ->
  Eq (treeEq
       (ap2 Pair (ap2 Pair tagAp1 (ap2 Pair (codeF1 I) xT)) xT)
       (codeFormula P))
     false ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI xT))
                     (codeFormula P))) ->
  Deriv bot
decode_at_axI_nomatch xT vxT P neq h =
  let
    v : Term
    v = ap2 Pair (ap2 Pair tagAp1 (ap2 Pair (codeF1 I) xT)) xT

    v_iv : IsValue v
    v_iv =
      valNd _ xT
        (valNd _ _ tagAp1_isValue
          (valNd _ _ (codeF1_isValue I) vxT))
        vxT

    -- thmT y = v via dispatch.
    red : Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI xT)) v))
    red = thmTDispAxI_param xT

    -- Hypothesis transports: thmT y = codeFormula P  ~>  v = codeFormula P.
    h' : Deriv (atomic (eqn v (codeFormula P)))
    h' = ruleTrans (ruleSym red) h

  in ineqLemma v (codeFormula P) v_iv (codeFormula_isValue P) neq h'

----------------------------------------------------------------------
-- decode_at signature (top-level, not implemented in this file).
--
-- The full general decode_at would pattern-match on y and on P,
-- delegating each case to decode_at_X_match or decode_at_X_nomatch
-- after deciding (decidably, on value-shape terms) whether the eval
-- value matches codeFormula P.  Output type is  Or (Deriv P)
-- (Deriv bot) , reflecting the fact that BRA's ex-falso cannot
-- promote a propositional contradiction to an arbitrary Deriv P.
--
-- For decode_bot specifically (P = bot), the Deriv bot branch IS the
-- desired output, so the Or collapses trivially.
--
-- See BRA2/DECODE-BOT-NEXT-SESSION.md for the implementation roadmap.

data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

----------------------------------------------------------------------
-- Generic _nomatch via EvalResult.
--
-- Once the caller has an EvalResult of y (provided by the existing
-- BRA2.DecodeBot.eval_dispatch_X family), and a meta-level proof that
-- the canonical value v differs from codeFormula P, ineqLemma converts
-- the equational hypothesis to Deriv bot.  This is the universal
-- mismatch discharge -- it works at any tag, in particular for the
-- recursive tags too.

decode_at_nomatch_eval :
  (y : Term) (ev : EvalResult y) (P : Formula) ->
  Eq (treeEq (evalValue y ev) (codeFormula P)) false ->
  Deriv (atomic (eqn (ap1 thmT y) (codeFormula P))) ->
  Deriv bot
decode_at_nomatch_eval y ev P neq h =
  let
    v : Term
    v = evalValue y ev

    v_iv : IsValue v
    v_iv = evalIsValue y ev

    eq_thmTy_v : Deriv (atomic (eqn (ap1 thmT y) v))
    eq_thmTy_v = evalEq y ev

    h' : Deriv (atomic (eqn v (codeFormula P)))
    h' = ruleTrans (ruleSym eq_thmTy_v) h

  in ineqLemma v (codeFormula P) v_iv (codeFormula_isValue P) neq h'

----------------------------------------------------------------------
-- decode_at_axRefl_match.
--
-- For y = Pair tagCode_axRefl xT, the eval value v = Pair xT xT, which
-- equals codeFormula (atomic (eqn t t)) when xT = code t.  Caller
-- certifies code t = xT; we return  axRefl t .

decode_at_axRefl_match :
  (xT : Term) -> IsValue xT ->
  (t : Term) -> Eq (code t) xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axRefl xT))
                     (codeFormula (atomic (eqn t t))))) ->
  Deriv (atomic (eqn t t))
decode_at_axRefl_match xT vxT t code_t_eq_xT _ = axRefl t

----------------------------------------------------------------------
-- decode_at_axFst_match.
--
-- For y = Pair tagCode_axFst (Pair aT bT), v = Pair (Pair tagAp1
-- (Pair (codeF1 Fst) (Pair tagAp2 (Pair (codeF2 Pair) (Pair aT bT)))))
-- aT, which equals codeFormula (atomic (eqn (ap1 Fst (ap2 Pair a b))
-- a)) when aT = code a, bT = code b.

decode_at_axFst_match :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  (a b : Term) -> Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axFst (ap2 Pair aT bT)))
                     (codeFormula (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))))) ->
  Deriv (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
decode_at_axFst_match aT bT vaT vbT a b _ _ _ = axFst a b

----------------------------------------------------------------------
-- decode_at_axSnd_match.

decode_at_axSnd_match :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  (a b : Term) -> Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axSnd (ap2 Pair aT bT)))
                     (codeFormula (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))))) ->
  Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
decode_at_axSnd_match aT bT vaT vbT a b _ _ _ = axSnd a b

----------------------------------------------------------------------
-- decode_at_axConst_match.

decode_at_axConst_match :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  (a b : Term) -> Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axConst (ap2 Pair aT bT)))
                     (codeFormula (atomic (eqn (ap2 Const a b) a))))) ->
  Deriv (atomic (eqn (ap2 Const a b) a))
decode_at_axConst_match aT bT vaT vbT a b _ _ _ = axConst a b

----------------------------------------------------------------------
-- Smoke test: the axI _match wrapper at a closed Term  t = O .
--
-- For t = O,  code t = O  (lf), so xT = O, and the match-witness
-- holds by refl.

private
  smokeTest_axI_O :
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI O))
                       (codeFormula (atomic (eqn (ap1 I O) O))))) ->
    Deriv (atomic (eqn (ap1 I O) O))
  smokeTest_axI_O h = decode_at_axI_match O valO O refl h

----------------------------------------------------------------------
-- Smoke test: the axI _nomatch wrapper at  P = bot .
--
-- For xT = O,  v = ap2 Pair (ap2 Pair tagAp1 (ap2 Pair (codeF1 I) O)) O.
-- codeFormula bot = ap2 Pair O (ap2 Pair O O).  treeEq v (codeFormula
-- bot) = false (Fst differs: tagAp1-Pair vs O leaf).

private
  smokeTest_axI_nomatch_bot :
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI O))
                       (codeFormula bot))) ->
    Deriv bot
  smokeTest_axI_nomatch_bot h = decode_at_axI_nomatch O valO bot refl h

----------------------------------------------------------------------
-- Generic-via-EvalResult smoke tests.

private
  smokeTest_axRefl_nomatch_bot :
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axRefl O))
                       (codeFormula bot))) ->
    Deriv bot
  smokeTest_axRefl_nomatch_bot h =
    decode_at_nomatch_eval _ (eval_dispatch_axRefl O valO) bot refl h

  smokeTest_axFst_nomatch_bot :
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axFst (ap2 Pair O O)))
                       (codeFormula bot))) ->
    Deriv bot
  smokeTest_axFst_nomatch_bot h =
    decode_at_nomatch_eval _ (eval_dispatch_axFst O O valO valO) bot refl h

  -- axRefl match at t = O: Pair O O  vs  codeFormula (eqn O O) = Pair O O.
  smokeTest_axRefl_match_O :
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axRefl O))
                       (codeFormula (atomic (eqn O O))))) ->
    Deriv (atomic (eqn O O))
  smokeTest_axRefl_match_O h = decode_at_axRefl_match O valO O refl h

  -- axFst match at a = O, b = O: aT=bT=O.
  smokeTest_axFst_match_OO :
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axFst (ap2 Pair O O)))
                       (codeFormula (atomic (eqn (ap1 Fst (ap2 Pair O O)) O))))) ->
    Deriv (atomic (eqn (ap1 Fst (ap2 Pair O O)) O))
  smokeTest_axFst_match_OO h = decode_at_axFst_match O O valO valO O O refl refl h
