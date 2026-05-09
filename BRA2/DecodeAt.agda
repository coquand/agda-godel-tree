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
  ; eval_O ; eval_dispatch_axI ; eval_dispatch_axRefl
  ; eval_dispatch_axFst ; eval_dispatch_axSnd
  ; eval_dispatch_axConst )

import BRA2.Thm.ThmT
open BRA2.Thm.ThmT using
  ( thmT ; thmTDispAxI_param ; thmTDispAxRefl_param
  ; thmTDispAxFst_param ; thmTDispAxSnd_param ; thmTDispAxConst_param )
open import BRA2.Thm.TagCodes using
  ( tagCode_axI ; tagCode_axRefl
  ; tagCode_axFst ; tagCode_axSnd ; tagCode_axConst
  ; tagCode_axKT ; tagCode_axIfLfL ; tagCode_axIfLfN ; tagCode_axIfLfNL
  ; tagCode_axTreeEqLN ; tagCode_axTreeEqNL ; tagCode_axTreeEqNN
  ; tagCode_axFstLf ; tagCode_axSndLf
  ; tagCode_axIfLfLL ; tagCode_axTreeEqLL
  ; tagCode_cong1 ; tagCode_congL ; tagCode_congR
  ; tagCode_ruleSym ; tagCode_ruleTrans ; tagCode_mp
  ; tagCode_ruleInst ; tagCode_ruleIndBT )

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
-- decode_at_axZ_match.
--
-- y = Pair tagCode_axKT (Pair (codeF1 Z) xT).  Conclusion: ap1 Z x = O.

decode_at_axZ_match :
  (xT : Term) -> IsValue xT ->
  (x : Term) -> Eq (code x) xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axKT
                                  (ap2 Pair (codeF1 Z) xT)))
                     (codeFormula (atomic (eqn (ap1 Z x) O))))) ->
  Deriv (atomic (eqn (ap1 Z x) O))
decode_at_axZ_match xT _ x _ _ = axZ x

----------------------------------------------------------------------
-- decode_at_axIfLfL_match.
--
-- y = Pair tagCode_axIfLfL (Pair aT bT).
-- Conclusion: ap2 IfLf O (Pair a b) = a.

decode_at_axIfLfL_match :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  (a b : Term) -> Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axIfLfL (ap2 Pair aT bT)))
                     (codeFormula (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))))) ->
  Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
decode_at_axIfLfL_match aT bT _ _ a b _ _ _ = axIfLfL a b

----------------------------------------------------------------------
-- decode_at_axIfLfN_match.

decode_at_axIfLfN_match :
  (xT yT aT bT : Term) -> IsValue xT -> IsValue yT -> IsValue aT -> IsValue bT ->
  (x y a b : Term) ->
  Eq (code x) xT -> Eq (code y) yT ->
  Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axIfLfN
                                  (ap2 Pair xT (ap2 Pair yT (ap2 Pair aT bT)))))
                     (codeFormula (atomic
                       (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))))) ->
  Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))
decode_at_axIfLfN_match xT yT aT bT _ _ _ _ x y a b _ _ _ _ _ =
  axIfLfN x y a b

----------------------------------------------------------------------
-- decode_at_axIfLfNL_match.

decode_at_axIfLfNL_match :
  (xT yT : Term) -> IsValue xT -> IsValue yT ->
  (x y : Term) -> Eq (code x) xT -> Eq (code y) yT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axIfLfNL (ap2 Pair xT yT)))
                     (codeFormula (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))))) ->
  Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))
decode_at_axIfLfNL_match xT yT _ _ x y _ _ _ = axIfLfNL x y

----------------------------------------------------------------------
-- decode_at_axTreeEqLN_match.

decode_at_axTreeEqLN_match :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  (a b : Term) -> Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axTreeEqLN (ap2 Pair aT bT)))
                     (codeFormula (atomic
                       (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))))) ->
  Deriv (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
decode_at_axTreeEqLN_match aT bT _ _ a b _ _ _ = axTreeEqLN a b

----------------------------------------------------------------------
-- decode_at_axTreeEqNL_match.

decode_at_axTreeEqNL_match :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  (a b : Term) -> Eq (code a) aT -> Eq (code b) bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axTreeEqNL (ap2 Pair aT bT)))
                     (codeFormula (atomic
                       (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))))) ->
  Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
decode_at_axTreeEqNL_match aT bT _ _ a b _ _ _ = axTreeEqNL a b

----------------------------------------------------------------------
-- decode_at_axTreeEqNN_match.
--
-- 4-arg payload: Pair (Pair a1T a2T) (Pair b1T b2T).

decode_at_axTreeEqNN_match :
  (a1T a2T b1T b2T : Term) ->
  IsValue a1T -> IsValue a2T -> IsValue b1T -> IsValue b2T ->
  (a1 a2 b1 b2 : Term) ->
  Eq (code a1) a1T -> Eq (code a2) a2T ->
  Eq (code b1) b1T -> Eq (code b2) b2T ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axTreeEqNN
                                  (ap2 Pair (ap2 Pair a1T a2T) (ap2 Pair b1T b2T))))
                     (codeFormula (atomic
                       (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                            (ap2 IfLf (ap2 TreeEq a1 b1)
                                       (ap2 Pair (ap2 TreeEq a2 b2)
                                                 (ap2 Pair O O)))))))) ->
  Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                     (ap2 IfLf (ap2 TreeEq a1 b1)
                                (ap2 Pair (ap2 TreeEq a2 b2)
                                          (ap2 Pair O O)))))
decode_at_axTreeEqNN_match _ _ _ _ _ _ _ _ a1 a2 b1 b2 _ _ _ _ _ =
  axTreeEqNN a1 a2 b1 b2

----------------------------------------------------------------------
-- Closed-output _match wrappers.  Conclusion is determined by the tag;
-- payT is unconstrained.

decode_at_axFstLf_match :
  (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axFstLf payT))
                     (codeFormula (atomic (eqn (ap1 Fst O) O))))) ->
  Deriv (atomic (eqn (ap1 Fst O) O))
decode_at_axFstLf_match _ _ = axFstLf

decode_at_axSndLf_match :
  (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axSndLf payT))
                     (codeFormula (atomic (eqn (ap1 Snd O) O))))) ->
  Deriv (atomic (eqn (ap1 Snd O) O))
decode_at_axSndLf_match _ _ = axSndLf

decode_at_axIfLfLL_match :
  (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axIfLfLL payT))
                     (codeFormula (atomic (eqn (ap2 IfLf O O) O))))) ->
  Deriv (atomic (eqn (ap2 IfLf O O) O))
decode_at_axIfLfLL_match _ _ = axIfLfLL

decode_at_axTreeEqLL_match :
  (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axTreeEqLL payT))
                     (codeFormula (atomic (eqn (ap2 TreeEq O O) O))))) ->
  Deriv (atomic (eqn (ap2 TreeEq O O) O))
decode_at_axTreeEqLL_match _ _ = axTreeEqLL

----------------------------------------------------------------------
-- Cong1 / CongL / CongR _match.
--
-- These take the recursively-decoded sub-Deriv as a parameter.  The
-- caller, which has the master decode_at, has already invoked it on
-- y_h_T to extract  Deriv (atomic (eqn t u)) .

decode_at_cong1_match :
  (f : Fun1) (y_h_T : Term) -> IsValue y_h_T ->
  (t u : Term) ->
  Deriv (atomic (eqn t u)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_cong1
                                    (ap2 Pair (codeF1 f) y_h_T)))
                     (codeFormula (atomic (eqn (ap1 f t) (ap1 f u)))))) ->
  Deriv (atomic (eqn (ap1 f t) (ap1 f u)))
decode_at_cong1_match f _ _ t u sub _ = cong1 f sub

decode_at_congL_match :
  (g : Fun2) (xT : Term) -> IsValue xT ->
  (y_h_T : Term) -> IsValue y_h_T ->
  (x t u : Term) -> Eq (code x) xT ->
  Deriv (atomic (eqn t u)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_congL
                                    (ap2 Pair (ap2 Pair (codeF2 g) xT) y_h_T)))
                     (codeFormula (atomic (eqn (ap2 g t x) (ap2 g u x)))))) ->
  Deriv (atomic (eqn (ap2 g t x) (ap2 g u x)))
decode_at_congL_match g _ _ _ _ x t u _ sub _ = congL g x sub

decode_at_congR_match :
  (g : Fun2) (xT : Term) -> IsValue xT ->
  (y_h_T : Term) -> IsValue y_h_T ->
  (x t u : Term) -> Eq (code x) xT ->
  Deriv (atomic (eqn t u)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_congR
                                    (ap2 Pair (ap2 Pair (codeF2 g) xT) y_h_T)))
                     (codeFormula (atomic (eqn (ap2 g x t) (ap2 g x u)))))) ->
  Deriv (atomic (eqn (ap2 g x t) (ap2 g x u)))
decode_at_congR_match g _ _ _ _ x t u _ sub _ = congR g x sub

----------------------------------------------------------------------
-- Truly-recursive rule _match wrappers.
--
-- Caller provides the recursively-decoded sub-Derivs.  Hypothesis is
-- unused (the rule is unconditionally derivable from the sub-Derivs);
-- it is in the signature to pin down the y-shape.

decode_at_ruleSym_match :
  (y_h_T : Term) -> IsValue y_h_T ->
  (t u : Term) ->
  Deriv (atomic (eqn t u)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_ruleSym y_h_T))
                     (codeFormula (atomic (eqn u t))))) ->
  Deriv (atomic (eqn u t))
decode_at_ruleSym_match _ _ t u sub _ = ruleSym sub

decode_at_ruleTrans_match :
  (y1T y2T : Term) -> IsValue y1T -> IsValue y2T ->
  (t u v : Term) ->
  Deriv (atomic (eqn t u)) ->
  Deriv (atomic (eqn u v)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
                     (codeFormula (atomic (eqn t v))))) ->
  Deriv (atomic (eqn t v))
decode_at_ruleTrans_match _ _ _ _ t u v sub1 sub2 _ = ruleTrans sub1 sub2

decode_at_mp_match :
  (y1T y2T : Term) -> IsValue y1T -> IsValue y2T ->
  (P Q : Formula) ->
  Deriv (P imp Q) ->
  Deriv P ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)))
                     (codeFormula Q))) ->
  Deriv Q
decode_at_mp_match _ _ _ _ P Q sub1 sub2 _ = mp sub1 sub2

decode_at_ruleInst_match :
  (y_h_T : Term) -> IsValue y_h_T ->
  (x : Nat) (t : Term) (P : Formula) ->
  Deriv P ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_ruleInst y_h_T))
                     (codeFormula (substF x t P)))) ->
  Deriv (substF x t P)
decode_at_ruleInst_match _ _ x t P sub _ = ruleInst x t sub

decode_at_ruleIndBT_match :
  (y1T y2T : Term) -> IsValue y1T -> IsValue y2T ->
  (P : Formula) (v1 v2 : Nat) ->
  Deriv (substF zero O P) ->
  Deriv ((substF zero (var v1) P) imp
         ((substF zero (var v2) P) imp
          (substF zero (ap2 Pair (var v1) (var v2)) P))) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_ruleIndBT (ap2 Pair y1T y2T)))
                     (codeFormula P))) ->
  Deriv P
decode_at_ruleIndBT_match _ _ _ _ P v1 v2 base step _ =
  ruleIndBT P v1 v2 base step

----------------------------------------------------------------------
-- Meta-level: codeFormula always produces a Pair-shape value, never O.
-- So  treeEq O (codeFormula P) = false  for every P.

codeFormula_not_O : (P : Formula) -> Eq (treeEq O (codeFormula P)) false
codeFormula_not_O (atomic (eqn _ _)) = refl
codeFormula_not_O (not _)            = refl
codeFormula_not_O (_ imp _)          = refl

----------------------------------------------------------------------
-- decode_at_O : the y = O case of the full synthesis.
--
-- thmT(O) = O (via thmT_O_eval); codeFormula P is always a Pair value.
-- So the hypothesis "thmT O = codeFormula P" is contradictory at the
-- equation level, and ineqLemma collapses it to Deriv bot.

decode_at_O :
  (P : Formula) ->
  Deriv (atomic (eqn (ap1 thmT O) (codeFormula P))) ->
  Or (Deriv P) (Deriv bot)
decode_at_O P D =
  inr (decode_at_nomatch_eval O eval_O P (codeFormula_not_O P) D)

----------------------------------------------------------------------
-- decode_bot_via_decode_at : collapse Or output to Deriv bot.
--
-- For decode_at instantiated at P = bot, both branches of the Or
-- produce Deriv bot (the inl branch by definition of bot, the inr
-- branch by ineqLemma).  The collapse is just Or.either id id.

decode_bot_via_decode_at : Or (Deriv bot) (Deriv bot) -> Deriv bot
decode_bot_via_decode_at (inl d) = d
decode_bot_via_decode_at (inr d) = d

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

  -- ruleSym match: caller has a sub-Deriv (Deriv (eqn O O)) and supplies
  -- the encoding hypothesis; we get Deriv (eqn O O) (degenerate swap).
  smokeTest_ruleSym_OO :
    Deriv (atomic (eqn O O)) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_ruleSym O))
                       (codeFormula (atomic (eqn O O))))) ->
    Deriv (atomic (eqn O O))
  smokeTest_ruleSym_OO sub h = decode_at_ruleSym_match O valO O O sub h

  -- mp match at the trivial formula  (atomic (eqn O O)) imp (atomic (eqn O O)) .
  smokeTest_mp_trivial :
    Deriv ((atomic (eqn O O)) imp (atomic (eqn O O))) ->
    Deriv (atomic (eqn O O)) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair O O)))
                       (codeFormula (atomic (eqn O O))))) ->
    Deriv (atomic (eqn O O))
  smokeTest_mp_trivial sub1 sub2 h =
    decode_at_mp_match O O valO valO (atomic (eqn O O)) (atomic (eqn O O))
                       sub1 sub2 h

  -- decode_at_O smoke test at  P = atomic (eqn O O) .  Should return inr.
  smokeTest_decode_at_O :
    Deriv (atomic (eqn (ap1 thmT O)
                       (codeFormula (atomic (eqn O O))))) ->
    Or (Deriv (atomic (eqn O O))) (Deriv bot)
  smokeTest_decode_at_O h = decode_at_O (atomic (eqn O O)) h
