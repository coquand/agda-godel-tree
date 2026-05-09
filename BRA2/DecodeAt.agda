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
-- End-to-end demonstration: recover decode_bot from decode_at via
-- the collapse helper.
--
-- This shows the intended composition pattern:
--   decode_bot_X = decode_bot_via_decode_at (decode_at P D)
-- once the full decode_at synthesis driver is in place.  Until then,
-- only the y = O case is proved here as a working example.

decode_bot_O_via_decode_at :
  Deriv (atomic (eqn (ap1 thmT O) (codeFormula bot))) ->
  Deriv bot
decode_bot_O_via_decode_at D =
  decode_bot_via_decode_at (decode_at_O bot D)

----------------------------------------------------------------------
-- decode_bot via decode_at + per-tag _nomatch wrappers.
--
-- Until the full synthesis driver dispatches automatically, callers
-- can hand-pick the appropriate _nomatch wrapper.  The existing
-- BRA2.DecodeBot.decode_bot_axI_v2 etc. use the same pattern; these
-- are the decode_at-based equivalents.

decode_bot_axI_via_decode_at :
  (xT : Term) -> IsValue xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axI xT)) (codeFormula bot))) ->
  Deriv bot
decode_bot_axI_via_decode_at xT vxT D =
  decode_at_axI_nomatch xT vxT bot refl D

-- axRefl is special: treeEq (Pair xT xT) codeBot = false depends on
-- xT's IsValue structure (not refl in xT), so the meta-witness is a
-- case-split helper.  Mirrors BRA2.DecodeBot.treeEq_axReflRhs_codeBot_false.

private
  treeEq_axRefl_v_codeBot_false :
    (xT : Term) -> IsValue xT ->
    Eq (treeEq (ap2 Pair xT xT) (codeFormula bot)) false
  treeEq_axRefl_v_codeBot_false .O                 valO                = refl
  treeEq_axRefl_v_codeBot_false (ap2 Pair a b)    (valNd .a .b va vb)  = refl

decode_bot_axRefl_via_decode_at :
  (xT : Term) -> IsValue xT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axRefl xT)) (codeFormula bot))) ->
  Deriv bot
decode_bot_axRefl_via_decode_at xT vxT D =
  decode_at_nomatch_eval _ (eval_dispatch_axRefl xT vxT) bot
    (treeEq_axRefl_v_codeBot_false xT vxT) D

decode_bot_axFst_via_decode_at :
  (aT bT : Term) -> IsValue aT -> IsValue bT ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axFst (ap2 Pair aT bT)))
                     (codeFormula bot))) ->
  Deriv bot
decode_bot_axFst_via_decode_at aT bT vaT vbT D =
  decode_at_nomatch_eval _ (eval_dispatch_axFst aT bT vaT vbT) bot refl D

----------------------------------------------------------------------
-- Boolean / treeEq helpers.
--
-- boolAnd_true_split : if  boolAnd b1 b2 = true  then both halves are
-- true.  Used to recover component equalities from  treeEq (Pair a b)
-- (Pair c d) = true .

boolAnd_true_split :
  (b1 b2 : Bool) -> Eq (boolAnd b1 b2) true ->
  Sigma (Eq b1 true) (\ _ -> Eq b2 true)
boolAnd_true_split true  true  refl = mkSigma refl refl
boolAnd_true_split true  false ()
boolAnd_true_split false true  ()
boolAnd_true_split false false ()

----------------------------------------------------------------------
-- treeEq_true_implies_eq : treeEq is correct on values.
--
-- For value-shape Terms u, v (built only from O and ap2 Pair),
--   treeEq u v = true   <==>   Eq u v
-- By induction on IsValue u and IsValue v.

treeEq_true_implies_eq :
  (u v : Term) -> IsValue u -> IsValue v ->
  Eq (treeEq u v) true -> Eq u v
treeEq_true_implies_eq .O                   .O                   valO              valO              _   = refl
treeEq_true_implies_eq .O                   .(ap2 Pair _ _)      valO              (valNd _ _ _ _)   ()
treeEq_true_implies_eq .(ap2 Pair _ _)      .O                   (valNd _ _ _ _)   valO              ()
treeEq_true_implies_eq (ap2 Pair a b)       (ap2 Pair c d)       (valNd .a .b va vb) (valNd .c .d vc vd) eqp =
  let split = boolAnd_true_split (treeEq a c) (treeEq b d) eqp
      eqAC : Eq a c
      eqAC = treeEq_true_implies_eq a c va vc (fst split)
      eqBD : Eq b d
      eqBD = treeEq_true_implies_eq b d vb vd (snd split)
  in eqCong2 (ap2 Pair) eqAC eqBD

----------------------------------------------------------------------
-- Or eliminator (top-level, since where-bound helpers don't propagate
-- to inner where-blocks in Agda).

caseOr : {A B C : Set} -> Or A B -> (A -> C) -> (B -> C) -> C
caseOr (inl a) f g = f a
caseOr (inr b) f g = g b

----------------------------------------------------------------------
-- decode_nat : invert  natCode  on Pair-shape value chains.
--
-- natCode n  is built as (Pair O (Pair O ... O)) -- a chain of n
-- nested  Pair O _  layers ending in O.  decode_nat takes a value
-- xT and returns either a Nat n with  natCode n = xT , or  inr tt
-- if the structure isn't a natCode chain.

decode_nat : (xT : Term) -> IsValue xT ->
             Or (Sigma Nat (\ n -> Eq (natCode n) xT)) Unit
decode_nat .O                          valO                       =
  inl (mkSigma zero refl)
decode_nat .(ap2 Pair O b)             (valNd .O b valO vb)       =
  caseOr (decode_nat b vb)
    (\ s -> inl (mkSigma (suc (fst s)) (eqCong (\ x -> ap2 Pair O x) (snd s))))
    (\ _ -> inr tt)
decode_nat .(ap2 Pair (ap2 Pair _ _) _) (valNd .(ap2 Pair _ _) _ (valNd _ _ _ _) _) =
  inr tt

----------------------------------------------------------------------
-- decode_term_atom : invert  code  on the simplest cases (O and
-- var n).
--
-- code O = O.
-- code (var n) = ap2 Pair tagVar (natCode n) where
--   tagVar = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O.
--
-- This stub handles those two; decoding ap1/ap2 requires inverting
-- codeF1 / codeF2, which is a separate piece (each functor is a
-- specific value of  natCode  + extra structure).
--
-- Returns inr if xT doesn't decode to O or var n; the FULL decode_term
-- would handle that branch by attempting ap1/ap2 inversion.

decode_term_O_or_var :
  (xT : Term) -> IsValue xT ->
  Or (Sigma Term (\ t -> Eq (code t) xT)) Unit
decode_term_O_or_var .O valO = inl (mkSigma O refl)
decode_term_O_or_var (ap2 Pair tagT rest) (valNd .tagT .rest vtagT vrest) =
  goVar (treeEq tagT tagVar) refl
  where
    -- Match against tagVar.  If treeEq tagT tagVar = true, treeEq's
    -- correctness on values (treeEq_true_implies_eq) gives  Eq tagT
    -- tagVar ; we then decode rest as a natCode and emerge with
    -- (var n , code (var n) = xT).
    --
    -- If treeEq is false, fall through to the tagAp1 dispatcher
    -- (handled by decode_term_full below).  This O_or_var stub stops
    -- here with  inr tt .
    goVar : (b : Bool) -> Eq (treeEq tagT tagVar) b ->
            Or (Sigma Term (\ t -> Eq (code t) (ap2 Pair tagT rest))) Unit
    goVar true  eqTrue =
      let
        eqTagT_tagVar : Eq tagT tagVar
        eqTagT_tagVar = treeEq_true_implies_eq tagT tagVar vtagT tagVar_isValue eqTrue

        natRec : Or (Sigma Nat (\ n -> Eq (natCode n) rest)) Unit
        natRec = decode_nat rest vrest
      in caseOr natRec
           (\ s ->
              let
                n : Nat
                n = fst s

                eq_natCode_n_rest : Eq (natCode n) rest
                eq_natCode_n_rest = snd s

                eq_codeVar_xT :
                  Eq (code (var n)) (ap2 Pair tagT rest)
                eq_codeVar_xT =
                  eqCong2 (ap2 Pair) (eqSym eqTagT_tagVar) eq_natCode_n_rest
              in inl (mkSigma (var n) eq_codeVar_xT))
           (\ _ -> inr tt)
    goVar false _ = inr tt

----------------------------------------------------------------------
-- decodeF1_I : recognise codeF1 I.
--
-- codeF1 I  is a specific value (a Pair with natCode 25 and lf inside).
-- treeEq comparison is decidable; if true, we recover Eq xT (codeF1 I)
-- and emerge with (I , Eq (codeF1 I) xT).

decodeF1_I :
  (xT : Term) -> IsValue xT ->
  Or (Eq (codeF1 I) xT) Unit
decodeF1_I xT vxT =
  goI (treeEq xT (codeF1 I)) refl
  where
    goI : (b : Bool) -> Eq (treeEq xT (codeF1 I)) b ->
          Or (Eq (codeF1 I) xT) Unit
    goI true  eqTrue =
      inl (eqSym (treeEq_true_implies_eq xT (codeF1 I)
                     vxT (codeF1_isValue I) eqTrue))
    goI false _ = inr tt

----------------------------------------------------------------------
-- decodeF1_atomic : recognise codeF1 X for X in {I, Fst, Snd, Z}.
--
-- Each atomic Fun1 has a specific codeF1 value (a Pair (natCode k) lf
-- for a tag-specific k).  We try each via treeEq dispatch.  The
-- recursive Comp / Comp2 cases are not in scope here -- they require
-- recursive structural inversion of the inner functor codes, and live
-- in a future decodeF1_full.

decodeF1_atomic :
  (xT : Term) -> IsValue xT ->
  Or (Sigma Fun1 (\ f -> Eq (codeF1 f) xT)) Unit
decodeF1_atomic xT vxT =
  goI (treeEq xT (codeF1 I)) refl
  where
    matchHit : (f : Fun1) -> Eq (treeEq xT (codeF1 f)) true ->
               Sigma Fun1 (\ g -> Eq (codeF1 g) xT)
    matchHit f eq =
      mkSigma f (eqSym (treeEq_true_implies_eq xT (codeF1 f)
                          vxT (codeF1_isValue f) eq))

    goZ : (b : Bool) -> Eq (treeEq xT (codeF1 Z)) b ->
          Or (Sigma Fun1 (\ f -> Eq (codeF1 f) xT)) Unit
    goZ true  eq = inl (matchHit Z eq)
    goZ false _  = inr tt

    goSnd : (b : Bool) -> Eq (treeEq xT (codeF1 Snd)) b ->
            Or (Sigma Fun1 (\ f -> Eq (codeF1 f) xT)) Unit
    goSnd true  eq = inl (matchHit Snd eq)
    goSnd false _  = goZ (treeEq xT (codeF1 Z)) refl

    goFst : (b : Bool) -> Eq (treeEq xT (codeF1 Fst)) b ->
            Or (Sigma Fun1 (\ f -> Eq (codeF1 f) xT)) Unit
    goFst true  eq = inl (matchHit Fst eq)
    goFst false _  = goSnd (treeEq xT (codeF1 Snd)) refl

    goI : (b : Bool) -> Eq (treeEq xT (codeF1 I)) b ->
          Or (Sigma Fun1 (\ f -> Eq (codeF1 f) xT)) Unit
    goI true  eq = inl (matchHit I eq)
    goI false _  = goFst (treeEq xT (codeF1 Fst)) refl

----------------------------------------------------------------------
-- decodeF2_atomic : recognise codeF2 X for X in {Pair, Const, IfLf,
-- TreeEq}.  Same pattern as decodeF1_atomic.  Lift / Post / Fan /
-- treeRec recurse on inner Fun1 / Fun2 codes and live in a future
-- decodeF2_full.

decodeF2_atomic :
  (xT : Term) -> IsValue xT ->
  Or (Sigma Fun2 (\ g -> Eq (codeF2 g) xT)) Unit
decodeF2_atomic xT vxT =
  goPair (treeEq xT (codeF2 Pair)) refl
  where
    matchHit2 : (g : Fun2) -> Eq (treeEq xT (codeF2 g)) true ->
                Sigma Fun2 (\ g' -> Eq (codeF2 g') xT)
    matchHit2 g eq =
      mkSigma g (eqSym (treeEq_true_implies_eq xT (codeF2 g)
                          vxT (codeF2_isValue g) eq))

    goTreeEq : (b : Bool) -> Eq (treeEq xT (codeF2 TreeEq)) b ->
               Or (Sigma Fun2 (\ g -> Eq (codeF2 g) xT)) Unit
    goTreeEq true  eq = inl (matchHit2 TreeEq eq)
    goTreeEq false _  = inr tt

    goIfLf : (b : Bool) -> Eq (treeEq xT (codeF2 IfLf)) b ->
             Or (Sigma Fun2 (\ g -> Eq (codeF2 g) xT)) Unit
    goIfLf true  eq = inl (matchHit2 IfLf eq)
    goIfLf false _  = goTreeEq (treeEq xT (codeF2 TreeEq)) refl

    goConst : (b : Bool) -> Eq (treeEq xT (codeF2 Const)) b ->
              Or (Sigma Fun2 (\ g -> Eq (codeF2 g) xT)) Unit
    goConst true  eq = inl (matchHit2 Const eq)
    goConst false _  = goIfLf (treeEq xT (codeF2 IfLf)) refl

    goPair : (b : Bool) -> Eq (treeEq xT (codeF2 Pair)) b ->
             Or (Sigma Fun2 (\ g -> Eq (codeF2 g) xT)) Unit
    goPair true  eq = inl (matchHit2 Pair eq)
    goPair false _  = goConst (treeEq xT (codeF2 Const)) refl

----------------------------------------------------------------------
-- decode_term : full inversion of  code  on value-shape Terms.
--
-- This handles three of the four code clauses:
--   * code O           = O                              [done]
--   * code (var n)     = ap2 Pair tagVar (natCode n)    [done]
--   * code (ap1 I t)   = ap2 Pair tagAp1 (ap2 Pair (codeF1 I) (code t))
--                         [done -- recurses on code t]
--
-- The fourth clause (code (ap2 g t1 t2) and code (ap1 (Comp _ _) t)
-- etc.) requires a full Fun1 / Fun2 inverter; that is the next piece
-- but is not delivered here.  In its absence, decode_term returns
-- inr tt  for those cases.

decode_term :
  (xT : Term) -> IsValue xT ->
  Or (Sigma Term (\ t -> Eq (code t) xT)) Unit
decode_term .O valO = inl (mkSigma O refl)

-- Case  rest = O .  Var-case for natCode 0 ; ap1/ap2 don't fit.
decode_term (ap2 Pair tagT O) (valNd .tagT .O vtagT valO) =
  goVar (treeEq tagT tagVar) refl
  where
    goVar : (b : Bool) -> Eq (treeEq tagT tagVar) b ->
            Or (Sigma Term (\ t -> Eq (code t) (ap2 Pair tagT O))) Unit
    goVar true  eqTrue =
      let
        eqTagT_tagVar : Eq tagT tagVar
        eqTagT_tagVar = treeEq_true_implies_eq tagT tagVar vtagT tagVar_isValue eqTrue

        eq_codeVar_xT : Eq (code (var zero)) (ap2 Pair tagT O)
        eq_codeVar_xT = eqCong (\ x -> ap2 Pair x O) (eqSym eqTagT_tagVar)
      in inl (mkSigma (var zero) eq_codeVar_xT)
    goVar false _ = inr tt

-- Case  rest = ap2 Pair restL (ap2 Pair codeT1 codeT2) -- the ap2
-- shape (also matches var/ap1 with deeper natCode/codeT structure).
-- Tries ap2 first (most specific); falls through to var/ap1 branches.
decode_term (ap2 Pair tagT (ap2 Pair restL (ap2 Pair codeT1 codeT2)))
            (valNd .tagT .(ap2 Pair restL (ap2 Pair codeT1 codeT2)) vtagT
                   (valNd .restL .(ap2 Pair codeT1 codeT2) vrestL
                          (valNd .codeT1 .codeT2 vcodeT1 vcodeT2))) =
  goVar (treeEq tagT tagVar) refl
  where
    -- Outer Pair structure: ap2 Pair tagT (ap2 Pair restL (ap2 Pair codeT1 codeT2))
    -- Three matches to try: tagVar (var), tagAp1 (ap1), tagAp2 (ap2).
    OuterT : Term
    OuterT = ap2 Pair tagT (ap2 Pair restL (ap2 Pair codeT1 codeT2))

    goAp2 : (b : Bool) -> Eq (treeEq tagT tagAp2) b ->
            Or (Sigma Term (\ t -> Eq (code t) OuterT)) Unit
    goAp2 false _ = inr tt
    goAp2 true  eqTrue =
      let
        eqTagT_tagAp2 : Eq tagT tagAp2
        eqTagT_tagAp2 = treeEq_true_implies_eq tagT tagAp2 vtagT tagAp2_isValue eqTrue

        codeF2_decision : Or (Sigma Fun2 (\ g -> Eq (codeF2 g) restL)) Unit
        codeF2_decision = decodeF2_atomic restL vrestL

        codeT1_decision : Or (Sigma Term (\ t -> Eq (code t) codeT1)) Unit
        codeT1_decision = decode_term codeT1 vcodeT1

        codeT2_decision : Or (Sigma Term (\ t -> Eq (code t) codeT2)) Unit
        codeT2_decision = decode_term codeT2 vcodeT2
      in caseOr codeF2_decision
           (\ sg ->
              caseOr codeT1_decision
                (\ st1 ->
                   caseOr codeT2_decision
                     (\ st2 ->
                        let
                          g  = fst sg
                          eq_codeF2g_restL = snd sg
                          t1 = fst st1
                          eq_code_t1 = snd st1
                          t2 = fst st2
                          eq_code_t2 = snd st2

                          eq_codeAp2_outerT :
                            Eq (code (ap2 g t1 t2)) OuterT
                          eq_codeAp2_outerT =
                            eqCong2 (ap2 Pair) (eqSym eqTagT_tagAp2)
                              (eqCong2 (ap2 Pair) eq_codeF2g_restL
                                (eqCong2 (ap2 Pair) eq_code_t1 eq_code_t2))
                        in inl (mkSigma (ap2 g t1 t2) eq_codeAp2_outerT))
                     (\ _ -> inr tt))
                (\ _ -> inr tt))
           (\ _ -> inr tt)

    -- ap1 case in the ap2-shaped clause would recurse on
    -- (ap2 Pair codeT1 codeT2) , which Agda's termination checker
    -- doesn't accept here (the reconstructed sub-IsValue isn't
    -- recognised as structurally smaller).  We fall through to the
    -- ap2 attempt, which only recurses on the directly-pattern-matched
    -- codeT1 / codeT2 sub-IsValues.  Net effect: nested ap1 like
    -- code (ap1 I (ap1 I O)) is not decoded by this clause; future
    -- work will lift this restriction.
    goAp1 : (b : Bool) -> Eq (treeEq tagT tagAp1) b ->
            Or (Sigma Term (\ t -> Eq (code t) OuterT)) Unit
    goAp1 false _ = goAp2 (treeEq tagT tagAp2) refl
    goAp1 true  _ = inr tt

    goVar : (b : Bool) -> Eq (treeEq tagT tagVar) b ->
            Or (Sigma Term (\ t -> Eq (code t) OuterT)) Unit
    goVar true  eqTrue =
      let
        eqTagT_tagVar : Eq tagT tagVar
        eqTagT_tagVar = treeEq_true_implies_eq tagT tagVar vtagT tagVar_isValue eqTrue

        natRec : Or (Sigma Nat (\ n -> Eq (natCode n) (ap2 Pair restL (ap2 Pair codeT1 codeT2)))) Unit
        natRec = decode_nat (ap2 Pair restL (ap2 Pair codeT1 codeT2))
                            (valNd restL (ap2 Pair codeT1 codeT2) vrestL
                                   (valNd codeT1 codeT2 vcodeT1 vcodeT2))
      in caseOr natRec
           (\ s ->
              let n = fst s
                  eqNC = snd s
                  eq_codeVar_outerT : Eq (code (var n)) OuterT
                  eq_codeVar_outerT = eqCong2 (ap2 Pair) (eqSym eqTagT_tagVar) eqNC
              in inl (mkSigma (var n) eq_codeVar_outerT))
           (\ _ -> inr tt)
    goVar false _ = goAp1 (treeEq tagT tagAp1) refl

-- Case  rest = ap2 Pair restL O .  Var with natCode (suc 0), or ap1
-- with codeT = O.  No ap2 case here (ap2 needs restR = Pair).
decode_term (ap2 Pair tagT (ap2 Pair restL O))
            (valNd .tagT .(ap2 Pair restL O) vtagT
                   (valNd .restL .O vrestL valO)) =
  goVar (treeEq tagT tagVar) refl
  where
    OuterT : Term
    OuterT = ap2 Pair tagT (ap2 Pair restL O)

    goAp1 : (b : Bool) -> Eq (treeEq tagT tagAp1) b ->
            Or (Sigma Term (\ t -> Eq (code t) OuterT)) Unit
    goAp1 false _ = inr tt
    goAp1 true eqTrue =
      let
        eqTagT_tagAp1 : Eq tagT tagAp1
        eqTagT_tagAp1 = treeEq_true_implies_eq tagT tagAp1 vtagT tagAp1_isValue eqTrue

        codeF_decision : Or (Sigma Fun1 (\ f -> Eq (codeF1 f) restL)) Unit
        codeF_decision = decodeF1_atomic restL vrestL

        -- restR = O; code O = O, so we can decode codeT = O to t = O.
        codeT_decision : Or (Sigma Term (\ t -> Eq (code t) O)) Unit
        codeT_decision = decode_term O valO
      in caseOr codeF_decision
           (\ sf ->
              caseOr codeT_decision
                (\ st ->
                   let f = fst sf
                       eq_codeF1f_restL = snd sf
                       t = fst st
                       eq_code_t_O = snd st
                       eq_codeAp1_outerT :
                         Eq (code (ap1 f t)) OuterT
                       eq_codeAp1_outerT =
                         eqCong2 (ap2 Pair) (eqSym eqTagT_tagAp1)
                           (eqCong2 (ap2 Pair) eq_codeF1f_restL eq_code_t_O)
                   in inl (mkSigma (ap1 f t) eq_codeAp1_outerT))
                (\ _ -> inr tt))
           (\ _ -> inr tt)

    goVar : (b : Bool) -> Eq (treeEq tagT tagVar) b ->
            Or (Sigma Term (\ t -> Eq (code t) OuterT)) Unit
    goVar true  eqTrue =
      let
        eqTagT_tagVar : Eq tagT tagVar
        eqTagT_tagVar = treeEq_true_implies_eq tagT tagVar vtagT tagVar_isValue eqTrue

        natRec : Or (Sigma Nat (\ n -> Eq (natCode n) (ap2 Pair restL O))) Unit
        natRec = decode_nat (ap2 Pair restL O) (valNd restL O vrestL valO)
      in caseOr natRec
           (\ s ->
              let n = fst s
                  eqNC = snd s
                  eq_codeVar_outerT : Eq (code (var n)) OuterT
                  eq_codeVar_outerT = eqCong2 (ap2 Pair) (eqSym eqTagT_tagVar) eqNC
              in inl (mkSigma (var n) eq_codeVar_outerT))
           (\ _ -> inr tt)
    goVar false _ = goAp1 (treeEq tagT tagAp1) refl

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

  -- decode_nat at natCode 0 = O: decodes to n = 0.
  smokeTest_decode_nat_zero :
    Or (Sigma Nat (\ n -> Eq (natCode n) O)) Unit
  smokeTest_decode_nat_zero = decode_nat O valO

  -- decode_nat at natCode 2 = Pair O (Pair O O): decodes to n = 2.
  smokeTest_decode_nat_two :
    Or (Sigma Nat (\ n -> Eq (natCode n) (ap2 Pair O (ap2 Pair O O)))) Unit
  smokeTest_decode_nat_two =
    decode_nat (ap2 Pair O (ap2 Pair O O))
               (valNd O (ap2 Pair O O) valO (valNd O O valO valO))

  -- decode_term_O_or_var on  code (var zero) : decodes to var zero.
  -- code (var zero) = ap2 Pair tagVar O.
  smokeTest_decode_term_var_zero :
    Or (Sigma Term (\ t -> Eq (code t) (code (var zero)))) Unit
  smokeTest_decode_term_var_zero =
    decode_term_O_or_var (code (var zero))
                         (valNd tagVar O tagVar_isValue valO)

  -- Full decode_term on  code (var zero) : decodes to var zero.
  smokeTest_decode_term_full_var_zero :
    Or (Sigma Term (\ t -> Eq (code t) (code (var zero)))) Unit
  smokeTest_decode_term_full_var_zero =
    decode_term (code (var zero)) (valNd tagVar O tagVar_isValue valO)

  -- Full decode_term on  code (ap1 I O) : decodes to ap1 I O via the
  -- ap1-branch with recursive call on code O = O.
  -- code (ap1 I O) = ap2 Pair tagAp1 (ap2 Pair (codeF1 I) O).
  smokeTest_decode_term_apI_O :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap1 I O)))) Unit
  smokeTest_decode_term_apI_O =
    decode_term (code (ap1 I O))
      (valNd tagAp1 (ap2 Pair (codeF1 I) O) tagAp1_isValue
        (valNd (codeF1 I) O (codeF1_isValue I) valO))

  -- Full decode_term on  code (ap1 I (ap1 I O)) : nested recursion.
  smokeTest_decode_term_apI_apI_O :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap1 I (ap1 I O))))) Unit
  smokeTest_decode_term_apI_apI_O =
    decode_term (code (ap1 I (ap1 I O)))
      (valNd tagAp1 (ap2 Pair (codeF1 I) (code (ap1 I O))) tagAp1_isValue
        (valNd (codeF1 I) (code (ap1 I O)) (codeF1_isValue I)
          (valNd tagAp1 (ap2 Pair (codeF1 I) O) tagAp1_isValue
            (valNd (codeF1 I) O (codeF1_isValue I) valO))))

  -- Full decode_term on  code (ap1 Fst O) : exercises the Fst branch
  -- of decodeF1_atomic.
  smokeTest_decode_term_apFst_O :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap1 Fst O)))) Unit
  smokeTest_decode_term_apFst_O =
    decode_term (code (ap1 Fst O))
      (valNd tagAp1 (ap2 Pair (codeF1 Fst) O) tagAp1_isValue
        (valNd (codeF1 Fst) O (codeF1_isValue Fst) valO))

  -- ap1 Snd O : exercises the Snd branch.
  smokeTest_decode_term_apSnd_O :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap1 Snd O)))) Unit
  smokeTest_decode_term_apSnd_O =
    decode_term (code (ap1 Snd O))
      (valNd tagAp1 (ap2 Pair (codeF1 Snd) O) tagAp1_isValue
        (valNd (codeF1 Snd) O (codeF1_isValue Snd) valO))

  -- ap1 Z O : exercises the Z branch.
  smokeTest_decode_term_apZ_O :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap1 Z O)))) Unit
  smokeTest_decode_term_apZ_O =
    decode_term (code (ap1 Z O))
      (valNd tagAp1 (ap2 Pair (codeF1 Z) O) tagAp1_isValue
        (valNd (codeF1 Z) O (codeF1_isValue Z) valO))

  -- ap2 Pair O O : exercises the ap2 branch with decodeF2_atomic +
  -- recursive decoding of two sub-Terms.
  smokeTest_decode_term_apPair_OO :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap2 Pair O O)))) Unit
  smokeTest_decode_term_apPair_OO =
    decode_term (code (ap2 Pair O O))
      (valNd tagAp2 (ap2 Pair (codeF2 Pair) (ap2 Pair O O)) tagAp2_isValue
        (valNd (codeF2 Pair) (ap2 Pair O O) (codeF2_isValue Pair)
          (valNd O O valO valO)))

  -- ap2 IfLf O O : exercises the IfLf branch.
  smokeTest_decode_term_apIfLf_OO :
    Or (Sigma Term (\ t -> Eq (code t) (code (ap2 IfLf O O)))) Unit
  smokeTest_decode_term_apIfLf_OO =
    decode_term (code (ap2 IfLf O O))
      (valNd tagAp2 (ap2 Pair (codeF2 IfLf) (ap2 Pair O O)) tagAp2_isValue
        (valNd (codeF2 IfLf) (ap2 Pair O O) (codeF2_isValue IfLf)
          (valNd O O valO valO)))
