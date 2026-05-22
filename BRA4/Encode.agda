{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Encode -- meta-Agda encoder  encode : {P : Formula} -> Deriv P -> Term .
--
-- Produces the Pair-tree code of a derivation, in the format the BRA4
-- thmT verifier (BRA4.ThmT) dispatches on.
--
-- TOP-LEVEL RULE TAGS:
--   tag_ax  : axiom case   (Pair tag_ax (Pair (natCode <idx>) extra))
--   tag_sb  : ruleInst     (Pair tag_sb (Pair (Pair (natCode k) substituent) inner))
--   tag_mp  : modus ponens (Pair tag_mp (Pair (encode dPQ) (encode dP)))
--   tag_ind : ruleIndNat   (Pair tag_ind (Pair (encode dB) (encode dS)))
--
-- AXIOM TAGS (inside the  Pair tag_ax (Pair (natCode <idx>) extra)  layer):
--
--    0  ax_succ_nonzero       extra = O                     (no params)
--    1  ax_o                  extra = O                     (sb-wraps t)
--    2  ax_u                  extra = O                     (sb-wraps t)
--    3  ax_v                  extra = O                     (sb-wraps a, b)
--    4  ax_eqTrans            extra = O                     (sb-wraps x, y, z)
--    5  ax_eqCong1            extra = codeFun1 f            (sb-wraps a, b)
--    6  ax_eqCongL            extra = codeFun2 g            (sb-wraps a, b, c)
--    7  ax_eqCongR            extra = codeFun2 g            (sb-wraps a, b, c)
--    8  ax_C                  extra = codeFun1 (C g h1 h2)  (sb-wraps t)
--    9  ax_R_base             extra = codeFun2 (R g h1 h2)  (sb-wraps x)
--   10  ax_R_step             extra = codeFun2 (R g h1 h2)  (sb-wraps x, n)
--   11  axK                   extra = Pair codeA codeB      (formula params, no sb)
--   12  axS                   extra = Pair codeA (Pair codeB codeC)
--   13  axNeg                 extra = Pair codeA codeB
--
-- Axioms 1..10 use the SCHEMA-SB encoding: the axiom closure outputs
-- the schema  codeFormula(SCHEMA-of-axN)  with var-0,var-1,var-2 placeholders,
-- and the sb-wrapping invokes  sbf  at each Term parameter via  thmT_at_sb .
--
-- See  BRA4.ThmT.axBranchN  for the schemas these correspond to and
-- BRA4.ThmTAtAxN  closures for the per-axiom Deriv equations.

module BRA4.Encode where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA3.RuleInst2 using ( maxN ; maxVarT )

------------------------------------------------------------------------
-- Helpers.

private
  pack : Nat -> Term -> Term
  pack k x = ap2 Pair (natCode k) x

  packAx : Nat -> Term -> Term
  packAx idx body = pack tag_ax (pack idx body)

  -- sb-wrapping: encode a  ruleInst k t  application around an inner
  -- already-encoded code  inner .
  encode_sb : Nat -> Term -> Term -> Term
  encode_sb k t inner = pack tag_sb (ap2 Pair (ap2 Pair (natCode k) t) inner)

------------------------------------------------------------------------
-- encode : Deriv P -> Term .

encode : {P : Formula} -> Deriv P -> Term

------------------------------------------------------------------------
-- Axiom 0 :  ~ s O = O .  No params.

encode ax_succ_nonzero =
  packAx 0 O

------------------------------------------------------------------------
-- Axiom 1 :  o(x_1) = O .  Schema:  o(var 0) = O .
-- encode (ax_o t) =  sb 0 (codeTerm t) <packAx 1 O> .

encode (ax_o t) =
  encode_sb zero (codeTerm t) (packAx 1 O)

------------------------------------------------------------------------
-- Axiom 2 :  u(x_1) = x_1 .  Schema:  u(var 0) = var 0 .

encode (ax_u t) =
  encode_sb zero (codeTerm t) (packAx 2 O)

------------------------------------------------------------------------
-- Axiom 3 :  v(x_1, x_2) = x_2 .  Schema:  v(var 0, var 1) = var 1 .
--
-- Closed-free encoding via 3-step substitution composition (Church
-- standard metatheorem VII / BRA3.RuleInst2 pattern).  Pick a fresh
-- index  c  with  c >= 2  AND  c > maxVarT a , then :
--   1. sb (var 1) -> (codeTerm (var c))     [alpha-rename schema's var 1]
--   2. sb (var 0) -> (codeTerm a)
--   3. sb (var c) -> (codeTerm b)
-- After cascade, thmT outputs
--   codeFormula (substF c b (substF 0 a (substF 1 (var c) SCHEMA)))
-- = codeFormula (atomic (eqn (ap2 v a b) b))    by substT_above_max
-- WITHOUT any  Closed a  premise.

encode (ax_v a b) =
  let c : Nat
      c = maxN (suc (suc zero)) (maxVarT a)
  in encode_sb c (codeTerm b)
       (encode_sb zero (codeTerm a)
         (encode_sb (suc zero) (codeTerm (var c)) (packAx 3 O)))

------------------------------------------------------------------------
-- Axiom 4 :  x_1 = x_2 > . x_1 = x_3 > x_2 = x_3 .

-- Closed-free encoding via 5-step composition.
-- c1 = maxN 3 (maxN (maxVarT x) (maxVarT y)) ;  c2 = suc c1 .

encode (ax_eqTrans x y z) =
  let c1 : Nat
      c1 = maxN (suc (suc (suc zero))) (maxN (maxVarT x) (maxVarT y))
      c2 : Nat
      c2 = suc c1
  in encode_sb c2 (codeTerm z)
       (encode_sb c1 (codeTerm y)
         (encode_sb zero (codeTerm x)
           (encode_sb (suc (suc zero)) (codeTerm (var c2))
             (encode_sb (suc zero) (codeTerm (var c1)) (packAx 4 O)))))

------------------------------------------------------------------------
-- Axiom 5 :  x_1 = x_2 > f(x_1) = f(x_2) .  extra = codeFun1 f .
-- Closed-free encoding via 3-step composition  (c = maxN 2 (maxVarT a)) .

encode (ax_eqCong1 f a b) =
  let c : Nat
      c = maxN (suc (suc zero)) (maxVarT a)
  in encode_sb c (codeTerm b)
       (encode_sb zero (codeTerm a)
         (encode_sb (suc zero) (codeTerm (var c)) (packAx 5 (codeFun1 f))))

------------------------------------------------------------------------
-- Axiom 6 :  x_1 = x_2 > g(x_1, x_3) = g(x_2, x_3) .

-- Closed-free encoding via 5-step composition.

encode (ax_eqCongL g a b c) =
  let c1 : Nat
      c1 = maxN (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
      c2 : Nat
      c2 = suc c1
  in encode_sb c2 (codeTerm c)
       (encode_sb c1 (codeTerm b)
         (encode_sb zero (codeTerm a)
           (encode_sb (suc (suc zero)) (codeTerm (var c2))
             (encode_sb (suc zero) (codeTerm (var c1)) (packAx 6 (codeFun2 g))))))

------------------------------------------------------------------------
-- Axiom 7 :  x_1 = x_2 > g(x_3, x_1) = g(x_3, x_2) .

-- Closed-free encoding via 5-step composition.

encode (ax_eqCongR g a b c) =
  let c1 : Nat
      c1 = maxN (suc (suc (suc zero))) (maxN (maxVarT a) (maxVarT b))
      c2 : Nat
      c2 = suc c1
  in encode_sb c2 (codeTerm c)
       (encode_sb c1 (codeTerm b)
         (encode_sb zero (codeTerm a)
           (encode_sb (suc (suc zero)) (codeTerm (var c2))
             (encode_sb (suc zero) (codeTerm (var c1)) (packAx 7 (codeFun2 g))))))

------------------------------------------------------------------------
-- Axiom 8 :  C g h1 h2 (x) = g(h1(x), h2(x)) .  extra = codeFun1 (C g h1 h2) .

encode (ax_C g h1 h2 t) =
  encode_sb zero (codeTerm t) (packAx 8 (codeFun1 (C g h1 h2)))

------------------------------------------------------------------------
-- Axiom 9 :  R g h1 h2 (x, O) = g(x) .  extra = codeFun2 (R g h1 h2) .

encode (ax_R_base g h1 h2 x) =
  encode_sb zero (codeTerm x) (packAx 9 (codeFun2 (R g h1 h2)))

------------------------------------------------------------------------
-- Axiom 10 :  R g h1 h2 (x, s n) = h1(h2(x, n), R g h1 h2(x, n)) .

-- Closed-free encoding via 3-step composition  (c = maxN 2 (maxVarT x)) .

encode (ax_R_step g h1 h2 x n) =
  let c : Nat
      c = maxN (suc (suc zero)) (maxVarT x)
  in encode_sb c (codeTerm n)
       (encode_sb zero (codeTerm x)
         (encode_sb (suc zero) (codeTerm (var c))
           (packAx 10 (codeFun2 (R g h1 h2)))))

------------------------------------------------------------------------
-- Axioms 11..13 : pure formula axioms.  No Term parameters, no sb.

encode (axK A B) =
  packAx 11 (ap2 Pair (codeFormula A) (codeFormula B))

encode (axS A B Cf) =
  packAx 12 (ap2 Pair (codeFormula A)
              (ap2 Pair (codeFormula B) (codeFormula Cf)))

encode (axNeg A B) =
  packAx 13 (ap2 Pair (codeFormula A) (codeFormula B))

------------------------------------------------------------------------
-- Rules.

encode (mp dPQ dP) =
  pack tag_mp (ap2 Pair (encode dPQ) (encode dP))

encode (ruleInst k t dP) =
  pack tag_sb (ap2 Pair (ap2 Pair (natCode k) (codeTerm t))
                          (encode dP))

encode (ruleIndNat k {P} dB dS) =
  pack tag_ind (ap2 Pair (encode dB) (encode dS))
