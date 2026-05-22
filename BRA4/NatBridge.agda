{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.NatBridge -- bridge from Pair-coded Terms (= codeTerm /
-- codeFormula outputs) to natCode-shaped Terms.
--
-- The Pair-tree of natCodes produced by codeTerm / codeFormula
-- Deriv-collapses to  natCode (cantor-tower)  via the BRA3 lemma
--  pi_natCode : ap2 pi (natCode x) (natCode y) = natCode (cantor x y) .
-- This lets us put a closed Pair-coded formula into a numeral, which
-- the Goedel diagonal requires when planting a constant into  var 0 .
--
-- Functions:
--   codeFun1Nat    : Fun1    -> Nat
--   codeFun2Nat    : Fun2    -> Nat
--   codeTermNat    : Term    -> Nat
--   codeFormulaNat : Formula -> Nat
--
-- Bridges:
--   codeFun1_eq    : (f : Fun1)    -> Deriv (eqF (codeFun1    f) (natCode (codeFun1Nat    f)))
--   codeFun2_eq    : (g : Fun2)    -> Deriv (eqF (codeFun2    g) (natCode (codeFun2Nat    g)))
--   codeTerm_eq    : (t : Term)    -> Deriv (eqF (codeTerm    t) (natCode (codeTermNat    t)))
--   codeFormula_eq : (F : Formula) -> Deriv (eqF (codeFormula F) (natCode (codeFormulaNat F)))

module BRA4.NatBridge where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

open import BRA3.Code.Tag using ( cantor )
open import BRA3.Numerals using ( pi_natCode )
open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- Pair = pi (BRA3.PairAlgebra) -- so  Pair = ap2 pi  syntactically.
-- pi_natCode  gives the natCode-bridge for any Pair (natCode a) (natCode b).

------------------------------------------------------------------------
-- Mutually-recursive meta-Nat encodings of Fun1 / Fun2.

codeFun1Nat : Fun1 -> Nat
codeFun2Nat : Fun2 -> Nat

codeFun1Nat s             = tag_s
codeFun1Nat o             = tag_o
codeFun1Nat u             = tag_u
codeFun1Nat (C g h1 h2)   = cantor tag_C
                              (cantor (codeFun2Nat g)
                                (cantor (codeFun1Nat h1) (codeFun1Nat h2)))

codeFun2Nat v             = tag_v
codeFun2Nat (R g h1 h2)   = cantor tag_R
                              (cantor (codeFun1Nat g)
                                (cantor (codeFun2Nat h1) (codeFun2Nat h2)))

------------------------------------------------------------------------
-- codeTermNat -- mirror codeTerm's Pair structure with cantor.

codeTermNat : Term -> Nat
codeTermNat O           = zero                                            -- codeTerm O = O = natCode 0
codeTermNat (var k)     = cantor tag_var k
codeTermNat (ap1 f t)   = cantor tag_ap1
                            (cantor (codeFun1Nat f) (codeTermNat t))
codeTermNat (ap2 g a b) = cantor tag_ap2
                            (cantor (codeFun2Nat g)
                              (cantor (codeTermNat a) (codeTermNat b)))

------------------------------------------------------------------------
-- codeFormulaNat.

codeFormulaNat : Formula -> Nat
codeFormulaNat (atomic (eqn a b)) = cantor tag_eq
                                      (cantor (codeTermNat a) (codeTermNat b))
codeFormulaNat (neg p)            = cantor tag_neg (codeFormulaNat p)
codeFormulaNat (imp p q)          = cantor tag_imp
                                      (cantor (codeFormulaNat p)
                                              (codeFormulaNat q))

------------------------------------------------------------------------
-- Deriv-level bridge:  Pair (natCode a) (natCode b) = natCode (cantor a b) .
-- This is exactly  pi_natCode  (since  Pair = pi ).

pi_bridge :
  (x y : Nat) ->
  Deriv (eqF (ap2 Pair (natCode x) (natCode y)) (natCode (cantor x y)))
pi_bridge = pi_natCode

------------------------------------------------------------------------
-- Bridges by structural induction.

codeFun1_eq : (f : Fun1) ->
              Deriv (eqF (codeFun1 f) (natCode (codeFun1Nat f)))
codeFun2_eq : (g : Fun2) ->
              Deriv (eqF (codeFun2 g) (natCode (codeFun2Nat g)))

-- Fun1 base cases (codeFun1 leaf = natCode tag = natCode (codeFun1Nat leaf)).
codeFun1_eq s = axRefl (natCode tag_s)
codeFun1_eq o = axRefl (natCode tag_o)
codeFun1_eq u = axRefl (natCode tag_u)
codeFun1_eq (C g h1 h2) =
  let
    -- codeFun1 (C g h1 h2)
    --   = Pair tag_C (Pair (codeFun2 g) (Pair (codeFun1 h1) (codeFun1 h2)))
    -- Goal:
    --   = natCode (cantor tag_C (cantor (codeFun2Nat g) (cantor (codeFun1Nat h1) (codeFun1Nat h2))))
    inner1 :
      Deriv (eqF (ap2 Pair (codeFun1 h1) (codeFun1 h2))
                  (ap2 Pair (natCode (codeFun1Nat h1)) (natCode (codeFun1Nat h2))))
    inner1 = ruleTrans (congL Pair (codeFun1 h2) (codeFun1_eq h1))
                        (congR Pair (natCode (codeFun1Nat h1)) (codeFun1_eq h2))

    inner1_pi :
      Deriv (eqF (ap2 Pair (codeFun1 h1) (codeFun1 h2))
                  (natCode (cantor (codeFun1Nat h1) (codeFun1Nat h2))))
    inner1_pi = ruleTrans inner1 (pi_bridge (codeFun1Nat h1) (codeFun1Nat h2))

    middle :
      Deriv (eqF (ap2 Pair (codeFun2 g) (ap2 Pair (codeFun1 h1) (codeFun1 h2)))
                  (ap2 Pair (natCode (codeFun2Nat g))
                             (natCode (cantor (codeFun1Nat h1) (codeFun1Nat h2)))))
    middle = ruleTrans
               (congL Pair (ap2 Pair (codeFun1 h1) (codeFun1 h2)) (codeFun2_eq g))
               (congR Pair (natCode (codeFun2Nat g)) inner1_pi)

    middle_pi :
      Deriv (eqF (ap2 Pair (codeFun2 g) (ap2 Pair (codeFun1 h1) (codeFun1 h2)))
                  (natCode (cantor (codeFun2Nat g)
                            (cantor (codeFun1Nat h1) (codeFun1Nat h2)))))
    middle_pi = ruleTrans middle
                  (pi_bridge (codeFun2Nat g)
                              (cantor (codeFun1Nat h1) (codeFun1Nat h2)))

    outer :
      Deriv (eqF (codeFun1 (C g h1 h2))
                  (ap2 Pair (natCode tag_C)
                    (natCode (cantor (codeFun2Nat g)
                              (cantor (codeFun1Nat h1) (codeFun1Nat h2))))))
    outer = congR Pair (natCode tag_C) middle_pi
  in ruleTrans outer
       (pi_bridge tag_C (cantor (codeFun2Nat g)
                          (cantor (codeFun1Nat h1) (codeFun1Nat h2))))

-- Fun2 cases.
codeFun2_eq v = axRefl (natCode tag_v)
codeFun2_eq (R g h1 h2) =
  let
    inner1 :
      Deriv (eqF (ap2 Pair (codeFun2 h1) (codeFun2 h2))
                  (natCode (cantor (codeFun2Nat h1) (codeFun2Nat h2))))
    inner1 = ruleTrans
               (ruleTrans (congL Pair (codeFun2 h2) (codeFun2_eq h1))
                          (congR Pair (natCode (codeFun2Nat h1)) (codeFun2_eq h2)))
               (pi_bridge (codeFun2Nat h1) (codeFun2Nat h2))

    middle :
      Deriv (eqF (ap2 Pair (codeFun1 g) (ap2 Pair (codeFun2 h1) (codeFun2 h2)))
                  (natCode (cantor (codeFun1Nat g)
                            (cantor (codeFun2Nat h1) (codeFun2Nat h2)))))
    middle = ruleTrans
               (ruleTrans (congL Pair (ap2 Pair (codeFun2 h1) (codeFun2 h2)) (codeFun1_eq g))
                          (congR Pair (natCode (codeFun1Nat g)) inner1))
               (pi_bridge (codeFun1Nat g)
                           (cantor (codeFun2Nat h1) (codeFun2Nat h2)))
  in ruleTrans
       (congR Pair (natCode tag_R) middle)
       (pi_bridge tag_R (cantor (codeFun1Nat g)
                          (cantor (codeFun2Nat h1) (codeFun2Nat h2))))

------------------------------------------------------------------------
-- codeTerm bridge.

codeTerm_eq : (t : Term) ->
              Deriv (eqF (codeTerm t) (natCode (codeTermNat t)))

codeTerm_eq O = axRefl O                                                  -- codeTerm O = O = natCode 0

codeTerm_eq (var k) =
  -- codeTerm (var k) = Pair (natCode tag_var) (natCode k)
  pi_bridge tag_var k

codeTerm_eq (ap1 f t) =
  let
    inner :
      Deriv (eqF (ap2 Pair (codeFun1 f) (codeTerm t))
                  (natCode (cantor (codeFun1Nat f) (codeTermNat t))))
    inner = ruleTrans
              (ruleTrans (congL Pair (codeTerm t) (codeFun1_eq f))
                         (congR Pair (natCode (codeFun1Nat f)) (codeTerm_eq t)))
              (pi_bridge (codeFun1Nat f) (codeTermNat t))
  in ruleTrans
       (congR Pair (natCode tag_ap1) inner)
       (pi_bridge tag_ap1 (cantor (codeFun1Nat f) (codeTermNat t)))

codeTerm_eq (ap2 g a b) =
  let
    inner1 :
      Deriv (eqF (ap2 Pair (codeTerm a) (codeTerm b))
                  (natCode (cantor (codeTermNat a) (codeTermNat b))))
    inner1 = ruleTrans
               (ruleTrans (congL Pair (codeTerm b) (codeTerm_eq a))
                          (congR Pair (natCode (codeTermNat a)) (codeTerm_eq b)))
               (pi_bridge (codeTermNat a) (codeTermNat b))

    middle :
      Deriv (eqF (ap2 Pair (codeFun2 g) (ap2 Pair (codeTerm a) (codeTerm b)))
                  (natCode (cantor (codeFun2Nat g)
                            (cantor (codeTermNat a) (codeTermNat b)))))
    middle = ruleTrans
               (ruleTrans (congL Pair (ap2 Pair (codeTerm a) (codeTerm b)) (codeFun2_eq g))
                          (congR Pair (natCode (codeFun2Nat g)) inner1))
               (pi_bridge (codeFun2Nat g)
                           (cantor (codeTermNat a) (codeTermNat b)))
  in ruleTrans
       (congR Pair (natCode tag_ap2) middle)
       (pi_bridge tag_ap2 (cantor (codeFun2Nat g)
                            (cantor (codeTermNat a) (codeTermNat b))))

------------------------------------------------------------------------
-- codeFormula bridge.

codeFormula_eq : (F : Formula) ->
                 Deriv (eqF (codeFormula F) (natCode (codeFormulaNat F)))

codeFormula_eq (atomic (eqn a b)) =
  let
    inner :
      Deriv (eqF (ap2 Pair (codeTerm a) (codeTerm b))
                  (natCode (cantor (codeTermNat a) (codeTermNat b))))
    inner = ruleTrans
              (ruleTrans (congL Pair (codeTerm b) (codeTerm_eq a))
                         (congR Pair (natCode (codeTermNat a)) (codeTerm_eq b)))
              (pi_bridge (codeTermNat a) (codeTermNat b))
  in ruleTrans
       (congR Pair (natCode tag_eq) inner)
       (pi_bridge tag_eq (cantor (codeTermNat a) (codeTermNat b)))

codeFormula_eq (neg p) =
  ruleTrans
    (congR Pair (natCode tag_neg) (codeFormula_eq p))
    (pi_bridge tag_neg (codeFormulaNat p))

codeFormula_eq (imp p q) =
  let
    inner :
      Deriv (eqF (ap2 Pair (codeFormula p) (codeFormula q))
                  (natCode (cantor (codeFormulaNat p) (codeFormulaNat q))))
    inner = ruleTrans
              (ruleTrans (congL Pair (codeFormula q) (codeFormula_eq p))
                         (congR Pair (natCode (codeFormulaNat p)) (codeFormula_eq q)))
              (pi_bridge (codeFormulaNat p) (codeFormulaNat q))
  in ruleTrans
       (congR Pair (natCode tag_imp) inner)
       (pi_bridge tag_imp (cantor (codeFormulaNat p) (codeFormulaNat q)))
