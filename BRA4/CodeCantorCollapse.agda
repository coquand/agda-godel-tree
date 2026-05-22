{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CodeCantorCollapse -- the codeX-to-natCode collapse lemma.
--
-- Every  codeFun1 f , codeFun2 g , codeTerm t , codeFormula P  is a
-- Pair-tree built from  natCode -leaves via  ap2 pi .  By BRA3's
--  pi_natCode  axiom, every such Pair-tree =Deriv= natCode of some
-- specific cantor-computed Nat.  This module ships the closed-form
-- Deriv-equations.
--
-- Primary use : the  natEqF  comparator in BRA4's  thmT  mp / ind
-- branches accepts ONLY  natCode -encoded inputs.  To make the
-- well-formedness check fire on  codeFormula -encoded antecedents,
-- the closure proofs of  thmT_at_mp / thmT_at_ind  rewrite both
-- arguments of  natEqF  to  natCode k  via these collapse lemmas,
-- then  natEq_eq k  fires  sO .

module BRA4.CodeCantorCollapse where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

open import BRA3.Church          using ( pi )
open import BRA3.Numerals        using ( pi_natCode )
open import BRA3.Code.Tag        using ( cantor )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )

------------------------------------------------------------------------
-- General helper :  pi (natCode-equivalent) X (natCode-equivalent) Y
-- collapses to  natCode (cantor _ _) .

pi_collapse :
  (X Y : Term) (a b : Nat) ->
  Deriv (eqF X (natCode a)) ->
  Deriv (eqF Y (natCode b)) ->
  Deriv (eqF (ap2 pi X Y) (natCode (cantor a b)))
pi_collapse X Y a b eqX eqY =
  let s1 : Deriv (eqF (ap2 pi X Y) (ap2 pi (natCode a) Y))
      s1 = congL pi Y eqX
      s2 : Deriv (eqF (ap2 pi (natCode a) Y) (ap2 pi (natCode a) (natCode b)))
      s2 = congR pi (natCode a) eqY
      s3 : Deriv (eqF (ap2 pi (natCode a) (natCode b)) (natCode (cantor a b)))
      s3 = pi_natCode a b
  in ruleTrans s1 (ruleTrans s2 s3)

-- Triple-nested form :  pi X (pi Y Z) -> natCode (cantor a (cantor b c)) .
pi3_collapse :
  (X Y Z : Term) (a b c : Nat) ->
  Deriv (eqF X (natCode a)) ->
  Deriv (eqF Y (natCode b)) ->
  Deriv (eqF Z (natCode c)) ->
  Deriv (eqF (ap2 pi X (ap2 pi Y Z)) (natCode (cantor a (cantor b c))))
pi3_collapse X Y Z a b c eqX eqY eqZ =
  let inner : Deriv (eqF (ap2 pi Y Z) (natCode (cantor b c)))
      inner = pi_collapse Y Z b c eqY eqZ
  in pi_collapse X (ap2 pi Y Z) a (cantor b c) eqX inner

-- Quadruple-nested :  pi X (pi Y (pi Z W)) -> natCode (cantor a (cantor b (cantor c d))) .
pi4_collapse :
  (X Y Z W : Term) (a b c d : Nat) ->
  Deriv (eqF X (natCode a)) ->
  Deriv (eqF Y (natCode b)) ->
  Deriv (eqF Z (natCode c)) ->
  Deriv (eqF W (natCode d)) ->
  Deriv (eqF (ap2 pi X (ap2 pi Y (ap2 pi Z W)))
              (natCode (cantor a (cantor b (cantor c d)))))
pi4_collapse X Y Z W a b c d eqX eqY eqZ eqW =
  let inner : Deriv (eqF (ap2 pi Y (ap2 pi Z W))
                          (natCode (cantor b (cantor c d))))
      inner = pi3_collapse Y Z W b c d eqY eqZ eqW
  in pi_collapse X (ap2 pi Y (ap2 pi Z W)) a (cantor b (cantor c d)) eqX inner

------------------------------------------------------------------------
-- The meta-Nat collapse values.  Forward-declared for mutual recursion.

codeFun1_to_nat : Fun1 -> Nat
codeFun2_to_nat : Fun2 -> Nat
codeTerm_to_nat : Term -> Nat
codeFormula_to_nat : Formula -> Nat

codeFun1_to_nat s = tag_s
codeFun1_to_nat o = tag_o
codeFun1_to_nat u = tag_u
codeFun1_to_nat (C g h1 h2) =
  cantor tag_C
    (cantor (codeFun2_to_nat g)
      (cantor (codeFun1_to_nat h1) (codeFun1_to_nat h2)))

codeFun2_to_nat v = tag_v
codeFun2_to_nat (R g h1 h2) =
  cantor tag_R
    (cantor (codeFun1_to_nat g)
      (cantor (codeFun2_to_nat h1) (codeFun2_to_nat h2)))

codeTerm_to_nat O           = zero
codeTerm_to_nat (var k)     = cantor tag_var k
codeTerm_to_nat (ap1 f t)   =
  cantor tag_ap1 (cantor (codeFun1_to_nat f) (codeTerm_to_nat t))
codeTerm_to_nat (ap2 g a b) =
  cantor tag_ap2
    (cantor (codeFun2_to_nat g)
      (cantor (codeTerm_to_nat a) (codeTerm_to_nat b)))

codeFormula_to_nat (atomic (eqn a b)) =
  cantor tag_eq (cantor (codeTerm_to_nat a) (codeTerm_to_nat b))
codeFormula_to_nat (neg P) =
  cantor tag_neg (codeFormula_to_nat P)
codeFormula_to_nat (imp P Q) =
  cantor tag_imp (cantor (codeFormula_to_nat P) (codeFormula_to_nat Q))

------------------------------------------------------------------------
-- Wait : the codeFormula(neg P) case is  pi (natCode tag_neg) (codeFormula P) ,
-- which has only ONE child  codeFormula P  inside pi (along with the tag).
-- For pi_collapse to fire we need natCode-equivalents on BOTH sides of pi .
-- Since  codeFormula P = natCode k_P  by IH, we have
--   pi (natCode tag_neg) (codeFormula P)
--     = pi (natCode tag_neg) (natCode k_P)        [congR + IH]
--     = natCode (cantor tag_neg k_P)               [pi_natCode] .
-- So  codeFormula_to_nat (neg P) = cantor tag_neg (codeFormula_to_nat P) -- match.

------------------------------------------------------------------------
-- The closed-form Deriv-equations.  Forward-declared for mutual recursion.

codeFun1_eq :
  (f : Fun1) -> Deriv (eqF (codeFun1 f) (natCode (codeFun1_to_nat f)))
codeFun2_eq :
  (g : Fun2) -> Deriv (eqF (codeFun2 g) (natCode (codeFun2_to_nat g)))
codeTerm_eq :
  (t : Term) -> Deriv (eqF (codeTerm t) (natCode (codeTerm_to_nat t)))
codeFormula_eq :
  (P : Formula) -> Deriv (eqF (codeFormula P) (natCode (codeFormula_to_nat P)))

codeFun1_eq s = axRefl (natCode tag_s)
codeFun1_eq o = axRefl (natCode tag_o)
codeFun1_eq u = axRefl (natCode tag_u)
codeFun1_eq (C g h1 h2) =
  -- codeFun1 (C g h1 h2) = pi tag_C (pi codeG (pi codeH1 codeH2)) .
  pi4_collapse (natCode tag_C) (codeFun2 g) (codeFun1 h1) (codeFun1 h2)
                tag_C (codeFun2_to_nat g) (codeFun1_to_nat h1) (codeFun1_to_nat h2)
                (axRefl (natCode tag_C))
                (codeFun2_eq g) (codeFun1_eq h1) (codeFun1_eq h2)

codeFun2_eq v = axRefl (natCode tag_v)
codeFun2_eq (R g h1 h2) =
  pi4_collapse (natCode tag_R) (codeFun1 g) (codeFun2 h1) (codeFun2 h2)
                tag_R (codeFun1_to_nat g) (codeFun2_to_nat h1) (codeFun2_to_nat h2)
                (axRefl (natCode tag_R))
                (codeFun1_eq g) (codeFun2_eq h1) (codeFun2_eq h2)

codeTerm_eq O = axRefl O   -- codeTerm O = O = natCode 0
codeTerm_eq (var k) =
  -- codeTerm (var k) = pi (natCode tag_var) (natCode k)
  pi_collapse (natCode tag_var) (natCode k) tag_var k
              (axRefl (natCode tag_var)) (axRefl (natCode k))
codeTerm_eq (ap1 f t) =
  -- codeTerm (ap1 f t) = pi tag_ap1 (pi codeFun1 codeT)
  pi3_collapse (natCode tag_ap1) (codeFun1 f) (codeTerm t)
                tag_ap1 (codeFun1_to_nat f) (codeTerm_to_nat t)
                (axRefl (natCode tag_ap1))
                (codeFun1_eq f) (codeTerm_eq t)
codeTerm_eq (ap2 g a b) =
  pi4_collapse (natCode tag_ap2) (codeFun2 g) (codeTerm a) (codeTerm b)
                tag_ap2 (codeFun2_to_nat g) (codeTerm_to_nat a) (codeTerm_to_nat b)
                (axRefl (natCode tag_ap2))
                (codeFun2_eq g) (codeTerm_eq a) (codeTerm_eq b)

codeFormula_eq (atomic (eqn a b)) =
  -- codeFormula (atomic (eqn a b)) = pi tag_eq (pi codeA codeB)
  pi3_collapse (natCode tag_eq) (codeTerm a) (codeTerm b)
                tag_eq (codeTerm_to_nat a) (codeTerm_to_nat b)
                (axRefl (natCode tag_eq))
                (codeTerm_eq a) (codeTerm_eq b)
codeFormula_eq (neg P) =
  -- codeFormula (neg P) = pi tag_neg (codeFormula P) -- pi_collapse with 2 args
  pi_collapse (natCode tag_neg) (codeFormula P) tag_neg (codeFormula_to_nat P)
              (axRefl (natCode tag_neg))
              (codeFormula_eq P)
codeFormula_eq (imp P Q) =
  pi3_collapse (natCode tag_imp) (codeFormula P) (codeFormula Q)
                tag_imp (codeFormula_to_nat P) (codeFormula_to_nat Q)
                (axRefl (natCode tag_imp))
                (codeFormula_eq P) (codeFormula_eq Q)

------------------------------------------------------------------------
-- Derived natEqF reflexivity on  codeT / codeF .

natEqF_codeT_refl :
  (t : Term) ->
  Deriv (eqF (ap2 natEqF (codeTerm t) (codeTerm t)) (ap1 s O))
natEqF_codeT_refl t =
  let kt : Nat
      kt = codeTerm_to_nat t
      ct_eq : Deriv (eqF (codeTerm t) (natCode kt))
      ct_eq = codeTerm_eq t
      s1 : Deriv (eqF (ap2 natEqF (codeTerm t) (codeTerm t))
                       (ap2 natEqF (natCode kt) (codeTerm t)))
      s1 = congL natEqF (codeTerm t) ct_eq
      s2 : Deriv (eqF (ap2 natEqF (natCode kt) (codeTerm t))
                       (ap2 natEqF (natCode kt) (natCode kt)))
      s2 = congR natEqF (natCode kt) ct_eq
      s3 : Deriv (eqF (ap2 natEqF (natCode kt) (natCode kt)) (ap1 s O))
      s3 = natEq_eq kt
  in ruleTrans s1 (ruleTrans s2 s3)

natEqF_codeF_refl :
  (P : Formula) ->
  Deriv (eqF (ap2 natEqF (codeFormula P) (codeFormula P)) (ap1 s O))
natEqF_codeF_refl P =
  let kp : Nat
      kp = codeFormula_to_nat P
      cf_eq : Deriv (eqF (codeFormula P) (natCode kp))
      cf_eq = codeFormula_eq P
      s1 : Deriv (eqF (ap2 natEqF (codeFormula P) (codeFormula P))
                       (ap2 natEqF (natCode kp) (codeFormula P)))
      s1 = congL natEqF (codeFormula P) cf_eq
      s2 : Deriv (eqF (ap2 natEqF (natCode kp) (codeFormula P))
                       (ap2 natEqF (natCode kp) (natCode kp)))
      s2 = congR natEqF (natCode kp) cf_eq
      s3 : Deriv (eqF (ap2 natEqF (natCode kp) (natCode kp)) (ap1 s O))
      s3 = natEq_eq kp
  in ruleTrans s1 (ruleTrans s2 s3)
