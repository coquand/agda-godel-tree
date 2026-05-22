{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.IsNat -- the Agda meta predicate  isNat : Term -> Set  picking
-- out numerals  s^n O , and the Deriv-level bridge
--
--   num_eq_code : (t : Term) -> isNat t -> Deriv (eqF (ap1 num t) (codeTerm t))
--
-- saying that  num  and  codeTerm  agree on numerals.  By meta-
-- induction on  isNat , the proof builds a Deriv chain using
-- num_at_O / num_at_S  ( BRA4.Num ).  Note  codeTerm  is meta-Agda; the
-- equation transports across the structural recurrence
--
--   codeTerm (ap1 s t) = Pair (natCode tag_ap1) (Pair (codeFun1 s) (codeTerm t))
--                      = Pair (natCode tag_ap1) (Pair (natCode tag_s) (codeTerm t))
--
-- The second equality holds DEFINITIONALLY since  codeFun1 s = natCode tag_s
-- (see BRA4.Code).

module BRA4.IsNat where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Num

------------------------------------------------------------------------
-- isNat predicate.

data isNat : Term -> Set where
  isNat_O : isNat O
  isNat_S : (t : Term) -> isNat t -> isNat (ap1 s t)

------------------------------------------------------------------------
-- The bridge.

num_eq_code :
  (t : Term) -> isNat t ->
  Deriv (eqF (ap1 num t) (codeTerm t))

-- Base case:  t = O .  num_at_O .
num_eq_code .O isNat_O = num_at_O

-- Step:  t = ap1 s t' .
--   num (s t') --[num_at_S]--> Pair tag_ap1 (Pair tag_s (num t'))
--              --[congR with IH]--> Pair tag_ap1 (Pair tag_s (codeTerm t'))
--              = codeTerm (s t') by definition.
num_eq_code .(ap1 s t') (isNat_S t' p) =
  let
    step1 :
      Deriv (eqF (ap1 num (ap1 s t'))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) (ap1 num t'))))
    step1 = num_at_S t'

    ih : Deriv (eqF (ap1 num t') (codeTerm t'))
    ih = num_eq_code t' p

    -- congR with tag_s in front:  Pair tag_s (num t') = Pair tag_s (codeTerm t')
    bridge_inner :
      Deriv (eqF (ap2 Pair (natCode tag_s) (ap1 num t'))
                  (ap2 Pair (natCode tag_s) (codeTerm t')))
    bridge_inner = congR Pair (natCode tag_s) ih

    -- congR with tag_ap1 in front:  Pair tag_ap1 X = Pair tag_ap1 Y
    bridge_outer :
      Deriv (eqF (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) (ap1 num t')))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (natCode tag_s) (codeTerm t'))))
    bridge_outer = congR Pair (natCode tag_ap1) bridge_inner
    -- The RHS is definitionally  codeTerm (ap1 s t')  since
    --   codeTerm (ap1 s t') = Pair tag_ap1 (Pair (codeFun1 s) (codeTerm t'))
    --                       = Pair tag_ap1 (Pair (natCode tag_s) (codeTerm t')).
  in ruleTrans step1 bridge_outer
