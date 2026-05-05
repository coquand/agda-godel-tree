{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundMpProto
--
-- Verifying body for mp.  V2 (post-audit): rebuilt as
--   body_mp_v = Post verifierF1 Pair
-- mirroring the original body_mp's shape, so that all extractors
-- reach into b (the IH-distributed argument carrying thmT y1T,
-- thmT y2T after distribution) via Snd of the synthesized pair
-- (Pair a b).
--
-- The previous V1 used Lift on the extractors, which by axLift
-- (ap2 (Lift f) a b = ap1 f a) ignored b entirely — the outer-check
-- there was TreeEq (Fst y1T) tagImp, NOT TreeEq (Fst (thmT y1T))
-- tagImp, so the prototype was semantically wrong.  See
-- BRA/SOUND-THMT-FINDINGS.md Blocker 1.
--
-- Verifying logic.  For input a = Pair tagCode_mp (Pair y1T y2T),
-- bb such that  Snd bb = Pair (thmT y1T) (thmT y2T) :
--   * outer_check : Fst (thmT y1T) ≡ tagImp        (imp head?)
--   * inner_check : thmT y2T ≡ Fst (Snd (thmT y1T))  (antecedent?)
-- If both checks pass, output  Snd (Snd (thmT y1T))  (= qT).
-- Else output  codeTriv = reify (codeFormula (atomic (eqn O O))).
--
-- Identifier convention:  camelCase for all helper functors.
-- Mid-identifier underscores collide with Agda's mixfix grammar
-- (turning  get_head  into a 1-argument operator  get _ head ).
--
-- ASCII only.  No postulates, no holes.

module BRA.SoundMpProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

----------------------------------------------------------------------
-- Encoded codeTriv.
--
-- codeFormula (atomic (eqn O O)) = nd (code O) (code O) = nd lf lf.
-- reify (nd lf lf) = ap2 Pair O O = falseT (definitionally).

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

-- Sanity check: codeTriv definitionally equals falseT.
codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- Extractors over the synthesized pair  t = (ap2 Pair a b)
-- (introduced by  Post _ Pair  via axPost).
--
-- Since  ap1 Fst t = a  and  ap1 Snd t = b , extractors that reach
-- into b are written as  Comp _ Snd  chains.

-- thmT y1T = Fst (Snd b) = Fst (Snd (Snd t)).
getD1 : Fun1
getD1 = Comp Fst (Comp Snd Snd)

-- thmT y2T = Snd (Snd b) = Snd (Snd (Snd t)).
getD2 : Fun1
getD2 = Comp Snd (Comp Snd Snd)

-- Fst (thmT y1T) = head (should be tagImp).
getHead : Fun1
getHead = Comp Fst getD1

-- Snd (thmT y1T) = body (Pair pT qT).
-- Fst (Snd (thmT y1T)) = pT.
getPT : Fun1
getPT = Comp Fst (Comp Snd getD1)

-- Snd (Snd (thmT y1T)) = qT.
getQT : Fun1
getQT = Comp Snd (Comp Snd getD1)

----------------------------------------------------------------------
-- The verifier as a Fun1 over  t = (Pair a b) .
--
-- verifierF1 = if (combinedCheck) then qT else codeTriv,
-- expressed as  Comp2 IfLf ccF1 qfailPairF1 .
--
-- ccF1 = if (outerCheck) then innerCheck else falseT,
-- expressed as  Comp2 IfLf outerCheckF1 innerOrFalsePairF1 .

outerCheckF1 : Fun1
outerCheckF1 = Comp2 TreeEq getHead (KT (reify tagImp))

innerCheckF1 : Fun1
innerCheckF1 = Comp2 TreeEq getD2 getPT

innerOrFalsePairF1 : Fun1
innerOrFalsePairF1 = Comp2 Pair innerCheckF1 (KT falseT)

ccF1 : Fun1
ccF1 = Comp2 IfLf outerCheckF1 innerOrFalsePairF1

qfailPairF1 : Fun1
qfailPairF1 = Comp2 Pair getQT (KT codeTriv)

verifierF1 : Fun1
verifierF1 = Comp2 IfLf ccF1 qfailPairF1

----------------------------------------------------------------------
-- The verifying body for mp.

body_mp_v : Fun2
body_mp_v = Post verifierF1 Pair

----------------------------------------------------------------------
-- The combinator typechecks; the eval proof  body_mp_v_eval_pass
-- lives in  BRA.SoundMpVProof  (closed-Formula version).
