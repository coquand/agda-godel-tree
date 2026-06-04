{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.ChaitinG1Out -- C.5 piece: the concrete hole PROJECTOR  out : Fun1  that
-- the recogniser  T4.ChaitinG1Neg.hitNeg  reads the subject back with, and its
-- correctness.
--
-- The incompressibility code is the closed num-headed
--   cNeg (codeFXeqY1 compHit z0 (s O))
--     = Pair tag_neg (Pair tag_eq (Pair (Pair tag_ap1 (Pair (codeFun1 compHit)
--                                                            (num z0)))
--                                       (num (s O)))) ,
-- whose single subject slot  num z0  sits at the fixed Fst/Snd path
--   Snd . Snd . Fst . Snd . Snd  (root to hole).
-- So  out = decode o (that path) o thmT :  out reads  thmT(w) , projects to the
-- slot  num z0 , and  decode s it back to  z0  (Decode round-trip  decode(num t)=t,
-- the shipped  decode_num_id_at , universal in  t  -- so  z0  may be symbolic, e.g.
-- the search output  ap1 search L_bin ).
--
-- out_correct: a matched proof  thmT(w) = cNeg (codeFXeqY1 compHit z0 (s O))  is
-- read back exactly:  ap1 out w = z0 .  Pure projection (axFst/axSnd on the Pair
-- tree, axComp to unfold the composition) + the Decode round-trip.  No codeTermF,
-- no codeFormula.  This discharges the  out  parameter of  ChaitinG1Neg.hitNeg /
-- ChaitinG1Witness.chaitin_G1_from_firing.

module T4.ChaitinG1Out where

open import T4.Base
open import T4.Tags        using ( tag_neg ; tag_eq ; tag_ap1 )
open import T4.ThmT        using ( thmT )
open import T4.Num         using ( num )
open import T4.Code        using ( codeFun1 )
open import T4.DefWit      using ( cNeg )
open import T4.Thm12.Thm13 using ( codeFXeqY1 )
open import T4.Decode      using ( decode ; decode_num_id_at )

------------------------------------------------------------------------
-- SECTION 1.  The projection path  proj = Snd . Snd . Fst . Snd . Snd .

proj : Fun1
proj = compose1U Snd (compose1U Snd (compose1U Fst (compose1U Snd Snd)))

-- proj applied to the incompressibility code reads off the subject slot  num z0 .
proj_at_code :
  (compHit : Fun1) (z0 : Term) ->
  Deriv (eqF (ap1 proj (cNeg (codeFXeqY1 compHit z0 (ap1 s O))))
             (ap1 num z0))
proj_at_code compHit z0 =
  let C : Term
      C = cNeg (codeFXeqY1 compHit z0 (ap1 s O))
      A1 : Term
      A1 = codeFXeqY1 compHit z0 (ap1 s O)
      A5 : Term
      A5 = ap2 Pair (codeFun1 compHit) (ap1 num z0)
      A3 : Term
      A3 = ap2 Pair (natCode tag_ap1) A5
      A4 : Term
      A4 = ap1 num (ap1 s O)
      A2 : Term
      A2 = ap2 Pair A3 A4

      q2 : Fun1
      q2 = compose1U Snd Snd
      q3 : Fun1
      q3 = compose1U Fst q2
      q4 : Fun1
      q4 = compose1U Snd q3

      -- the five single-projection reductions (definitional on the Pair tree).
      r1 : Deriv (eqF (ap1 Snd C) A1)
      r1 = axSnd (natCode tag_neg) A1
      r2 : Deriv (eqF (ap1 Snd A1) A2)
      r2 = axSnd (natCode tag_eq) A2
      r3 : Deriv (eqF (ap1 Fst A2) A3)
      r3 = axFst A3 A4
      r4 : Deriv (eqF (ap1 Snd A3) A5)
      r4 = axSnd (natCode tag_ap1) A5
      r5 : Deriv (eqF (ap1 Snd A5) (ap1 num z0))
      r5 = axSnd (codeFun1 compHit) (ap1 num z0)

      -- unfold each compose1U, then reduce.
      e_q2 : Deriv (eqF (ap1 q2 C) A2)
      e_q2 = ruleTrans (axComp Snd Snd C)
               (ruleTrans (cong1 Snd r1) r2)
      e_q3 : Deriv (eqF (ap1 q3 C) A3)
      e_q3 = ruleTrans (axComp Fst q2 C)
               (ruleTrans (cong1 Fst e_q2) r3)
      e_q4 : Deriv (eqF (ap1 q4 C) A5)
      e_q4 = ruleTrans (axComp Snd q3 C)
               (ruleTrans (cong1 Snd e_q3) r4)
  in ruleTrans (axComp Snd q4 C)
       (ruleTrans (cong1 Snd e_q4) r5)

------------------------------------------------------------------------
-- SECTION 2.  out = decode o proj o thmT , and its correctness.

out : Fun1
out = compose1U decode (compose1U proj thmT)

out_correct :
  (compHit : Fun1) (z0 w : Term) ->
  Deriv (eqF (ap1 thmT w) (cNeg (codeFXeqY1 compHit z0 (ap1 s O)))) ->
  Deriv (eqF (ap1 out w) z0)
out_correct compHit z0 w hyp =
  ruleTrans (axComp decode (compose1U proj thmT) w)
    (ruleTrans (cong1 decode (axComp proj thmT w))
      (ruleTrans (cong1 decode (cong1 proj hyp))
        (ruleTrans (cong1 decode (proj_at_code compHit z0))
                   (decode_num_id_at z0))))
