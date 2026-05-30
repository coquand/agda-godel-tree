{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Decode -- the object  decode : Fun1 , the structural inverse of
-- BRA4.Num.num  on numeral codes, with the round-trip proved by INTERNAL
-- induction.  Step 3 of  BRA4/NEXT-SESSION-CHAITIN-G1-FRESH.md (the crux).
--
-- ======================================================================
-- WHY (the corrected denotation crux).
-- ======================================================================
--
-- The Chaitin-G1 subject  z  is read off the found proof  w  as a VALUE
-- (a numeral) by DECODING the subject slot, not recomputed by an object
-- coder.  The only coherence point is that  dPos 's subject (num z, from
-- Thm12) equals  dNeg 's  num -headed subject slot.  With  z := decode(slot)
-- this is the round-trip  num (decode (num t)) = num t  -- the (D2) below.
--
-- num  is the value-coder (BRA4.Num):
--   num O      = O
--   num (s t)  = Pair tag_ap1 (Pair tag_s (num t))             [num_at_S]
-- so its image on numerals is the right-nested  tag_ap1 / tag_s  spine.
-- decode  peels exactly that spine:
--   decode O                              = O
--   decode (Pair tag_ap1 (Pair tag_s w))  = s (decode w)        [decode_at_spine]
-- (the recursive call is on  w = Snd (Snd node) , value-smaller than the
-- node since pairing strictly increases value -- hence COURSE-OF-VALUES,
-- realised as the shipped  BRA4.FoldRec.fold  with no tag dispatch, the
-- simplest fold instance after  BRA4.LenR ).
--
-- ======================================================================
-- THE ROUND-TRIP IS INTERNAL INDUCTION (the decisive design point).
-- ======================================================================
--
--   (D1)  decode_num_id : Deriv (eqF (ap1 decode (ap1 num (var 0))) (var 0))
--
-- is a SINGLE Deriv of the universally-quantified statement, by ONE object
-- ruleIndNat with motive  INV(var0) = eqF (ap1 decode (ap1 num (var0))) (var0)
-- (the SpikeParsons / SpikeD shape; decode, num are closed Fun1 so substF
-- commutes through ap1 and no closeCoe is needed).  It is NOT a meta-indexed
-- family  (n : Nat) -> ... :
--   * base  INV[var0:=O]  : decode (num O) = decode O = O          (num_at_O + decode_at_O)
--   * step  INV var0 -> INV (s var0)  :  decode (num (s var0))
--       = decode (Pair tag_ap1 (Pair tag_s (num var0)))            (num_at_S, UNIVERSAL in t,
--       = s (decode (num var0))                                     so it fires on  s var0)
--       = s var0                                                    (decode_at_spine + IH).
-- The step is a PURE equational congruence: ax_eqCong1 s (forward s-congruence
-- as an implication) composed with  prependEqLeft  on  eqStep .  No D1/D3.
--
-- Because (D1) is internal, it is  ruleInst -able at ANY term -- in particular
-- at the SYMBOLIC subject slot  t  (decode_num_id_at below) WITHOUT needing
-- num t  to reduce (it does not, for a non-numeral t).  That instantiability
-- is the whole payoff and the reason internal (not meta) induction is required.
--
--   (D2)  num_decode_num t : Deriv (eqF (ap1 num (ap1 decode (ap1 num t))) (ap1 num t))
--
-- then follows for ANY  t  by  cong1 num (decode_num_id_at t)  -- the slot match.
--
-- (NB: the recursion-target variable is named  w  -- NOT  u , which is the
-- identity-functor Fun1 constructor.)

module BRA4.Decode where

open import BRA4.Base
open import BRA4.FoldRec
open import BRA4.CoVSpec      using ( cov_spec )
open import BRA4.CoVSpecUniv  using ( HistP_sbt )
open import BRA4.Stability    using ( HPsbt )
open import BRA4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import BRA4.LeqMono      using ( leq_sigma_right ; leq_pi_right ; leq_trans )
open import BRA4.Num          using ( num ; num_at_O ; num_at_S )
open import BRA4.Tags         using ( tag_ap1 ; tag_s )

open import BRA3.Church          using ( pi ; sub ; sigma ; tau )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using
  ( Pair ; axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Logic           using ( prependEqLeft ; impTrans )

------------------------------------------------------------------------
-- SECTION 1.  decode : Fun1 .
--
-- No tag dispatch: at every node  decode  prepends  s  and recurses on the
-- second-of-second component  w = Snd (Snd node) .  The base value (fuel O)
-- is  o O = O .  So  decode = fold o stepFun_decode  with the step body
--   stepBody = s . (lookup at the recursion target  Snd (Snd node)) .

-- recursion target:  Snd (Snd (get_newK input)) = Snd (Snd node) = w .
decode_rc : Fun1
decode_rc = compose1U Snd (compose1U Snd get_newK)

-- the recovered prior value  decode w  (under  leq w (predecessor)).
priorDecode : Fun1
priorDecode = lookupAt decode_rc

-- the step body:  s (decode w) .
decodeStepBody : Fun1
decodeStepBody = compose1U s priorDecode

stepFun_decode : Fun2
stepFun_decode = Post decodeStepBody pi

decode : Fun1
decode = fold o stepFun_decode

------------------------------------------------------------------------
-- SECTION 2.  decode_at_O :  ap1 decode O = O .

decode_at_O : Deriv (eqF (ap1 decode O) O)
decode_at_O = ruleTrans (fold_at_O o stepFun_decode) (ax_o O)

------------------------------------------------------------------------
-- SECTION 3.  priorDecode_at -- the recursion-recovery, GENERIC in a, b, w.
--
-- At the step input  input_pkg = pi P_outer (Snd prev)  for the node
--   node = pi (s a) (pi b w)   (P_outer = pi_succ_outer a (pi b w)),
-- the prior-value lookup recovers  decode w .  This is the  BRA4.Parse
-- priorStack_at  pattern, but with the recursion target TWO  Snd s deep
-- (w = Snd (Snd node)  vs parse's  rest = Snd node), so the lookup validity
-- needs  leq w P_outer  -- discharged by  leq_trans  of  leq_pi_right  (w
-- bounded by  pi b w ) and  leq_sigma_right  (pi b w  bounded by  P_outer ).

priorDecode_at :
  (a b w : Term) ->
  Deriv (eqF (ap1 priorDecode
               (ap2 pi (pi_succ_outer a (ap2 pi b w))
                       (ap1 Snd (ap2 (cov_spec o stepFun_decode) O
                                      (pi_succ_outer a (ap2 pi b w))))))
              (ap1 decode w))
priorDecode_at a b w =
  let node : Term
      node = ap2 pi (ap1 s a) (ap2 pi b w)

      P_outer : Term
      P_outer = pi_succ_outer a (ap2 pi b w)

      prev : Term
      prev = ap2 (cov_spec o stepFun_decode) O P_outer

      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)

      -- decode_rc input_pkg = w  (peel s; two Snds of the node).
      decode_rc_value : Deriv (eqF (ap1 decode_rc input_pkg) w)
      decode_rc_value =
        let r1 : Deriv (eqF (ap1 decode_rc input_pkg)
                            (ap1 Snd (ap1 (compose1U Snd get_newK) input_pkg)))
            r1 = compose1U_eq Snd (compose1U Snd get_newK) input_pkg

            r2 : Deriv (eqF (ap1 (compose1U Snd get_newK) input_pkg)
                            (ap1 Snd (ap1 get_newK input_pkg)))
            r2 = compose1U_eq Snd get_newK input_pkg

            r3 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
            r3 = get_newK_at_pi P_outer (ap1 Snd prev)

            r4 : Deriv (eqF (ap1 s P_outer) node)
            r4 = ruleSym (pi_at_succ a (ap2 pi b w))

            r5 : Deriv (eqF (ap1 Snd node) (ap2 pi b w))
            r5 = axSnd (ap1 s a) (ap2 pi b w)

            r6 : Deriv (eqF (ap1 Snd (ap2 pi b w)) w)
            r6 = axSnd b w
        in ruleTrans r1
             (ruleTrans (cong1 Snd r2)
               (ruleTrans (cong1 Snd (cong1 Snd r3))
                 (ruleTrans (cong1 Snd (cong1 Snd r4))
                   (ruleTrans (cong1 Snd r5) r6))))

      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg)
                    (HistP_sbt o stepFun_decode O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- priorDecode input_pkg = HPsbt o stepFun_decode O w P_outer .
      lookup_to_HP :
        Deriv (eqF (ap1 priorDecode input_pkg)
                    (HPsbt o stepFun_decode O w P_outer))
      lookup_to_HP =
        let u1 :
              Deriv (eqF (ap1 priorDecode input_pkg)
                          (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                    (ap2 sub (ap1 get_K input_pkg) (ap1 decode_rc input_pkg)))))
            u1 = lookupAt_unfold decode_rc input_pkg

            sub_eq :
              Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 decode_rc input_pkg))
                          (ap2 sub P_outer w))
            sub_eq = ruleTrans (congL sub (ap1 decode_rc input_pkg) get_K_value)
                               (congR sub P_outer decode_rc_value)

            iter_eq :
              Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 decode_rc input_pkg)))
                          (ap2 (iter Snd) (HistP_sbt o stepFun_decode O P_outer)
                          (ap2 sub P_outer w)))
            iter_eq =
              ruleTrans (congL (iter Snd)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 decode_rc input_pkg))
                          get_table_value)
                        (congR (iter Snd) (HistP_sbt o stepFun_decode O P_outer) sub_eq)
        in ruleTrans u1 (cong1 Fst iter_eq)

      -- leq w P_outer :  w <= pi b w <= P_outer .
      leq_w_P : Deriv (leq w P_outer)
      leq_w_P =
        leq_trans w (ap2 pi b w) P_outer
          (leq_pi_right b w)
          (leq_sigma_right
            (ap2 sigma (ap2 sigma a (ap2 pi b w)) (ap1 tau (ap2 sigma a (ap2 pi b w))))
            (ap2 pi b w))

      HP_to_decode :
        Deriv (eqF (HPsbt o stepFun_decode O w P_outer) (ap1 decode w))
      HP_to_decode = lookup_eq_fold o stepFun_decode w P_outer leq_w_P
  in ruleTrans lookup_to_HP HP_to_decode

------------------------------------------------------------------------
-- SECTION 4.  decode_at_spine -- the node closure.
--
-- decode_at_spine_gen a b w :  decode (pi (s a) (pi b w)) = s (decode w) .
-- Universal in a, b, w (no Closed): fire the fold step (no dispatch), then
-- recover  decode w  via priorDecode_at.  This is the BRA4.Parse parse_at_leaf
-- shape, MINUS the condFork tag-dispatch (decode does the same at every node).

decode_at_spine_gen :
  (a b w : Term) ->
  Deriv (eqF (ap1 decode (ap2 pi (ap1 s a) (ap2 pi b w)))
              (ap1 s (ap1 decode w)))
decode_at_spine_gen a b w =
  let node : Term
      node = ap2 pi (ap1 s a) (ap2 pi b w)

      P_outer : Term
      P_outer = pi_succ_outer a (ap2 pi b w)

      prev : Term
      prev = ap2 (cov_spec o stepFun_decode) O P_outer

      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)

      -- the fold step fires on the node.
      step_fires :
        Deriv (eqF (ap1 decode node)
                    (ap2 stepFun_decode P_outer (ap1 Snd prev)))
      step_fires = fold_node_unfold o stepFun_decode a (ap2 pi b w)

      -- Post: the step body sees the packaged input.
      post_eq :
        Deriv (eqF (ap2 stepFun_decode P_outer (ap1 Snd prev))
                    (ap1 decodeStepBody input_pkg))
      post_eq = axPost decodeStepBody pi P_outer (ap1 Snd prev)

      -- the body:  s (priorDecode input_pkg) .
      body_eq :
        Deriv (eqF (ap1 decodeStepBody input_pkg)
                    (ap1 s (ap1 priorDecode input_pkg)))
      body_eq = compose1U_eq s priorDecode input_pkg

      -- priorDecode input_pkg = decode w .
      prior_v : Deriv (eqF (ap1 priorDecode input_pkg) (ap1 decode w))
      prior_v = priorDecode_at a b w

      tail :
        Deriv (eqF (ap1 s (ap1 priorDecode input_pkg)) (ap1 s (ap1 decode w)))
      tail = cong1 s prior_v
  in ruleTrans step_fires
       (ruleTrans post_eq
         (ruleTrans body_eq tail))

-- decode_at_spine : the closure at the EXACT num_at_S spine
--   (tag_ap1 = 2 => natCode tag_ap1 = s (natCode 1);  Pair = pi).
decode_at_spine :
  (w : Term) ->
  Deriv (eqF (ap1 decode (ap2 Pair (natCode tag_ap1) (ap2 Pair (natCode tag_s) w)))
              (ap1 s (ap1 decode w)))
decode_at_spine w = decode_at_spine_gen (natCode 1) (natCode tag_s) w

------------------------------------------------------------------------
-- SECTION 5.  The round-trip, by INTERNAL induction.
--
-- INV(j) = eqF (ap1 decode (ap1 num j)) j .  ONE object ruleIndNat.

INV : Term -> Formula
INV j = eqF (ap1 decode (ap1 num j)) j

-- base:  substF zero O (INV (var 0)) = INV O  (decode, num closed Fun1).
indBase : Deriv (INV O)
indBase = ruleTrans (cong1 decode num_at_O) decode_at_O

-- step (universal in j):  INV j -> INV (s j) , a pure equational congruence.
indStep : (j : Term) -> Deriv (imp (INV j) (INV (ap1 s j)))
indStep j =
  let bigX : Term
      bigX = ap1 decode (ap1 num j)

      -- decode (num (s j)) = s (decode (num j)) = s bigX  (unconditional).
      eqStep : Deriv (eqF (ap1 decode (ap1 num (ap1 s j))) (ap1 s bigX))
      eqStep = ruleTrans (cong1 decode (num_at_S j))
                         (decode_at_spine (ap1 num j))

      -- forward s-congruence as an implication (equation = antecedent).
      congImp : Deriv (imp (eqF bigX j) (eqF (ap1 s bigX) (ap1 s j)))
      congImp = ax_eqCong1 s bigX j

      -- transport the conclusion's LHS  s bigX -> decode (num (s j))  via eqStep.
      transp : Deriv (imp (eqF (ap1 s bigX) (ap1 s j))
                          (eqF (ap1 decode (ap1 num (ap1 s j))) (ap1 s j)))
      transp = prependEqLeft (ap1 decode (ap1 num (ap1 s j))) (ap1 s bigX) (ap1 s j) eqStep
  in impTrans congImp transp

-- (D1) the internal universal:  decode (num (var 0)) = var 0 .
decode_num_id : Deriv (eqF (ap1 decode (ap1 num (var zero))) (var zero))
decode_num_id = ruleIndNat zero {P = INV (var zero)} indBase (indStep (var zero))

-- (D1') instantiation at ANY term -- in particular the symbolic subject slot.
decode_num_id_at :
  (t : Term) -> Deriv (eqF (ap1 decode (ap1 num t)) t)
decode_num_id_at t = ruleInst zero t decode_num_id

-- (D2) the slot match:  num (decode (num t)) = num t , for ANY t.
num_decode_num :
  (t : Term) -> Deriv (eqF (ap1 num (ap1 decode (ap1 num t))) (ap1 num t))
num_decode_num t = cong1 num (decode_num_id_at t)
