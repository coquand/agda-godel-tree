{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.LenR -- the right-recursive length functor, the FIRST concrete
-- BRA4.FoldRec instance (validates the Phase A0 API end-to-end) and the
-- length measure the Berry argument needs.
--
-- lenR counts the right-spine depth of a Cantor-pair structure: the number
-- of  Snd-steps before reaching the leaf  O .  It descends on the SECOND
-- child only (Snd strictly decreases for K > 0), so it is well-defined as
-- an object  Fun1  -- unlike a "raw node count" which would need the
-- non-well-founded binary fold (Cantor  Fst  does not decrease:  Fst 1 = 1).
--
-- Closures (the fold instance's API):
--
--   lenR_at_O    :  ap1 lenR O = O                       (= natCode 0)
--   lenR_at_node :  ap1 lenR (pi (s A) b) = s (ap1 lenR b)   (universal in A, b)
--
-- For a right-nested bit-list  binMeta m = pi b0 (pi b1 (... O))  this gives
--  lenR (binMeta m) = natCode (#bits) = O(log m)  -- the compressed-numeral
-- length that makes the Berry counting finite and the self-reference
--  Len(B) < m0  achievable.  (binMeta + the bound live in BRA4.Bin, next.)

module BRA4.LenR where

open import BRA4.Base
open import BRA4.FoldRec
open import BRA4.CoVSpec      using ( cov_spec )
open import BRA4.CoVSpecUniv  using ( HistP_sbt )
open import BRA4.Stability    using ( HPsbt )
open import BRA4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import BRA4.LeqMono      using ( leq_sigma_right )

open import BRA3.Church       using ( pi ; sub ; sigma ; tau )
open import BRA3.ChurchT117   using ( Fst )
open import BRA3.ChurchT116   using ( Snd )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.CourseOfValues using ( iter )

------------------------------------------------------------------------
-- The step body.
--
-- At a node  N = s K_term = pi (s A) b , the right child is  b = Snd N .
-- The step looks up  lenR b  from the table and returns  s (lenR b) .
--
--   get_rc input = Snd (s (get_K input)) = Snd N   -- the right child
--   stepBody_lenR input = s (lookupAt get_rc input)

get_rc : Fun1
get_rc = compose1U Snd get_newK

stepBody_lenR : Fun1
stepBody_lenR = compose1U s (lookupAt get_rc)

stepFun_lenR : Fun2
stepFun_lenR = Post stepBody_lenR pi

-- Base  o  (so  lenR O = o O = O = natCode 0).

lenR : Fun1
lenR = fold o stepFun_lenR

------------------------------------------------------------------------
-- lenR_at_O :  ap1 lenR O = O .

lenR_at_O : Deriv (eqF (ap1 lenR O) O)
lenR_at_O = ruleTrans (fold_at_O o stepFun_lenR) (ax_o O)

------------------------------------------------------------------------
-- lenR_at_node :  ap1 lenR (pi (s A) b) = s (ap1 lenR b) .  Universal.

lenR_at_node :
  (A b : Term) ->
  Deriv (eqF (ap1 lenR (ap2 pi (ap1 s A) b)) (ap1 s (ap1 lenR b)))
lenR_at_node A b =
  let node : Term
      node = ap2 pi (ap1 s A) b

      P_outer : Term
      P_outer = pi_succ_outer A b

      prev : Term
      prev = ap2 (cov_spec o stepFun_lenR) O P_outer

      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)

      -- Step 1: fold_node_unfold -- the step fires.
      step1 :
        Deriv (eqF (ap1 lenR node)
                    (ap2 stepFun_lenR P_outer (ap1 Snd prev)))
      step1 = fold_node_unfold o stepFun_lenR A b

      -- Step 2: stepFun_lenR = Post stepBody_lenR pi.
      step2 :
        Deriv (eqF (ap2 stepFun_lenR P_outer (ap1 Snd prev))
                    (ap1 stepBody_lenR input_pkg))
      step2 = axPost stepBody_lenR pi P_outer (ap1 Snd prev)

      -- Step 3: get_rc input_pkg = b.
      get_rc_value : Deriv (eqF (ap1 get_rc input_pkg) b)
      get_rc_value =
        let s1 :
              Deriv (eqF (ap1 get_rc input_pkg) (ap1 Snd (ap1 get_newK input_pkg)))
            s1 = compose1U_eq Snd get_newK input_pkg

            s2 :
              Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
            s2 = get_newK_at_pi P_outer (ap1 Snd prev)

            -- s P_outer = node  (pi_at_succ reversed).
            s3 :
              Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd node))
            s3 = cong1 Snd (ruleSym (pi_at_succ A b))

            s4 : Deriv (eqF (ap1 Snd node) b)
            s4 = axSnd (ap1 s A) b
        in ruleTrans s1
             (ruleTrans (cong1 Snd s2) (ruleTrans s3 s4))

      -- Step 4: get_K input_pkg = P_outer.
      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      -- Step 5: get_table input_pkg = HistP_sbt o stepFun_lenR O P_outer
      -- (= Snd (Snd prev), definitionally).
      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg)
                    (HistP_sbt o stepFun_lenR O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- Step 6: lookupAt get_rc input_pkg = HPsbt o stepFun_lenR O b P_outer.
      lookup_to_HP :
        Deriv (eqF (ap1 (lookupAt get_rc) input_pkg)
                    (HPsbt o stepFun_lenR O b P_outer))
      lookup_to_HP =
        let u1 :
              Deriv (eqF (ap1 (lookupAt get_rc) input_pkg)
                          (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                    (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg)))))
            u1 = lookupAt_unfold get_rc input_pkg

            -- sub (get_K input_pkg) (get_rc input_pkg) = sub P_outer b.
            sub_eq :
              Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg))
                          (ap2 sub P_outer b))
            sub_eq = ruleTrans (congL sub (ap1 get_rc input_pkg) get_K_value)
                               (congR sub P_outer get_rc_value)

            iter_eq :
              Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg)))
                          (ap2 (iter Snd) (HistP_sbt o stepFun_lenR O P_outer)
                          (ap2 sub P_outer b)))
            iter_eq =
              ruleTrans (congL (iter Snd)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg))
                          get_table_value)
                        (congR (iter Snd) (HistP_sbt o stepFun_lenR O P_outer) sub_eq)
        in ruleTrans u1 (cong1 Fst iter_eq)

      -- Step 7: leq b P_outer  (b is the right child;  P_outer = sigma X b).
      leq_b_P : Deriv (leq b P_outer)
      leq_b_P =
        leq_sigma_right
          (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

      -- Step 8: HPsbt ... = ap1 lenR b  (recursive call recovery).
      HP_to_lenR :
        Deriv (eqF (HPsbt o stepFun_lenR O b P_outer) (ap1 lenR b))
      HP_to_lenR = lookup_eq_fold o stepFun_lenR b P_outer leq_b_P

      lookup_value :
        Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 lenR b))
      lookup_value = ruleTrans lookup_to_HP HP_to_lenR

      -- Step 9: stepBody_lenR input_pkg = s (lenR b).
      stepBody_value :
        Deriv (eqF (ap1 stepBody_lenR input_pkg) (ap1 s (ap1 lenR b)))
      stepBody_value =
        ruleTrans (compose1U_eq s (lookupAt get_rc) input_pkg)
                  (cong1 s lookup_value)
  in ruleTrans step1 (ruleTrans step2 stepBody_value)
