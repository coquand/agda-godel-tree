{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CheckAlph -- the OBJECT well-formedness checker  checkAlph : Fun1  for
-- program-code strings (SURPRISE-GII-INTERNAL-COVERAGE-HANDOFF.md, PLAN step 1).
--
-- A program code is a right-nested spine of tag-cells  pi (natCode tag) rest
-- ending in the leaf  O  ( the  enc -image, T4.ProgEnc :  enc t = encApp t O ,
-- with every cell head  natCode tag  a positive numeral, tag in {1,2,3} ).
-- checkAlph walks the right spine ( Snd-descending, the well-founded direction,
-- exactly as  T4.LenR.lenR ) and accepts iff
--
--   * the leaf is  O                       ( base : checkAlph O = s O ) , and
--   * every cell head is a SUCCESSOR        ( node : checkAlph (pi (s A) b)
--                                             = checkAlph b , the head  s A
--                                             being positive ) .
--
-- The cell-head positivity test is the object analog of "the tag is a genuine
-- alphabet symbol" ( meta  InAlph 's  iaPi / iaS , whose heads  natCode tag  are
-- all  s -headed ).   The two closure equations below are all the downstream
-- internalisation ( the  ⋁_k p = enum k  coverage ) consumes per program ; the
-- firing lemma  checkAlph_enc  shows every  enc t  passes.
--
-- Construction MIRRORS  T4.LenR  verbatim ( same course-of-values  fold  + the
-- same node-recovery plumbing ) ; only the step BODY differs : where  lenR
-- returns  s (lenR b) , checkAlph returns  condFork (pi O (checkAlph b))
-- (isZero head) , i.e. "if the head is zero reject ( O ) else pass on the
-- recursive verdict checkAlph b".

module T4.CheckAlph where

open import T4.Base
open import T4.FoldRec
open import T4.CoVSpec      using ( cov_spec )
open import T4.CoVSpecUniv  using ( HistP_sbt )
open import T4.Stability    using ( HPsbt )
open import T4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import T4.LeqMono      using ( leq_sigma_right )
open import T4.LenR         using ( get_rc )
open import T4.ProgParse    using ( get_tag )
open import T4.ProgEnc      using ( enc ; encApp ; tagLeaf ; tagUnary ; tagBinary )

open import BRA3.Church       using ( pi ; sub ; sigma ; tau ; isZero ; TisZeroSucc )
open import BRA3.ChurchT117   using ( Fst )
open import BRA3.ChurchT116   using ( Snd )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.Dispatch     using ( condFork ; condFork_false )

------------------------------------------------------------------------
-- SECTION 0.  The step body and the recursor.
--
--   stepBody_checkAlph input
--     = condFork (pi (Z input) (checkAlph b)) (isZero (get_tag input))
--
-- where  b = right child  ( get_rc input , the Snd-descending recursion target,
-- shared with  lenR ) and  get_tag input = Fst (node)  is the cell head.   At a
-- node  pi (s A) b  the head is  s A ,  isZero (s A) = O , so condFork selects
-- Snd = checkAlph b ; at the leaf  O  the recursor returns the base value  s O .

stepBody_checkAlph : Fun1
stepBody_checkAlph =
  C condFork (C pi Z (lookupAt get_rc)) (compose1U isZero get_tag)

stepFun_checkAlph : Fun2
stepFun_checkAlph = Post stepBody_checkAlph pi

-- Base  s O  (so  checkAlph O = (compose1U s Z) O = s (Z O) = s O ).
cbase : Fun1
cbase = compose1U s Z

checkAlph : Fun1
checkAlph = fold cbase stepFun_checkAlph

------------------------------------------------------------------------
-- SECTION 1.  checkAlph_at_O :  ap1 checkAlph O = s O .

checkAlph_at_O : Deriv (eqF (ap1 checkAlph O) (ap1 s O))
checkAlph_at_O =
  ruleTrans (fold_at_O cbase stepFun_checkAlph)
    (ruleTrans (compose1U_eq s Z O) (cong1 s (axZ O)))

------------------------------------------------------------------------
-- SECTION 2.  checkAlph_at_node :  ap1 checkAlph (pi (s A) b) = ap1 checkAlph b .
-- Universal in A, b.   Plumbing copied from  T4.LenR.lenR_at_node  ( same
-- fold / lookup recovery ), final step the condFork dispatch.

checkAlph_at_node :
  (A b : Term) ->
  Deriv (eqF (ap1 checkAlph (ap2 pi (ap1 s A) b)) (ap1 checkAlph b))
checkAlph_at_node A b =
  let node : Term
      node = ap2 pi (ap1 s A) b

      P_outer : Term
      P_outer = pi_succ_outer A b

      prev : Term
      prev = ap2 (cov_spec cbase stepFun_checkAlph) O P_outer

      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)

      -- Step 1: fold_node_unfold -- the step fires.
      step1 :
        Deriv (eqF (ap1 checkAlph node)
                    (ap2 stepFun_checkAlph P_outer (ap1 Snd prev)))
      step1 = fold_node_unfold cbase stepFun_checkAlph A b

      -- Step 2: stepFun_checkAlph = Post stepBody_checkAlph pi.
      step2 :
        Deriv (eqF (ap2 stepFun_checkAlph P_outer (ap1 Snd prev))
                    (ap1 stepBody_checkAlph input_pkg))
      step2 = axPost stepBody_checkAlph pi P_outer (ap1 Snd prev)

      -- Step 3: get_rc input_pkg = b   ( identical to lenR's get_rc_value ).
      get_rc_value : Deriv (eqF (ap1 get_rc input_pkg) b)
      get_rc_value =
        let s1 :
              Deriv (eqF (ap1 get_rc input_pkg) (ap1 Snd (ap1 get_newK input_pkg)))
            s1 = compose1U_eq Snd get_newK input_pkg
            s2 :
              Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
            s2 = get_newK_at_pi P_outer (ap1 Snd prev)
            s3 :
              Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd node))
            s3 = cong1 Snd (ruleSym (pi_at_succ A b))
            s4 : Deriv (eqF (ap1 Snd node) b)
            s4 = axSnd (ap1 s A) b
        in ruleTrans s1 (ruleTrans (cong1 Snd s2) (ruleTrans s3 s4))

      -- Step 4: get_K input_pkg = P_outer.
      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      -- Step 5: get_table input_pkg = HistP_sbt cbase stepFun_checkAlph O P_outer.
      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg)
                    (HistP_sbt cbase stepFun_checkAlph O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- Step 6: lookupAt get_rc input_pkg = HPsbt cbase stepFun_checkAlph O b P_outer.
      lookup_to_HP :
        Deriv (eqF (ap1 (lookupAt get_rc) input_pkg)
                    (HPsbt cbase stepFun_checkAlph O b P_outer))
      lookup_to_HP =
        let u1 :
              Deriv (eqF (ap1 (lookupAt get_rc) input_pkg)
                          (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                    (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg)))))
            u1 = lookupAt_unfold get_rc input_pkg
            sub_eq :
              Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg))
                          (ap2 sub P_outer b))
            sub_eq = ruleTrans (congL sub (ap1 get_rc input_pkg) get_K_value)
                               (congR sub P_outer get_rc_value)
            iter_eq :
              Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg)))
                          (ap2 (iter Snd) (HistP_sbt cbase stepFun_checkAlph O P_outer)
                          (ap2 sub P_outer b)))
            iter_eq =
              ruleTrans (congL (iter Snd)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg))
                          get_table_value)
                        (congR (iter Snd) (HistP_sbt cbase stepFun_checkAlph O P_outer) sub_eq)
        in ruleTrans u1 (cong1 Fst iter_eq)

      -- Step 7: leq b P_outer.
      leq_b_P : Deriv (leq b P_outer)
      leq_b_P =
        leq_sigma_right
          (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

      -- Step 8: HPsbt ... = ap1 checkAlph b  ( recursive call recovery ).
      HP_to_checkAlph :
        Deriv (eqF (HPsbt cbase stepFun_checkAlph O b P_outer) (ap1 checkAlph b))
      HP_to_checkAlph = lookup_eq_fold cbase stepFun_checkAlph b P_outer leq_b_P

      lookup_value :
        Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 checkAlph b))
      lookup_value = ruleTrans lookup_to_HP HP_to_checkAlph

      ------------------------------------------------------------------
      -- Step 9: the condFork dispatch.   The head  get_tag input_pkg = s A ,
      -- so its  isZero  is  O , so condFork selects  Snd = checkAlph b .

      -- 9a: get_tag input_pkg = s A.
      get_tag_value : Deriv (eqF (ap1 get_tag input_pkg) (ap1 s A))
      get_tag_value =
        let t1 : Deriv (eqF (ap1 get_tag input_pkg) (ap1 Fst (ap1 get_newK input_pkg)))
            t1 = compose1U_eq Fst get_newK input_pkg
            t2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
            t2 = get_newK_at_pi P_outer (ap1 Snd prev)
            t3 : Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst node))
            t3 = cong1 Fst (ruleSym (pi_at_succ A b))
            t4 : Deriv (eqF (ap1 Fst node) (ap1 s A))
            t4 = axFst (ap1 s A) b
        in ruleTrans t1 (ruleTrans (cong1 Fst t2) (ruleTrans t3 t4))

      -- 9b: the condition  isZero (get_tag input) = O .
      cond_value :
        Deriv (eqF (ap1 (compose1U isZero get_tag) input_pkg) O)
      cond_value =
        ruleTrans (compose1U_eq isZero get_tag input_pkg)
          (ruleTrans (cong1 isZero get_tag_value)
                     (ruleInst 0 A TisZeroSucc))

      -- 9c: the pair  C pi Z (lookupAt get_rc) input = pi (Z input) (checkAlph b).
      pairT : Term
      pairT = ap1 (C pi Z (lookupAt get_rc)) input_pkg

      pair_eq :
        Deriv (eqF pairT (ap2 pi (ap1 Z input_pkg) (ap1 (lookupAt get_rc) input_pkg)))
      pair_eq = ax_C pi Z (lookupAt get_rc) input_pkg

      -- 9d: stepBody = condFork pairT cond ; cond -> O ; condFork_false -> Snd pairT.
      sb1 :
        Deriv (eqF (ap1 stepBody_checkAlph input_pkg)
                    (ap2 condFork pairT (ap1 (compose1U isZero get_tag) input_pkg)))
      sb1 = ax_C condFork (C pi Z (lookupAt get_rc)) (compose1U isZero get_tag) input_pkg

      sb2 :
        Deriv (eqF (ap2 condFork pairT (ap1 (compose1U isZero get_tag) input_pkg))
                    (ap2 condFork pairT O))
      sb2 = congR condFork pairT cond_value

      sb3 : Deriv (eqF (ap2 condFork pairT O) (ap1 Snd pairT))
      sb3 = condFork_false pairT

      -- 9e: Snd pairT = checkAlph b.
      snd_value : Deriv (eqF (ap1 Snd pairT) (ap1 checkAlph b))
      snd_value =
        ruleTrans (cong1 Snd pair_eq)
          (ruleTrans (axSnd (ap1 Z input_pkg) (ap1 (lookupAt get_rc) input_pkg))
                     lookup_value)

      stepBody_value :
        Deriv (eqF (ap1 stepBody_checkAlph input_pkg) (ap1 checkAlph b))
      stepBody_value = ruleTrans sb1 (ruleTrans sb2 (ruleTrans sb3 snd_value))
  in ruleTrans step1 (ruleTrans step2 stepBody_value)

------------------------------------------------------------------------
-- SECTION 3.  Firing lemma :  every program-code string  encApp t rest
-- whose tail  rest  passes the check also passes ( threaded form, mirroring
-- T4.ProgEnc.lenR_encApp ) ; hence  checkAlph (enc t) = s O  for all  t .
--
-- The cell heads produced by  encApp  are  natCode tagLeaf / tagUnary /
-- tagBinary , all  s -headed positives, so every cell fires  checkAlph_at_node .

checkAlph_encApp :
  (t rest : Term) ->
  Deriv (eqF (ap1 checkAlph rest) (ap1 s O)) ->
  Deriv (eqF (ap1 checkAlph (encApp t rest)) (ap1 s O))
checkAlph_encApp O rest h =
  ruleTrans (checkAlph_at_node O rest) h
checkAlph_encApp (var k) rest h =
  ruleTrans (checkAlph_at_node O rest) h
checkAlph_encApp (ap1 f t) rest h =
  ruleTrans (checkAlph_at_node (ap1 s O) (encApp t rest))
            (checkAlph_encApp t rest h)
checkAlph_encApp (ap2 g a b) rest h =
  ruleTrans (checkAlph_at_node (ap1 s (ap1 s O)) (encApp a (encApp b rest)))
            (checkAlph_encApp a (encApp b rest)
              (checkAlph_encApp b rest h))

-- HEADLINE :  checkAlph (enc t) = s O  for every program tree  t .
checkAlph_enc :
  (t : Term) -> Deriv (eqF (ap1 checkAlph (enc t)) (ap1 s O))
checkAlph_enc t = checkAlph_encApp t O checkAlph_at_O
