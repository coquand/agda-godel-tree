{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ProgParse -- Phase E4, step R1b (CHAITIN-G1-FAITHFUL-BLUEPRINT.md S5bis):
-- the object DECODER  parse : Fun1  and the round-trip  parse (enc t) = t .
--
-- The universal machine runs  parse (nm)  on a program-string  nm ; on the
-- canonical preorder string  enc t  (BRA4.ProgEnc) the stack machine rebuilds
-- exactly the program  t .  This is the standard "decoder inverts encoder"
-- content of "U runs the description"; it is a straight SIMPLIFICATION of
-- BRA4.Parse / BRA4.ParseRoundtrip:
--   * cells are BARE  pi (natCode tag) rest  (no payload sub-pair) -- the
--     first child  natCode tag = s (...)  fires the fold directly;
--   * three tags push  O  / wrap  ap1 s  / wrap  ap2 pi  (no payload read);
--   * the round-trip target is  t  itself (not  codeTerm t ), on the
--     {O, ap1 s, ap2 pi} fragment  InAlph  (which  mcode  programs inhabit).

module BRA4.ProgParse where

open import BRA4.Base
open import BRA4.FoldRec
open import BRA4.CoVSpec      using ( cov_spec )
open import BRA4.CoVSpecUniv  using ( HistP_sbt )
open import BRA4.Stability    using ( HPsbt )
open import BRA4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import BRA4.LeqMono      using ( leq_sigma_right )
open import BRA4.ProgEnc      using ( enc ; encApp ; tagLeaf ; tagUnary ; tagBinary )

open import BRA3.Church          using ( pi ; sub ; sigma ; tau )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost ; Z ; axZ )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( condFork ; condFork_true_nc ; condFork_false ; constN ; constN_eq )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- Accessors.  The node is  pi (natCode tag) rest :  Fst = natCode tag
-- (the token tag, directly -- no cell sub-pair),  Snd = rest (recursion
-- target, = LenR's get_rc).

get_rest : Fun1
get_rest = compose1U Snd get_newK

get_tag : Fun1
get_tag = compose1U Fst get_newK

-- Recovered prior stack  parseS rest  (under leq rest P_outer).
priorStack : Fun1
priorStack = lookupAt get_rest

ps_top1 : Fun1
ps_top1 = compose1U Fst priorStack

ps_sub1 : Fun1
ps_sub1 = compose1U Snd priorStack

ps_top2 : Fun1
ps_top2 = compose1U Fst ps_sub1

ps_sub2 : Fun1
ps_sub2 = compose1U Snd ps_sub1

------------------------------------------------------------------------
-- Dispatch witnesses and the branch bodies.

isLeaf : Fun1
isLeaf = C natEqF get_tag (constN tagLeaf)

isUnary : Fun1
isUnary = C natEqF get_tag (constN tagUnary)

-- leaf  (push O):       pi O priorStack .
leaf_branch : Fun1
leaf_branch = C pi Z priorStack

-- unary (pop1, wrap s): pi (ap1 s top1) sub1 .
unary_branch : Fun1
unary_branch = C pi (compose1U s ps_top1) ps_sub1

-- binary (pop2, wrap pi): pi (ap2 pi top1 top2) sub2 .
binary_branch : Fun1
binary_branch = C pi (C pi ps_top1 ps_top2) ps_sub2

------------------------------------------------------------------------
-- The dispatch cascade.
--   isLeaf ? leaf_branch : (isUnary ? unary_branch : binary_branch)

unary_or_binary : Fun1
unary_or_binary = C condFork (C pi unary_branch binary_branch) isUnary

stepBody_parse : Fun1
stepBody_parse = C condFork (C pi leaf_branch unary_or_binary) isLeaf

stepFun_parse : Fun2
stepFun_parse = Post stepBody_parse pi

parseS : Fun1
parseS = fold o stepFun_parse

parse : Fun1
parse = compose1U Fst parseS

------------------------------------------------------------------------
-- parseS_at_O :  ap1 parseS O = O  (empty stack).

parseS_at_O : Deriv (eqF (ap1 parseS O) O)
parseS_at_O = ruleTrans (fold_at_O o stepFun_parse) (ax_o O)

------------------------------------------------------------------------
-- priorStack_at :  the recursion-recovery (LenR steps 3-8), GENERIC in A, b.
-- Copied from BRA4.Parse with  stepFun_parse  this module's.

priorStack_at :
  (A b : Term) ->
  Deriv (eqF (ap1 priorStack
               (ap2 pi (pi_succ_outer A b)
                       (ap1 Snd (ap2 (cov_spec o stepFun_parse) O (pi_succ_outer A b)))))
              (ap1 parseS b))
priorStack_at A b =
  let node : Term
      node = ap2 pi (ap1 s A) b
      P_outer : Term
      P_outer = pi_succ_outer A b
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)

      get_rest_value : Deriv (eqF (ap1 get_rest input_pkg) b)
      get_rest_value =
        let r1 : Deriv (eqF (ap1 get_rest input_pkg) (ap1 Snd (ap1 get_newK input_pkg)))
            r1 = compose1U_eq Snd get_newK input_pkg
            r2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
            r2 = get_newK_at_pi P_outer (ap1 Snd prev)
            r3 : Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd node))
            r3 = cong1 Snd (ruleSym (pi_at_succ A b))
            r4 : Deriv (eqF (ap1 Snd node) b)
            r4 = axSnd (ap1 s A) b
        in ruleTrans r1 (ruleTrans (cong1 Snd r2) (ruleTrans r3 r4))

      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg)
                    (HistP_sbt o stepFun_parse O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      lookup_to_HP :
        Deriv (eqF (ap1 priorStack input_pkg)
                    (HPsbt o stepFun_parse O b P_outer))
      lookup_to_HP =
        let u1 :
              Deriv (eqF (ap1 priorStack input_pkg)
                          (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                    (ap2 sub (ap1 get_K input_pkg) (ap1 get_rest input_pkg)))))
            u1 = lookupAt_unfold get_rest input_pkg
            sub_eq :
              Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 get_rest input_pkg))
                          (ap2 sub P_outer b))
            sub_eq = ruleTrans (congL sub (ap1 get_rest input_pkg) get_K_value)
                               (congR sub P_outer get_rest_value)
            iter_eq :
              Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 get_rest input_pkg)))
                          (ap2 (iter Snd) (HistP_sbt o stepFun_parse O P_outer)
                          (ap2 sub P_outer b)))
            iter_eq =
              ruleTrans (congL (iter Snd)
                          (ap2 sub (ap1 get_K input_pkg) (ap1 get_rest input_pkg))
                          get_table_value)
                        (congR (iter Snd) (HistP_sbt o stepFun_parse O P_outer) sub_eq)
        in ruleTrans u1 (cong1 Fst iter_eq)

      leq_b_P : Deriv (leq b P_outer)
      leq_b_P =
        leq_sigma_right
          (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

      HP_to_parse :
        Deriv (eqF (HPsbt o stepFun_parse O b P_outer) (ap1 parseS b))
      HP_to_parse = lookup_eq_fold o stepFun_parse b P_outer leq_b_P
  in ruleTrans lookup_to_HP HP_to_parse

------------------------------------------------------------------------
-- Per-node accessor reductions, parametric in (m, rest).  The node is
--   pi (natCode (suc m)) rest = pi (s (natCode m)) rest  (s-headed directly).

private
  get_newK_eq_node :
    (m : Nat) (rest : Term) ->
    let P_outer = pi_succ_outer (natCode m) rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 get_newK input_pkg) (ap2 pi (natCode (suc m)) rest))
  get_newK_eq_node m rest =
    let P_outer : Term
        P_outer = pi_succ_outer (natCode m) rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        g1 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        g1 = get_newK_at_pi P_outer (ap1 Snd prev)
        g2 : Deriv (eqF (ap1 s P_outer) (ap2 pi (ap1 s (natCode m)) rest))
        g2 = ruleSym (pi_at_succ (natCode m) rest)
    in ruleTrans g1 g2

  get_tag_eq :
    (m : Nat) (rest : Term) ->
    let P_outer = pi_succ_outer (natCode m) rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 get_tag input_pkg) (natCode (suc m)))
  get_tag_eq m rest =
    let P_outer : Term
        P_outer = pi_succ_outer (natCode m) rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        t1 : Deriv (eqF (ap1 get_tag input_pkg) (ap1 Fst (ap1 get_newK input_pkg)))
        t1 = compose1U_eq Fst get_newK input_pkg
        t2 : Deriv (eqF (ap1 Fst (ap1 get_newK input_pkg))
                        (ap1 Fst (ap2 pi (natCode (suc m)) rest)))
        t2 = cong1 Fst (get_newK_eq_node m rest)
        t3 : Deriv (eqF (ap1 Fst (ap2 pi (natCode (suc m)) rest)) (natCode (suc m)))
        t3 = axFst (natCode (suc m)) rest
    in ruleTrans t1 (ruleTrans t2 t3)

  isLeaf_value :
    (m : Nat) (rest : Term) ->
    let P_outer = pi_succ_outer (natCode m) rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 isLeaf input_pkg)
                  (ap2 natEqF (natCode (suc m)) (natCode tagLeaf)))
  isLeaf_value m rest =
    let P_outer : Term
        P_outer = pi_succ_outer (natCode m) rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        i1 : Deriv (eqF (ap1 isLeaf input_pkg)
                        (ap2 natEqF (ap1 get_tag input_pkg) (ap1 (constN tagLeaf) input_pkg)))
        i1 = ax_C natEqF get_tag (constN tagLeaf) input_pkg
        i2 : Deriv (eqF (ap1 (constN tagLeaf) input_pkg) (natCode tagLeaf))
        i2 = constN_eq tagLeaf input_pkg
        i3 : Deriv (eqF (ap1 get_tag input_pkg) (natCode (suc m)))
        i3 = get_tag_eq m rest
    in ruleTrans i1 (ruleTrans (congL natEqF (ap1 (constN tagLeaf) input_pkg) i3)
                               (congR natEqF (natCode (suc m)) i2))

  isUnary_value :
    (m : Nat) (rest : Term) ->
    let P_outer = pi_succ_outer (natCode m) rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 isUnary input_pkg)
                  (ap2 natEqF (natCode (suc m)) (natCode tagUnary)))
  isUnary_value m rest =
    let P_outer : Term
        P_outer = pi_succ_outer (natCode m) rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        i1 : Deriv (eqF (ap1 isUnary input_pkg)
                        (ap2 natEqF (ap1 get_tag input_pkg) (ap1 (constN tagUnary) input_pkg)))
        i1 = ax_C natEqF get_tag (constN tagUnary) input_pkg
        i2 : Deriv (eqF (ap1 (constN tagUnary) input_pkg) (natCode tagUnary))
        i2 = constN_eq tagUnary input_pkg
        i3 : Deriv (eqF (ap1 get_tag input_pkg) (natCode (suc m)))
        i3 = get_tag_eq m rest
    in ruleTrans i1 (ruleTrans (congL natEqF (ap1 (constN tagUnary) input_pkg) i3)
                               (congR natEqF (natCode (suc m)) i2))

------------------------------------------------------------------------
-- Tag-distinctness witnesses.

private
  w_unary_leaf : NatNeqWitness 2 1
  w_unary_leaf = decideNatNeq 2 1 (\ ())
  w_binary_leaf : NatNeqWitness 3 1
  w_binary_leaf = decideNatNeq 3 1 (\ ())
  w_binary_unary : NatNeqWitness 3 2
  w_binary_unary = decideNatNeq 3 2 (\ ())

------------------------------------------------------------------------
-- Cascade firing (generic in the step input).

private
  stepBody_to_leaf :
    (input : Term) -> Deriv (eqF (ap1 isLeaf input) (ap1 s O)) ->
    Deriv (eqF (ap1 stepBody_parse input) (ap1 leaf_branch input))
  stepBody_to_leaf input isLeaf_sO =
    let pairT : Term
        pairT = ap1 (C pi leaf_branch unary_or_binary) input
        e1 : Deriv (eqF (ap1 stepBody_parse input) (ap2 condFork pairT (ap1 isLeaf input)))
        e1 = ax_C condFork (C pi leaf_branch unary_or_binary) isLeaf input
        sub_eq : Deriv (eqF (ap2 condFork pairT (ap1 isLeaf input)) (ap2 condFork pairT (ap1 s O)))
        sub_eq = congR condFork pairT isLeaf_sO
        fire : Deriv (eqF (ap2 condFork pairT (ap1 s O)) (ap1 Fst pairT))
        fire = condFork_true_nc pairT O
        pi_eq : Deriv (eqF pairT (ap2 pi (ap1 leaf_branch input) (ap1 unary_or_binary input)))
        pi_eq = ax_C pi leaf_branch unary_or_binary input
        Fst_pi : Deriv (eqF (ap1 Fst (ap2 pi (ap1 leaf_branch input) (ap1 unary_or_binary input)))
                            (ap1 leaf_branch input))
        Fst_pi = axFst (ap1 leaf_branch input) (ap1 unary_or_binary input)
    in ruleTrans e1 (ruleTrans sub_eq (ruleTrans fire (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  stepBody_to_uob :
    (input : Term) -> Deriv (eqF (ap1 isLeaf input) O) ->
    Deriv (eqF (ap1 stepBody_parse input) (ap1 unary_or_binary input))
  stepBody_to_uob input isLeaf_O =
    let pairT : Term
        pairT = ap1 (C pi leaf_branch unary_or_binary) input
        e1 : Deriv (eqF (ap1 stepBody_parse input) (ap2 condFork pairT (ap1 isLeaf input)))
        e1 = ax_C condFork (C pi leaf_branch unary_or_binary) isLeaf input
        sub_eq : Deriv (eqF (ap2 condFork pairT (ap1 isLeaf input)) (ap2 condFork pairT O))
        sub_eq = congR condFork pairT isLeaf_O
        fire : Deriv (eqF (ap2 condFork pairT O) (ap1 Snd pairT))
        fire = condFork_false pairT
        pi_eq : Deriv (eqF pairT (ap2 pi (ap1 leaf_branch input) (ap1 unary_or_binary input)))
        pi_eq = ax_C pi leaf_branch unary_or_binary input
        Snd_pi : Deriv (eqF (ap1 Snd (ap2 pi (ap1 leaf_branch input) (ap1 unary_or_binary input)))
                            (ap1 unary_or_binary input))
        Snd_pi = axSnd (ap1 leaf_branch input) (ap1 unary_or_binary input)
    in ruleTrans e1 (ruleTrans sub_eq (ruleTrans fire (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  uob_to_unary :
    (input : Term) -> Deriv (eqF (ap1 isUnary input) (ap1 s O)) ->
    Deriv (eqF (ap1 unary_or_binary input) (ap1 unary_branch input))
  uob_to_unary input isUnary_sO =
    let pair2 : Term
        pair2 = ap1 (C pi unary_branch binary_branch) input
        e1 : Deriv (eqF (ap1 unary_or_binary input) (ap2 condFork pair2 (ap1 isUnary input)))
        e1 = ax_C condFork (C pi unary_branch binary_branch) isUnary input
        sub_eq : Deriv (eqF (ap2 condFork pair2 (ap1 isUnary input)) (ap2 condFork pair2 (ap1 s O)))
        sub_eq = congR condFork pair2 isUnary_sO
        fire : Deriv (eqF (ap2 condFork pair2 (ap1 s O)) (ap1 Fst pair2))
        fire = condFork_true_nc pair2 O
        pi_eq : Deriv (eqF pair2 (ap2 pi (ap1 unary_branch input) (ap1 binary_branch input)))
        pi_eq = ax_C pi unary_branch binary_branch input
        Fst_pi : Deriv (eqF (ap1 Fst (ap2 pi (ap1 unary_branch input) (ap1 binary_branch input)))
                            (ap1 unary_branch input))
        Fst_pi = axFst (ap1 unary_branch input) (ap1 binary_branch input)
    in ruleTrans e1 (ruleTrans sub_eq (ruleTrans fire (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  uob_to_binary :
    (input : Term) -> Deriv (eqF (ap1 isUnary input) O) ->
    Deriv (eqF (ap1 unary_or_binary input) (ap1 binary_branch input))
  uob_to_binary input isUnary_O =
    let pair2 : Term
        pair2 = ap1 (C pi unary_branch binary_branch) input
        e1 : Deriv (eqF (ap1 unary_or_binary input) (ap2 condFork pair2 (ap1 isUnary input)))
        e1 = ax_C condFork (C pi unary_branch binary_branch) isUnary input
        sub_eq : Deriv (eqF (ap2 condFork pair2 (ap1 isUnary input)) (ap2 condFork pair2 O))
        sub_eq = congR condFork pair2 isUnary_O
        fire : Deriv (eqF (ap2 condFork pair2 O) (ap1 Snd pair2))
        fire = condFork_false pair2
        pi_eq : Deriv (eqF pair2 (ap2 pi (ap1 unary_branch input) (ap1 binary_branch input)))
        pi_eq = ax_C pi unary_branch binary_branch input
        Snd_pi : Deriv (eqF (ap1 Snd (ap2 pi (ap1 unary_branch input) (ap1 binary_branch input)))
                            (ap1 binary_branch input))
        Snd_pi = axSnd (ap1 unary_branch input) (ap1 binary_branch input)
    in ruleTrans e1 (ruleTrans sub_eq (ruleTrans fire (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

------------------------------------------------------------------------
-- Node closure: LEAF.   parseS (pi (natCode tagLeaf) rest) = pi O (parseS rest).

parse_at_leaf :
  (rest : Term) ->
  Deriv (eqF (ap1 parseS (ap2 pi (natCode tagLeaf) rest)) (ap2 pi O (ap1 parseS rest)))
parse_at_leaf rest =
  let P_outer : Term
      P_outer = pi_succ_outer O rest
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)

      e0 : Deriv (eqF (ap1 parseS (ap2 pi (ap1 s O) rest))
                      (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      e0 = fold_node_unfold o stepFun_parse O rest

      post_eq : Deriv (eqF (ap2 stepFun_parse P_outer (ap1 Snd prev))
                           (ap1 stepBody_parse input_pkg))
      post_eq = axPost stepBody_parse pi P_outer (ap1 Snd prev)

      isLeaf_sO : Deriv (eqF (ap1 isLeaf input_pkg) (ap1 s O))
      isLeaf_sO = ruleTrans (isLeaf_value 0 rest) (natEq_eq tagLeaf)

      to_leaf : Deriv (eqF (ap1 stepBody_parse input_pkg) (ap1 leaf_branch input_pkg))
      to_leaf = stepBody_to_leaf input_pkg isLeaf_sO

      lb_eq : Deriv (eqF (ap1 leaf_branch input_pkg)
                         (ap2 pi (ap1 Z input_pkg) (ap1 priorStack input_pkg)))
      lb_eq = ax_C pi Z priorStack input_pkg

      z_v : Deriv (eqF (ap1 Z input_pkg) O)
      z_v = axZ input_pkg

      prior_v : Deriv (eqF (ap1 priorStack input_pkg) (ap1 parseS rest))
      prior_v = priorStack_at O rest

      lb_value : Deriv (eqF (ap1 leaf_branch input_pkg) (ap2 pi O (ap1 parseS rest)))
      lb_value = ruleTrans lb_eq
                   (ruleTrans (congL pi (ap1 priorStack input_pkg) z_v)
                              (congR pi O prior_v))
  in ruleTrans e0 (ruleTrans post_eq (ruleTrans to_leaf lb_value))

------------------------------------------------------------------------
-- Node closure: UNARY.   parseS (pi (natCode tagUnary) rest)
--   = pi (ap1 s (Fst PS)) (Snd PS)  where PS = parseS rest.

parse_at_unary :
  (rest : Term) ->
  Deriv (eqF (ap1 parseS (ap2 pi (natCode tagUnary) rest))
              (ap2 pi (ap1 s (ap1 Fst (ap1 parseS rest))) (ap1 Snd (ap1 parseS rest))))
parse_at_unary rest =
  let P_outer : Term
      P_outer = pi_succ_outer (natCode 1) rest
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)
      PS : Term
      PS = ap1 parseS rest

      e0 : Deriv (eqF (ap1 parseS (ap2 pi (ap1 s (natCode 1)) rest))
                      (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      e0 = fold_node_unfold o stepFun_parse (natCode 1) rest

      post_eq : Deriv (eqF (ap2 stepFun_parse P_outer (ap1 Snd prev))
                           (ap1 stepBody_parse input_pkg))
      post_eq = axPost stepBody_parse pi P_outer (ap1 Snd prev)

      isLeaf_O : Deriv (eqF (ap1 isLeaf input_pkg) O)
      isLeaf_O = ruleTrans (isLeaf_value 1 rest) (natEqF_at_neq 2 1 w_unary_leaf)

      isUnary_sO : Deriv (eqF (ap1 isUnary input_pkg) (ap1 s O))
      isUnary_sO = ruleTrans (isUnary_value 1 rest) (natEq_eq tagUnary)

      to_unary : Deriv (eqF (ap1 stepBody_parse input_pkg) (ap1 unary_branch input_pkg))
      to_unary = ruleTrans (stepBody_to_uob input_pkg isLeaf_O)
                           (uob_to_unary input_pkg isUnary_sO)

      prior_v : Deriv (eqF (ap1 priorStack input_pkg) PS)
      prior_v = priorStack_at (natCode 1) rest

      top1_v : Deriv (eqF (ap1 ps_top1 input_pkg) (ap1 Fst PS))
      top1_v = ruleTrans (compose1U_eq Fst priorStack input_pkg) (cong1 Fst prior_v)

      sub1_v : Deriv (eqF (ap1 ps_sub1 input_pkg) (ap1 Snd PS))
      sub1_v = ruleTrans (compose1U_eq Snd priorStack input_pkg) (cong1 Snd prior_v)

      built_v : Deriv (eqF (ap1 (compose1U s ps_top1) input_pkg) (ap1 s (ap1 Fst PS)))
      built_v = ruleTrans (compose1U_eq s ps_top1 input_pkg) (cong1 s top1_v)

      ub_eq : Deriv (eqF (ap1 unary_branch input_pkg)
                         (ap2 pi (ap1 (compose1U s ps_top1) input_pkg) (ap1 ps_sub1 input_pkg)))
      ub_eq = ax_C pi (compose1U s ps_top1) ps_sub1 input_pkg

      ub_full : Deriv (eqF (ap1 unary_branch input_pkg)
                           (ap2 pi (ap1 s (ap1 Fst PS)) (ap1 Snd PS)))
      ub_full = ruleTrans ub_eq
                  (ruleTrans (congL pi (ap1 ps_sub1 input_pkg) built_v)
                             (congR pi (ap1 s (ap1 Fst PS)) sub1_v))
  in ruleTrans e0 (ruleTrans post_eq (ruleTrans to_unary ub_full))

------------------------------------------------------------------------
-- Node closure: BINARY.   parseS (pi (natCode tagBinary) rest)
--   = pi (ap2 pi (Fst PS) (Fst (Snd PS))) (Snd (Snd PS))  where PS = parseS rest.

parse_at_binary :
  (rest : Term) ->
  Deriv (eqF (ap1 parseS (ap2 pi (natCode tagBinary) rest))
              (ap2 pi (ap2 pi (ap1 Fst (ap1 parseS rest))
                              (ap1 Fst (ap1 Snd (ap1 parseS rest))))
                      (ap1 Snd (ap1 Snd (ap1 parseS rest)))))
parse_at_binary rest =
  let P_outer : Term
      P_outer = pi_succ_outer (natCode 2) rest
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)
      PS : Term
      PS = ap1 parseS rest

      e0 : Deriv (eqF (ap1 parseS (ap2 pi (ap1 s (natCode 2)) rest))
                      (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      e0 = fold_node_unfold o stepFun_parse (natCode 2) rest

      post_eq : Deriv (eqF (ap2 stepFun_parse P_outer (ap1 Snd prev))
                           (ap1 stepBody_parse input_pkg))
      post_eq = axPost stepBody_parse pi P_outer (ap1 Snd prev)

      isLeaf_O : Deriv (eqF (ap1 isLeaf input_pkg) O)
      isLeaf_O = ruleTrans (isLeaf_value 2 rest) (natEqF_at_neq 3 1 w_binary_leaf)

      isUnary_O : Deriv (eqF (ap1 isUnary input_pkg) O)
      isUnary_O = ruleTrans (isUnary_value 2 rest) (natEqF_at_neq 3 2 w_binary_unary)

      to_binary : Deriv (eqF (ap1 stepBody_parse input_pkg) (ap1 binary_branch input_pkg))
      to_binary = ruleTrans (stepBody_to_uob input_pkg isLeaf_O)
                            (uob_to_binary input_pkg isUnary_O)

      prior_v : Deriv (eqF (ap1 priorStack input_pkg) PS)
      prior_v = priorStack_at (natCode 2) rest

      top1_v : Deriv (eqF (ap1 ps_top1 input_pkg) (ap1 Fst PS))
      top1_v = ruleTrans (compose1U_eq Fst priorStack input_pkg) (cong1 Fst prior_v)

      sub1_v : Deriv (eqF (ap1 ps_sub1 input_pkg) (ap1 Snd PS))
      sub1_v = ruleTrans (compose1U_eq Snd priorStack input_pkg) (cong1 Snd prior_v)

      top2_v : Deriv (eqF (ap1 ps_top2 input_pkg) (ap1 Fst (ap1 Snd PS)))
      top2_v = ruleTrans (compose1U_eq Fst ps_sub1 input_pkg) (cong1 Fst sub1_v)

      sub2_v : Deriv (eqF (ap1 ps_sub2 input_pkg) (ap1 Snd (ap1 Snd PS)))
      sub2_v = ruleTrans (compose1U_eq Snd ps_sub1 input_pkg) (cong1 Snd sub1_v)

      inner_eq : Deriv (eqF (ap1 (C pi ps_top1 ps_top2) input_pkg)
                            (ap2 pi (ap1 ps_top1 input_pkg) (ap1 ps_top2 input_pkg)))
      inner_eq = ax_C pi ps_top1 ps_top2 input_pkg

      inner_full : Deriv (eqF (ap1 (C pi ps_top1 ps_top2) input_pkg)
                              (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS))))
      inner_full = ruleTrans inner_eq
                     (ruleTrans (congL pi (ap1 ps_top2 input_pkg) top1_v)
                                (congR pi (ap1 Fst PS) top2_v))

      bb_eq : Deriv (eqF (ap1 binary_branch input_pkg)
                         (ap2 pi (ap1 (C pi ps_top1 ps_top2) input_pkg) (ap1 ps_sub2 input_pkg)))
      bb_eq = ax_C pi (C pi ps_top1 ps_top2) ps_sub2 input_pkg

      bb_full : Deriv (eqF (ap1 binary_branch input_pkg)
                           (ap2 pi (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS)))
                                   (ap1 Snd (ap1 Snd PS))))
      bb_full = ruleTrans bb_eq
                  (ruleTrans (congL pi (ap1 ps_sub2 input_pkg) inner_full)
                             (congR pi (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS))) sub2_v))
  in ruleTrans e0 (ruleTrans post_eq (ruleTrans to_binary bb_full))

------------------------------------------------------------------------
-- The {O, ap1 s, ap2 pi} fragment that mcode programs inhabit, and the
-- round-trip stack-PUSH invariant over it.

data InAlph : Term -> Set where
  iaO  : InAlph O
  iaS  : (t : Term) -> InAlph t -> InAlph (ap1 s t)
  iaPi : (a b : Term) -> InAlph a -> InAlph b -> InAlph (ap2 pi a b)

private
  unary_collapse :
    (rest q1 tail : Term) ->
    Deriv (eqF (ap1 parseS rest) (ap2 pi q1 tail)) ->
    Deriv (eqF (ap1 parseS (ap2 pi (natCode tagUnary) rest))
                (ap2 pi (ap1 s q1) tail))
  unary_collapse rest q1 tail ps_eq =
    let PS : Term
        PS = ap1 parseS rest
        raw : Deriv (eqF (ap1 parseS (ap2 pi (natCode tagUnary) rest))
                          (ap2 pi (ap1 s (ap1 Fst PS)) (ap1 Snd PS)))
        raw = parse_at_unary rest
        fst_ps : Deriv (eqF (ap1 Fst PS) q1)
        fst_ps = ruleTrans (cong1 Fst ps_eq) (axFst q1 tail)
        snd_ps : Deriv (eqF (ap1 Snd PS) tail)
        snd_ps = ruleTrans (cong1 Snd ps_eq) (axSnd q1 tail)
        full : Deriv (eqF (ap2 pi (ap1 s (ap1 Fst PS)) (ap1 Snd PS))
                          (ap2 pi (ap1 s q1) tail))
        full = ruleTrans (congL pi (ap1 Snd PS) (cong1 s fst_ps))
                         (congR pi (ap1 s q1) snd_ps)
    in ruleTrans raw full

  binary_collapse :
    (rest q1 q2 tail : Term) ->
    Deriv (eqF (ap1 parseS rest) (ap2 pi q1 (ap2 pi q2 tail))) ->
    Deriv (eqF (ap1 parseS (ap2 pi (natCode tagBinary) rest))
                (ap2 pi (ap2 pi q1 q2) tail))
  binary_collapse rest q1 q2 tail ps_eq =
    let PS : Term
        PS = ap1 parseS rest
        raw : Deriv (eqF (ap1 parseS (ap2 pi (natCode tagBinary) rest))
                          (ap2 pi (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS)))
                                  (ap1 Snd (ap1 Snd PS))))
        raw = parse_at_binary rest
        fst_ps : Deriv (eqF (ap1 Fst PS) q1)
        fst_ps = ruleTrans (cong1 Fst ps_eq) (axFst q1 (ap2 pi q2 tail))
        snd_ps : Deriv (eqF (ap1 Snd PS) (ap2 pi q2 tail))
        snd_ps = ruleTrans (cong1 Snd ps_eq) (axSnd q1 (ap2 pi q2 tail))
        fst_snd_ps : Deriv (eqF (ap1 Fst (ap1 Snd PS)) q2)
        fst_snd_ps = ruleTrans (cong1 Fst snd_ps) (axFst q2 tail)
        snd_snd_ps : Deriv (eqF (ap1 Snd (ap1 Snd PS)) tail)
        snd_snd_ps = ruleTrans (cong1 Snd snd_ps) (axSnd q2 tail)
        inner : Deriv (eqF (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS))) (ap2 pi q1 q2))
        inner = ruleTrans (congL pi (ap1 Fst (ap1 Snd PS)) fst_ps) (congR pi q1 fst_snd_ps)
        full : Deriv (eqF (ap2 pi (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS)))
                                  (ap1 Snd (ap1 Snd PS)))
                          (ap2 pi (ap2 pi q1 q2) tail))
        full = ruleTrans (congL pi (ap1 Snd (ap1 Snd PS)) inner)
                         (congR pi (ap2 pi q1 q2) snd_snd_ps)
    in ruleTrans raw full

push :
  (t : Term) -> InAlph t -> (rest : Term) ->
  Deriv (eqF (ap1 parseS (encApp t rest)) (ap2 pi t (ap1 parseS rest)))
push O          iaO            rest = parse_at_leaf rest
push (ap1 s t)  (iaS .t ia)    rest =
  unary_collapse (encApp t rest) t (ap1 parseS rest) (push t ia rest)
push (ap2 pi a b) (iaPi .a .b iaa iab) rest =
  binary_collapse (encApp a (encApp b rest)) a b (ap1 parseS rest)
    (ruleTrans (push a iaa (encApp b rest)) (congR pi a (push b iab rest)))

------------------------------------------------------------------------
-- HEADLINE:  parse (enc t) = t   for every  t  in the fragment.

parse_enc :
  (t : Term) -> InAlph t ->
  Deriv (eqF (ap1 parse (enc t)) t)
parse_enc t ia =
  let e1 : Deriv (eqF (ap1 parse (enc t)) (ap1 Fst (ap1 parseS (enc t))))
      e1 = compose1U_eq Fst parseS (enc t)
      e2 : Deriv (eqF (ap1 parseS (enc t)) (ap2 pi t (ap1 parseS O)))
      e2 = push t ia O
      e3 : Deriv (eqF (ap1 Fst (ap1 parseS (enc t))) (ap1 Fst (ap2 pi t (ap1 parseS O))))
      e3 = cong1 Fst e2
      e4 : Deriv (eqF (ap1 Fst (ap2 pi t (ap1 parseS O))) t)
      e4 = axFst t (ap1 parseS O)
  in ruleTrans e1 (ruleTrans e3 e4)
