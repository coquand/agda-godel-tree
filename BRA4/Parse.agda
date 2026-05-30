{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Parse -- the object  parse : Fun1  for the Kritchman-Raz KR-A
-- name format:  a STACK-MACHINE  FoldRec  instance that decodes a
-- right-recursive PREFIX (Polish) linearization of a TERM back into
-- the tree code  codeTerm t  that  thmT  reads.
--
-- ======================================================================
-- WHY (recap of SPIKE-KR-NAME-FORMAT-DECISION.md / PARSE-DESIGN.md).
-- ======================================================================
--
-- The KR-C pigeonhole needs the length-<=ell "name" class FINITE.
-- lenR over TREE codes is infinite-per-length (it ignores Fst children),
-- so names are right-recursive LINEAR codes (lenR = faithful token count)
-- and  parse  rebuilds the tree code.  Names are atomic equations
-- "v0 = t" with  t  a TERM, so  parse  decodes linearized TERMS only.
--
-- ======================================================================
-- CONSTRUCTION.
-- ======================================================================
--
-- A linearization is a right-recursive list of CELLS:
--
--   list  ::=  O                          -- empty
--          |   pi cell rest                -- cons
--   cell  ::=  pi (natCode ptag) payload   -- a token (ptag >= 1)
--
-- Three token kinds (ptag = 1/2/3):
--   * ptag_leaf : payload = the code to PUSH (a leaf term/Fun1/Fun2 code,
--                 or codeTerm (var k) which carries its own k).
--   * ptag_ar2  : an ARITY-2 builder (ap1).  payload = the built-node tag.
--   * ptag_ar3  : an ARITY-3 builder (ap2 / C / R).  payload = built tag.
--
-- parse  is  fold o stepFun_parse  whose accumulator is a STACK
-- (a right-nested Pair list).  Because  FoldRec.fold  is a course-of-
-- values RIGHT fold, a PREFIX list is processed right-to-left with the
-- stack -- the classic "evaluate Polish notation right-to-left".  The
-- stepFun dispatches on the token tag and does the stack op:
--   * leaf : push  payload .
--   * ar2  : pop 2 (top1, top2), push  pi payload (pi top1 top2) .
--   * ar3  : pop 3 (top1,top2,top3), push  pi payload (pi top1 (pi top2 top3)) .
--
-- The user-facing  parse = Fst o parseS  reads the final (single) stack
-- top.  Correctness (round-trip) is in BRA4.ParseRoundtrip.
--
-- This is a straight REDEPLOY of  BRA4.LenR  (the simplest FoldRec
-- instance) + the  condFork  tag-dispatch cascade of  BRA4.SbtAtAp .
-- No new primitive.

module BRA4.Parse where

open import BRA4.Base
open import BRA4.FoldRec
open import BRA4.CoVSpec      using ( cov_spec )
open import BRA4.CoVSpecUniv  using ( HistP_sbt )
open import BRA4.Stability    using ( HPsbt )
open import BRA4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import BRA4.LeqMono      using ( leq_sigma_right )

open import BRA3.Church          using ( pi ; sub ; sigma ; tau )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using
  ( condFork ; condFork_true_nc ; condFork_false ; constN ; constN_eq )
open import BRA3.SubT.NatEq      using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq   using
  ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- Token tags.

ptag_leaf : Nat
ptag_leaf = 1

ptag_ar2  : Nat
ptag_ar2  = 2

ptag_ar3  : Nat
ptag_ar3  = 3

-- Cells (meta-level Term builders).

cellLeaf : Term -> Term
cellLeaf code = ap2 pi (natCode ptag_leaf) code

cellAr2 : Term -> Term
cellAr2 p = ap2 pi (natCode ptag_ar2) p

cellAr3 : Term -> Term
cellAr3 p = ap2 pi (natCode ptag_ar3) p

------------------------------------------------------------------------
-- Accessors (Fun1 of the packaged step input  pi P_outer inner ).
--
-- get_newK input = s (Fst input) = the NODE  pi cell rest .
-- get_rest = Snd o get_newK  = rest  (the recursion target, = LenR's get_rc).
-- get_cell = Fst o get_newK  = cell.
-- get_toktag = Fst o get_cell = natCode ptag.
-- get_payload = Snd o get_cell = payload.

get_rest : Fun1
get_rest = compose1U Snd get_newK

get_cell : Fun1
get_cell = compose1U Fst get_newK

get_toktag : Fun1
get_toktag = compose1U Fst get_cell

get_payload : Fun1
get_payload = compose1U Snd get_cell

-- The recovered prior stack  parseS rest  (under leq rest P_outer).

priorStack : Fun1
priorStack = lookupAt get_rest

------------------------------------------------------------------------
-- Stack-op helpers.

-- Tops of the prior stack.
ps_top1 : Fun1
ps_top1 = compose1U Fst priorStack

ps_sub1 : Fun1                                   -- Snd priorStack
ps_sub1 = compose1U Snd priorStack

ps_top2 : Fun1
ps_top2 = compose1U Fst ps_sub1

ps_sub2 : Fun1                                   -- Snd (Snd priorStack)
ps_sub2 = compose1U Snd ps_sub1

ps_top3 : Fun1
ps_top3 = compose1U Fst ps_sub2

ps_sub3 : Fun1                                   -- Snd (Snd (Snd priorStack))
ps_sub3 = compose1U Snd ps_sub2

------------------------------------------------------------------------
-- Dispatch witnesses.

isLeaf : Fun1
isLeaf = C natEqF get_toktag (constN ptag_leaf)

isAr2 : Fun1
isAr2 = C natEqF get_toktag (constN ptag_ar2)

------------------------------------------------------------------------
-- Branch bodies (Fun1 of the packaged input).

-- leaf: push payload.            ->  pi payload priorStack
leaf_branch : Fun1
leaf_branch = C pi get_payload priorStack

-- ar2: pop 2, build  pi payload (pi top1 top2) , push.
--   newstack = pi (pi payload (pi top1 top2)) rest2
ar2_built : Fun1
ar2_built = C pi get_payload (C pi ps_top1 ps_top2)

ar2_branch : Fun1
ar2_branch = C pi ar2_built ps_sub2

-- ar3: pop 3, build  pi payload (pi top1 (pi top2 top3)) , push.
--   newstack = pi (pi payload (pi top1 (pi top2 top3))) rest3
ar3_built : Fun1
ar3_built = C pi get_payload (C pi ps_top1 (C pi ps_top2 ps_top3))

ar3_branch : Fun1
ar3_branch = C pi ar3_built ps_sub3

------------------------------------------------------------------------
-- The dispatch cascade.
--
--   isLeaf ? leaf_branch : (isAr2 ? ar2_branch : ar3_branch)

ar2_or_ar3 : Fun1
ar2_or_ar3 = C condFork (C pi ar2_branch ar3_branch) isAr2

stepBody_parse : Fun1
stepBody_parse = C condFork (C pi leaf_branch ar2_or_ar3) isLeaf

stepFun_parse : Fun2
stepFun_parse = Post stepBody_parse pi

------------------------------------------------------------------------
-- The fold (stack-valued) and the user-facing  parse  (final top).

parseS : Fun1
parseS = fold o stepFun_parse

parse : Fun1
parse = compose1U Fst parseS

------------------------------------------------------------------------
-- parseS_at_O :  ap1 parseS O = O .  (empty stack)

parseS_at_O : Deriv (eqF (ap1 parseS O) O)
parseS_at_O = ruleTrans (fold_at_O o stepFun_parse) (ax_o O)

------------------------------------------------------------------------
-- priorStack_at :  the recursion-recovery, GENERIC in A, b.
--
-- At the step input  input_pkg = pi P_outer (Snd prev)  (P_outer =
-- pi_succ_outer A b , prev = cov_spec o stepFun_parse O P_outer), the
-- prior-stack lookup recovers  parseS b .  This is exactly LenR's
-- lookup chain (steps 3-8), parametric in A, b, for h = stepFun_parse.

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

      -- get_rest input_pkg = b.
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

      -- get_K input_pkg = P_outer.
      get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
      get_K_value = get_K_at_pi P_outer (ap1 Snd prev)

      -- get_table input_pkg = HistP_sbt o stepFun_parse O P_outer.
      get_table_value :
        Deriv (eqF (ap1 get_table input_pkg)
                    (HistP_sbt o stepFun_parse O P_outer))
      get_table_value = get_table_at_pi P_outer (ap1 Snd prev)

      -- lookupAt get_rest input_pkg = HPsbt o stepFun_parse O b P_outer.
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

      -- leq b P_outer.
      leq_b_P : Deriv (leq b P_outer)
      leq_b_P =
        leq_sigma_right
          (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

      -- HPsbt ... = parseS b.
      HP_to_parse :
        Deriv (eqF (HPsbt o stepFun_parse O b P_outer) (ap1 parseS b))
      HP_to_parse = lookup_eq_fold o stepFun_parse b P_outer leq_b_P
  in ruleTrans lookup_to_HP HP_to_parse

------------------------------------------------------------------------
-- Per-branch "read the cell" fragment: at a CONCRETE cell
--   node = pi (pi (natCode ptag) payload) rest
-- with  ptag = suc m , recover  get_newK input_pkg = node ,
-- and the cell projections.
--
-- A_cell = pi_succ_outer (natCode m) payload  ;  cell = s A_cell.
-- We package the common derivations once, parametric in (m, payload, rest).

private
  -- m  is the predecessor of the (concrete) token tag.
  get_newK_eq_node :
    (m : Nat) (payload rest : Term) ->
    let A_cell  = pi_succ_outer (natCode m) payload
        P_outer = pi_succ_outer A_cell rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        node    = ap2 pi (ap2 pi (natCode (suc m)) payload) rest
    in Deriv (eqF (ap1 get_newK input_pkg) node)
  get_newK_eq_node m payload rest =
    let A_cell : Term
        A_cell = pi_succ_outer (natCode m) payload

        cell : Term
        cell = ap2 pi (natCode (suc m)) payload

        P_outer : Term
        P_outer = pi_succ_outer A_cell rest

        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer

        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)

        node : Term
        node = ap2 pi cell rest

        -- cell = s A_cell.
        cell_eq : Deriv (eqF cell (ap1 s A_cell))
        cell_eq = pi_at_succ (natCode m) payload

        -- get_newK input_pkg = s P_outer.
        g1 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        g1 = get_newK_at_pi P_outer (ap1 Snd prev)

        -- s P_outer = pi (s A_cell) rest.
        g2 : Deriv (eqF (ap1 s P_outer) (ap2 pi (ap1 s A_cell) rest))
        g2 = ruleSym (pi_at_succ A_cell rest)

        -- pi (s A_cell) rest = pi cell rest = node.
        g3 : Deriv (eqF (ap2 pi (ap1 s A_cell) rest) node)
        g3 = congL pi rest (ruleSym cell_eq)
    in ruleTrans g1 (ruleTrans g2 g3)

  -- get_cell input_pkg = cell.
  get_cell_eq :
    (m : Nat) (payload rest : Term) ->
    let A_cell  = pi_succ_outer (natCode m) payload
        P_outer = pi_succ_outer A_cell rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        cell    = ap2 pi (natCode (suc m)) payload
    in Deriv (eqF (ap1 get_cell input_pkg) cell)
  get_cell_eq m payload rest =
    let A_cell : Term
        A_cell = pi_succ_outer (natCode m) payload
        P_outer : Term
        P_outer = pi_succ_outer A_cell rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        cell : Term
        cell = ap2 pi (natCode (suc m)) payload

        c1 : Deriv (eqF (ap1 get_cell input_pkg) (ap1 Fst (ap1 get_newK input_pkg)))
        c1 = compose1U_eq Fst get_newK input_pkg

        c2 : Deriv (eqF (ap1 Fst (ap1 get_newK input_pkg)) (ap1 Fst (ap2 pi cell rest)))
        c2 = cong1 Fst (get_newK_eq_node m payload rest)

        c3 : Deriv (eqF (ap1 Fst (ap2 pi cell rest)) cell)
        c3 = axFst cell rest
    in ruleTrans c1 (ruleTrans c2 c3)

  -- get_toktag input_pkg = natCode (suc m).
  get_toktag_eq :
    (m : Nat) (payload rest : Term) ->
    let A_cell  = pi_succ_outer (natCode m) payload
        P_outer = pi_succ_outer A_cell rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 get_toktag input_pkg) (natCode (suc m)))
  get_toktag_eq m payload rest =
    let A_cell : Term
        A_cell = pi_succ_outer (natCode m) payload
        P_outer : Term
        P_outer = pi_succ_outer A_cell rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        cell : Term
        cell = ap2 pi (natCode (suc m)) payload

        t1 : Deriv (eqF (ap1 get_toktag input_pkg) (ap1 Fst (ap1 get_cell input_pkg)))
        t1 = compose1U_eq Fst get_cell input_pkg

        t2 : Deriv (eqF (ap1 Fst (ap1 get_cell input_pkg)) (ap1 Fst cell))
        t2 = cong1 Fst (get_cell_eq m payload rest)

        t3 : Deriv (eqF (ap1 Fst cell) (natCode (suc m)))
        t3 = axFst (natCode (suc m)) payload
    in ruleTrans t1 (ruleTrans t2 t3)

  -- get_payload input_pkg = payload.
  get_payload_eq :
    (m : Nat) (payload rest : Term) ->
    let A_cell  = pi_succ_outer (natCode m) payload
        P_outer = pi_succ_outer A_cell rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 get_payload input_pkg) payload)
  get_payload_eq m payload rest =
    let A_cell : Term
        A_cell = pi_succ_outer (natCode m) payload
        P_outer : Term
        P_outer = pi_succ_outer A_cell rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
        cell : Term
        cell = ap2 pi (natCode (suc m)) payload

        p1 : Deriv (eqF (ap1 get_payload input_pkg) (ap1 Snd (ap1 get_cell input_pkg)))
        p1 = compose1U_eq Snd get_cell input_pkg

        p2 : Deriv (eqF (ap1 Snd (ap1 get_cell input_pkg)) (ap1 Snd cell))
        p2 = cong1 Snd (get_cell_eq m payload rest)

        p3 : Deriv (eqF (ap1 Snd cell) payload)
        p3 = axSnd (natCode (suc m)) payload
    in ruleTrans p1 (ruleTrans p2 p3)

------------------------------------------------------------------------
-- Tag-distinctness witnesses for the dispatch cascade.

private
  w_ar2_leaf : NatNeqWitness 2 1
  w_ar2_leaf = decideNatNeq 2 1 (\ ())

  w_ar3_leaf : NatNeqWitness 3 1
  w_ar3_leaf = decideNatNeq 3 1 (\ ())

  w_ar3_ar2 : NatNeqWitness 3 2
  w_ar3_ar2 = decideNatNeq 3 2 (\ ())

------------------------------------------------------------------------
-- isLeaf / isAr2 evaluated at the step input (with concrete token tag
--   natCode (suc m) ).

private
  isLeaf_value :
    (m : Nat) (payload rest : Term) ->
    let A_cell  = pi_succ_outer (natCode m) payload
        P_outer = pi_succ_outer A_cell rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 isLeaf input_pkg)
                  (ap2 natEqF (natCode (suc m)) (natCode ptag_leaf)))
  isLeaf_value m payload rest =
    let A_cell : Term
        A_cell = pi_succ_outer (natCode m) payload
        P_outer : Term
        P_outer = pi_succ_outer A_cell rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)

        i1 : Deriv (eqF (ap1 isLeaf input_pkg)
                        (ap2 natEqF (ap1 get_toktag input_pkg)
                                    (ap1 (constN ptag_leaf) input_pkg)))
        i1 = ax_C natEqF get_toktag (constN ptag_leaf) input_pkg

        i2 : Deriv (eqF (ap1 (constN ptag_leaf) input_pkg) (natCode ptag_leaf))
        i2 = constN_eq ptag_leaf input_pkg

        i3 : Deriv (eqF (ap1 get_toktag input_pkg) (natCode (suc m)))
        i3 = get_toktag_eq m payload rest

        i4 : Deriv (eqF (ap2 natEqF (ap1 get_toktag input_pkg)
                                    (ap1 (constN ptag_leaf) input_pkg))
                        (ap2 natEqF (natCode (suc m)) (natCode ptag_leaf)))
        i4 = ruleTrans (congL natEqF (ap1 (constN ptag_leaf) input_pkg) i3)
                       (congR natEqF (natCode (suc m)) i2)
    in ruleTrans i1 i4

  isAr2_value :
    (m : Nat) (payload rest : Term) ->
    let A_cell  = pi_succ_outer (natCode m) payload
        P_outer = pi_succ_outer A_cell rest
        prev    = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg = ap2 pi P_outer (ap1 Snd prev)
    in Deriv (eqF (ap1 isAr2 input_pkg)
                  (ap2 natEqF (natCode (suc m)) (natCode ptag_ar2)))
  isAr2_value m payload rest =
    let A_cell : Term
        A_cell = pi_succ_outer (natCode m) payload
        P_outer : Term
        P_outer = pi_succ_outer A_cell rest
        prev : Term
        prev = ap2 (cov_spec o stepFun_parse) O P_outer
        input_pkg : Term
        input_pkg = ap2 pi P_outer (ap1 Snd prev)

        i1 : Deriv (eqF (ap1 isAr2 input_pkg)
                        (ap2 natEqF (ap1 get_toktag input_pkg)
                                    (ap1 (constN ptag_ar2) input_pkg)))
        i1 = ax_C natEqF get_toktag (constN ptag_ar2) input_pkg

        i2 : Deriv (eqF (ap1 (constN ptag_ar2) input_pkg) (natCode ptag_ar2))
        i2 = constN_eq ptag_ar2 input_pkg

        i3 : Deriv (eqF (ap1 get_toktag input_pkg) (natCode (suc m)))
        i3 = get_toktag_eq m payload rest

        i4 : Deriv (eqF (ap2 natEqF (ap1 get_toktag input_pkg)
                                    (ap1 (constN ptag_ar2) input_pkg))
                        (ap2 natEqF (natCode (suc m)) (natCode ptag_ar2)))
        i4 = ruleTrans (congL natEqF (ap1 (constN ptag_ar2) input_pkg) i3)
                       (congR natEqF (natCode (suc m)) i2)
    in ruleTrans i1 i4

------------------------------------------------------------------------
-- Cascade firing (generic in the step input).

private
  stepBody_to_leaf :
    (input : Term) -> Deriv (eqF (ap1 isLeaf input) (ap1 s O)) ->
    Deriv (eqF (ap1 stepBody_parse input) (ap1 leaf_branch input))
  stepBody_to_leaf input isLeaf_sO =
    let pairT : Term
        pairT = ap1 (C pi leaf_branch ar2_or_ar3) input

        e1 : Deriv (eqF (ap1 stepBody_parse input)
                        (ap2 condFork pairT (ap1 isLeaf input)))
        e1 = ax_C condFork (C pi leaf_branch ar2_or_ar3) isLeaf input

        sub_eq : Deriv (eqF (ap2 condFork pairT (ap1 isLeaf input))
                            (ap2 condFork pairT (ap1 s O)))
        sub_eq = congR condFork pairT isLeaf_sO

        fire : Deriv (eqF (ap2 condFork pairT (ap1 s O)) (ap1 Fst pairT))
        fire = condFork_true_nc pairT O

        pi_eq : Deriv (eqF pairT
                          (ap2 pi (ap1 leaf_branch input) (ap1 ar2_or_ar3 input)))
        pi_eq = ax_C pi leaf_branch ar2_or_ar3 input

        Fst_pi : Deriv (eqF (ap1 Fst (ap2 pi (ap1 leaf_branch input) (ap1 ar2_or_ar3 input)))
                            (ap1 leaf_branch input))
        Fst_pi = axFst (ap1 leaf_branch input) (ap1 ar2_or_ar3 input)
    in ruleTrans e1 (ruleTrans sub_eq
         (ruleTrans fire (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  stepBody_to_ar2or3 :
    (input : Term) -> Deriv (eqF (ap1 isLeaf input) O) ->
    Deriv (eqF (ap1 stepBody_parse input) (ap1 ar2_or_ar3 input))
  stepBody_to_ar2or3 input isLeaf_O =
    let pairT : Term
        pairT = ap1 (C pi leaf_branch ar2_or_ar3) input

        e1 : Deriv (eqF (ap1 stepBody_parse input)
                        (ap2 condFork pairT (ap1 isLeaf input)))
        e1 = ax_C condFork (C pi leaf_branch ar2_or_ar3) isLeaf input

        sub_eq : Deriv (eqF (ap2 condFork pairT (ap1 isLeaf input))
                            (ap2 condFork pairT O))
        sub_eq = congR condFork pairT isLeaf_O

        fire : Deriv (eqF (ap2 condFork pairT O) (ap1 Snd pairT))
        fire = condFork_false pairT

        pi_eq : Deriv (eqF pairT
                          (ap2 pi (ap1 leaf_branch input) (ap1 ar2_or_ar3 input)))
        pi_eq = ax_C pi leaf_branch ar2_or_ar3 input

        Snd_pi : Deriv (eqF (ap1 Snd (ap2 pi (ap1 leaf_branch input) (ap1 ar2_or_ar3 input)))
                            (ap1 ar2_or_ar3 input))
        Snd_pi = axSnd (ap1 leaf_branch input) (ap1 ar2_or_ar3 input)
    in ruleTrans e1 (ruleTrans sub_eq
         (ruleTrans fire (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

  ar2or3_to_ar2 :
    (input : Term) -> Deriv (eqF (ap1 isAr2 input) (ap1 s O)) ->
    Deriv (eqF (ap1 ar2_or_ar3 input) (ap1 ar2_branch input))
  ar2or3_to_ar2 input isAr2_sO =
    let pair2 : Term
        pair2 = ap1 (C pi ar2_branch ar3_branch) input

        e1 : Deriv (eqF (ap1 ar2_or_ar3 input)
                        (ap2 condFork pair2 (ap1 isAr2 input)))
        e1 = ax_C condFork (C pi ar2_branch ar3_branch) isAr2 input

        sub_eq : Deriv (eqF (ap2 condFork pair2 (ap1 isAr2 input))
                            (ap2 condFork pair2 (ap1 s O)))
        sub_eq = congR condFork pair2 isAr2_sO

        fire : Deriv (eqF (ap2 condFork pair2 (ap1 s O)) (ap1 Fst pair2))
        fire = condFork_true_nc pair2 O

        pi_eq : Deriv (eqF pair2
                          (ap2 pi (ap1 ar2_branch input) (ap1 ar3_branch input)))
        pi_eq = ax_C pi ar2_branch ar3_branch input

        Fst_pi : Deriv (eqF (ap1 Fst (ap2 pi (ap1 ar2_branch input) (ap1 ar3_branch input)))
                            (ap1 ar2_branch input))
        Fst_pi = axFst (ap1 ar2_branch input) (ap1 ar3_branch input)
    in ruleTrans e1 (ruleTrans sub_eq
         (ruleTrans fire (ruleTrans (cong1 Fst pi_eq) Fst_pi)))

  ar2or3_to_ar3 :
    (input : Term) -> Deriv (eqF (ap1 isAr2 input) O) ->
    Deriv (eqF (ap1 ar2_or_ar3 input) (ap1 ar3_branch input))
  ar2or3_to_ar3 input isAr2_O =
    let pair2 : Term
        pair2 = ap1 (C pi ar2_branch ar3_branch) input

        e1 : Deriv (eqF (ap1 ar2_or_ar3 input)
                        (ap2 condFork pair2 (ap1 isAr2 input)))
        e1 = ax_C condFork (C pi ar2_branch ar3_branch) isAr2 input

        sub_eq : Deriv (eqF (ap2 condFork pair2 (ap1 isAr2 input))
                            (ap2 condFork pair2 O))
        sub_eq = congR condFork pair2 isAr2_O

        fire : Deriv (eqF (ap2 condFork pair2 O) (ap1 Snd pair2))
        fire = condFork_false pair2

        pi_eq : Deriv (eqF pair2
                          (ap2 pi (ap1 ar2_branch input) (ap1 ar3_branch input)))
        pi_eq = ax_C pi ar2_branch ar3_branch input

        Snd_pi : Deriv (eqF (ap1 Snd (ap2 pi (ap1 ar2_branch input) (ap1 ar3_branch input)))
                            (ap1 ar3_branch input))
        Snd_pi = axSnd (ap1 ar2_branch input) (ap1 ar3_branch input)
    in ruleTrans e1 (ruleTrans sub_eq
         (ruleTrans fire (ruleTrans (cong1 Snd pi_eq) Snd_pi)))

------------------------------------------------------------------------
-- Node closure: LEAF.   parseS (pi (cellLeaf code) rest) = pi code (parseS rest).

parse_at_leaf :
  (code rest : Term) ->
  Deriv (eqF (ap1 parseS (ap2 pi (cellLeaf code) rest))
              (ap2 pi code (ap1 parseS rest)))
parse_at_leaf code rest =
  let A_cell : Term
      A_cell = pi_succ_outer (natCode 0) code
      P_outer : Term
      P_outer = pi_succ_outer A_cell rest
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)
      node : Term
      node = ap2 pi (cellLeaf code) rest

      cell_eq : Deriv (eqF (cellLeaf code) (ap1 s A_cell))
      cell_eq = pi_at_succ (natCode 0) code

      node_eq : Deriv (eqF node (ap2 pi (ap1 s A_cell) rest))
      node_eq = congL pi rest cell_eq

      step_fires : Deriv (eqF (ap1 parseS (ap2 pi (ap1 s A_cell) rest))
                              (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      step_fires = fold_node_unfold o stepFun_parse A_cell rest

      e0 : Deriv (eqF (ap1 parseS node)
                      (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      e0 = ruleTrans (cong1 parseS node_eq) step_fires

      post_eq : Deriv (eqF (ap2 stepFun_parse P_outer (ap1 Snd prev))
                           (ap1 stepBody_parse input_pkg))
      post_eq = axPost stepBody_parse pi P_outer (ap1 Snd prev)

      isLeaf_sO : Deriv (eqF (ap1 isLeaf input_pkg) (ap1 s O))
      isLeaf_sO = ruleTrans (isLeaf_value 0 code rest) (natEq_eq ptag_leaf)

      to_leaf : Deriv (eqF (ap1 stepBody_parse input_pkg) (ap1 leaf_branch input_pkg))
      to_leaf = stepBody_to_leaf input_pkg isLeaf_sO

      lb_eq : Deriv (eqF (ap1 leaf_branch input_pkg)
                         (ap2 pi (ap1 get_payload input_pkg) (ap1 priorStack input_pkg)))
      lb_eq = ax_C pi get_payload priorStack input_pkg

      payload_v : Deriv (eqF (ap1 get_payload input_pkg) code)
      payload_v = get_payload_eq 0 code rest

      prior_v : Deriv (eqF (ap1 priorStack input_pkg) (ap1 parseS rest))
      prior_v = priorStack_at A_cell rest

      lb_value : Deriv (eqF (ap1 leaf_branch input_pkg)
                            (ap2 pi code (ap1 parseS rest)))
      lb_value = ruleTrans lb_eq
                   (ruleTrans (congL pi (ap1 priorStack input_pkg) payload_v)
                              (congR pi code prior_v))
  in ruleTrans e0 (ruleTrans post_eq (ruleTrans to_leaf lb_value))

------------------------------------------------------------------------
-- Node closure: ARITY-2 (ap1).
--   parseS (pi (cellAr2 p) rest)
--     = pi (pi p (pi top1 top2)) rest2
--   where PS = parseS rest, top1 = Fst PS, top2 = Fst (Snd PS),
--         rest2 = Snd (Snd PS).

parse_at_ar2 :
  (p rest : Term) ->
  Deriv (eqF (ap1 parseS (ap2 pi (cellAr2 p) rest))
              (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst (ap1 parseS rest))
                                        (ap1 Fst (ap1 Snd (ap1 parseS rest)))))
                      (ap1 Snd (ap1 Snd (ap1 parseS rest)))))
parse_at_ar2 p rest =
  let A_cell : Term
      A_cell = pi_succ_outer (natCode 1) p
      P_outer : Term
      P_outer = pi_succ_outer A_cell rest
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)
      node : Term
      node = ap2 pi (cellAr2 p) rest

      PS : Term
      PS = ap1 parseS rest

      cell_eq : Deriv (eqF (cellAr2 p) (ap1 s A_cell))
      cell_eq = pi_at_succ (natCode 1) p

      node_eq : Deriv (eqF node (ap2 pi (ap1 s A_cell) rest))
      node_eq = congL pi rest cell_eq

      step_fires : Deriv (eqF (ap1 parseS (ap2 pi (ap1 s A_cell) rest))
                              (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      step_fires = fold_node_unfold o stepFun_parse A_cell rest

      e0 : Deriv (eqF (ap1 parseS node)
                      (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      e0 = ruleTrans (cong1 parseS node_eq) step_fires

      post_eq : Deriv (eqF (ap2 stepFun_parse P_outer (ap1 Snd prev))
                           (ap1 stepBody_parse input_pkg))
      post_eq = axPost stepBody_parse pi P_outer (ap1 Snd prev)

      isLeaf_O : Deriv (eqF (ap1 isLeaf input_pkg) O)
      isLeaf_O = ruleTrans (isLeaf_value 1 p rest) (natEqF_at_neq 2 1 w_ar2_leaf)

      isAr2_sO : Deriv (eqF (ap1 isAr2 input_pkg) (ap1 s O))
      isAr2_sO = ruleTrans (isAr2_value 1 p rest) (natEq_eq ptag_ar2)

      to_ar2 : Deriv (eqF (ap1 stepBody_parse input_pkg) (ap1 ar2_branch input_pkg))
      to_ar2 = ruleTrans (stepBody_to_ar2or3 input_pkg isLeaf_O)
                         (ar2or3_to_ar2 input_pkg isAr2_sO)

      -- Stack reads.
      prior_v : Deriv (eqF (ap1 priorStack input_pkg) PS)
      prior_v = priorStack_at A_cell rest

      payload_v : Deriv (eqF (ap1 get_payload input_pkg) p)
      payload_v = get_payload_eq 1 p rest

      top1_v : Deriv (eqF (ap1 ps_top1 input_pkg) (ap1 Fst PS))
      top1_v = ruleTrans (compose1U_eq Fst priorStack input_pkg)
                         (cong1 Fst prior_v)

      sub1_v : Deriv (eqF (ap1 ps_sub1 input_pkg) (ap1 Snd PS))
      sub1_v = ruleTrans (compose1U_eq Snd priorStack input_pkg)
                         (cong1 Snd prior_v)

      top2_v : Deriv (eqF (ap1 ps_top2 input_pkg) (ap1 Fst (ap1 Snd PS)))
      top2_v = ruleTrans (compose1U_eq Fst ps_sub1 input_pkg)
                         (cong1 Fst sub1_v)

      sub2_v : Deriv (eqF (ap1 ps_sub2 input_pkg) (ap1 Snd (ap1 Snd PS)))
      sub2_v = ruleTrans (compose1U_eq Snd ps_sub1 input_pkg)
                         (cong1 Snd sub1_v)

      -- Inner pair  pi top1 top2 .
      inner_eq : Deriv (eqF (ap1 (C pi ps_top1 ps_top2) input_pkg)
                            (ap2 pi (ap1 ps_top1 input_pkg) (ap1 ps_top2 input_pkg)))
      inner_eq = ax_C pi ps_top1 ps_top2 input_pkg

      inner_full : Deriv (eqF (ap1 (C pi ps_top1 ps_top2) input_pkg)
                              (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS))))
      inner_full = ruleTrans inner_eq
                     (ruleTrans (congL pi (ap1 ps_top2 input_pkg) top1_v)
                                (congR pi (ap1 Fst PS) top2_v))

      -- ar2_built input = pi p (pi top1 top2).
      built_eq : Deriv (eqF (ap1 ar2_built input_pkg)
                            (ap2 pi (ap1 get_payload input_pkg)
                                    (ap1 (C pi ps_top1 ps_top2) input_pkg)))
      built_eq = ax_C pi get_payload (C pi ps_top1 ps_top2) input_pkg

      built_full : Deriv (eqF (ap1 ar2_built input_pkg)
                              (ap2 pi p (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS)))))
      built_full = ruleTrans built_eq
                     (ruleTrans (congL pi (ap1 (C pi ps_top1 ps_top2) input_pkg) payload_v)
                                (congR pi p inner_full))

      -- ar2_branch input = pi built rest2.
      ab_eq : Deriv (eqF (ap1 ar2_branch input_pkg)
                         (ap2 pi (ap1 ar2_built input_pkg) (ap1 ps_sub2 input_pkg)))
      ab_eq = ax_C pi ar2_built ps_sub2 input_pkg

      ab_full : Deriv (eqF (ap1 ar2_branch input_pkg)
                           (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS))))
                                   (ap1 Snd (ap1 Snd PS))))
      ab_full = ruleTrans ab_eq
                  (ruleTrans (congL pi (ap1 ps_sub2 input_pkg) built_full)
                             (congR pi (ap2 pi p (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS)))) sub2_v))
  in ruleTrans e0 (ruleTrans post_eq (ruleTrans to_ar2 ab_full))

------------------------------------------------------------------------
-- Node closure: ARITY-3 (ap2 / C / R).
--   parseS (pi (cellAr3 p) rest)
--     = pi (pi p (pi top1 (pi top2 top3))) rest3 .

parse_at_ar3 :
  (p rest : Term) ->
  Deriv (eqF (ap1 parseS (ap2 pi (cellAr3 p) rest))
              (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst (ap1 parseS rest))
                                        (ap2 pi (ap1 Fst (ap1 Snd (ap1 parseS rest)))
                                                (ap1 Fst (ap1 Snd (ap1 Snd (ap1 parseS rest)))))))
                      (ap1 Snd (ap1 Snd (ap1 Snd (ap1 parseS rest))))))
parse_at_ar3 p rest =
  let A_cell : Term
      A_cell = pi_succ_outer (natCode 2) p
      P_outer : Term
      P_outer = pi_succ_outer A_cell rest
      prev : Term
      prev = ap2 (cov_spec o stepFun_parse) O P_outer
      input_pkg : Term
      input_pkg = ap2 pi P_outer (ap1 Snd prev)
      node : Term
      node = ap2 pi (cellAr3 p) rest

      PS : Term
      PS = ap1 parseS rest

      cell_eq : Deriv (eqF (cellAr3 p) (ap1 s A_cell))
      cell_eq = pi_at_succ (natCode 2) p

      node_eq : Deriv (eqF node (ap2 pi (ap1 s A_cell) rest))
      node_eq = congL pi rest cell_eq

      step_fires : Deriv (eqF (ap1 parseS (ap2 pi (ap1 s A_cell) rest))
                              (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      step_fires = fold_node_unfold o stepFun_parse A_cell rest

      e0 : Deriv (eqF (ap1 parseS node)
                      (ap2 stepFun_parse P_outer (ap1 Snd prev)))
      e0 = ruleTrans (cong1 parseS node_eq) step_fires

      post_eq : Deriv (eqF (ap2 stepFun_parse P_outer (ap1 Snd prev))
                           (ap1 stepBody_parse input_pkg))
      post_eq = axPost stepBody_parse pi P_outer (ap1 Snd prev)

      isLeaf_O : Deriv (eqF (ap1 isLeaf input_pkg) O)
      isLeaf_O = ruleTrans (isLeaf_value 2 p rest) (natEqF_at_neq 3 1 w_ar3_leaf)

      isAr2_O : Deriv (eqF (ap1 isAr2 input_pkg) O)
      isAr2_O = ruleTrans (isAr2_value 2 p rest) (natEqF_at_neq 3 2 w_ar3_ar2)

      to_ar3 : Deriv (eqF (ap1 stepBody_parse input_pkg) (ap1 ar3_branch input_pkg))
      to_ar3 = ruleTrans (stepBody_to_ar2or3 input_pkg isLeaf_O)
                         (ar2or3_to_ar3 input_pkg isAr2_O)

      -- Stack reads.
      prior_v : Deriv (eqF (ap1 priorStack input_pkg) PS)
      prior_v = priorStack_at A_cell rest

      payload_v : Deriv (eqF (ap1 get_payload input_pkg) p)
      payload_v = get_payload_eq 2 p rest

      top1_v : Deriv (eqF (ap1 ps_top1 input_pkg) (ap1 Fst PS))
      top1_v = ruleTrans (compose1U_eq Fst priorStack input_pkg)
                         (cong1 Fst prior_v)

      sub1_v : Deriv (eqF (ap1 ps_sub1 input_pkg) (ap1 Snd PS))
      sub1_v = ruleTrans (compose1U_eq Snd priorStack input_pkg)
                         (cong1 Snd prior_v)

      top2_v : Deriv (eqF (ap1 ps_top2 input_pkg) (ap1 Fst (ap1 Snd PS)))
      top2_v = ruleTrans (compose1U_eq Fst ps_sub1 input_pkg)
                         (cong1 Fst sub1_v)

      sub2_v : Deriv (eqF (ap1 ps_sub2 input_pkg) (ap1 Snd (ap1 Snd PS)))
      sub2_v = ruleTrans (compose1U_eq Snd ps_sub1 input_pkg)
                         (cong1 Snd sub1_v)

      top3_v : Deriv (eqF (ap1 ps_top3 input_pkg) (ap1 Fst (ap1 Snd (ap1 Snd PS))))
      top3_v = ruleTrans (compose1U_eq Fst ps_sub2 input_pkg)
                         (cong1 Fst sub2_v)

      sub3_v : Deriv (eqF (ap1 ps_sub3 input_pkg) (ap1 Snd (ap1 Snd (ap1 Snd PS))))
      sub3_v = ruleTrans (compose1U_eq Snd ps_sub2 input_pkg)
                         (cong1 Snd sub2_v)

      -- Inner pair  pi top2 top3 .
      inner2_eq : Deriv (eqF (ap1 (C pi ps_top2 ps_top3) input_pkg)
                             (ap2 pi (ap1 ps_top2 input_pkg) (ap1 ps_top3 input_pkg)))
      inner2_eq = ax_C pi ps_top2 ps_top3 input_pkg

      inner2_full : Deriv (eqF (ap1 (C pi ps_top2 ps_top3) input_pkg)
                               (ap2 pi (ap1 Fst (ap1 Snd PS))
                                       (ap1 Fst (ap1 Snd (ap1 Snd PS)))))
      inner2_full = ruleTrans inner2_eq
                      (ruleTrans (congL pi (ap1 ps_top3 input_pkg) top2_v)
                                 (congR pi (ap1 Fst (ap1 Snd PS)) top3_v))

      -- Inner pair  pi top1 (pi top2 top3) .
      inner_eq : Deriv (eqF (ap1 (C pi ps_top1 (C pi ps_top2 ps_top3)) input_pkg)
                            (ap2 pi (ap1 ps_top1 input_pkg)
                                    (ap1 (C pi ps_top2 ps_top3) input_pkg)))
      inner_eq = ax_C pi ps_top1 (C pi ps_top2 ps_top3) input_pkg

      inner_full : Deriv (eqF (ap1 (C pi ps_top1 (C pi ps_top2 ps_top3)) input_pkg)
                              (ap2 pi (ap1 Fst PS)
                                      (ap2 pi (ap1 Fst (ap1 Snd PS))
                                              (ap1 Fst (ap1 Snd (ap1 Snd PS))))))
      inner_full = ruleTrans inner_eq
                     (ruleTrans (congL pi (ap1 (C pi ps_top2 ps_top3) input_pkg) top1_v)
                                (congR pi (ap1 Fst PS) inner2_full))

      -- ar3_built input = pi p (pi top1 (pi top2 top3)).
      built_eq : Deriv (eqF (ap1 ar3_built input_pkg)
                            (ap2 pi (ap1 get_payload input_pkg)
                                    (ap1 (C pi ps_top1 (C pi ps_top2 ps_top3)) input_pkg)))
      built_eq = ax_C pi get_payload (C pi ps_top1 (C pi ps_top2 ps_top3)) input_pkg

      built_full : Deriv (eqF (ap1 ar3_built input_pkg)
                              (ap2 pi p (ap2 pi (ap1 Fst PS)
                                                (ap2 pi (ap1 Fst (ap1 Snd PS))
                                                        (ap1 Fst (ap1 Snd (ap1 Snd PS)))))))
      built_full = ruleTrans built_eq
                     (ruleTrans (congL pi (ap1 (C pi ps_top1 (C pi ps_top2 ps_top3)) input_pkg) payload_v)
                                (congR pi p inner_full))

      -- ar3_branch input = pi built rest3.
      ab_eq : Deriv (eqF (ap1 ar3_branch input_pkg)
                         (ap2 pi (ap1 ar3_built input_pkg) (ap1 ps_sub3 input_pkg)))
      ab_eq = ax_C pi ar3_built ps_sub3 input_pkg

      builtV : Term
      builtV = ap2 pi p (ap2 pi (ap1 Fst PS)
                                (ap2 pi (ap1 Fst (ap1 Snd PS))
                                        (ap1 Fst (ap1 Snd (ap1 Snd PS)))))

      ab_full : Deriv (eqF (ap1 ar3_branch input_pkg)
                           (ap2 pi builtV (ap1 Snd (ap1 Snd (ap1 Snd PS)))))
      ab_full = ruleTrans ab_eq
                  (ruleTrans (congL pi (ap1 ps_sub3 input_pkg) built_full)
                             (congR pi builtV sub3_v))
  in ruleTrans e0 (ruleTrans post_eq (ruleTrans to_ar3 ab_full))

