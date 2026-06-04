{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.NextString -- the small-code flat-string SUCCESSOR generator.
--
-- A flat program-string is a right-nested tag-cell chain
--   cons t1 (cons t2 (... (cons tm O)))     ( cons a b = ap2 pi a b ),
-- with each head a tag  natCode d ,  d in {1,2,3} .   nextString is the
-- successor in BIJECTIVE-base-3 order ( least-significant digit OUTERMOST ),
-- digits {1,2,3} :
--
--   nextString O              = cons tag1 O                  ( 0  ->  "1" )
--   nextString (cons tag1 b)  = cons tag2 b                  ( d=1 -> 2 )
--   nextString (cons tag2 b)  = cons tag3 b                  ( d=2 -> 3 )
--   nextString (cons tag3 b)  = cons tag1 (nextString b)     ( d=3 -> 1, CARRY )
--
-- candidate := iter nextString  ( T4.Candidate ) then enumerates EVERY flat
-- tag-{1,2,3} string : candidate(natCode k) = the k-th string.   Crucially the
-- CODE of nextString is CONSTANT ( a fixed fold, no  Lstar ), so the diagonal
-- that embeds  candidate / the bounded-conjunction atom stays  O(1) -- exactly
-- the property that  checkAlphN (depth-indexed, code  ~ 3^Lstar ) lacked.
--
-- Construction MIRRORS  T4.CheckAlph  ( same fold + node-recovery plumbing );
-- only the step BODY differs : a 3-way  natEqF  cascade on the cell head that
-- REBUILDS the incremented cell ( with a recursive carry ), instead of
-- returning a verdict.

module T4.NextString where

open import T4.Base
open import T4.FoldRec
open import T4.CoVSpec      using ( cov_spec )
open import T4.CoVSpecUniv  using ( HistP_sbt )
open import T4.Stability    using ( HPsbt )
open import T4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import T4.LeqMono      using ( leq_sigma_right )
open import T4.LenR         using ( get_rc )
open import T4.ProgParse    using ( get_tag )
open import T4.ProgEnc      using ( tagLeaf ; tagUnary ; tagBinary )

open import BRA3.Church        using ( pi ; sub ; sigma ; tau )
open import BRA3.ChurchT117    using ( Fst )
open import BRA3.ChurchT116    using ( Snd )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.PairAlgebra   using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.Dispatch      using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  cells and the step body / recursor.

cons : Term -> Term -> Term
cons a b = ap2 pi a b

-- the three branch cells ( get_rc input = right child b ; lookupAt = nextString b ).
cellA : Fun1
cellA = C pi (constN tagUnary)  get_rc                 -- cons tag2 b
cellB : Fun1
cellB = C pi (constN tagBinary) get_rc                 -- cons tag3 b
cellC : Fun1
cellC = C pi (constN tagLeaf)  (lookupAt get_rc)       -- cons tag1 (nextString b)

test1Fun : Fun1
test1Fun = C natEqF get_tag (constN tagLeaf)           -- natEqF head tag1
test2Fun : Fun1
test2Fun = C natEqF get_tag (constN tagUnary)          -- natEqF head tag2

innerFun : Fun1
innerFun = C condFork (C pi cellB cellC) test2Fun

stepBody_next : Fun1
stepBody_next = C condFork (C pi cellA innerFun) test1Fun

stepFun_next : Fun2
stepFun_next = Post stepBody_next pi

nbase : Fun1
nbase = C pi (constN tagLeaf) Z                        -- O ↦ cons tag1 O

nextString : Fun1
nextString = fold nbase stepFun_next

------------------------------------------------------------------------
-- SECTION 1.  nextString O = cons tag1 O .

next_at_O : Deriv (eqF (ap1 nextString O) (cons (natCode tagLeaf) O))
next_at_O =
  ruleTrans (fold_at_O nbase stepFun_next)
    (ruleTrans (ax_C pi (constN tagLeaf) Z O)
      (ruleTrans (congL pi (ap1 Z O) (constN_eq tagLeaf O))
                 (congR pi (natCode tagLeaf) (axZ O))))

------------------------------------------------------------------------
-- SECTION 2.  Shared node plumbing ( generic in A, b ; copied from
-- T4.CheckAlph.checkAlph_at_node steps 1-8 + get_tag_value ).

module NodePlumb (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec nbase stepFun_next) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  -- nextString node = stepBody_next input_pkg .
  np_unfold : Deriv (eqF (ap1 nextString node) (ap1 stepBody_next input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold nbase stepFun_next A b)
              (axPost stepBody_next pi P_outer (ap1 Snd prev))

  -- get_rc input_pkg = b .
  np_rc : Deriv (eqF (ap1 get_rc input_pkg) b)
  np_rc =
    let s1 : Deriv (eqF (ap1 get_rc input_pkg) (ap1 Snd (ap1 get_newK input_pkg)))
        s1 = compose1U_eq Snd get_newK input_pkg
        s2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        s2 = get_newK_at_pi P_outer (ap1 Snd prev)
        s3 : Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd node))
        s3 = cong1 Snd (ruleSym (pi_at_succ A b))
        s4 : Deriv (eqF (ap1 Snd node) b)
        s4 = axSnd (ap1 s A) b
    in ruleTrans s1 (ruleTrans (cong1 Snd s2) (ruleTrans s3 s4))

  -- get_tag input_pkg = s A .
  np_head : Deriv (eqF (ap1 get_tag input_pkg) (ap1 s A))
  np_head =
    let t1 : Deriv (eqF (ap1 get_tag input_pkg) (ap1 Fst (ap1 get_newK input_pkg)))
        t1 = compose1U_eq Fst get_newK input_pkg
        t2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        t2 = get_newK_at_pi P_outer (ap1 Snd prev)
        t3 : Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst node))
        t3 = cong1 Fst (ruleSym (pi_at_succ A b))
        t4 : Deriv (eqF (ap1 Fst node) (ap1 s A))
        t4 = axFst (ap1 s A) b
    in ruleTrans t1 (ruleTrans (cong1 Fst t2) (ruleTrans t3 t4))

  -- lookupAt get_rc input_pkg = nextString b  ( recursive-call recovery ).
  np_lookup : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 nextString b))
  np_lookup =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt nbase stepFun_next O P_outer))
        get_table_value = get_table_at_pi P_outer (ap1 Snd prev)
        u1 : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg)
                        (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                  (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg)))))
        u1 = lookupAt_unfold get_rc input_pkg
        sub_eq : Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg))
                            (ap2 sub P_outer b))
        sub_eq = ruleTrans (congL sub (ap1 get_rc input_pkg) get_K_value)
                           (congR sub P_outer np_rc)
        iter_eq : Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                              (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg)))
                              (ap2 (iter Snd) (HistP_sbt nbase stepFun_next O P_outer)
                              (ap2 sub P_outer b)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 get_rc input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt nbase stepFun_next O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg)
                                  (HPsbt nbase stepFun_next O b P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        leq_b_P : Deriv (leq b P_outer)
        leq_b_P = leq_sigma_right
                    (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b
        HP_to_next : Deriv (eqF (HPsbt nbase stepFun_next O b P_outer) (ap1 nextString b))
        HP_to_next = lookup_eq_fold nbase stepFun_next b P_outer leq_b_P
    in ruleTrans lookup_to_HP HP_to_next

------------------------------------------------------------------------
-- SECTION 3.  The dispatch, generic in (A, b) given the head test values.
-- stepBody_next input = condFork (pi (cellA input) (innerFun input)) (test1 input) .

module Dispatch (A b : Term) where
  open NodePlumb A b

  pairT1 : Term
  pairT1 = ap1 (C pi cellA innerFun) input_pkg
  pairT2 : Term
  pairT2 = ap1 (C pi cellB cellC) input_pkg

  -- the four pi-projections of the two branch pairs.
  fst_pairT1 : Deriv (eqF (ap1 Fst pairT1) (ap1 cellA input_pkg))
  fst_pairT1 = ruleTrans (cong1 Fst (ax_C pi cellA innerFun input_pkg))
                         (axFst (ap1 cellA input_pkg) (ap1 innerFun input_pkg))
  snd_pairT1 : Deriv (eqF (ap1 Snd pairT1) (ap1 innerFun input_pkg))
  snd_pairT1 = ruleTrans (cong1 Snd (ax_C pi cellA innerFun input_pkg))
                         (axSnd (ap1 cellA input_pkg) (ap1 innerFun input_pkg))
  fst_pairT2 : Deriv (eqF (ap1 Fst pairT2) (ap1 cellB input_pkg))
  fst_pairT2 = ruleTrans (cong1 Fst (ax_C pi cellB cellC input_pkg))
                         (axFst (ap1 cellB input_pkg) (ap1 cellC input_pkg))
  snd_pairT2 : Deriv (eqF (ap1 Snd pairT2) (ap1 cellC input_pkg))
  snd_pairT2 = ruleTrans (cong1 Snd (ax_C pi cellB cellC input_pkg))
                         (axSnd (ap1 cellB input_pkg) (ap1 cellC input_pkg))

  -- stepBody_next input = condFork pairT1 (test1Fun input).
  sb_eq : Deriv (eqF (ap1 stepBody_next input_pkg)
                     (ap2 condFork pairT1 (ap1 test1Fun input_pkg)))
  sb_eq = ax_C condFork (C pi cellA innerFun) test1Fun input_pkg

  -- innerFun input = condFork pairT2 (test2Fun input).
  inner_eq : Deriv (eqF (ap1 innerFun input_pkg)
                        (ap2 condFork pairT2 (ap1 test2Fun input_pkg)))
  inner_eq = ax_C condFork (C pi cellB cellC) test2Fun input_pkg

  -- test1Fun input = natEqF (s A) (natCode tagLeaf).
  test1_val : Deriv (eqF (ap1 test1Fun input_pkg)
                         (ap2 natEqF (ap1 s A) (natCode tagLeaf)))
  test1_val =
    ruleTrans (ax_C natEqF get_tag (constN tagLeaf) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN tagLeaf) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq tagLeaf input_pkg)))

  -- test2Fun input = natEqF (s A) (natCode tagUnary).
  test2_val : Deriv (eqF (ap1 test2Fun input_pkg)
                         (ap2 natEqF (ap1 s A) (natCode tagUnary)))
  test2_val =
    ruleTrans (ax_C natEqF get_tag (constN tagUnary) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN tagUnary) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq tagUnary input_pkg)))

  -- cellA input = cons tag2 b.
  cellA_val : Deriv (eqF (ap1 cellA input_pkg) (cons (natCode tagUnary) b))
  cellA_val =
    ruleTrans (ax_C pi (constN tagUnary) get_rc input_pkg)
      (ruleTrans (congL pi (ap1 get_rc input_pkg) (constN_eq tagUnary input_pkg))
                 (congR pi (natCode tagUnary) np_rc))

  -- cellB input = cons tag3 b.
  cellB_val : Deriv (eqF (ap1 cellB input_pkg) (cons (natCode tagBinary) b))
  cellB_val =
    ruleTrans (ax_C pi (constN tagBinary) get_rc input_pkg)
      (ruleTrans (congL pi (ap1 get_rc input_pkg) (constN_eq tagBinary input_pkg))
                 (congR pi (natCode tagBinary) np_rc))

  -- cellC input = cons tag1 (nextString b).
  cellC_val : Deriv (eqF (ap1 cellC input_pkg) (cons (natCode tagLeaf) (ap1 nextString b)))
  cellC_val =
    ruleTrans (ax_C pi (constN tagLeaf) (lookupAt get_rc) input_pkg)
      (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq tagLeaf input_pkg))
                 (congR pi (natCode tagLeaf) np_lookup))

------------------------------------------------------------------------
-- SECTION 4.  The three node reduction laws.

-- nextString (cons tag1 b) = cons tag2 b .   ( node = pi (s O) b ,  A = O )
next_at_tag1 :
  (b : Term) ->
  Deriv (eqF (ap1 nextString (cons (natCode tagLeaf) b)) (cons (natCode tagUnary) b))
next_at_tag1 b =
  let open NodePlumb O b
      open Dispatch O b
      -- test1 fires ( head = s O = natCode 1 = tag1 ).
      t1_fire : Deriv (eqF (ap1 test1Fun input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq tagLeaf)
      -- stepBody = Fst pairT1 = cellA input.
      to_cellA : Deriv (eqF (ap1 stepBody_next input_pkg) (ap1 cellA input_pkg))
      to_cellA =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairT1 t1_fire)
            (ruleTrans (condFork_true_nc pairT1 O) fst_pairT1))
  in ruleTrans np_unfold (ruleTrans to_cellA cellA_val)

-- nextString (cons tag2 b) = cons tag3 b .   ( node = pi (s (natCode 1)) b , A = natCode 1 )
next_at_tag2 :
  (b : Term) ->
  Deriv (eqF (ap1 nextString (cons (natCode tagUnary) b)) (cons (natCode tagBinary) b))
next_at_tag2 b =
  let open NodePlumb (natCode tagLeaf) b
      open Dispatch (natCode tagLeaf) b
      w21 : NatNeqWitness tagUnary tagLeaf
      w21 = decideNatNeq tagUnary tagLeaf (\ ())
      -- test1 = natEqF (natCode 2)(natCode 1) = O.
      t1_O : Deriv (eqF (ap1 test1Fun input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq tagUnary tagLeaf w21)
      to_inner : Deriv (eqF (ap1 stepBody_next input_pkg) (ap1 innerFun input_pkg))
      to_inner =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairT1 t1_O)
            (ruleTrans (condFork_false pairT1) snd_pairT1))
      -- test2 fires ( head = natCode 2 = tag2 ).
      t2_fire : Deriv (eqF (ap1 test2Fun input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq tagUnary)
      inner_to_cellB : Deriv (eqF (ap1 innerFun input_pkg) (ap1 cellB input_pkg))
      inner_to_cellB =
        ruleTrans inner_eq
          (ruleTrans (congR condFork pairT2 t2_fire)
            (ruleTrans (condFork_true_nc pairT2 O) fst_pairT2))
  in ruleTrans np_unfold
       (ruleTrans to_inner (ruleTrans inner_to_cellB cellB_val))

-- nextString (cons tag3 b) = cons tag1 (nextString b) .   ( A = natCode 2 ; CARRY )
next_at_tag3 :
  (b : Term) ->
  Deriv (eqF (ap1 nextString (cons (natCode tagBinary) b))
             (cons (natCode tagLeaf) (ap1 nextString b)))
next_at_tag3 b =
  let open NodePlumb (natCode tagUnary) b
      open Dispatch (natCode tagUnary) b
      w31 : NatNeqWitness tagBinary tagLeaf
      w31 = decideNatNeq tagBinary tagLeaf (\ ())
      w32 : NatNeqWitness tagBinary tagUnary
      w32 = decideNatNeq tagBinary tagUnary (\ ())
      t1_O : Deriv (eqF (ap1 test1Fun input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq tagBinary tagLeaf w31)
      to_inner : Deriv (eqF (ap1 stepBody_next input_pkg) (ap1 innerFun input_pkg))
      to_inner =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairT1 t1_O)
            (ruleTrans (condFork_false pairT1) snd_pairT1))
      t2_O : Deriv (eqF (ap1 test2Fun input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq tagBinary tagUnary w32)
      inner_to_cellC : Deriv (eqF (ap1 innerFun input_pkg) (ap1 cellC input_pkg))
      inner_to_cellC =
        ruleTrans inner_eq
          (ruleTrans (congR condFork pairT2 t2_O)
            (ruleTrans (condFork_false pairT2) snd_pairT2))
  in ruleTrans np_unfold
       (ruleTrans to_inner (ruleTrans inner_to_cellC cellC_val))
