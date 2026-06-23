{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfRed -- the OBJECT STRICT VALIDITY predicate  wfRed : Fun1  for coded
-- parallel-reduction derivations of the FULL p.r. calculus, over ARBITRARY codes
-- p : Term (NOT the meta shadow), generalising T4.WfRed.  base-reject:
--
--   wfRed O                = s O            (REJECT: O is not a derivation)
--   wfRed (derLeaf)        = O              (a leaf is valid)
--   wfRed (ap1c f d)       = wfRed d
--   wfRed (ap2c g d1 d2)   = pi (wfRed d1) (wfRed d2)
--   wfRed (derO d)         = wfRed d
--   wfRed (derU d)         = wfRed d
--   wfRed (derV d1 d2)     = pi (wfRed d1) (wfRed d2)
--   wfRed (derC g h1 h2 d) = wfRed d
--   wfRed (derRb g h1 h2 d)= wfRed d
--   wfRed (derRs g h1 h2 d1 d2) = pi (wfRed d1) (wfRed d2)
--   wfRed (node, tag not in 1..8) = s O     (REJECT)
--
-- The dispatch reads the tag = Fst (label) (= derTagIdx), with a reject default;
-- the fold BASE is rejectCell (= s O), so any code with an O subterm gets
-- wfRed /= O -- thus  wfRed p = O  forces  p  to be a genuine derivation TREE
-- (every node non-O, valid tag, recursively-valid non-O children = codeDer
-- structure).  This validity checks the TREE, not the carried fun-codes (the
-- triangle/diamond equations are schematic in the funs).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrWfRed where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; derC ; derRb ; derRs
        ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs
        ; filler ; bun3 )
open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt ; fold_at_O )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )
open import T4.PrDev using ( idxTest_fire ; idxTest_skip )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Index, cells, the strict cascade and  wfRed .

derTagIdx : Fun1
derTagIdx = compose1U Fst nIdx

wfAdCell : Fun1                                       -- pi (wfRed l) (wfRed r)
wfAdCell = C pi (lookupAt lIdx) (lookupAt rIdx)
unaryCell : Fun1                                      -- wfRed l
unaryCell = lookupAt lIdx
rejectCell : Fun1                                     -- s O
rejectCell = constN 1

testTag : Nat -> Fun1
testTag k = C natEqF derTagIdx (constN k)

w_l8 : Fun1
w_l8 = C condFork (C pi wfAdCell rejectCell) (testTag 8)
w_l7 : Fun1
w_l7 = C condFork (C pi unaryCell w_l8) (testTag 7)
w_l6 : Fun1
w_l6 = C condFork (C pi unaryCell w_l7) (testTag 6)
w_l5 : Fun1
w_l5 = C condFork (C pi wfAdCell w_l6) (testTag 5)
w_l4 : Fun1
w_l4 = C condFork (C pi unaryCell w_l5) (testTag 4)
w_l3 : Fun1
w_l3 = C condFork (C pi unaryCell w_l4) (testTag 3)
w_l2 : Fun1
w_l2 = C condFork (C pi wfAdCell w_l3) (testTag 2)
wfCellNode : Fun1
wfCellNode = C condFork (C pi unaryCell w_l2) (testTag 1)

wfRed : Fun1
wfRed = binRec rejectCell Z wfCellNode

------------------------------------------------------------------------
-- SECTION 2.  wfRed O = s O  (base-reject) and the leaf.

wfRed_O : Deriv (eqF (ap1 wfRed O) (ap1 s O))
wfRed_O = ruleTrans (fold_at_O rejectCell (Post (stepOf Z wfCellNode) pi)) (constN_eq 1 O)
  where open import T4.ParsObj using ( stepOf )

wfRed_reflO : Deriv (eqF (ap1 wfRed derLeaf) O)
wfRed_reflO =
  let open NP rejectCell Z wfCellNode O dgReflO
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (axZ input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  Shared node plumbing.

w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())
wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
wn m k p = decideNatNeq m k p

module Node (lab l r : Term) where
  open NP rejectCell Z wfCellNode (natCode 1) (ap2 Pair lab (ap2 Pair l r)) public
  t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
  t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
  nIdx_eq : Deriv (eqF (ap1 nIdx input_pkg) lab)
  nIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
              (ruleTrans (cong1 Fst np_rc) (axFst lab (ap2 Pair l r)))
  sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair l r))
  sndArg_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                (ruleTrans (cong1 Snd np_rc) (axSnd lab (ap2 Pair l r)))
  lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) l)
  lIdx_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
              (ruleTrans (cong1 Fst sndArg_eq) (axFst l r))
  rIdx_eq : Deriv (eqF (ap1 rIdx input_pkg) r)
  rIdx_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
              (ruleTrans (cong1 Snd sndArg_eq) (axSnd l r))
  leq_lr_P : Deriv (leq (ap2 Pair l r) P_outer)
  leq_lr_P = leq_trans (ap2 Pair l r) (ap2 Pair lab (ap2 Pair l r)) P_outer
               (leq_pi_right lab (ap2 Pair l r)) leq_b_P
  recL : Deriv (eqF (ap1 unaryCell input_pkg) (ap1 wfRed l))
  recL = np_lookup_gen lIdx l lIdx_eq
           (leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P)
  recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 wfRed r))
  recR = np_lookup_gen rIdx r rIdx_eq
           (leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P)
  tag_eq : (hf : Term) -> Deriv (eqF (ap1 Fst lab) hf) ->
           Deriv (eqF (ap1 derTagIdx input_pkg) hf)
  tag_eq hf eq = ruleTrans (compose1U_eq Fst nIdx input_pkg)
                   (ruleTrans (cong1 Fst nIdx_eq) eq)
  -- pi (wfRed l) (wfRed r) for binary nodes.
  ad_val : Deriv (eqF (ap1 wfAdCell input_pkg) (ap2 pi (ap1 wfRed l) (ap1 wfRed r)))
  ad_val = ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
             (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                        (congR pi (ap1 wfRed l) recR))
  to_cellNode : Deriv (eqF (ap1 wfRed (binNode lab l r)) (ap1 wfCellNode input_pkg))
  to_cellNode = collapse_snd t1_O

------------------------------------------------------------------------
-- SECTION 4.  Unary-node equations (wfRed = wfRed left child).

wfRed_ap1c : (f d : Term) -> Deriv (eqF (ap1 wfRed (ap1c f d)) (ap1 wfRed d))
wfRed_ap1c f d =
  let open Node (ap2 Pair dgAp1c f) d filler
      tg = tag_eq (natCode 1) (axFst dgAp1c f)
      fires = fork_true_to_fst unaryCell w_l2 (testTag 1) input_pkg (idxTest_fire derTagIdx 1 input_pkg tg)
  in ruleTrans to_cellNode (ruleTrans fires recL)

wfRed_rO : (d : Term) -> Deriv (eqF (ap1 wfRed (derO d)) (ap1 wfRed d))
wfRed_rO d =
  let open Node (ap2 Pair dgRo O) d filler
      tg = tag_eq (natCode 3) (axFst dgRo O)
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 3 1 input_pkg (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 3 2 input_pkg (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst unaryCell w_l4 (testTag 3) input_pkg (idxTest_fire derTagIdx 3 input_pkg tg)))
  in ruleTrans to_cellNode (ruleTrans fires recL)

wfRed_rU : (d : Term) -> Deriv (eqF (ap1 wfRed (derU d)) (ap1 wfRed d))
wfRed_rU d =
  let open Node (ap2 Pair dgRu O) d filler
      tg = tag_eq (natCode 4) (axFst dgRu O)
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 4 1 input_pkg (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 4 2 input_pkg (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 4 3 input_pkg (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst unaryCell w_l5 (testTag 4) input_pkg (idxTest_fire derTagIdx 4 input_pkg tg))))
  in ruleTrans to_cellNode (ruleTrans fires recL)

wfRed_rC : (g h1 h2 d : Term) -> Deriv (eqF (ap1 wfRed (derC g h1 h2 d)) (ap1 wfRed d))
wfRed_rC g h1 h2 d =
  let open Node (ap2 Pair dgRC (bun3 g h1 h2)) d filler
      tg = tag_eq (natCode 6) (axFst dgRC (bun3 g h1 h2))
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 6 1 input_pkg (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 6 2 input_pkg (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 6 3 input_pkg (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 6 4 input_pkg (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) input_pkg (idxTest_skip derTagIdx 6 5 input_pkg (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst unaryCell w_l7 (testTag 6) input_pkg (idxTest_fire derTagIdx 6 input_pkg tg))))))
  in ruleTrans to_cellNode (ruleTrans fires recL)

wfRed_rRb : (g h1 h2 d : Term) -> Deriv (eqF (ap1 wfRed (derRb g h1 h2 d)) (ap1 wfRed d))
wfRed_rRb g h1 h2 d =
  let open Node (ap2 Pair dgRb (bun3 g h1 h2)) d filler
      tg = tag_eq (natCode 7) (axFst dgRb (bun3 g h1 h2))
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 7 1 input_pkg (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 7 2 input_pkg (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 7 3 input_pkg (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 7 4 input_pkg (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) input_pkg (idxTest_skip derTagIdx 7 5 input_pkg (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd unaryCell w_l7 (testTag 6) input_pkg (idxTest_skip derTagIdx 7 6 input_pkg (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst unaryCell w_l8 (testTag 7) input_pkg (idxTest_fire derTagIdx 7 input_pkg tg)))))))
  in ruleTrans to_cellNode (ruleTrans fires recL)

------------------------------------------------------------------------
-- SECTION 5.  Binary-node equations (wfRed = pi (wfRed l) (wfRed r)).

wfRed_ap2c : (g d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRed (ap2c g d1 d2)) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
wfRed_ap2c g d1 d2 =
  let open Node (ap2 Pair dgAp2c g) d1 d2
      tg = tag_eq (natCode 2) (axFst dgAp2c g)
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 2 1 input_pkg w21 tg))
                  (fork_true_to_fst wfAdCell w_l3 (testTag 2) input_pkg (idxTest_fire derTagIdx 2 input_pkg tg))
  in ruleTrans to_cellNode (ruleTrans fires ad_val)

wfRed_rV : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRed (derV d1 d2)) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
wfRed_rV d1 d2 =
  let open Node (ap2 Pair dgRv O) d1 d2
      tg = tag_eq (natCode 5) (axFst dgRv O)
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 5 1 input_pkg (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 5 2 input_pkg (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 5 3 input_pkg (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 5 4 input_pkg (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst wfAdCell w_l6 (testTag 5) input_pkg (idxTest_fire derTagIdx 5 input_pkg tg)))))
  in ruleTrans to_cellNode (ruleTrans fires ad_val)

wfRed_rRs : (g h1 h2 d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRed (derRs g h1 h2 d1 d2)) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
wfRed_rRs g h1 h2 d1 d2 =
  let open Node (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2
      tg = tag_eq (natCode 8) (axFst dgRs (bun3 g h1 h2))
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) input_pkg (idxTest_skip derTagIdx 8 1 input_pkg (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) input_pkg (idxTest_skip derTagIdx 8 2 input_pkg (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) input_pkg (idxTest_skip derTagIdx 8 3 input_pkg (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) input_pkg (idxTest_skip derTagIdx 8 4 input_pkg (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) input_pkg (idxTest_skip derTagIdx 8 5 input_pkg (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd unaryCell w_l7 (testTag 6) input_pkg (idxTest_skip derTagIdx 8 6 input_pkg (wn 8 6 (\ ())) tg))
                    (ruleTrans (fork_false_to_snd unaryCell w_l8 (testTag 7) input_pkg (idxTest_skip derTagIdx 8 7 input_pkg (wn 8 7 (\ ())) tg))
                               (fork_true_to_fst wfAdCell rejectCell (testTag 8) input_pkg (idxTest_fire derTagIdx 8 input_pkg tg))))))))
  in ruleTrans to_cellNode (ruleTrans fires ad_val)
