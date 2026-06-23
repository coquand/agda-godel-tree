{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfFun -- DEEP (recursive) funcode-validity predicate  wfFun : Fun1 , a
-- course-of-values fold over the funcode Pair-tree (dispatch on the funcode tag
-- get_tag = Fst f), base-reject:
--
--   wfFun cSuc/cZero/cId/cProj = O                 (Fst f in {3,4,5,7})
--   wfFun (cComp g h1 h2) = pi (wfFun g) (pi (wfFun h1) (wfFun h2))   (Fst f = 6)
--   wfFun (cRec  g h1 h2) = pi (wfFun g) (pi (wfFun h1) (wfFun h2))   (Fst f = 8)
--   wfFun O = s O      (reject)
--
-- Unlike the SHALLOW T4.PrFunValid.funValid, wfFun validates ALL sub-funcodes,
-- so  wfFun (cComp g h1 h2) = O  =>  wfFun g/h1/h2 = O  (via piZero) -- exactly
-- what the compound-fun congruences of the opaque triangle need.  Sub-funcodes
-- sit at the derivation-node projector positions: g = nIdx, h1 = lIdx, h2 = rIdx.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfFun where

open import T4.Base

open import T4.PrCodeObj using ( cSuc ; cZero ; cId ; cProj ; cComp ; cRec )
open import T4.PrDerCode using ( bun3 )
open import T4.BinTree using ( binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; stepOf ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt ; fold_at_O )
open import T4.ProgParse using ( get_tag )
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
-- SECTION 1.  Cells, the head-tag cascade and  wfFun .

leafCell : Fun1
leafCell = Z
fv3cell : Fun1                       -- pi (wfFun g) (pi (wfFun h1) (wfFun h2))
fv3cell = C pi (lookupAt nIdx) (C pi (lookupAt lIdx) (lookupAt rIdx))
rejectCell : Fun1
rejectCell = constN 1

testHd : Nat -> Fun1
testHd k = C natEqF get_tag (constN k)

wfn_l8 : Fun1
wfn_l8 = C condFork (C pi fv3cell rejectCell) (testHd 8)
wfn_l7 : Fun1
wfn_l7 = C condFork (C pi leafCell wfn_l8) (testHd 7)
wfn_l6 : Fun1
wfn_l6 = C condFork (C pi fv3cell wfn_l7) (testHd 6)
wfn_l5 : Fun1
wfn_l5 = C condFork (C pi leafCell wfn_l6) (testHd 5)
wfn_l4 : Fun1
wfn_l4 = C condFork (C pi leafCell wfn_l5) (testHd 4)
wfFunNodeCell : Fun1
wfFunNodeCell = C condFork (C pi leafCell wfn_l4) (testHd 3)

wfFun : Fun1
wfFun = binRec rejectCell Z wfFunNodeCell

------------------------------------------------------------------------
-- SECTION 2.  wfFun O = s O.

wfFun_O : Deriv (eqF (ap1 wfFun O) (ap1 s O))
wfFun_O = ruleTrans (fold_at_O rejectCell (Post (stepOf Z wfFunNodeCell) pi)) (constN_eq 1 O)

------------------------------------------------------------------------
-- SECTION 3.  Shared plumbing.

private
  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k p = decideNatNeq m k p

-- A funcode  Pair (natCode (suc kp)) b  is a fold NODE (tag = natCode (suc kp),
-- payload b).  This module mirrors T4.PrWfRed.Node / BinTree.isWfW_node.
module Node (kp : Nat) (b : Term) (w1 : NatNeqWitness (suc kp) 1) where
  open NP rejectCell Z wfFunNodeCell (natCode kp) b public
  head_eq : Deriv (eqF (ap1 get_tag input_pkg) (natCode (suc kp)))
  head_eq = np_head
  t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
  t1_O = ruleTrans test1_val (natEqF_at_neq (suc kp) 1 w1)
  to_cellNode : Deriv (eqF (ap1 wfFun (ap2 pi (ap1 s (natCode kp)) b)) (ap1 wfFunNodeCell input_pkg))
  to_cellNode = collapse_snd t1_O

------------------------------------------------------------------------
-- SECTION 4.  Leaf funcodes  (Fst in {3,4,5,7} -> leafCell = Z -> O).

wfFun_cSuc : Deriv (eqF (ap1 wfFun cSuc) O)
wfFun_cSuc =
  let open Node 2 O (decideNatNeq 3 1 (\ ()))
      fires = fork_true_to_fst leafCell wfn_l4 (testHd 3) input_pkg (idxTest_fire get_tag 3 input_pkg head_eq)
  in ruleTrans to_cellNode (ruleTrans fires (axZ input_pkg))

wfFun_cZero : Deriv (eqF (ap1 wfFun cZero) O)
wfFun_cZero =
  let open Node 3 O (decideNatNeq 4 1 (\ ()))
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) input_pkg (idxTest_skip get_tag 4 3 input_pkg (wn 4 3 (\ ())) head_eq))
                  (fork_true_to_fst leafCell wfn_l5 (testHd 4) input_pkg (idxTest_fire get_tag 4 input_pkg head_eq))
  in ruleTrans to_cellNode (ruleTrans fires (axZ input_pkg))

wfFun_cId : Deriv (eqF (ap1 wfFun cId) O)
wfFun_cId =
  let open Node 4 O (decideNatNeq 5 1 (\ ()))
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) input_pkg (idxTest_skip get_tag 5 3 input_pkg (wn 5 3 (\ ())) head_eq))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) input_pkg (idxTest_skip get_tag 5 4 input_pkg (wn 5 4 (\ ())) head_eq))
                     (fork_true_to_fst leafCell wfn_l6 (testHd 5) input_pkg (idxTest_fire get_tag 5 input_pkg head_eq)))
  in ruleTrans to_cellNode (ruleTrans fires (axZ input_pkg))

wfFun_cProj : Deriv (eqF (ap1 wfFun cProj) O)
wfFun_cProj =
  let open Node 6 O (decideNatNeq 7 1 (\ ()))
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) input_pkg (idxTest_skip get_tag 7 3 input_pkg (wn 7 3 (\ ())) head_eq))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) input_pkg (idxTest_skip get_tag 7 4 input_pkg (wn 7 4 (\ ())) head_eq))
            (ruleTrans (fork_false_to_snd leafCell wfn_l6 (testHd 5) input_pkg (idxTest_skip get_tag 7 5 input_pkg (wn 7 5 (\ ())) head_eq))
              (ruleTrans (fork_false_to_snd fv3cell wfn_l7 (testHd 6) input_pkg (idxTest_skip get_tag 7 6 input_pkg (wn 7 6 (\ ())) head_eq))
                         (fork_true_to_fst leafCell wfn_l8 (testHd 7) input_pkg (idxTest_fire get_tag 7 input_pkg head_eq)))))
  in ruleTrans to_cellNode (ruleTrans fires (axZ input_pkg))

------------------------------------------------------------------------
-- SECTION 5.  Compound funcodes  (cComp / cRec, recover 3 sub-funcodes).

module CompNode (kp : Nat) (g h1 h2 : Term) (w1 : NatNeqWitness (suc kp) 1) where
  open Node kp (bun3 g h1 h2) w1 public
  nIdx_eq : Deriv (eqF (ap1 nIdx input_pkg) g)
  nIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
              (ruleTrans (cong1 Fst np_rc) (axFst g (ap2 Pair h1 h2)))
  sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair h1 h2))
  sndArg_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                (ruleTrans (cong1 Snd np_rc) (axSnd g (ap2 Pair h1 h2)))
  lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) h1)
  lIdx_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
              (ruleTrans (cong1 Fst sndArg_eq) (axFst h1 h2))
  rIdx_eq : Deriv (eqF (ap1 rIdx input_pkg) h2)
  rIdx_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
              (ruleTrans (cong1 Snd sndArg_eq) (axSnd h1 h2))
  -- value bounds : g / (Pair h1 h2) / h1 / h2  all <= P_outer .
  leq_pair_P : Deriv (leq (ap2 Pair h1 h2) P_outer)
  leq_pair_P = leq_trans (ap2 Pair h1 h2) (ap2 Pair g (ap2 Pair h1 h2)) P_outer
                 (leq_pi_right g (ap2 Pair h1 h2)) leq_b_P
  recN : Deriv (eqF (ap1 (lookupAt nIdx) input_pkg) (ap1 wfFun g))
  recN = np_lookup_gen nIdx g nIdx_eq
           (leq_trans g (ap2 Pair g (ap2 Pair h1 h2)) P_outer (leq_pi_left g (ap2 Pair h1 h2)) leq_b_P)
  recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 wfFun h1))
  recL = np_lookup_gen lIdx h1 lIdx_eq
           (leq_trans h1 (ap2 Pair h1 h2) P_outer (leq_pi_left h1 h2) leq_pair_P)
  recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 wfFun h2))
  recR = np_lookup_gen rIdx h2 rIdx_eq
           (leq_trans h2 (ap2 Pair h1 h2) P_outer (leq_pi_right h1 h2) leq_pair_P)
  -- fv3cell value.
  fv3_val : Deriv (eqF (ap1 fv3cell input_pkg)
                       (ap2 pi (ap1 wfFun g) (ap2 pi (ap1 wfFun h1) (ap1 wfFun h2))))
  fv3_val =
    ruleTrans (ax_C pi (lookupAt nIdx) (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
      (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg) recN)
        (congR pi (ap1 wfFun g)
          (ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
            (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                       (congR pi (ap1 wfFun h1) recR)))))

wfFun_cComp : (g h1 h2 : Term) ->
  Deriv (eqF (ap1 wfFun (cComp g h1 h2))
             (ap2 pi (ap1 wfFun g) (ap2 pi (ap1 wfFun h1) (ap1 wfFun h2))))
wfFun_cComp g h1 h2 =
  let open CompNode 5 g h1 h2 (decideNatNeq 6 1 (\ ()))
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) input_pkg (idxTest_skip get_tag 6 3 input_pkg (wn 6 3 (\ ())) head_eq))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) input_pkg (idxTest_skip get_tag 6 4 input_pkg (wn 6 4 (\ ())) head_eq))
            (ruleTrans (fork_false_to_snd leafCell wfn_l6 (testHd 5) input_pkg (idxTest_skip get_tag 6 5 input_pkg (wn 6 5 (\ ())) head_eq))
                       (fork_true_to_fst fv3cell wfn_l7 (testHd 6) input_pkg (idxTest_fire get_tag 6 input_pkg head_eq))))
  in ruleTrans to_cellNode (ruleTrans fires fv3_val)

wfFun_cRec : (g h1 h2 : Term) ->
  Deriv (eqF (ap1 wfFun (cRec g h1 h2))
             (ap2 pi (ap1 wfFun g) (ap2 pi (ap1 wfFun h1) (ap1 wfFun h2))))
wfFun_cRec g h1 h2 =
  let open CompNode 7 g h1 h2 (decideNatNeq 8 1 (\ ()))
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) input_pkg (idxTest_skip get_tag 8 3 input_pkg (wn 8 3 (\ ())) head_eq))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) input_pkg (idxTest_skip get_tag 8 4 input_pkg (wn 8 4 (\ ())) head_eq))
            (ruleTrans (fork_false_to_snd leafCell wfn_l6 (testHd 5) input_pkg (idxTest_skip get_tag 8 5 input_pkg (wn 8 5 (\ ())) head_eq))
              (ruleTrans (fork_false_to_snd fv3cell wfn_l7 (testHd 6) input_pkg (idxTest_skip get_tag 8 6 input_pkg (wn 8 6 (\ ())) head_eq))
                (ruleTrans (fork_false_to_snd leafCell wfn_l8 (testHd 7) input_pkg (idxTest_skip get_tag 8 7 input_pkg (wn 8 7 (\ ())) head_eq))
                           (fork_true_to_fst fv3cell rejectCell (testHd 8) input_pkg (idxTest_fire get_tag 8 input_pkg head_eq))))))
  in ruleTrans to_cellNode (ruleTrans fires fv3_val)
