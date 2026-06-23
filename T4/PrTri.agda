{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTri -- the OBJECT TRIANGLE MAP  triF : Fun1  over the PrDerCode
-- derivation coding (full p.r. calculus), generalising T4.DerTri / DerTri2.
-- A binRec fold that BUILDS new derivation codes; triF (d : s => t) is a
-- derivation  t => dev(s)  (Takahashi).  Using  src(triF d') = tgt d' :
--
--   triF (derLeaf)               = derLeaf
--   triF (ap1c cSuc d')          = ap1c cSuc (triF d')                  -- s-cong
--   triF (ap1c cZero d')         = derO (triF d')                       -- o exposed
--   triF (ap1c cId d')           = derU (triF d')                       -- u exposed
--   triF (ap1c (cComp g h1 h2) d')= derC g h1 h2 (triF d')              -- C exposed
--   triF (ap2c cProj d1 d2)      = derV (triF d1) (triF d2)             -- v exposed
--   triF (ap2c (cRec g h1 h2) d1 derLeaf)        = derRb g h1 h2 (triF d1)         (PrTri2)
--   triF (ap2c (cRec g h1 h2) d1 (ap1c cSuc e))  = derRs g h1 h2 (triF d1)(triF e) (PrTri2)
--   triF (ap2c (cRec g h1 h2) d1 d2)             = ap2c (cRec g h1 h2)(triF d1)(triF d2) (PrTri2)
--   triF (derO d)                = derLeaf
--   triF (derU d)                = triF d
--   triF (derV d1 d2)            = triF d2
--   triF (derC g h1 h2 d)        = ap2c g (ap1c h1 (triF d)) (ap1c h2 (triF d))
--   triF (derRb g h1 h2 d)       = ap1c g (triF d)
--   triF (derRs g h1 h2 d1 d2)   = ap2c h1 (ap2c h2 (triF d1)(triF d2))
--                                          (ap2c (cRec g h1 h2)(triF d1)(triF d2))
--
-- This file defines  triF  in full (incl. the depth-2 ap2c-cRec dispatch) and
-- proves all equations EXCEPT the three depth-2 ap2c-cRec cases (-> PrTri2).
-- Derivation nodes are built with mkAp2 (= binNode shape, definitionally) from
-- T4.PrDev; the label  Pair (natCode tag) bundle  via mkLabel.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTri where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; derC ; derRb ; derRs
        ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs
        ; filler ; bun3 )
open import T4.PrCodeObj
  using ( cSuc ; cZero ; cId ; cComp ; cProj ; cRec
        ; tgSuc ; tgZero ; tgId ; tgComp ; tgProj ; tgRec )
open import T4.PrDev
  using ( mkAp2 ; mkAp2_val ; cSucF ; cSucF_val ; idxTest_fire ; idxTest_skip )

open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Builders for derivation codes.

mkLabel : Nat -> Fun1 -> Fun1                  -- Pair (natCode k) (B .)
mkLabel k B = C pi (constN k) B

mkLeafD : Fun1                                 -- constant derLeaf
mkLeafD = C pi (constN 1) Z

mkLabel_val : (k : Nat) (B : Fun1) (input vb : Term) ->
  Deriv (eqF (ap1 B input) vb) ->
  Deriv (eqF (ap1 (mkLabel k B) input) (ap2 Pair (natCode k) vb))
mkLabel_val k B input vb eB =
  ruleTrans (ax_C pi (constN k) B input)
    (ruleTrans (congL pi (ap1 B input) (constN_eq k input)) (congR pi (natCode k) eB))

mkLeafD_val : (input : Term) -> Deriv (eqF (ap1 mkLeafD input) derLeaf)
mkLeafD_val input = mkLabel_val 1 Z input O (axZ input)

------------------------------------------------------------------------
-- SECTION 2.  Index Fun1s.

derTagIdx : Fun1
derTagIdx = compose1U Fst nIdx
derBunIdx : Fun1
derBunIdx = compose1U Snd nIdx
funHd : Fun1                                   -- Fst (bundle) = head of carried fun
funHd = compose1U Fst derBunIdx
bunSnd : Fun1                                  -- Snd (bundle)  (Pair g (Pair h1 h2) inner)
bunSnd = compose1U Snd derBunIdx
bunH1' : Fun1                                  -- Fst (Snd bundle)
bunH1' = compose1U Fst bunSnd
bunH2' : Fun1                                  -- Snd (Snd bundle)
bunH2' = compose1U Snd bunSnd

triFL : Fun1
triFL = lookupAt lIdx
triFR : Fun1
triFR = lookupAt rIdx

-- derL extractor (= Fst (Snd (Snd z))), from DerTri.
derLF : Fun1
derLF = compose1U Fst (compose1U Snd Snd)

-- depth-2 (ap2c-cRec) reads on the right child d2.
d2tag : Fun1                                   -- binTag d2
d2tag = compose1U Fst rIdx
d2lab : Fun1                                   -- label of d2  = Fst (Snd d2)
d2lab = compose1U Fst (compose1U Snd rIdx)
d2labTag : Fun1                                -- deriv-tag of d2
d2labTag = compose1U Fst d2lab
d2FunHd : Fun1                                 -- head of d2's carried fun
d2FunHd = compose1U Fst (compose1U Snd d2lab)

------------------------------------------------------------------------
-- SECTION 3.  Cells.

-- ap1c sub-dispatch on the carried fun head (o/u/C ; else s).
br_s_cell : Fun1
br_s_cell = mkAp2 (mkLabel 1 cSucF) triFL mkLeafD
br_o_cell : Fun1
br_o_cell = mkAp2 (mkLabel 3 Z) triFL mkLeafD
br_u_cell : Fun1
br_u_cell = mkAp2 (mkLabel 4 Z) triFL mkLeafD
br_C_cell : Fun1
br_C_cell = mkAp2 (mkLabel 6 bunSnd) triFL mkLeafD

ap1_l3 : Fun1
ap1_l3 = C condFork (C pi br_C_cell br_s_cell) (C natEqF funHd (constN 6))
ap1_l2 : Fun1
ap1_l2 = C condFork (C pi br_u_cell ap1_l3) (C natEqF funHd (constN 5))
ap1Cell : Fun1
ap1Cell = C condFork (C pi br_o_cell ap1_l2) (C natEqF funHd (constN 4))

-- ap2c sub-dispatch on g head (v ; else R) then depth-2 on d2.
br_v_cell : Fun1
br_v_cell = mkAp2 (mkLabel 5 Z) triFL triFR
br_Rb_cell : Fun1
br_Rb_cell = mkAp2 (mkLabel 7 bunSnd) triFL mkLeafD
br_Rs_cell : Fun1
br_Rs_cell = mkAp2 (mkLabel 8 bunSnd) triFL (compose1U derLF triFR)
br_Rcong_cell : Fun1
br_Rcong_cell = mkAp2 (mkLabel 2 derBunIdx) triFL triFR

R_inner : Fun1
R_inner = C condFork (C pi br_Rs_cell br_Rcong_cell) (C natEqF d2FunHd (constN 3))
R_mid : Fun1
R_mid = C condFork (C pi R_inner br_Rcong_cell) (C natEqF d2labTag (constN 1))
R_disp : Fun1
R_disp = C condFork (C pi br_Rb_cell R_mid) (C natEqF d2tag (constN 1))

ap2Cell : Fun1
ap2Cell = C condFork (C pi br_v_cell R_disp) (C natEqF funHd (constN 7))

-- redex cells (derTag 3..8).
o_cell : Fun1
o_cell = mkLeafD
u_cell : Fun1
u_cell = triFL
v_cell : Fun1
v_cell = triFR
C_cell : Fun1
C_cell = mkAp2 (mkLabel 2 funHd)
           (mkAp2 (mkLabel 1 bunH1') triFL mkLeafD)
           (mkAp2 (mkLabel 1 bunH2') triFL mkLeafD)
Rb_cell : Fun1
Rb_cell = mkAp2 (mkLabel 1 funHd) triFL mkLeafD
Rs_cell : Fun1
Rs_cell = mkAp2 (mkLabel 2 bunH1')
            (mkAp2 (mkLabel 2 bunH2') triFL triFR)
            (mkAp2 (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR)

testTag : Nat -> Fun1
testTag k = C natEqF derTagIdx (constN k)

tri_l7 : Fun1
tri_l7 = C condFork (C pi Rb_cell Rs_cell) (testTag 7)
tri_l6 : Fun1
tri_l6 = C condFork (C pi C_cell tri_l7) (testTag 6)
tri_l5 : Fun1
tri_l5 = C condFork (C pi v_cell tri_l6) (testTag 5)
tri_l4 : Fun1
tri_l4 = C condFork (C pi u_cell tri_l5) (testTag 4)
tri_l3 : Fun1
tri_l3 = C condFork (C pi o_cell tri_l4) (testTag 3)
tri_l2 : Fun1
tri_l2 = C condFork (C pi ap2Cell tri_l3) (testTag 2)
cellNodeTri : Fun1
cellNodeTri = C condFork (C pi ap1Cell tri_l2) (testTag 1)

triF : Fun1
triF = binRec Z mkLeafD cellNodeTri

------------------------------------------------------------------------
-- SECTION 4.  Leaf equation.

triF_reflO : Deriv (eqF (ap1 triF derLeaf) derLeaf)
triF_reflO =
  let open NP Z mkLeafD cellNodeTri O dgReflO
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (mkLeafD_val input_pkg)

------------------------------------------------------------------------
-- SECTION 5.  Shared node plumbing.

w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())
wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
wn m k p = decideNatNeq m k p

module Node (lab l r : Term) where
  open NP Z mkLeafD cellNodeTri (natCode 1) (ap2 Pair lab (ap2 Pair l r)) public
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
  recL : Deriv (eqF (ap1 triFL input_pkg) (ap1 triF l))
  recL = np_lookup_gen lIdx l lIdx_eq
           (leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P)
  recR : Deriv (eqF (ap1 triFR input_pkg) (ap1 triF r))
  recR = np_lookup_gen rIdx r rIdx_eq
           (leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P)
  tag_eq : (hf : Term) -> Deriv (eqF (ap1 Fst lab) hf) ->
           Deriv (eqF (ap1 derTagIdx input_pkg) hf)
  tag_eq hf eq = ruleTrans (compose1U_eq Fst nIdx input_pkg)
                   (ruleTrans (cong1 Fst nIdx_eq) eq)
  bun_eq : (bn : Term) -> Deriv (eqF (ap1 Snd lab) bn) ->
           Deriv (eqF (ap1 derBunIdx input_pkg) bn)
  bun_eq bn eq = ruleTrans (compose1U_eq Snd nIdx input_pkg)
                   (ruleTrans (cong1 Snd nIdx_eq) eq)
  to_cellNode : Deriv (eqF (ap1 triF (binNode lab l r)) (ap1 cellNodeTri input_pkg))
  to_cellNode = collapse_snd t1_O

------------------------------------------------------------------------
-- SECTION 6.  ap1c equations (dispatch on the carried fun head).

-- helper: under bun_eq f, read funHd input = Fst f.
module Ap1cNode (f l : Term) where
  open Node (ap2 Pair dgAp1c f) l filler public
  tg1 : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 1))
  tg1 = tag_eq (natCode 1) (axFst dgAp1c f)
  bf : Deriv (eqF (ap1 derBunIdx input_pkg) f)
  bf = bun_eq f (axSnd dgAp1c f)
  funHd_eq : (hf : Term) -> Deriv (eqF (ap1 Fst f) hf) ->
             Deriv (eqF (ap1 funHd input_pkg) hf)
  funHd_eq hf eq = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
                     (ruleTrans (cong1 Fst bf) eq)
  to_ap1Cell : Deriv (eqF (ap1 triF (ap1c f l)) (ap1 ap1Cell input_pkg))
  to_ap1Cell =
    ruleTrans to_cellNode
      (fork_true_to_fst ap1Cell tri_l2 (testTag 1) input_pkg
        (idxTest_fire derTagIdx 1 input_pkg tg1))

triF_ap1c_s : (d : Term) -> Deriv (eqF (ap1 triF (ap1c cSuc d)) (ap1c cSuc (ap1 triF d)))
triF_ap1c_s d =
  let open Ap1cNode cSuc d
      hf : Deriv (eqF (ap1 funHd input_pkg) (natCode 3))
      hf = funHd_eq (natCode 3) (axFst tgSuc O)
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_s_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_o_cell ap1_l2 (C natEqF funHd (constN 4)) input_pkg
                     (idxTest_skip funHd 3 4 input_pkg (wn 3 4 (\ ())) hf))
          (ruleTrans (fork_false_to_snd br_u_cell ap1_l3 (C natEqF funHd (constN 5)) input_pkg
                       (idxTest_skip funHd 3 5 input_pkg (wn 3 5 (\ ())) hf))
                     (fork_false_to_snd br_C_cell br_s_cell (C natEqF funHd (constN 6)) input_pkg
                       (idxTest_skip funHd 3 6 input_pkg (wn 3 6 (\ ())) hf)))
      val : Deriv (eqF (ap1 br_s_cell input_pkg) (ap1c cSuc (ap1 triF d)))
      val = mkAp2_val (mkLabel 1 cSucF) triFL mkLeafD input_pkg
              (ap2 Pair (natCode 1) cSuc) (ap1 triF d) derLeaf
              (mkLabel_val 1 cSucF input_pkg cSuc (cSucF_val input_pkg)) recL (mkLeafD_val input_pkg)
  in ruleTrans to_ap1Cell (ruleTrans fires val)

triF_ap1c_o : (d : Term) -> Deriv (eqF (ap1 triF (ap1c cZero d)) (derO (ap1 triF d)))
triF_ap1c_o d =
  let open Ap1cNode cZero d
      hf : Deriv (eqF (ap1 funHd input_pkg) (natCode 4))
      hf = funHd_eq (natCode 4) (axFst tgZero O)
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_o_cell input_pkg))
      fires = fork_true_to_fst br_o_cell ap1_l2 (C natEqF funHd (constN 4)) input_pkg
                (idxTest_fire funHd 4 input_pkg hf)
      val : Deriv (eqF (ap1 br_o_cell input_pkg) (derO (ap1 triF d)))
      val = mkAp2_val (mkLabel 3 Z) triFL mkLeafD input_pkg
              (ap2 Pair (natCode 3) O) (ap1 triF d) derLeaf
              (mkLabel_val 3 Z input_pkg O (axZ input_pkg)) recL (mkLeafD_val input_pkg)
  in ruleTrans to_ap1Cell (ruleTrans fires val)

triF_ap1c_u : (d : Term) -> Deriv (eqF (ap1 triF (ap1c cId d)) (derU (ap1 triF d)))
triF_ap1c_u d =
  let open Ap1cNode cId d
      hf : Deriv (eqF (ap1 funHd input_pkg) (natCode 5))
      hf = funHd_eq (natCode 5) (axFst tgId O)
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_u_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_o_cell ap1_l2 (C natEqF funHd (constN 4)) input_pkg
                     (idxTest_skip funHd 5 4 input_pkg (wn 5 4 (\ ())) hf))
                  (fork_true_to_fst br_u_cell ap1_l3 (C natEqF funHd (constN 5)) input_pkg
                     (idxTest_fire funHd 5 input_pkg hf))
      val : Deriv (eqF (ap1 br_u_cell input_pkg) (derU (ap1 triF d)))
      val = mkAp2_val (mkLabel 4 Z) triFL mkLeafD input_pkg
              (ap2 Pair (natCode 4) O) (ap1 triF d) derLeaf
              (mkLabel_val 4 Z input_pkg O (axZ input_pkg)) recL (mkLeafD_val input_pkg)
  in ruleTrans to_ap1Cell (ruleTrans fires val)

triF_ap1c_C : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 triF (ap1c (cComp g h1 h2) d)) (derC g h1 h2 (ap1 triF d)))
triF_ap1c_C g h1 h2 d =
  let open Ap1cNode (cComp g h1 h2) d
      hf : Deriv (eqF (ap1 funHd input_pkg) (natCode 6))
      hf = funHd_eq (natCode 6) (axFst tgComp (ap2 Pair g (ap2 Pair h1 h2)))
      -- bunSnd input = Snd (cComp g h1 h2) = Pair g (Pair h1 h2).
      bunSnd_eq : Deriv (eqF (ap1 bunSnd input_pkg) (bun3 g h1 h2))
      bunSnd_eq = ruleTrans (compose1U_eq Snd derBunIdx input_pkg)
                    (ruleTrans (cong1 Snd bf) (axSnd tgComp (ap2 Pair g (ap2 Pair h1 h2))))
      fires : Deriv (eqF (ap1 ap1Cell input_pkg) (ap1 br_C_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_o_cell ap1_l2 (C natEqF funHd (constN 4)) input_pkg
                     (idxTest_skip funHd 6 4 input_pkg (wn 6 4 (\ ())) hf))
          (ruleTrans (fork_false_to_snd br_u_cell ap1_l3 (C natEqF funHd (constN 5)) input_pkg
                       (idxTest_skip funHd 6 5 input_pkg (wn 6 5 (\ ())) hf))
                     (fork_true_to_fst br_C_cell br_s_cell (C natEqF funHd (constN 6)) input_pkg
                       (idxTest_fire funHd 6 input_pkg hf)))
      val : Deriv (eqF (ap1 br_C_cell input_pkg) (derC g h1 h2 (ap1 triF d)))
      val = mkAp2_val (mkLabel 6 bunSnd) triFL mkLeafD input_pkg
              (ap2 Pair (natCode 6) (bun3 g h1 h2)) (ap1 triF d) derLeaf
              (mkLabel_val 6 bunSnd input_pkg (bun3 g h1 h2) bunSnd_eq) recL (mkLeafD_val input_pkg)
  in ruleTrans to_ap1Cell (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 7.  ap2c v-redex equation (g = cProj ; not depth-2).

triF_ap2c_v : (d1 d2 : Term) ->
  Deriv (eqF (ap1 triF (ap2c cProj d1 d2)) (derV (ap1 triF d1) (ap1 triF d2)))
triF_ap2c_v d1 d2 =
  let open Node (ap2 Pair dgAp2c cProj) d1 d2
      tg2 : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 2))
      tg2 = tag_eq (natCode 2) (axFst dgAp2c cProj)
      bf : Deriv (eqF (ap1 derBunIdx input_pkg) cProj)
      bf = bun_eq cProj (axSnd dgAp2c cProj)
      hf : Deriv (eqF (ap1 funHd input_pkg) (natCode 7))
      hf = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
             (ruleTrans (cong1 Fst bf) (axFst tgProj O))
      toCell : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 ap2Cell input_pkg))
      toCell =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 2 1 input_pkg w21 tg2))
                  (fork_true_to_fst ap2Cell tri_l3 (testTag 2) input_pkg
                     (idxTest_fire derTagIdx 2 input_pkg tg2))
      fires : Deriv (eqF (ap1 ap2Cell input_pkg) (ap1 br_v_cell input_pkg))
      fires = fork_true_to_fst br_v_cell R_disp (C natEqF funHd (constN 7)) input_pkg
                (idxTest_fire funHd 7 input_pkg hf)
      val : Deriv (eqF (ap1 br_v_cell input_pkg) (derV (ap1 triF d1) (ap1 triF d2)))
      val = mkAp2_val (mkLabel 5 Z) triFL triFR input_pkg
              (ap2 Pair (natCode 5) O) (ap1 triF d1) (ap1 triF d2)
              (mkLabel_val 5 Z input_pkg O (axZ input_pkg)) recL recR
  in ruleTrans to_cellNode (ruleTrans toCell (ruleTrans fires val))

------------------------------------------------------------------------
-- SECTION 8.  Redex triangle equations (derTag 3..8).

-- shared cascade-to-tag-k for the outer dispatch (skip 1,2,..,k-1 then fire k).
module RedexNode (lab l r : Term) where
  open Node lab l r public

triF_O : (d : Term) -> Deriv (eqF (ap1 triF (derO d)) derLeaf)
triF_O d =
  let open Node (ap2 Pair dgRo O) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 3))
      tg = tag_eq (natCode 3) (axFst dgRo O)
      fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 o_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 3 1 input_pkg (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 3 2 input_pkg (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst o_cell tri_l4 (testTag 3) input_pkg
                       (idxTest_fire derTagIdx 3 input_pkg tg)))
  in ruleTrans to_cellNode (ruleTrans fires (mkLeafD_val input_pkg))

triF_U : (d : Term) -> Deriv (eqF (ap1 triF (derU d)) (ap1 triF d))
triF_U d =
  let open Node (ap2 Pair dgRu O) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 4))
      tg = tag_eq (natCode 4) (axFst dgRu O)
      fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 u_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 4 1 input_pkg (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 4 2 input_pkg (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 4 3 input_pkg (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst u_cell tri_l5 (testTag 4) input_pkg
                         (idxTest_fire derTagIdx 4 input_pkg tg))))
  in ruleTrans to_cellNode (ruleTrans fires recL)

triF_V : (d1 d2 : Term) -> Deriv (eqF (ap1 triF (derV d1 d2)) (ap1 triF d2))
triF_V d1 d2 =
  let open Node (ap2 Pair dgRv O) d1 d2
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 5))
      tg = tag_eq (natCode 5) (axFst dgRv O)
      fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 v_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 5 1 input_pkg (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 5 2 input_pkg (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 5 3 input_pkg (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 5 4 input_pkg (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst v_cell tri_l6 (testTag 5) input_pkg
                           (idxTest_fire derTagIdx 5 input_pkg tg)))))
  in ruleTrans to_cellNode (ruleTrans fires recR)

triF_C : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 triF (derC g h1 h2 d))
             (ap2c g (ap1c h1 (ap1 triF d)) (ap1c h2 (ap1 triF d))))
triF_C g h1 h2 d =
  let open Node (ap2 Pair dgRC (bun3 g h1 h2)) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 6))
      tg = tag_eq (natCode 6) (axFst dgRC (bun3 g h1 h2))
      bf : Deriv (eqF (ap1 derBunIdx input_pkg) (bun3 g h1 h2))
      bf = bun_eq (bun3 g h1 h2) (axSnd dgRC (bun3 g h1 h2))
      gEq : Deriv (eqF (ap1 funHd input_pkg) g)
      gEq = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
              (ruleTrans (cong1 Fst bf) (axFst g (ap2 Pair h1 h2)))
      bunSnd_eq : Deriv (eqF (ap1 bunSnd input_pkg) (ap2 Pair h1 h2))
      bunSnd_eq = ruleTrans (compose1U_eq Snd derBunIdx input_pkg)
                    (ruleTrans (cong1 Snd bf) (axSnd g (ap2 Pair h1 h2)))
      h1Eq : Deriv (eqF (ap1 bunH1' input_pkg) h1)
      h1Eq = ruleTrans (compose1U_eq Fst bunSnd input_pkg)
               (ruleTrans (cong1 Fst bunSnd_eq) (axFst h1 h2))
      h2Eq : Deriv (eqF (ap1 bunH2' input_pkg) h2)
      h2Eq = ruleTrans (compose1U_eq Snd bunSnd input_pkg)
               (ruleTrans (cong1 Snd bunSnd_eq) (axSnd h1 h2))
      fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 C_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 6 1 input_pkg (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 6 2 input_pkg (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 6 3 input_pkg (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 6 4 input_pkg (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd v_cell tri_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 6 5 input_pkg (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst C_cell tri_l7 (testTag 6) input_pkg
                             (idxTest_fire derTagIdx 6 input_pkg tg))))))
      armH1 : Deriv (eqF (ap1 (mkAp2 (mkLabel 1 bunH1') triFL mkLeafD) input_pkg)
                         (ap1c h1 (ap1 triF d)))
      armH1 = mkAp2_val (mkLabel 1 bunH1') triFL mkLeafD input_pkg
                (ap2 Pair (natCode 1) h1) (ap1 triF d) derLeaf
                (mkLabel_val 1 bunH1' input_pkg h1 h1Eq) recL (mkLeafD_val input_pkg)
      armH2 : Deriv (eqF (ap1 (mkAp2 (mkLabel 1 bunH2') triFL mkLeafD) input_pkg)
                         (ap1c h2 (ap1 triF d)))
      armH2 = mkAp2_val (mkLabel 1 bunH2') triFL mkLeafD input_pkg
                (ap2 Pair (natCode 1) h2) (ap1 triF d) derLeaf
                (mkLabel_val 1 bunH2' input_pkg h2 h2Eq) recL (mkLeafD_val input_pkg)
      val : Deriv (eqF (ap1 C_cell input_pkg)
                       (ap2c g (ap1c h1 (ap1 triF d)) (ap1c h2 (ap1 triF d))))
      val = mkAp2_val (mkLabel 2 funHd)
              (mkAp2 (mkLabel 1 bunH1') triFL mkLeafD) (mkAp2 (mkLabel 1 bunH2') triFL mkLeafD)
              input_pkg (ap2 Pair (natCode 2) g)
              (ap1c h1 (ap1 triF d)) (ap1c h2 (ap1 triF d))
              (mkLabel_val 2 funHd input_pkg g gEq) armH1 armH2
  in ruleTrans to_cellNode (ruleTrans fires val)

triF_Rb : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 triF (derRb g h1 h2 d)) (ap1c g (ap1 triF d)))
triF_Rb g h1 h2 d =
  let open Node (ap2 Pair dgRb (bun3 g h1 h2)) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 7))
      tg = tag_eq (natCode 7) (axFst dgRb (bun3 g h1 h2))
      bf : Deriv (eqF (ap1 derBunIdx input_pkg) (bun3 g h1 h2))
      bf = bun_eq (bun3 g h1 h2) (axSnd dgRb (bun3 g h1 h2))
      gEq : Deriv (eqF (ap1 funHd input_pkg) g)
      gEq = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
              (ruleTrans (cong1 Fst bf) (axFst g (ap2 Pair h1 h2)))
      fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 Rb_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 7 1 input_pkg (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 7 2 input_pkg (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 7 3 input_pkg (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 7 4 input_pkg (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd v_cell tri_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 7 5 input_pkg (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd C_cell tri_l7 (testTag 6) input_pkg
                               (idxTest_skip derTagIdx 7 6 input_pkg (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst Rb_cell Rs_cell (testTag 7) input_pkg
                               (idxTest_fire derTagIdx 7 input_pkg tg)))))))
      val : Deriv (eqF (ap1 Rb_cell input_pkg) (ap1c g (ap1 triF d)))
      val = mkAp2_val (mkLabel 1 funHd) triFL mkLeafD input_pkg
              (ap2 Pair (natCode 1) g) (ap1 triF d) derLeaf
              (mkLabel_val 1 funHd input_pkg g gEq) recL (mkLeafD_val input_pkg)
  in ruleTrans to_cellNode (ruleTrans fires val)

triF_Rs : (g h1 h2 d1 d2 : Term) ->
  Deriv (eqF (ap1 triF (derRs g h1 h2 d1 d2))
             (ap2c h1 (ap2c h2 (ap1 triF d1) (ap1 triF d2))
                      (ap2c (cRec g h1 h2) (ap1 triF d1) (ap1 triF d2))))
triF_Rs g h1 h2 d1 d2 =
  let open Node (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 8))
      tg = tag_eq (natCode 8) (axFst dgRs (bun3 g h1 h2))
      bf : Deriv (eqF (ap1 derBunIdx input_pkg) (bun3 g h1 h2))
      bf = bun_eq (bun3 g h1 h2) (axSnd dgRs (bun3 g h1 h2))
      bunSnd_eq : Deriv (eqF (ap1 bunSnd input_pkg) (ap2 Pair h1 h2))
      bunSnd_eq = ruleTrans (compose1U_eq Snd derBunIdx input_pkg)
                    (ruleTrans (cong1 Snd bf) (axSnd g (ap2 Pair h1 h2)))
      h1Eq : Deriv (eqF (ap1 bunH1' input_pkg) h1)
      h1Eq = ruleTrans (compose1U_eq Fst bunSnd input_pkg)
               (ruleTrans (cong1 Fst bunSnd_eq) (axFst h1 h2))
      h2Eq : Deriv (eqF (ap1 bunH2' input_pkg) h2)
      h2Eq = ruleTrans (compose1U_eq Snd bunSnd input_pkg)
               (ruleTrans (cong1 Snd bunSnd_eq) (axSnd h1 h2))
      fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 Rs_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 8 1 input_pkg (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 8 2 input_pkg (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 8 3 input_pkg (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 8 4 input_pkg (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd v_cell tri_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 8 5 input_pkg (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd C_cell tri_l7 (testTag 6) input_pkg
                               (idxTest_skip derTagIdx 8 6 input_pkg (wn 8 6 (\ ())) tg))
                             (fork_false_to_snd Rb_cell Rs_cell (testTag 7) input_pkg
                               (idxTest_skip derTagIdx 8 7 input_pkg (wn 8 7 (\ ())) tg)))))))
      arm2 : Deriv (eqF (ap1 (mkAp2 (mkLabel 2 bunH2') triFL triFR) input_pkg)
                        (ap2c h2 (ap1 triF d1) (ap1 triF d2)))
      arm2 = mkAp2_val (mkLabel 2 bunH2') triFL triFR input_pkg
               (ap2 Pair (natCode 2) h2) (ap1 triF d1) (ap1 triF d2)
               (mkLabel_val 2 bunH2' input_pkg h2 h2Eq) recL recR
      recFun : Deriv (eqF (ap1 (mkLabel 2 (mkLabel 8 derBunIdx)) input_pkg)
                          (ap2 Pair (natCode 2) (cRec g h1 h2)))
      recFun = mkLabel_val 2 (mkLabel 8 derBunIdx) input_pkg (cRec g h1 h2)
                 (mkLabel_val 8 derBunIdx input_pkg (bun3 g h1 h2) bf)
      arm3 : Deriv (eqF (ap1 (mkAp2 (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR) input_pkg)
                        (ap2c (cRec g h1 h2) (ap1 triF d1) (ap1 triF d2)))
      arm3 = mkAp2_val (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR input_pkg
               (ap2 Pair (natCode 2) (cRec g h1 h2)) (ap1 triF d1) (ap1 triF d2)
               recFun recL recR
      val : Deriv (eqF (ap1 Rs_cell input_pkg)
                       (ap2c h1 (ap2c h2 (ap1 triF d1) (ap1 triF d2))
                                (ap2c (cRec g h1 h2) (ap1 triF d1) (ap1 triF d2))))
      val = mkAp2_val (mkLabel 2 bunH1')
              (mkAp2 (mkLabel 2 bunH2') triFL triFR)
              (mkAp2 (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR)
              input_pkg (ap2 Pair (natCode 2) h1)
              (ap2c h2 (ap1 triF d1) (ap1 triF d2))
              (ap2c (cRec g h1 h2) (ap1 triF d1) (ap1 triF d2))
              (mkLabel_val 2 bunH1' input_pkg h1 h1Eq) arm2 arm3
  in ruleTrans to_cellNode (ruleTrans fires val)
