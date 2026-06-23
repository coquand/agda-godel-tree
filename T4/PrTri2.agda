{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTri2 -- the DEPTH-2 critical-pair triangle equations for the ap2c-cRec
-- congruence (generalising T4.DerTri2).  triF inspects the RIGHT child d2 of an
-- ap2c (cRec g h1 h2) d1 d2 congruence to decide whether the source has an
-- exposed R-redex:
--
--   triF (ap2c (cRec g h1 h2) d1 derLeaf)        = derRb g h1 h2 (triF d1)
--   triF (ap2c (cRec g h1 h2) d1 (ap1c cSuc e))  = derRs g h1 h2 (triF d1) (triF e)
--   triF (ap2c (cRec g h1 h2) d1 d2)             = ap2c (cRec g h1 h2)(triF d1)(triF d2)
--                                                  (d2 not derLeaf / not ap1c-cSuc)
--
-- The Rcong "else" is split into two generic lemmas (d2 a non-ap1c node, or an
-- ap1c node with non-cSuc fun) so downstream (shadow route) can instantiate per
-- right-child shape.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTri2 where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derRb ; derRs
        ; dgAp1c ; dgAp2c ; dgReflO ; dgRb ; dgRs ; filler ; bun3 )
open import T4.PrCodeObj using ( cSuc ; cRec ; tgSuc ; tgRec )
open import T4.PrDev using ( mkAp2 ; mkAp2_val ; idxTest_fire ; idxTest_skip )
open import T4.PrTri

open import T4.BinTree using ( binLeaf ; binNode ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )

open import BRA3.Church       using ( pi )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Shared ap2c-cRec node plumbing.

module RecNode (g0 h1 h2 d1 d2 : Term) where
  open Node (ap2 Pair dgAp2c (cRec g0 h1 h2)) d1 d2 public
  tg2 : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 2))
  tg2 = tag_eq (natCode 2) (axFst dgAp2c (cRec g0 h1 h2))
  bf : Deriv (eqF (ap1 derBunIdx input_pkg) (cRec g0 h1 h2))
  bf = bun_eq (cRec g0 h1 h2) (axSnd dgAp2c (cRec g0 h1 h2))
  hf8 : Deriv (eqF (ap1 funHd input_pkg) (natCode 8))
  hf8 = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
          (ruleTrans (cong1 Fst bf) (axFst tgRec (bun3 g0 h1 h2)))
  bunSnd_eq : Deriv (eqF (ap1 bunSnd input_pkg) (bun3 g0 h1 h2))
  bunSnd_eq = ruleTrans (compose1U_eq Snd derBunIdx input_pkg)
                (ruleTrans (cong1 Snd bf) (axSnd tgRec (bun3 g0 h1 h2)))
  to_ap2Cell : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 ap2Cell input_pkg))
  to_ap2Cell =
    ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) input_pkg
                 (idxTest_skip derTagIdx 2 1 input_pkg w21 tg2))
              (fork_true_to_fst ap2Cell tri_l3 (testTag 2) input_pkg
                 (idxTest_fire derTagIdx 2 input_pkg tg2))
  to_R_disp : Deriv (eqF (ap1 ap2Cell input_pkg) (ap1 R_disp input_pkg))
  to_R_disp = fork_false_to_snd br_v_cell R_disp (C natEqF funHd (constN 7)) input_pkg
                (idxTest_skip funHd 8 7 input_pkg (wn 8 7 (\ ())) hf8)
  -- d2-read helpers (via rIdx_eq : rIdx input = d2).
  d2tagAt : (vt : Term) -> Deriv (eqF (ap1 Fst d2) vt) ->
            Deriv (eqF (ap1 d2tag input_pkg) vt)
  d2tagAt vt eq = ruleTrans (compose1U_eq Fst rIdx input_pkg)
                   (ruleTrans (cong1 Fst rIdx_eq) eq)
  d2sndAt : (vt : Term) -> Deriv (eqF (ap1 Snd d2) vt) ->
            Deriv (eqF (ap1 (compose1U Snd rIdx) input_pkg) vt)
  d2sndAt vt eq = ruleTrans (compose1U_eq Snd rIdx input_pkg)
                   (ruleTrans (cong1 Snd rIdx_eq) eq)

w87 : NatNeqWitness 8 7
w87 = decideNatNeq 8 7 (\ ())

------------------------------------------------------------------------
-- SECTION 2.  Rb:  triF (ap2c (cRec g h1 h2) d1 derLeaf) = derRb g h1 h2 (triF d1).

triF_ap2c_Rb : (g0 h1 h2 d1 : Term) ->
  Deriv (eqF (ap1 triF (ap2c (cRec g0 h1 h2) d1 derLeaf))
             (derRb g0 h1 h2 (ap1 triF d1)))
triF_ap2c_Rb g0 h1 h2 d1 =
  let open RecNode g0 h1 h2 d1 derLeaf
      d2tag1 : Deriv (eqF (ap1 d2tag input_pkg) (natCode 1))
      d2tag1 = d2tagAt (natCode 1) (axFst (natCode 1) dgReflO)
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rb_cell input_pkg))
      fires = fork_true_to_fst br_Rb_cell R_mid (C natEqF d2tag (constN 1)) input_pkg
                (idxTest_fire d2tag 1 input_pkg d2tag1)
      val : Deriv (eqF (ap1 br_Rb_cell input_pkg) (derRb g0 h1 h2 (ap1 triF d1)))
      val = mkAp2_val (mkLabel 7 bunSnd) triFL mkLeafD input_pkg
              (ap2 Pair (natCode 7) (bun3 g0 h1 h2)) (ap1 triF d1) derLeaf
              (mkLabel_val 7 bunSnd input_pkg (bun3 g0 h1 h2) bunSnd_eq) recL (mkLeafD_val input_pkg)
  in ruleTrans to_cellNode (ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val)))

------------------------------------------------------------------------
-- SECTION 3.  Rs:  triF (ap2c (cRec g h1 h2) d1 (ap1c cSuc e))
--                = derRs g h1 h2 (triF d1) (triF e).

-- derL of an ap1c node :  derLF (ap1c f X) = X.
derL_ap1c : (f X : Term) -> Deriv (eqF (ap1 derLF (ap1c f X)) X)
derL_ap1c f X =
  let snd1 : Deriv (eqF (ap1 (compose1U Snd Snd) (ap1c f X)) (ap2 Pair X filler))
      snd1 = ruleTrans (compose1U_eq Snd Snd (ap1c f X))
               (ruleTrans (cong1 Snd (axSnd (natCode 2)
                            (ap2 Pair (ap2 Pair dgAp1c f) (ap2 Pair X filler))))
                          (axSnd (ap2 Pair dgAp1c f) (ap2 Pair X filler)))
  in ruleTrans (compose1U_eq Fst (compose1U Snd Snd) (ap1c f X))
       (ruleTrans (cong1 Fst snd1) (axFst X filler))

triF_ap2c_Rs : (g0 h1 h2 d1 e : Term) ->
  Deriv (eqF (ap1 triF (ap2c (cRec g0 h1 h2) d1 (ap1c cSuc e)))
             (derRs g0 h1 h2 (ap1 triF d1) (ap1 triF e)))
triF_ap2c_Rs g0 h1 h2 d1 e =
  let open RecNode g0 h1 h2 d1 (ap1c cSuc e)
      -- d2 = ap1c cSuc e = binNode (Pair dgAp1c cSuc) e filler.
      sndD2 : Deriv (eqF (ap1 Snd (ap1c cSuc e))
                         (ap2 Pair (ap2 Pair dgAp1c cSuc) (ap2 Pair e filler)))
      sndD2 = axSnd (natCode 2) (ap2 Pair (ap2 Pair dgAp1c cSuc) (ap2 Pair e filler))
      d2tag2 : Deriv (eqF (ap1 d2tag input_pkg) (natCode 2))
      d2tag2 = d2tagAt (natCode 2) (axFst (natCode 2)
                 (ap2 Pair (ap2 Pair dgAp1c cSuc) (ap2 Pair e filler)))
      innerSnd : Deriv (eqF (ap1 (compose1U Snd rIdx) input_pkg)
                            (ap2 Pair (ap2 Pair dgAp1c cSuc) (ap2 Pair e filler)))
      innerSnd = d2sndAt (ap2 Pair (ap2 Pair dgAp1c cSuc) (ap2 Pair e filler)) sndD2
      d2lab_v : Deriv (eqF (ap1 d2lab input_pkg) (ap2 Pair dgAp1c cSuc))
      d2lab_v = ruleTrans (compose1U_eq Fst (compose1U Snd rIdx) input_pkg)
                  (ruleTrans (cong1 Fst innerSnd)
                             (axFst (ap2 Pair dgAp1c cSuc) (ap2 Pair e filler)))
      d2labTag1 : Deriv (eqF (ap1 d2labTag input_pkg) (natCode 1))
      d2labTag1 = ruleTrans (compose1U_eq Fst d2lab input_pkg)
                    (ruleTrans (cong1 Fst d2lab_v) (axFst dgAp1c cSuc))
      d2FunHd3 : Deriv (eqF (ap1 d2FunHd input_pkg) (natCode 3))
      d2FunHd3 = ruleTrans (compose1U_eq Fst (compose1U Snd d2lab) input_pkg)
                   (ruleTrans (cong1 Fst (ruleTrans (compose1U_eq Snd d2lab input_pkg)
                                           (cong1 Snd d2lab_v)))
                              (ruleTrans (cong1 Fst (axSnd dgAp1c cSuc)) (axFst tgSuc O)))
      w21' : NatNeqWitness 2 1
      w21' = decideNatNeq 2 1 (\ ())
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rs_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_Rb_cell R_mid (C natEqF d2tag (constN 1)) input_pkg
                     (idxTest_skip d2tag 2 1 input_pkg w21' d2tag2))
          (ruleTrans (fork_true_to_fst R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) input_pkg
                       (idxTest_fire d2labTag 1 input_pkg d2labTag1))
                     (fork_true_to_fst br_Rs_cell br_Rcong_cell (C natEqF d2FunHd (constN 3)) input_pkg
                       (idxTest_fire d2FunHd 3 input_pkg d2FunHd3)))
      -- third arm:  derLF (triF d2) = triF e , via triF_ap1c_s + derL_ap1c.
      thirdArm : Deriv (eqF (ap1 (compose1U derLF triFR) input_pkg) (ap1 triF e))
      thirdArm = ruleTrans (compose1U_eq derLF triFR input_pkg)
                   (ruleTrans (cong1 derLF (ruleTrans recR (triF_ap1c_s e)))
                              (derL_ap1c cSuc (ap1 triF e)))
      val : Deriv (eqF (ap1 br_Rs_cell input_pkg) (derRs g0 h1 h2 (ap1 triF d1) (ap1 triF e)))
      val = mkAp2_val (mkLabel 8 bunSnd) triFL (compose1U derLF triFR) input_pkg
              (ap2 Pair (natCode 8) (bun3 g0 h1 h2)) (ap1 triF d1) (ap1 triF e)
              (mkLabel_val 8 bunSnd input_pkg (bun3 g0 h1 h2) bunSnd_eq) recL thirdArm
  in ruleTrans to_cellNode (ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val)))

------------------------------------------------------------------------
-- SECTION 4.  R-congruence "else" (two flavors).

br_Rcong_val : (g0 h1 h2 d1 d2 : Term) -> let open RecNode g0 h1 h2 d1 d2 in
  Deriv (eqF (ap1 br_Rcong_cell input_pkg)
             (ap2c (cRec g0 h1 h2) (ap1 triF d1) (ap1 triF d2)))
br_Rcong_val g0 h1 h2 d1 d2 =
  let open RecNode g0 h1 h2 d1 d2
  in mkAp2_val (mkLabel 2 derBunIdx) triFL triFR input_pkg
       (ap2 Pair (natCode 2) (cRec g0 h1 h2)) (ap1 triF d1) (ap1 triF d2)
       (mkLabel_val 2 derBunIdx input_pkg (cRec g0 h1 h2) bf) recL recR

-- (A) d2 a non-ap1c node:  binTag d2 = 2 , label-tag = m != 1.
triF_ap2c_Rcong_notAp1c : (g0 h1 h2 d1 d2 n2 l2 r2 : Term) (m : Nat) ->
  Deriv (eqF d2 (binNode n2 l2 r2)) ->
  Deriv (eqF (ap1 Fst n2) (natCode m)) -> ((Eq m 1) -> Empty) ->
  Deriv (eqF (ap1 triF (ap2c (cRec g0 h1 h2) d1 d2))
             (ap2c (cRec g0 h1 h2) (ap1 triF d1) (ap1 triF d2)))
triF_ap2c_Rcong_notAp1c g0 h1 h2 d1 d2 n2 l2 r2 m d2node labm m1 =
  let open RecNode g0 h1 h2 d1 d2
      d2tag2 : Deriv (eqF (ap1 d2tag input_pkg) (natCode 2))
      d2tag2 = d2tagAt (natCode 2)
                 (ruleTrans (cong1 Fst d2node) (axFst (natCode 2) (ap2 Pair n2 (ap2 Pair l2 r2))))
      sndEq : Deriv (eqF (ap1 Snd d2) (ap2 Pair n2 (ap2 Pair l2 r2)))
      sndEq = ruleTrans (cong1 Snd d2node) (axSnd (natCode 2) (ap2 Pair n2 (ap2 Pair l2 r2)))
      innerSnd : Deriv (eqF (ap1 (compose1U Snd rIdx) input_pkg) (ap2 Pair n2 (ap2 Pair l2 r2)))
      innerSnd = d2sndAt (ap2 Pair n2 (ap2 Pair l2 r2)) sndEq
      d2lab_v : Deriv (eqF (ap1 d2lab input_pkg) n2)
      d2lab_v = ruleTrans (compose1U_eq Fst (compose1U Snd rIdx) input_pkg)
                  (ruleTrans (cong1 Fst innerSnd) (axFst n2 (ap2 Pair l2 r2)))
      d2labTagM : Deriv (eqF (ap1 d2labTag input_pkg) (natCode m))
      d2labTagM = ruleTrans (compose1U_eq Fst d2lab input_pkg)
                    (ruleTrans (cong1 Fst d2lab_v) labm)
      w21' : NatNeqWitness 2 1
      w21' = decideNatNeq 2 1 (\ ())
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rcong_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_Rb_cell R_mid (C natEqF d2tag (constN 1)) input_pkg
                     (idxTest_skip d2tag 2 1 input_pkg w21' d2tag2))
                  (fork_false_to_snd R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) input_pkg
                     (idxTest_skip d2labTag m 1 input_pkg (decideNatNeq m 1 m1) d2labTagM))
  in ruleTrans to_cellNode (ruleTrans to_ap2Cell (ruleTrans to_R_disp
       (ruleTrans fires (br_Rcong_val g0 h1 h2 d1 d2))))

-- (B) d2 an ap1c node with non-cSuc fun:  d2 = ap1c f l2 ... , Fst f = m' != 3.
triF_ap2c_Rcong_ap1cNotSuc : (g0 h1 h2 d1 d2 f l2 r2 : Term) (m : Nat) ->
  Deriv (eqF d2 (binNode (ap2 Pair dgAp1c f) l2 r2)) ->
  Deriv (eqF (ap1 Fst f) (natCode m)) -> ((Eq m 3) -> Empty) ->
  Deriv (eqF (ap1 triF (ap2c (cRec g0 h1 h2) d1 d2))
             (ap2c (cRec g0 h1 h2) (ap1 triF d1) (ap1 triF d2)))
triF_ap2c_Rcong_ap1cNotSuc g0 h1 h2 d1 d2 f l2 r2 m d2node funm m3 =
  let open RecNode g0 h1 h2 d1 d2
      lab2 : Term
      lab2 = ap2 Pair dgAp1c f
      d2tag2 : Deriv (eqF (ap1 d2tag input_pkg) (natCode 2))
      d2tag2 = d2tagAt (natCode 2)
                 (ruleTrans (cong1 Fst d2node) (axFst (natCode 2) (ap2 Pair lab2 (ap2 Pair l2 r2))))
      sndEq : Deriv (eqF (ap1 Snd d2) (ap2 Pair lab2 (ap2 Pair l2 r2)))
      sndEq = ruleTrans (cong1 Snd d2node) (axSnd (natCode 2) (ap2 Pair lab2 (ap2 Pair l2 r2)))
      innerSnd : Deriv (eqF (ap1 (compose1U Snd rIdx) input_pkg) (ap2 Pair lab2 (ap2 Pair l2 r2)))
      innerSnd = d2sndAt (ap2 Pair lab2 (ap2 Pair l2 r2)) sndEq
      d2lab_v : Deriv (eqF (ap1 d2lab input_pkg) lab2)
      d2lab_v = ruleTrans (compose1U_eq Fst (compose1U Snd rIdx) input_pkg)
                  (ruleTrans (cong1 Fst innerSnd) (axFst lab2 (ap2 Pair l2 r2)))
      d2labTag1 : Deriv (eqF (ap1 d2labTag input_pkg) (natCode 1))
      d2labTag1 = ruleTrans (compose1U_eq Fst d2lab input_pkg)
                    (ruleTrans (cong1 Fst d2lab_v) (axFst dgAp1c f))
      d2FunHdM : Deriv (eqF (ap1 d2FunHd input_pkg) (natCode m))
      d2FunHdM = ruleTrans (compose1U_eq Fst (compose1U Snd d2lab) input_pkg)
                   (ruleTrans (cong1 Fst (ruleTrans (compose1U_eq Snd d2lab input_pkg)
                                           (cong1 Snd d2lab_v)))
                              (ruleTrans (cong1 Fst (axSnd dgAp1c f)) funm))
      w21' : NatNeqWitness 2 1
      w21' = decideNatNeq 2 1 (\ ())
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rcong_cell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_Rb_cell R_mid (C natEqF d2tag (constN 1)) input_pkg
                     (idxTest_skip d2tag 2 1 input_pkg w21' d2tag2))
          (ruleTrans (fork_true_to_fst R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) input_pkg
                       (idxTest_fire d2labTag 1 input_pkg d2labTag1))
                     (fork_false_to_snd br_Rs_cell br_Rcong_cell (C natEqF d2FunHd (constN 3)) input_pkg
                       (idxTest_skip d2FunHd m 3 input_pkg (decideNatNeq m 3 m3) d2FunHdM)))
  in ruleTrans to_cellNode (ruleTrans to_ap2Cell (ruleTrans to_R_disp
       (ruleTrans fires (br_Rcong_val g0 h1 h2 d1 d2))))
