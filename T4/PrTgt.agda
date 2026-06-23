{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTgt -- the OBJECT TARGET endpoint  tgtF : Fun1  over the PrDerCode
-- derivation coding (full p.r. calculus, 9 tags), generalising T4.DerTgt.
--
--   tgtF (derLeaf)            = tmO
--   tgtF (ap1c f d)           = tmAp1 f (tgtF d)
--   tgtF (ap2c g d1 d2)       = tmAp2 g (tgtF d1) (tgtF d2)
--   tgtF (derO d)             = tmO
--   tgtF (derU d)             = tgtF d
--   tgtF (derV d1 d2)         = tgtF d2
--   tgtF (derC g h1 h2 d)     = tmAp2 g (tmAp1 h1 (tgtF d)) (tmAp1 h2 (tgtF d))
--   tgtF (derRb g h1 h2 d)    = tmAp1 g (tgtF d)
--   tgtF (derRs g h1 h2 d1 d2)=
--        tmAp2 h1 (tmAp2 h2 (tgtF d1)(tgtF d2)) (tmAp2 (cRec g h1 h2)(tgtF d1)(tgtF d2))
--
-- Same dispatch skeleton as T4.PrSrc; only the per-tag cells differ (they
-- encode the rule RIGHT-hand sides, contracting each redex).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTgt where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; derC ; derRb ; derRs
        ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs
        ; filler ; bun3 )
open import T4.PrCodeObj
  using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cRec )
open import T4.PrDev
  using ( mkAp1 ; mkAp2 ; mkRec ; tmOF
        ; mkAp1_val ; mkAp2_val ; mkRec_val ; tmOF_val
        ; idxTest_fire ; idxTest_skip )

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
-- SECTION 1.  Index Fun1s and the cells.

derTagIdx : Fun1
derTagIdx = compose1U Fst nIdx
derBunIdx : Fun1
derBunIdx = compose1U Snd nIdx

bunF : Fun1
bunF = derBunIdx
bunG : Fun1
bunG = compose1U Fst derBunIdx
bunH1 : Fun1
bunH1 = compose1U Fst (compose1U Snd derBunIdx)
bunH2 : Fun1
bunH2 = compose1U Snd (compose1U Snd derBunIdx)

tgtL : Fun1
tgtL = lookupAt lIdx
tgtR : Fun1
tgtR = lookupAt rIdx

ap1cCell : Fun1
ap1cCell = mkAp1 bunF tgtL
ap2cCell : Fun1
ap2cCell = mkAp2 bunF tgtL tgtR
rOCell : Fun1
rOCell = tmOF
rUCell : Fun1
rUCell = tgtL
rVCell : Fun1
rVCell = tgtR
rCCell : Fun1
rCCell = mkAp2 bunG (mkAp1 bunH1 tgtL) (mkAp1 bunH2 tgtL)
rRbCell : Fun1
rRbCell = mkAp1 bunG tgtL
rRsCell : Fun1
rRsCell = mkAp2 bunH1 (mkAp2 bunH2 tgtL tgtR) (mkAp2 (mkRec bunG bunH1 bunH2) tgtL tgtR)

testTag : Nat -> Fun1
testTag k = C natEqF derTagIdx (constN k)

tgt_l7 : Fun1
tgt_l7 = C condFork (C pi rRbCell rRsCell) (testTag 7)
tgt_l6 : Fun1
tgt_l6 = C condFork (C pi rCCell tgt_l7) (testTag 6)
tgt_l5 : Fun1
tgt_l5 = C condFork (C pi rVCell tgt_l6) (testTag 5)
tgt_l4 : Fun1
tgt_l4 = C condFork (C pi rUCell tgt_l5) (testTag 4)
tgt_l3 : Fun1
tgt_l3 = C condFork (C pi rOCell tgt_l4) (testTag 3)
tgt_l2 : Fun1
tgt_l2 = C condFork (C pi ap2cCell tgt_l3) (testTag 2)
cellNodeTgt : Fun1
cellNodeTgt = C condFork (C pi ap1cCell tgt_l2) (testTag 1)

tgtF : Fun1
tgtF = binRec Z tmOF cellNodeTgt

------------------------------------------------------------------------
-- SECTION 2.  Leaf equation.

tgtF_reflO : Deriv (eqF (ap1 tgtF derLeaf) tmO)
tgtF_reflO =
  let open NP Z tmOF cellNodeTgt O dgReflO
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (tmOF_val input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  Shared node plumbing (identical to PrSrc, for tgtF).

w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())

wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
wn m k p = decideNatNeq m k p

module Node (lab l r : Term) where
  open NP Z tmOF cellNodeTgt (natCode 1) (ap2 Pair lab (ap2 Pair l r)) public
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
  recL : Deriv (eqF (ap1 tgtL input_pkg) (ap1 tgtF l))
  recL = np_lookup_gen lIdx l lIdx_eq
           (leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P)
  recR : Deriv (eqF (ap1 tgtR input_pkg) (ap1 tgtF r))
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
  to_cellNode : Deriv (eqF (ap1 tgtF (binNode lab l r)) (ap1 cellNodeTgt input_pkg))
  to_cellNode = collapse_snd t1_O

module Bundle (lab l r g h1 h2 : Term)
  (bunIsTriple : Deriv (eqF (ap1 Snd lab) (bun3 g h1 h2))) where
  open Node lab l r public
  bndl : Deriv (eqF (ap1 derBunIdx input_pkg) (bun3 g h1 h2))
  bndl = bun_eq (bun3 g h1 h2) bunIsTriple
  bG : Deriv (eqF (ap1 bunG input_pkg) g)
  bG = ruleTrans (compose1U_eq Fst derBunIdx input_pkg)
         (ruleTrans (cong1 Fst bndl) (axFst g (ap2 Pair h1 h2)))
  bInner : Deriv (eqF (ap1 (compose1U Snd derBunIdx) input_pkg) (ap2 Pair h1 h2))
  bInner = ruleTrans (compose1U_eq Snd derBunIdx input_pkg)
             (ruleTrans (cong1 Snd bndl) (axSnd g (ap2 Pair h1 h2)))
  bH1 : Deriv (eqF (ap1 bunH1 input_pkg) h1)
  bH1 = ruleTrans (compose1U_eq Fst (compose1U Snd derBunIdx) input_pkg)
          (ruleTrans (cong1 Fst bInner) (axFst h1 h2))
  bH2 : Deriv (eqF (ap1 bunH2 input_pkg) h2)
  bH2 = ruleTrans (compose1U_eq Snd (compose1U Snd derBunIdx) input_pkg)
          (ruleTrans (cong1 Snd bInner) (axSnd h1 h2))

------------------------------------------------------------------------
-- SECTION 4.  ap1c / ap2c congruences.

tgtF_ap1c : (f d : Term) -> Deriv (eqF (ap1 tgtF (ap1c f d)) (tmAp1 f (ap1 tgtF d)))
tgtF_ap1c f d =
  let open Node (ap2 Pair dgAp1c f) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 1))
      tg = tag_eq (natCode 1) (axFst dgAp1c f)
      bf : Deriv (eqF (ap1 bunF input_pkg) f)
      bf = bun_eq f (axSnd dgAp1c f)
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 ap1cCell input_pkg))
      fires = fork_true_to_fst ap1cCell tgt_l2 (testTag 1) input_pkg
                (idxTest_fire derTagIdx 1 input_pkg tg)
      val : Deriv (eqF (ap1 ap1cCell input_pkg) (tmAp1 f (ap1 tgtF d)))
      val = mkAp1_val bunF tgtL input_pkg f (ap1 tgtF d) bf recL
  in ruleTrans to_cellNode (ruleTrans fires val)

tgtF_ap2c : (g d1 d2 : Term) ->
  Deriv (eqF (ap1 tgtF (ap2c g d1 d2)) (tmAp2 g (ap1 tgtF d1) (ap1 tgtF d2)))
tgtF_ap2c g d1 d2 =
  let open Node (ap2 Pair dgAp2c g) d1 d2
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 2))
      tg = tag_eq (natCode 2) (axFst dgAp2c g)
      bf : Deriv (eqF (ap1 bunF input_pkg) g)
      bf = bun_eq g (axSnd dgAp2c g)
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 ap2cCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 2 1 input_pkg w21 tg))
                  (fork_true_to_fst ap2cCell tgt_l3 (testTag 2) input_pkg
                     (idxTest_fire derTagIdx 2 input_pkg tg))
      val : Deriv (eqF (ap1 ap2cCell input_pkg) (tmAp2 g (ap1 tgtF d1) (ap1 tgtF d2)))
      val = mkAp2_val bunF tgtL tgtR input_pkg g (ap1 tgtF d1) (ap1 tgtF d2) bf recL recR
  in ruleTrans to_cellNode (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 5.  o / u / v redex targets.

tgtF_rO : (d : Term) -> Deriv (eqF (ap1 tgtF (derO d)) tmO)
tgtF_rO d =
  let open Node (ap2 Pair dgRo O) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 3))
      tg = tag_eq (natCode 3) (axFst dgRo O)
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 rOCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 3 1 input_pkg (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 3 2 input_pkg (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst rOCell tgt_l4 (testTag 3) input_pkg
                       (idxTest_fire derTagIdx 3 input_pkg tg)))
  in ruleTrans to_cellNode (ruleTrans fires (tmOF_val input_pkg))

tgtF_rU : (d : Term) -> Deriv (eqF (ap1 tgtF (derU d)) (ap1 tgtF d))
tgtF_rU d =
  let open Node (ap2 Pair dgRu O) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 4))
      tg = tag_eq (natCode 4) (axFst dgRu O)
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 rUCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 4 1 input_pkg (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 4 2 input_pkg (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 4 3 input_pkg (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst rUCell tgt_l5 (testTag 4) input_pkg
                         (idxTest_fire derTagIdx 4 input_pkg tg))))
  in ruleTrans to_cellNode (ruleTrans fires recL)

tgtF_rV : (d1 d2 : Term) -> Deriv (eqF (ap1 tgtF (derV d1 d2)) (ap1 tgtF d2))
tgtF_rV d1 d2 =
  let open Node (ap2 Pair dgRv O) d1 d2
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 5))
      tg = tag_eq (natCode 5) (axFst dgRv O)
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 rVCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 5 1 input_pkg (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 5 2 input_pkg (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 5 3 input_pkg (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 5 4 input_pkg (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst rVCell tgt_l6 (testTag 5) input_pkg
                           (idxTest_fire derTagIdx 5 input_pkg tg)))))
  in ruleTrans to_cellNode (ruleTrans fires recR)

------------------------------------------------------------------------
-- SECTION 6.  C / Rb / Rs redex targets.

tgtF_rC : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 tgtF (derC g h1 h2 d))
             (tmAp2 g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d))))
tgtF_rC g h1 h2 d =
  let open Bundle (ap2 Pair dgRC (bun3 g h1 h2)) d filler g h1 h2 (axSnd dgRC (bun3 g h1 h2))
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 6))
      tg = tag_eq (natCode 6) (axFst dgRC (bun3 g h1 h2))
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 rCCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 6 1 input_pkg (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 6 2 input_pkg (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 6 3 input_pkg (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 6 4 input_pkg (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell tgt_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 6 5 input_pkg (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst rCCell tgt_l7 (testTag 6) input_pkg
                             (idxTest_fire derTagIdx 6 input_pkg tg))))))
      armH1 : Deriv (eqF (ap1 (mkAp1 bunH1 tgtL) input_pkg) (tmAp1 h1 (ap1 tgtF d)))
      armH1 = mkAp1_val bunH1 tgtL input_pkg h1 (ap1 tgtF d) bH1 recL
      armH2 : Deriv (eqF (ap1 (mkAp1 bunH2 tgtL) input_pkg) (tmAp1 h2 (ap1 tgtF d)))
      armH2 = mkAp1_val bunH2 tgtL input_pkg h2 (ap1 tgtF d) bH2 recL
      val : Deriv (eqF (ap1 rCCell input_pkg)
                       (tmAp2 g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d))))
      val = mkAp2_val bunG (mkAp1 bunH1 tgtL) (mkAp1 bunH2 tgtL) input_pkg
              g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d)) bG armH1 armH2
  in ruleTrans to_cellNode (ruleTrans fires val)

tgtF_rRb : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 tgtF (derRb g h1 h2 d)) (tmAp1 g (ap1 tgtF d)))
tgtF_rRb g h1 h2 d =
  let open Bundle (ap2 Pair dgRb (bun3 g h1 h2)) d filler g h1 h2 (axSnd dgRb (bun3 g h1 h2))
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 7))
      tg = tag_eq (natCode 7) (axFst dgRb (bun3 g h1 h2))
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 rRbCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 7 1 input_pkg (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 7 2 input_pkg (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 7 3 input_pkg (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 7 4 input_pkg (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell tgt_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 7 5 input_pkg (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rCCell tgt_l7 (testTag 6) input_pkg
                               (idxTest_skip derTagIdx 7 6 input_pkg (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst rRbCell rRsCell (testTag 7) input_pkg
                               (idxTest_fire derTagIdx 7 input_pkg tg)))))))
      val : Deriv (eqF (ap1 rRbCell input_pkg) (tmAp1 g (ap1 tgtF d)))
      val = mkAp1_val bunG tgtL input_pkg g (ap1 tgtF d) bG recL
  in ruleTrans to_cellNode (ruleTrans fires val)

tgtF_rRs : (g h1 h2 d1 d2 : Term) ->
  Deriv (eqF (ap1 tgtF (derRs g h1 h2 d1 d2))
             (tmAp2 h1 (tmAp2 h2 (ap1 tgtF d1) (ap1 tgtF d2))
                       (tmAp2 (cRec g h1 h2) (ap1 tgtF d1) (ap1 tgtF d2))))
tgtF_rRs g h1 h2 d1 d2 =
  let open Bundle (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2 g h1 h2 (axSnd dgRs (bun3 g h1 h2))
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 8))
      tg = tag_eq (natCode 8) (axFst dgRs (bun3 g h1 h2))
      fires : Deriv (eqF (ap1 cellNodeTgt input_pkg) (ap1 rRsCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 8 1 input_pkg (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 8 2 input_pkg (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 8 3 input_pkg (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 8 4 input_pkg (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell tgt_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 8 5 input_pkg (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rCCell tgt_l7 (testTag 6) input_pkg
                               (idxTest_skip derTagIdx 8 6 input_pkg (wn 8 6 (\ ())) tg))
                             (fork_false_to_snd rRbCell rRsCell (testTag 7) input_pkg
                               (idxTest_skip derTagIdx 8 7 input_pkg (wn 8 7 (\ ())) tg)))))))
      arm2 : Deriv (eqF (ap1 (mkAp2 bunH2 tgtL tgtR) input_pkg)
                        (tmAp2 h2 (ap1 tgtF d1) (ap1 tgtF d2)))
      arm2 = mkAp2_val bunH2 tgtL tgtR input_pkg h2 (ap1 tgtF d1) (ap1 tgtF d2) bH2 recL recR
      recFun : Deriv (eqF (ap1 (mkRec bunG bunH1 bunH2) input_pkg) (cRec g h1 h2))
      recFun = mkRec_val bunG bunH1 bunH2 input_pkg g h1 h2 bG bH1 bH2
      arm3 : Deriv (eqF (ap1 (mkAp2 (mkRec bunG bunH1 bunH2) tgtL tgtR) input_pkg)
                        (tmAp2 (cRec g h1 h2) (ap1 tgtF d1) (ap1 tgtF d2)))
      arm3 = mkAp2_val (mkRec bunG bunH1 bunH2) tgtL tgtR input_pkg
               (cRec g h1 h2) (ap1 tgtF d1) (ap1 tgtF d2) recFun recL recR
      val : Deriv (eqF (ap1 rRsCell input_pkg)
                       (tmAp2 h1 (tmAp2 h2 (ap1 tgtF d1) (ap1 tgtF d2))
                                 (tmAp2 (cRec g h1 h2) (ap1 tgtF d1) (ap1 tgtF d2))))
      val = mkAp2_val bunH1 (mkAp2 bunH2 tgtL tgtR) (mkAp2 (mkRec bunG bunH1 bunH2) tgtL tgtR)
              input_pkg h1 (tmAp2 h2 (ap1 tgtF d1) (ap1 tgtF d2))
              (tmAp2 (cRec g h1 h2) (ap1 tgtF d1) (ap1 tgtF d2)) bH1 arm2 arm3
  in ruleTrans to_cellNode (ruleTrans fires val)
