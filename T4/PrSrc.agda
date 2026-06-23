{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrSrc -- the OBJECT SOURCE endpoint  srcF : Fun1  over the PrDerCode
-- derivation coding (full p.r. calculus, 9 tags), generalising T4.DerSrc.
--
--   srcF (derLeaf)            = tmO
--   srcF (ap1c f d)           = tmAp1 f (srcF d)
--   srcF (ap2c g d1 d2)       = tmAp2 g (srcF d1) (srcF d2)
--   srcF (derO d)             = tmAp1 cZero (srcF d)
--   srcF (derU d)             = tmAp1 cId   (srcF d)
--   srcF (derV d1 d2)         = tmAp2 cProj (srcF d1) (srcF d2)
--   srcF (derC g h1 h2 d)     = tmAp1 (cComp g h1 h2) (srcF d)
--   srcF (derRb g h1 h2 d)    = tmAp2 (cRec g h1 h2) (srcF d) tmO
--   srcF (derRs g h1 h2 d1 d2)= tmAp2 (cRec g h1 h2) (srcF d1) (tmAp1 cSuc (srcF d2))
--
-- The node cell dispatches on the derivation tag (Fst of the label) with a
-- nested condFork / natEqF cascade, reads the carried fun-codes from the
-- label's bundle (Snd of the label, RAW) and the child fold-values via
-- lookupAt lIdx / rIdx.  Builders (mkAp1/mkAp2/mkRec/tmOF/cSucF) reused from
-- T4.PrDev.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrSrc where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; derC ; derRb ; derRs
        ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs
        ; filler ; bun3 )
open import T4.PrCodeObj
  using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cZero ; cId ; cComp ; cProj ; cRec )
open import T4.PrDev
  using ( mkAp1 ; mkAp2 ; mkRec ; tmOF ; cSucF
        ; mkAp1_val ; mkAp2_val ; mkRec_val ; tmOF_val ; cSucF_val
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
-- SECTION 1.  Constant fun-code cells and the compose builder.

cZeroF : Fun1
cZeroF = C pi (constN 4) Z
cIdF : Fun1
cIdF = C pi (constN 5) Z
cProjF : Fun1
cProjF = C pi (constN 7) Z

cZeroF_val : (input : Term) -> Deriv (eqF (ap1 cZeroF input) cZero)
cZeroF_val input = ruleTrans (ax_C pi (constN 4) Z input)
  (ruleTrans (congL pi (ap1 Z input) (constN_eq 4 input)) (congR pi (natCode 4) (axZ input)))
cIdF_val : (input : Term) -> Deriv (eqF (ap1 cIdF input) cId)
cIdF_val input = ruleTrans (ax_C pi (constN 5) Z input)
  (ruleTrans (congL pi (ap1 Z input) (constN_eq 5 input)) (congR pi (natCode 5) (axZ input)))
cProjF_val : (input : Term) -> Deriv (eqF (ap1 cProjF input) cProj)
cProjF_val input = ruleTrans (ax_C pi (constN 7) Z input)
  (ruleTrans (congL pi (ap1 Z input) (constN_eq 7 input)) (congR pi (natCode 7) (axZ input)))

mkComp : Fun1 -> Fun1 -> Fun1 -> Fun1
mkComp G0 H1 H2 = C pi (constN 6) (C pi G0 (C pi H1 H2))

mkComp_val : (G0 H1 H2 : Fun1) (input vg vh1 vh2 : Term) ->
  Deriv (eqF (ap1 G0 input) vg) -> Deriv (eqF (ap1 H1 input) vh1) -> Deriv (eqF (ap1 H2 input) vh2) ->
  Deriv (eqF (ap1 (mkComp G0 H1 H2) input) (cComp vg vh1 vh2))
mkComp_val G0 H1 H2 input vg vh1 vh2 eG eH1 eH2 =
  let inH : Deriv (eqF (ap1 (C pi H1 H2) input) (ap2 Pair vh1 vh2))
      inH = ruleTrans (ax_C pi H1 H2 input)
              (ruleTrans (congL pi (ap1 H2 input) eH1) (congR pi vh1 eH2))
      inner : Deriv (eqF (ap1 (C pi G0 (C pi H1 H2)) input) (ap2 Pair vg (ap2 Pair vh1 vh2)))
      inner = ruleTrans (ax_C pi G0 (C pi H1 H2) input)
                (ruleTrans (congL pi (ap1 (C pi H1 H2) input) eG) (congR pi vg inH))
  in ruleTrans (ax_C pi (constN 6) (C pi G0 (C pi H1 H2)) input)
       (ruleTrans (congL pi (ap1 (C pi G0 (C pi H1 H2)) input) (constN_eq 6 input))
                  (congR pi (natCode 6) inner))

------------------------------------------------------------------------
-- SECTION 2.  Index Fun1s and the cells.

derTagIdx : Fun1                     -- Fst label = tag
derTagIdx = compose1U Fst nIdx
derBunIdx : Fun1                     -- Snd label = bundle (= f / g / Pair g (Pair h1 h2))
derBunIdx = compose1U Snd nIdx

bunF : Fun1                          -- whole bundle (= f for ap1c, g for ap2c)
bunF = derBunIdx
bunG : Fun1                          -- bundle Fst (= g for C/R)
bunG = compose1U Fst derBunIdx
bunH1 : Fun1
bunH1 = compose1U Fst (compose1U Snd derBunIdx)
bunH2 : Fun1
bunH2 = compose1U Snd (compose1U Snd derBunIdx)

srcL : Fun1                          -- srcF of left child
srcL = lookupAt lIdx
srcR : Fun1                          -- srcF of right child
srcR = lookupAt rIdx

-- per-tag source builder cells.
ap1cCell : Fun1
ap1cCell = mkAp1 bunF srcL
ap2cCell : Fun1
ap2cCell = mkAp2 bunF srcL srcR
rOCell : Fun1
rOCell = mkAp1 cZeroF srcL
rUCell : Fun1
rUCell = mkAp1 cIdF srcL
rVCell : Fun1
rVCell = mkAp2 cProjF srcL srcR
rCCell : Fun1
rCCell = mkAp1 (mkComp bunG bunH1 bunH2) srcL
rRbCell : Fun1
rRbCell = mkAp2 (mkRec bunG bunH1 bunH2) srcL tmOF
rRsCell : Fun1
rRsCell = mkAp2 (mkRec bunG bunH1 bunH2) srcL (mkAp1 cSucF srcR)

testTag : Nat -> Fun1
testTag k = C natEqF derTagIdx (constN k)

src_l7 : Fun1
src_l7 = C condFork (C pi rRbCell rRsCell) (testTag 7)
src_l6 : Fun1
src_l6 = C condFork (C pi rCCell src_l7) (testTag 6)
src_l5 : Fun1
src_l5 = C condFork (C pi rVCell src_l6) (testTag 5)
src_l4 : Fun1
src_l4 = C condFork (C pi rUCell src_l5) (testTag 4)
src_l3 : Fun1
src_l3 = C condFork (C pi rOCell src_l4) (testTag 3)
src_l2 : Fun1
src_l2 = C condFork (C pi ap2cCell src_l3) (testTag 2)
cellNodeSrc : Fun1
cellNodeSrc = C condFork (C pi ap1cCell src_l2) (testTag 1)

srcF : Fun1
srcF = binRec Z tmOF cellNodeSrc

------------------------------------------------------------------------
-- SECTION 3.  Leaf equation:  srcF (derLeaf) = tmO .

srcF_reflO : Deriv (eqF (ap1 srcF derLeaf) tmO)
srcF_reflO =
  let open NP Z tmOF cellNodeSrc O dgReflO
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (tmOF_val input_pkg)

------------------------------------------------------------------------
-- SECTION 4.  Shared node plumbing.

w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())

module Node (lab l r : Term) where
  open NP Z tmOF cellNodeSrc (natCode 1) (ap2 Pair lab (ap2 Pair l r)) public
  t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
  t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
  nIdx_eq : Deriv (eqF (ap1 nIdx input_pkg) lab)
  nIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
              (ruleTrans (cong1 Fst np_rc) (axFst lab (ap2 Pair l r)))
  -- children l, r recovered and bounded.
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
  recL : Deriv (eqF (ap1 srcL input_pkg) (ap1 srcF l))
  recL = np_lookup_gen lIdx l lIdx_eq
           (leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P)
  recR : Deriv (eqF (ap1 srcR input_pkg) (ap1 srcF r))
  recR = np_lookup_gen rIdx r rIdx_eq
           (leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P)
  -- tag / bundle reads.
  tag_eq : (hf : Term) -> Deriv (eqF (ap1 Fst lab) hf) ->
           Deriv (eqF (ap1 derTagIdx input_pkg) hf)
  tag_eq hf eq = ruleTrans (compose1U_eq Fst nIdx input_pkg)
                   (ruleTrans (cong1 Fst nIdx_eq) eq)
  bun_eq : (bn : Term) -> Deriv (eqF (ap1 Snd lab) bn) ->
           Deriv (eqF (ap1 derBunIdx input_pkg) bn)
  bun_eq bn eq = ruleTrans (compose1U_eq Snd nIdx input_pkg)
                   (ruleTrans (cong1 Snd nIdx_eq) eq)
  to_cellNode : Deriv (eqF (ap1 srcF (binNode lab l r)) (ap1 cellNodeSrc input_pkg))
  to_cellNode = collapse_snd t1_O

-- neq witnesses for the tag cascade.
wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
wn m k p = decideNatNeq m k p

------------------------------------------------------------------------
-- SECTION 5.  ap1c / ap2c congruences (bundle = f / g).

srcF_ap1c : (f d : Term) -> Deriv (eqF (ap1 srcF (ap1c f d)) (tmAp1 f (ap1 srcF d)))
srcF_ap1c f d =
  let open Node (ap2 Pair dgAp1c f) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 1))
      tg = tag_eq (natCode 1) (axFst dgAp1c f)
      bf : Deriv (eqF (ap1 bunF input_pkg) f)
      bf = bun_eq f (axSnd dgAp1c f)
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 ap1cCell input_pkg))
      fires = fork_true_to_fst ap1cCell src_l2 (testTag 1) input_pkg
                (idxTest_fire derTagIdx 1 input_pkg tg)
      val : Deriv (eqF (ap1 ap1cCell input_pkg) (tmAp1 f (ap1 srcF d)))
      val = mkAp1_val bunF srcL input_pkg f (ap1 srcF d) bf recL
  in ruleTrans to_cellNode (ruleTrans fires val)

srcF_ap2c : (g d1 d2 : Term) ->
  Deriv (eqF (ap1 srcF (ap2c g d1 d2)) (tmAp2 g (ap1 srcF d1) (ap1 srcF d2)))
srcF_ap2c g d1 d2 =
  let open Node (ap2 Pair dgAp2c g) d1 d2
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 2))
      tg = tag_eq (natCode 2) (axFst dgAp2c g)
      bf : Deriv (eqF (ap1 bunF input_pkg) g)
      bf = bun_eq g (axSnd dgAp2c g)
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 ap2cCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 2 1 input_pkg w21 tg))
                  (fork_true_to_fst ap2cCell src_l3 (testTag 2) input_pkg
                     (idxTest_fire derTagIdx 2 input_pkg tg))
      val : Deriv (eqF (ap1 ap2cCell input_pkg) (tmAp2 g (ap1 srcF d1) (ap1 srcF d2)))
      val = mkAp2_val bunF srcL srcR input_pkg g (ap1 srcF d1) (ap1 srcF d2) bf recL recR
  in ruleTrans to_cellNode (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 6.  o / u / v redex sources (fixed funs).

srcF_rO : (d : Term) -> Deriv (eqF (ap1 srcF (derO d)) (tmAp1 cZero (ap1 srcF d)))
srcF_rO d =
  let open Node (ap2 Pair dgRo O) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 3))
      tg = tag_eq (natCode 3) (axFst dgRo O)
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 rOCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 3 1 input_pkg (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell src_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 3 2 input_pkg (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst rOCell src_l4 (testTag 3) input_pkg
                       (idxTest_fire derTagIdx 3 input_pkg tg)))
      val : Deriv (eqF (ap1 rOCell input_pkg) (tmAp1 cZero (ap1 srcF d)))
      val = mkAp1_val cZeroF srcL input_pkg cZero (ap1 srcF d) (cZeroF_val input_pkg) recL
  in ruleTrans to_cellNode (ruleTrans fires val)

srcF_rU : (d : Term) -> Deriv (eqF (ap1 srcF (derU d)) (tmAp1 cId (ap1 srcF d)))
srcF_rU d =
  let open Node (ap2 Pair dgRu O) d filler
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 4))
      tg = tag_eq (natCode 4) (axFst dgRu O)
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 rUCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 4 1 input_pkg (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell src_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 4 2 input_pkg (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell src_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 4 3 input_pkg (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst rUCell src_l5 (testTag 4) input_pkg
                         (idxTest_fire derTagIdx 4 input_pkg tg))))
      val : Deriv (eqF (ap1 rUCell input_pkg) (tmAp1 cId (ap1 srcF d)))
      val = mkAp1_val cIdF srcL input_pkg cId (ap1 srcF d) (cIdF_val input_pkg) recL
  in ruleTrans to_cellNode (ruleTrans fires val)

srcF_rV : (d1 d2 : Term) ->
  Deriv (eqF (ap1 srcF (derV d1 d2)) (tmAp2 cProj (ap1 srcF d1) (ap1 srcF d2)))
srcF_rV d1 d2 =
  let open Node (ap2 Pair dgRv O) d1 d2
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 5))
      tg = tag_eq (natCode 5) (axFst dgRv O)
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 rVCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 5 1 input_pkg (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell src_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 5 2 input_pkg (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell src_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 5 3 input_pkg (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell src_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 5 4 input_pkg (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst rVCell src_l6 (testTag 5) input_pkg
                           (idxTest_fire derTagIdx 5 input_pkg tg)))))
      val : Deriv (eqF (ap1 rVCell input_pkg) (tmAp2 cProj (ap1 srcF d1) (ap1 srcF d2)))
      val = mkAp2_val cProjF srcL srcR input_pkg cProj (ap1 srcF d1) (ap1 srcF d2)
              (cProjF_val input_pkg) recL recR
  in ruleTrans to_cellNode (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 7.  C / Rb / Rs redex sources (bundle = Pair g (Pair h1 h2)).

-- shared: project the three carried fun-codes from the bundle.
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

srcF_rC : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 srcF (derC g h1 h2 d)) (tmAp1 (cComp g h1 h2) (ap1 srcF d)))
srcF_rC g h1 h2 d =
  let open Bundle (ap2 Pair dgRC (bun3 g h1 h2)) d filler g h1 h2 (axSnd dgRC (bun3 g h1 h2))
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 6))
      tg = tag_eq (natCode 6) (axFst dgRC (bun3 g h1 h2))
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 rCCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 6 1 input_pkg (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell src_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 6 2 input_pkg (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell src_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 6 3 input_pkg (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell src_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 6 4 input_pkg (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell src_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 6 5 input_pkg (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst rCCell src_l7 (testTag 6) input_pkg
                             (idxTest_fire derTagIdx 6 input_pkg tg))))))
      val : Deriv (eqF (ap1 rCCell input_pkg) (tmAp1 (cComp g h1 h2) (ap1 srcF d)))
      val = mkAp1_val (mkComp bunG bunH1 bunH2) srcL input_pkg (cComp g h1 h2) (ap1 srcF d)
              (mkComp_val bunG bunH1 bunH2 input_pkg g h1 h2 bG bH1 bH2) recL
  in ruleTrans to_cellNode (ruleTrans fires val)

srcF_rRb : (g h1 h2 d : Term) ->
  Deriv (eqF (ap1 srcF (derRb g h1 h2 d)) (tmAp2 (cRec g h1 h2) (ap1 srcF d) tmO))
srcF_rRb g h1 h2 d =
  let open Bundle (ap2 Pair dgRb (bun3 g h1 h2)) d filler g h1 h2 (axSnd dgRb (bun3 g h1 h2))
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 7))
      tg = tag_eq (natCode 7) (axFst dgRb (bun3 g h1 h2))
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 rRbCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 7 1 input_pkg (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell src_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 7 2 input_pkg (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell src_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 7 3 input_pkg (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell src_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 7 4 input_pkg (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell src_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 7 5 input_pkg (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rCCell src_l7 (testTag 6) input_pkg
                               (idxTest_skip derTagIdx 7 6 input_pkg (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst rRbCell rRsCell (testTag 7) input_pkg
                               (idxTest_fire derTagIdx 7 input_pkg tg)))))))
      val : Deriv (eqF (ap1 rRbCell input_pkg) (tmAp2 (cRec g h1 h2) (ap1 srcF d) tmO))
      val = mkAp2_val (mkRec bunG bunH1 bunH2) srcL tmOF input_pkg
              (cRec g h1 h2) (ap1 srcF d) tmO
              (mkRec_val bunG bunH1 bunH2 input_pkg g h1 h2 bG bH1 bH2) recL (tmOF_val input_pkg)
  in ruleTrans to_cellNode (ruleTrans fires val)

srcF_rRs : (g h1 h2 d1 d2 : Term) ->
  Deriv (eqF (ap1 srcF (derRs g h1 h2 d1 d2))
             (tmAp2 (cRec g h1 h2) (ap1 srcF d1) (tmAp1 cSuc (ap1 srcF d2))))
srcF_rRs g h1 h2 d1 d2 =
  let open Bundle (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2 g h1 h2 (axSnd dgRs (bun3 g h1 h2))
      tg : Deriv (eqF (ap1 derTagIdx input_pkg) (natCode 8))
      tg = tag_eq (natCode 8) (axFst dgRs (bun3 g h1 h2))
      fires : Deriv (eqF (ap1 cellNodeSrc input_pkg) (ap1 rRsCell input_pkg))
      fires =
        ruleTrans (fork_false_to_snd ap1cCell src_l2 (testTag 1) input_pkg
                     (idxTest_skip derTagIdx 8 1 input_pkg (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell src_l3 (testTag 2) input_pkg
                       (idxTest_skip derTagIdx 8 2 input_pkg (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell src_l4 (testTag 3) input_pkg
                         (idxTest_skip derTagIdx 8 3 input_pkg (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell src_l5 (testTag 4) input_pkg
                           (idxTest_skip derTagIdx 8 4 input_pkg (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell src_l6 (testTag 5) input_pkg
                             (idxTest_skip derTagIdx 8 5 input_pkg (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rCCell src_l7 (testTag 6) input_pkg
                               (idxTest_skip derTagIdx 8 6 input_pkg (wn 8 6 (\ ())) tg))
                             (fork_false_to_snd rRbCell rRsCell (testTag 7) input_pkg
                               (idxTest_skip derTagIdx 8 7 input_pkg (wn 8 7 (\ ())) tg)))))))
      srcSuc : Deriv (eqF (ap1 (mkAp1 cSucF srcR) input_pkg) (tmAp1 cSuc (ap1 srcF d2)))
      srcSuc = mkAp1_val cSucF srcR input_pkg cSuc (ap1 srcF d2) (cSucF_val input_pkg) recR
      val : Deriv (eqF (ap1 rRsCell input_pkg)
                       (tmAp2 (cRec g h1 h2) (ap1 srcF d1) (tmAp1 cSuc (ap1 srcF d2))))
      val = mkAp2_val (mkRec bunG bunH1 bunH2) srcL (mkAp1 cSucF srcR) input_pkg
              (cRec g h1 h2) (ap1 srcF d1) (tmAp1 cSuc (ap1 srcF d2))
              (mkRec_val bunG bunH1 bunH2 input_pkg g h1 h2 bG bH1 bH2) recL srcSuc
  in ruleTrans to_cellNode (ruleTrans fires val)
