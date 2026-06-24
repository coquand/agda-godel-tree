{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfFunRecUOpaqueImp -- IMP-FORM opaque wfFunRec equations for the full p.r.
-- calculus, carried under [negLeaf, htag] (nodes) / Hleaf (leaf).  wfFunRec
-- validates carried funcodes (funValid) and recurses; the cov-dispatch uses these
-- to extract  funValid (funP p) = O  (for src_tri compound-fun reconstruction)
-- and the children's wfFunRec.  base = Z (HBase Z), since O subterms are excluded
-- already by wfRed.
--
--   reflO  => wfFunRec p = O
--   ap1c   => wfFunRec p = pi (funValid (funP p)) (wfFunRec (pL p))
--   ap2c   => wfFunRec p = pi (funValid (funP p)) (pi (wfFunRec pL) (wfFunRec pR))
--   derO/derU => wfFunRec p = wfFunRec (pL p)
--   derV   => wfFunRec p = pi (wfFunRec pL) (wfFunRec pR)
--   derC/derRb => wfFunRec p = pi (fv3 g h1 h2) (wfFunRec pL)
--   derRs  => wfFunRec p = pi (fv3 g h1 h2) (pi (wfFunRec pL) (wfFunRec pR))
-- with fv3val = pi (funValid (gP p)) (pi (funValid (h1P p)) (funValid (h2P p))).
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfFunRecUOpaqueImp where

open import T4.Base

open import T4.PrDerCode using ( dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrWfFunRec using ( funValid ; funValidF ; funValidF_eq )
open import T4.PrWfFunRec
  using ( wfFunRec ; derTagIdx ; derBunIdx ; bunGidx ; bunSndIdx ; bunH1idx ; bunH2idx
        ; fvB ; fv3 ; unaryCell ; wfAdCell ; arF1cell ; arF2cell
        ; ap1cCell ; ap2cCell ; rcUnaryCell ; rcBinCell ; rcCompC ; rcCompRb
        ; recRForm ; recRwf ; recCForm ; recCwf
        ; ff_l2 ; ff_l3 ; ff_l4 ; ff_l5 ; ff_l6 ; ff_l7 ; ff_l8 ; fnCellNode ; testTag )
open import T4.PrWfFun using ( wfFun ; isF1 ; isF2 )
open import T4.PrCodeObj using ( cComp ; cRec )
open import T4.PrSrcUOpaque using ( funP ; gP ; h1P ; h2P )

open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )

open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; natEqFire_imp ; natEqSkip_imp )
open import T4.CtxKit using ( lift2 ; trans2c )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )

import T4.OpaqueHarness
private
  wfFunStepU : Fun1
  wfFunStepU = stepOf Z fnCellNode
open T4.OpaqueHarness.HBase Z wfFunStepU

private
  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf

  op_tag : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 get_tag (opkg p)) (ap1 Fst p))
  op_tag p ne = ruleTrans (compose1U_eq Fst get_newK (opkg p)) (cong1 Fst (op_newK p ne))

  test1At : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) (opkg p)) (ap2 natEqF (ap1 Fst p) (natCode 1)))
  test1At p ne =
    ruleTrans (ax_C natEqF get_tag (constN 1) (opkg p))
      (ruleTrans (congL natEqF (ap1 (constN 1) (opkg p)) (op_tag p ne))
                 (congR natEqF (ap1 Fst p) (constN_eq 1 (opkg p))))

  recBun : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 derBunIdx (opkg p)) (funP p))
  recBun p ne = ruleTrans (compose1U_eq Snd nIdx (opkg p)) (cong1 Snd (op_nIdx p ne))

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 unaryCell (opkg p)) (ap1 wfFunRec (pL p)))
  recPL p ne = lookup_op Z wfFunStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 wfFunRec (pR p)))
  recPR p ne = lookup_op Z wfFunStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

  ad_val : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 wfAdCell (opkg p)) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p))))
  ad_val p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
         (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recPL p ne))
                    (congR pi (ap1 wfFunRec (pL p)) (recPR p ne)))

  -- funValid of the single bundle.
  fvB_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 fvB (opkg p)) (funValid (funP p)))
  fvB_op p ne =
    let opk = opkg p
    in ruleTrans (compose1U_eq funValidF derBunIdx opk)
         (ruleTrans (cong1 funValidF (recBun p ne)) (funValidF_eq (funP p)))

  -- fv3 cell value (redex bundle components).
  bunG_op : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunGidx (opkg p)) (gP p))
  bunG_op p ne = ruleTrans (compose1U_eq Fst derBunIdx (opkg p)) (cong1 Fst (recBun p ne))
  bunSnd_op : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunSndIdx (opkg p)) (ap1 Snd (funP p)))
  bunSnd_op p ne = ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))
  bunH1_op : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH1idx (opkg p)) (h1P p))
  bunH1_op p ne = ruleTrans (compose1U_eq Fst bunSndIdx (opkg p)) (cong1 Fst (bunSnd_op p ne))
  bunH2_op : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH2idx (opkg p)) (h2P p))
  bunH2_op p ne = ruleTrans (compose1U_eq Snd bunSndIdx (opkg p)) (cong1 Snd (bunSnd_op p ne))

  fv3val : Term -> Term
  fv3val p = ap2 pi (funValid (gP p)) (ap2 pi (funValid (h1P p)) (funValid (h2P p)))

  fv3_op : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 fv3 (opkg p)) (fv3val p))
  fv3_op p ne =
    let opk = opkg p
        innerCell : Fun1
        innerCell = C pi (compose1U funValidF bunH1idx) (compose1U funValidF bunH2idx)
        fvG : Deriv (eqF (ap1 (compose1U funValidF bunGidx) opk) (funValid (gP p)))
        fvG = ruleTrans (compose1U_eq funValidF bunGidx opk) (ruleTrans (cong1 funValidF (bunG_op p ne)) (funValidF_eq (gP p)))
        fvH1 : Deriv (eqF (ap1 (compose1U funValidF bunH1idx) opk) (funValid (h1P p)))
        fvH1 = ruleTrans (compose1U_eq funValidF bunH1idx opk) (ruleTrans (cong1 funValidF (bunH1_op p ne)) (funValidF_eq (h1P p)))
        fvH2 : Deriv (eqF (ap1 (compose1U funValidF bunH2idx) opk) (funValid (h2P p)))
        fvH2 = ruleTrans (compose1U_eq funValidF bunH2idx opk) (ruleTrans (cong1 funValidF (bunH2_op p ne)) (funValidF_eq (h2P p)))
        inner_val : Deriv (eqF (ap1 innerCell opk) (ap2 pi (funValid (h1P p)) (funValid (h2P p))))
        inner_val =
          ruleTrans (ax_C pi (compose1U funValidF bunH1idx) (compose1U funValidF bunH2idx) opk)
            (ruleTrans (congL pi (ap1 (compose1U funValidF bunH2idx) opk) fvH1)
                       (congR pi (funValid (h1P p)) fvH2))
    in ruleTrans (ax_C pi (compose1U funValidF bunGidx) innerCell opk)
         (ruleTrans (congL pi (ap1 innerCell opk) fvG)
                    (congR pi (funValid (gP p)) inner_val))

  -- FIX(C) arity opaque value lemmas (head of funP p = gP p = Fst (funP p)).
  nHb_op : (p : Term) -> Deriv (neg (eqF p O)) -> (k : Nat) ->
    Deriv (eqF (ap1 (C natEqF bunGidx (constN k)) (opkg p)) (ap2 natEqF (ap1 Fst (funP p)) (natCode k)))
  nHb_op p ne k =
    ruleTrans (ax_C natEqF bunGidx (constN k) (opkg p))
      (ruleTrans (congL natEqF (ap1 (constN k) (opkg p)) (bunG_op p ne))
                 (congR natEqF (gP p) (constN_eq k (opkg p))))
  arF1_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 arF1cell (opkg p)) (isF1 (funP p)))
  arF1_op p ne =
    ruleTrans (ax_C pi (C natEqF bunGidx (constN 7)) (C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1))) (opkg p))
      (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1))) (opkg p)) (nHb_op p ne 7))
        (congR pi (ap2 natEqF (ap1 Fst (funP p)) (natCode 7))
          (ruleTrans (ax_C pi (C natEqF bunGidx (constN 8)) (C natEqF bunGidx (constN 1)) (opkg p))
            (ruleTrans (congL pi (ap1 (C natEqF bunGidx (constN 1)) (opkg p)) (nHb_op p ne 8))
                       (congR pi (ap2 natEqF (ap1 Fst (funP p)) (natCode 8)) (nHb_op p ne 1))))))
  arF2_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 arF2cell (opkg p)) (isF2 (funP p)))
  arF2_op p ne =
    ruleTrans (ax_C pi (C natEqF bunGidx (constN 3)) (C pi (C natEqF bunGidx (constN 4)) (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))))) (opkg p))
      (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 4)) (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))))) (opkg p)) (nHb_op p ne 3))
        (congR pi (ap2 natEqF (ap1 Fst (funP p)) (natCode 3))
          (ruleTrans (ax_C pi (C natEqF bunGidx (constN 4)) (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)))) (opkg p))
            (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)))) (opkg p)) (nHb_op p ne 4))
              (congR pi (ap2 natEqF (ap1 Fst (funP p)) (natCode 4))
                (ruleTrans (ax_C pi (C natEqF bunGidx (constN 5)) (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))) (opkg p))
                  (ruleTrans (congL pi (ap1 (C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1))) (opkg p)) (nHb_op p ne 5))
                    (congR pi (ap2 natEqF (ap1 Fst (funP p)) (natCode 5))
                      (ruleTrans (ax_C pi (C natEqF bunGidx (constN 6)) (C natEqF bunGidx (constN 1)) (opkg p))
                        (ruleTrans (congL pi (ap1 (C natEqF bunGidx (constN 1)) (opkg p)) (nHb_op p ne 6))
                                   (congR pi (ap2 natEqF (ap1 Fst (funP p)) (natCode 6)) (nHb_op p ne 1))))))))))))
  -- the node cell values (FIX(C): arity-prefixed).
  ap1cInner_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (C pi fvB unaryCell) (opkg p)) (ap2 pi (funValid (funP p)) (ap1 wfFunRec (pL p))))
  ap1cInner_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi fvB unaryCell opk)
         (ruleTrans (congL pi (ap1 unaryCell opk) (fvB_op p ne))
                    (congR pi (funValid (funP p)) (recPL p ne)))
  ap1cCell_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 ap1cCell (opkg p)) (ap2 pi (isF1 (funP p)) (ap2 pi (funValid (funP p)) (ap1 wfFunRec (pL p)))))
  ap1cCell_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi arF1cell (C pi fvB unaryCell) opk)
         (ruleTrans (congL pi (ap1 (C pi fvB unaryCell) opk) (arF1_op p ne))
                    (congR pi (isF1 (funP p)) (ap1cInner_op p ne)))
  ap2cInner_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (C pi fvB wfAdCell) (opkg p))
               (ap2 pi (funValid (funP p)) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p)))))
  ap2cInner_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi fvB wfAdCell opk)
         (ruleTrans (congL pi (ap1 wfAdCell opk) (fvB_op p ne))
                    (congR pi (funValid (funP p)) (ad_val p ne)))
  ap2cCell_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 ap2cCell (opkg p))
               (ap2 pi (isF2 (funP p)) (ap2 pi (funValid (funP p)) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p))))))
  ap2cCell_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi arF2cell (C pi fvB wfAdCell) opk)
         (ruleTrans (congL pi (ap1 (C pi fvB wfAdCell) opk) (arF2_op p ne))
                    (congR pi (isF2 (funP p)) (ap2cInner_op p ne)))
  rcUnary_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 rcUnaryCell (opkg p)) (ap2 pi (fv3val p) (ap1 wfFunRec (pL p))))
  rcUnary_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi fv3 unaryCell opk)
         (ruleTrans (congL pi (ap1 unaryCell opk) (fv3_op p ne))
                    (congR pi (fv3val p) (recPL p ne)))
  -- FIX(C): reconstructed compound terms for derC (Pair 6) / derRb (Pair 8) .
  reconCterm : Term -> Term
  reconCterm p = ap2 Pair (natCode 6) (funP p)
  rcCompC_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 rcCompC (opkg p))
               (ap2 pi (ap1 wfFun (reconCterm p)) (ap1 wfFunRec (pL p))))
  rcCompC_op p ne =
    let opk = opkg p
        recCForm_op : Deriv (eqF (ap1 recCForm opk) (reconCterm p))
        recCForm_op = ruleTrans (ax_C Pair (constN 6) derBunIdx opk)
                        (ruleTrans (congL Pair (ap1 derBunIdx opk) (constN_eq 6 opk))
                                   (congR Pair (natCode 6) (recBun p ne)))
        recCwf_op : Deriv (eqF (ap1 recCwf opk) (ap1 wfFun (reconCterm p)))
        recCwf_op = ruleTrans (compose1U_eq wfFun recCForm opk) (cong1 wfFun recCForm_op)
    in ruleTrans (ax_C pi recCwf unaryCell opk)
         (ruleTrans (congL pi (ap1 unaryCell opk) recCwf_op)
                    (congR pi (ap1 wfFun (reconCterm p)) (recPL p ne)))
  -- FIX(B): reconstructed R-combinator term  Pair (natCode 8) (funP p) .
  reconRterm : Term -> Term
  reconRterm p = ap2 Pair (natCode 8) (funP p)
  rcCompRb_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 rcCompRb (opkg p))
               (ap2 pi (ap1 wfFun (reconRterm p)) (ap1 wfFunRec (pL p))))
  rcCompRb_op p ne =
    let opk = opkg p
        recRForm_op : Deriv (eqF (ap1 recRForm opk) (reconRterm p))
        recRForm_op = ruleTrans (ax_C Pair (constN 8) derBunIdx opk)
                        (ruleTrans (congL Pair (ap1 derBunIdx opk) (constN_eq 8 opk))
                                   (congR Pair (natCode 8) (recBun p ne)))
        recRwf_op : Deriv (eqF (ap1 recRwf opk) (ap1 wfFun (reconRterm p)))
        recRwf_op = ruleTrans (compose1U_eq wfFun recRForm opk) (cong1 wfFun recRForm_op)
    in ruleTrans (ax_C pi recRwf unaryCell opk)
         (ruleTrans (congL pi (ap1 unaryCell opk) recRwf_op)
                    (congR pi (ap1 wfFun (reconRterm p)) (recPL p ne)))
  rcBin_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 rcBinCell (opkg p))
               (ap2 pi (ap1 wfFun (reconRterm p))
                       (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p)))))
  rcBin_op p ne =
    let opk = opkg p
        recRForm_op : Deriv (eqF (ap1 recRForm opk) (reconRterm p))
        recRForm_op = ruleTrans (ax_C Pair (constN 8) derBunIdx opk)
                        (ruleTrans (congL Pair (ap1 derBunIdx opk) (constN_eq 8 opk))
                                   (congR Pair (natCode 8) (recBun p ne)))
        recRwf_op : Deriv (eqF (ap1 recRwf opk) (ap1 wfFun (reconRterm p)))
        recRwf_op = ruleTrans (compose1U_eq wfFun recRForm opk) (cong1 wfFun recRForm_op)
    in ruleTrans (ax_C pi recRwf wfAdCell opk)
         (ruleTrans (congL pi (ap1 wfAdCell opk) recRwf_op)
                    (congR pi (ap1 wfFun (reconRterm p)) (ad_val p ne)))

  module Node (p : Term) (ne : Deriv (neg (eqF p O))) (lbl : Term) where
    opk = opkg p
    negLeaf : Formula
    negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
    htag : Formula
    htag = eqF (ap1 Fst (dtag p)) lbl
    t1f : Term
    t1f = ap1 (C natEqF get_tag (constN 1)) opk
    nl_neg : Deriv (imp negLeaf (eqF t1f O))
    nl_neg = impEqTrans t1f (ap2 natEqF (ap1 Fst p) (natCode 1)) O
               (impLift (test1At p ne)) (natEqF_complete (ap1 Fst p) (natCode 1))
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 wfFunStepU opk) (ap1 fnCellNode opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf Z fnCellNode
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 wfFunStepU opk) (ap1 fnCellNode opk)) htag)
    derTag_bare : Deriv (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p)))
    derTag_bare = ruleTrans (compose1U_eq Fst nIdx opk) (cong1 Fst (op_nIdx p ne))
    nieq_imp : Deriv (imp htag (eqF (ap1 derTagIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) lbl
                 (impLift derTag_bare) (identP htag)

  mkChain : (p : Term) (ne : Deriv (neg (eqF p O))) (negLeaf htag : Formula) (cell : Fun1) (rhs : Term) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 wfFunStepU (opkg p)) (ap1 fnCellNode (opkg p))))) ->
    Deriv (imp htag (eqF (ap1 fnCellNode (opkg p)) (ap1 cell (opkg p)))) ->
    Deriv (eqF (ap1 cell (opkg p)) rhs) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 wfFunRec p) rhs)))
  mkChain p ne negLeaf htag cell rhs step2 node_fires cell_val =
    let opk = opkg p
    in trans2c (ap1 wfFunRec p) (ap1 wfFunStepU opk) rhs
         (lift2 negLeaf htag (opUnfold p ne))
         (trans2c (ap1 wfFunStepU opk) (ap1 fnCellNode opk) rhs step2
           (trans2c (ap1 fnCellNode opk) (ap1 cell opk) rhs
             (liftP negLeaf node_fires) (lift2 negLeaf htag cell_val)))

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

wfFunRec_op_reflO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 wfFunRec p) O))
wfFunRec_op_reflO_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      cell_fires : Deriv (imp Hleaf (eqF (ap1 wfFunStepU opk) (ap1 Z opk)))
      cell_fires = fork_true_to_fst_imp Hleaf Z fnCellNode (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp Hleaf get_tag 1 opk gtag)
  in impEqTrans (ap1 wfFunRec p) (ap1 wfFunStepU opk) O
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 wfFunStepU opk) (ap1 Z opk) O cell_fires (impLift (axZ opk)))

------------------------------------------------------------------------
-- SECTION 3.  Congruences ap1c / ap2c.

wfFunRec_op_ap1c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c)
                  (eqF (ap1 wfFunRec p)
                       (ap2 pi (isF1 (funP p)) (ap2 pi (funValid (funP p)) (ap1 wfFunRec (pL p)))))))
wfFunRec_op_ap1c_imp p ne =
  let open Node p ne dgAp1c
      node_fires = fork_true_to_fst_imp htag ap1cCell ff_l2 (testTag 1) opk
                     (natEqFire_imp htag derTagIdx 1 opk nieq_imp)
  in mkChain p ne negLeaf htag ap1cCell
       (ap2 pi (isF1 (funP p)) (ap2 pi (funValid (funP p)) (ap1 wfFunRec (pL p))))
       step2 node_fires (ap1cCell_op p ne)

wfFunRec_op_ap2c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (eqF (ap1 wfFunRec p)
                       (ap2 pi (isF2 (funP p)) (ap2 pi (funValid (funP p)) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p))))))))
wfFunRec_op_ap2c_imp p ne =
  let open Node p ne dgAp2c
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 ap2cCell opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 2 1 opk (wn 2 1 (\ ())) nieq_imp))
          (fork_true_to_fst_imp htag ap2cCell ff_l3 (testTag 2) opk
             (natEqFire_imp htag derTagIdx 2 opk nieq_imp))
  in mkChain p ne negLeaf htag ap2cCell
       (ap2 pi (isF2 (funP p)) (ap2 pi (funValid (funP p)) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p)))))
       step2 node_fires (ap2cCell_op p ne)

------------------------------------------------------------------------
-- SECTION 4.  derO / derU / derV (no funValid).

wfFunRec_op_rO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRo) (eqF (ap1 wfFunRec p) (ap1 wfFunRec (pL p)))))
wfFunRec_op_rO_imp p ne =
  let open Node p ne dgRo
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 3 1 opk (wn 3 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 ff_l2 opk) (ap1 ff_l3 opk) (ap1 unaryCell opk)
            (fork_false_to_snd_imp htag ap2cCell ff_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 3 2 opk (wn 3 2 (\ ())) nieq_imp))
            (fork_true_to_fst_imp htag unaryCell ff_l4 (testTag 3) opk
               (natEqFire_imp htag derTagIdx 3 opk nieq_imp)))
  in mkChain p ne negLeaf htag unaryCell (ap1 wfFunRec (pL p)) step2 node_fires (recPL p ne)

wfFunRec_op_rU_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRu) (eqF (ap1 wfFunRec p) (ap1 wfFunRec (pL p)))))
wfFunRec_op_rU_imp p ne =
  let open Node p ne dgRu
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 4 1 opk (wn 4 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 ff_l2 opk) (ap1 ff_l3 opk) (ap1 unaryCell opk)
            (fork_false_to_snd_imp htag ap2cCell ff_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 4 2 opk (wn 4 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 ff_l3 opk) (ap1 ff_l4 opk) (ap1 unaryCell opk)
              (fork_false_to_snd_imp htag unaryCell ff_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 4 3 opk (wn 4 3 (\ ())) nieq_imp))
              (fork_true_to_fst_imp htag unaryCell ff_l5 (testTag 4) opk
                 (natEqFire_imp htag derTagIdx 4 opk nieq_imp))))
  in mkChain p ne negLeaf htag unaryCell (ap1 wfFunRec (pL p)) step2 node_fires (recPL p ne)

wfFunRec_op_rV_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRv)
                  (eqF (ap1 wfFunRec p) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p))))))
wfFunRec_op_rV_imp p ne =
  let open Node p ne dgRv
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 wfAdCell opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 5 1 opk (wn 5 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 ff_l2 opk) (ap1 ff_l3 opk) (ap1 wfAdCell opk)
            (fork_false_to_snd_imp htag ap2cCell ff_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 5 2 opk (wn 5 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 ff_l3 opk) (ap1 ff_l4 opk) (ap1 wfAdCell opk)
              (fork_false_to_snd_imp htag unaryCell ff_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 5 3 opk (wn 5 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 ff_l4 opk) (ap1 ff_l5 opk) (ap1 wfAdCell opk)
                (fork_false_to_snd_imp htag unaryCell ff_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 5 4 opk (wn 5 4 (\ ())) nieq_imp))
                (fork_true_to_fst_imp htag wfAdCell ff_l6 (testTag 5) opk
                   (natEqFire_imp htag derTagIdx 5 opk nieq_imp)))))
  in mkChain p ne negLeaf htag wfAdCell (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p))) step2 node_fires (ad_val p ne)

------------------------------------------------------------------------
-- SECTION 5.  derC / derRb / derRs (fv3 bundle validation).

wfFunRec_op_rC_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRC)
                  (eqF (ap1 wfFunRec p) (ap2 pi (ap1 wfFun (ap2 Pair (natCode 6) (funP p))) (ap1 wfFunRec (pL p))))))
wfFunRec_op_rC_imp p ne =
  let open Node p ne dgRC
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 rcCompC opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 6 1 opk (wn 6 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 ff_l2 opk) (ap1 ff_l3 opk) (ap1 rcCompC opk)
            (fork_false_to_snd_imp htag ap2cCell ff_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 6 2 opk (wn 6 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 ff_l3 opk) (ap1 ff_l4 opk) (ap1 rcCompC opk)
              (fork_false_to_snd_imp htag unaryCell ff_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 6 3 opk (wn 6 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 ff_l4 opk) (ap1 ff_l5 opk) (ap1 rcCompC opk)
                (fork_false_to_snd_imp htag unaryCell ff_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 6 4 opk (wn 6 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 ff_l5 opk) (ap1 ff_l6 opk) (ap1 rcCompC opk)
                  (fork_false_to_snd_imp htag wfAdCell ff_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 6 5 opk (wn 6 5 (\ ())) nieq_imp))
                  (fork_true_to_fst_imp htag rcCompC ff_l7 (testTag 6) opk
                     (natEqFire_imp htag derTagIdx 6 opk nieq_imp))))))
  in mkChain p ne negLeaf htag rcCompC
       (ap2 pi (ap1 wfFun (ap2 Pair (natCode 6) (funP p))) (ap1 wfFunRec (pL p)))
       step2 node_fires (rcCompC_op p ne)

wfFunRec_op_rRb_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRb)
                  (eqF (ap1 wfFunRec p) (ap2 pi (ap1 wfFun (ap2 Pair (natCode 8) (funP p))) (ap1 wfFunRec (pL p))))))
wfFunRec_op_rRb_imp p ne =
  let open Node p ne dgRb
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 rcCompRb opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 7 1 opk (wn 7 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 ff_l2 opk) (ap1 ff_l3 opk) (ap1 rcCompRb opk)
            (fork_false_to_snd_imp htag ap2cCell ff_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 7 2 opk (wn 7 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 ff_l3 opk) (ap1 ff_l4 opk) (ap1 rcCompRb opk)
              (fork_false_to_snd_imp htag unaryCell ff_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 7 3 opk (wn 7 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 ff_l4 opk) (ap1 ff_l5 opk) (ap1 rcCompRb opk)
                (fork_false_to_snd_imp htag unaryCell ff_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 7 4 opk (wn 7 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 ff_l5 opk) (ap1 ff_l6 opk) (ap1 rcCompRb opk)
                  (fork_false_to_snd_imp htag wfAdCell ff_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 7 5 opk (wn 7 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 ff_l6 opk) (ap1 ff_l7 opk) (ap1 rcCompRb opk)
                    (fork_false_to_snd_imp htag rcCompC ff_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 7 6 opk (wn 7 6 (\ ())) nieq_imp))
                    (fork_true_to_fst_imp htag rcCompRb ff_l8 (testTag 7) opk
                       (natEqFire_imp htag derTagIdx 7 opk nieq_imp)))))))
  in mkChain p ne negLeaf htag rcCompRb
       (ap2 pi (ap1 wfFun (ap2 Pair (natCode 8) (funP p))) (ap1 wfFunRec (pL p)))
       step2 node_fires (rcCompRb_op p ne)

wfFunRec_op_rRs_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRs)
                  (eqF (ap1 wfFunRec p)
                       (ap2 pi (ap1 wfFun (ap2 Pair (natCode 8) (funP p)))
                               (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p)))))))
wfFunRec_op_rRs_imp p ne =
  let open Node p ne dgRs
      node_fires =
        impEqTrans (ap1 fnCellNode opk) (ap1 ff_l2 opk) (ap1 rcBinCell opk)
          (fork_false_to_snd_imp htag ap1cCell ff_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 8 1 opk (wn 8 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 ff_l2 opk) (ap1 ff_l3 opk) (ap1 rcBinCell opk)
            (fork_false_to_snd_imp htag ap2cCell ff_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 8 2 opk (wn 8 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 ff_l3 opk) (ap1 ff_l4 opk) (ap1 rcBinCell opk)
              (fork_false_to_snd_imp htag unaryCell ff_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 8 3 opk (wn 8 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 ff_l4 opk) (ap1 ff_l5 opk) (ap1 rcBinCell opk)
                (fork_false_to_snd_imp htag unaryCell ff_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 8 4 opk (wn 8 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 ff_l5 opk) (ap1 ff_l6 opk) (ap1 rcBinCell opk)
                  (fork_false_to_snd_imp htag wfAdCell ff_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 8 5 opk (wn 8 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 ff_l6 opk) (ap1 ff_l7 opk) (ap1 rcBinCell opk)
                    (fork_false_to_snd_imp htag rcCompC ff_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 8 6 opk (wn 8 6 (\ ())) nieq_imp))
                    (impEqTrans (ap1 ff_l7 opk) (ap1 ff_l8 opk) (ap1 rcBinCell opk)
                      (fork_false_to_snd_imp htag rcCompRb ff_l8 (testTag 7) opk
                         (natEqSkip_imp htag derTagIdx 8 7 opk (wn 8 7 (\ ())) nieq_imp))
                      (fork_true_to_fst_imp htag rcBinCell Z (testTag 8) opk
                         (natEqFire_imp htag derTagIdx 8 opk nieq_imp))))))))
  in mkChain p ne negLeaf htag rcBinCell
       (ap2 pi (ap1 wfFun (ap2 Pair (natCode 8) (funP p))) (ap2 pi (ap1 wfFunRec (pL p)) (ap1 wfFunRec (pR p))))
       step2 node_fires (rcBin_op p ne)
