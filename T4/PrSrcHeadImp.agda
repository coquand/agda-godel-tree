{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrSrcHeadImp -- IMP-FORM source of an ap1c CHILD derivation, threading the
-- head condition  Fst p = natCode 2  (a binNode) and the tag  Fst(dtag p)=dgAp1c
-- as antecedents, deriving the non-O witness internally:
--
--   srcF_ap1c_himp p :
--     imp (Fst p = natCode 2) (imp (Fst(dtag p) = dgAp1c)
--       (srcF p = tmAp1 (funP p) (srcL opk)))            -- left child kept OPAQUE
--
-- The left child  srcL opk = lookupAt lIdx opk  is left UN-evaluated (we only
-- need the head structure of  srcF p ), so this avoids the heavy  lookup_op
-- re-derivation.  Used by the ap2c cRec Rcong sub-glue, whose  devF_ap2_Rcong_h
-- only needs  Fst(srcF p) = tgAp1  and  Fst(Fst(Snd(srcF p))) = Fst(funP p) .
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrSrcHeadImp where

open import T4.Base

open import T4.PrDerCode using ( dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv )
open import T4.PrCodeObj using ( tmAp1 ; tmAp2 ; tgAp2 ; cZero ; cId ; cProj )
open import T4.PrDev using ( mkAp1 ; mkAp1_val ; mkAp2 ; mkAp2_val ; tmOF )
open import T4.PrSrc
  using ( srcF ; cellNodeSrc ; ap1cCell ; ap2cCell ; rOCell ; rUCell ; rVCell
        ; src_l2 ; src_l3 ; src_l4 ; src_l5 ; src_l6 ; bunF ; srcL ; srcR
        ; cZeroF ; cZeroF_val ; cIdF ; cIdF_val ; cProjF ; cProjF_val ; derTagIdx ; derBunIdx ; testTag )
open import T4.PrSrcUOpaque using ( funP )
open import T4.DerCodeS using ( dtag )
open import T4.BinTree using ( nIdx )
open import T4.FoldRec using ( get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )

open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )
open import T4.ForkImp using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; natEqFire_imp ; natEqSkip_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impCongL ; impCongR ; impMp ; impRuleSym )
open import BRA3.Contrapositive using ( compI ; identP ; liftP )
open import BRA3.Classical using ( axContrapos )
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR ; cnjCurry )
open import T4.AdDispatchAux using ( FstO )
open import T4.CtxKit using ( trans2c )
open import T4.DescSndImp using ( neSucc )
open import T4.PrCodeObj using ( tgAp1 )

import T4.OpaqueHarnessImp

private
  srcStepU : Fun1
  srcStepU = stepOf tmOF cellNodeSrc
module Hs = T4.OpaqueHarnessImp.HimpBase Z srcStepU

private
  ne_from_head2 : (p : Term) -> Deriv (imp (eqF (ap1 Fst p) (natCode 2)) (neg (eqF p O)))
  ne_from_head2 p =
    let H = eqF (ap1 Fst p) (natCode 2)
        P = eqF p O
        Q = eqF (natCode 2) O
        leg1 : Deriv (imp H (imp P (eqF (natCode 2) (ap1 Fst p))))
        leg1 = compI (impRuleSym (identP H)) (axK (eqF (natCode 2) (ap1 Fst p)) P)
        bareLeg : Deriv (imp P (eqF (ap1 Fst p) O))
        bareLeg = impEqTrans (ap1 Fst p) (ap1 Fst O) O (impCong1 Fst p O (identP P)) (impLift FstO)
        combined : Deriv (imp H (imp P Q))
        combined = trans2c (natCode 2) (ap1 Fst p) O leg1 (impLift bareLeg)
    in impMp (impMp (impLift (axContrapos P Q)) combined) (impLift (neSucc (natCode 1)))

  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf

------------------------------------------------------------------------

-- the (opaque, un-evaluated) left-child argument of the ap1c source.
srcChildArg : Term -> Term
srcChildArg p = ap1 srcL (Hs.opkg p)

srcF_ap1c_himp : (p : Term) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 2))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c)
                  (eqF (ap1 srcF p) (tmAp1 (funP p) (srcChildArg p)))))
srcF_ap1c_himp p =
  let Hd2 = eqF (ap1 Fst p) (natCode 2)
      htag = eqF (ap1 Fst (dtag p)) dgAp1c
      HH = Cnj Hd2 htag
      opk = Hs.opkg p
      ne : Deriv (imp HH (neg (eqF p O)))
      ne = compI (cnjL Hd2 htag) (ne_from_head2 p)
      rhs = tmAp1 (funP p) (ap1 srcL opk)
      rawCell = tmAp1 (ap1 bunF opk) (ap1 srcL opk)
      -- get_tag opk = natCode 2.
      op_tag_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 get_tag opk) (ap1 Fst p)))
      op_tag_ne = impEqTrans (ap1 get_tag opk) (ap1 Fst (ap1 get_newK opk)) (ap1 Fst p)
                    (impLift (compose1U_eq Fst get_newK opk)) (impCong1 Fst (ap1 get_newK opk) p (Hs.op_newK_imp p))
      gtag : Deriv (imp HH (eqF (ap1 get_tag opk) (natCode 2)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 2) (compI ne op_tag_ne) (cnjL Hd2 htag)
      -- (1) srcF p = srcStepU opk.
      e1 : Deriv (imp HH (eqF (ap1 srcF p) (ap1 srcStepU opk)))
      e1 = compI ne (Hs.opUnfold_imp p)
      -- (2) srcStepU opk = cellNodeSrc opk  (leaf-skip).
      t1O : Deriv (imp HH (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
      t1O = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk) (ap2 natEqF (ap1 get_tag opk) (natCode 1)) O
              (impLift (ruleTrans (ax_C natEqF get_tag (constN 1) opk) (congR natEqF (ap1 get_tag opk) (constN_eq 1 opk))))
              (impEqTrans (ap2 natEqF (ap1 get_tag opk) (natCode 1)) (ap2 natEqF (natCode 2) (natCode 1)) O
                (impCongL natEqF (ap1 get_tag opk) (natCode 2) (natCode 1) gtag)
                (impLift (natEqF_at_neq 2 1 (wn 2 1 (\ ())))))
      e2 : Deriv (imp HH (eqF (ap1 srcStepU opk) (ap1 cellNodeSrc opk)))
      e2 = fork_false_to_snd_imp HH tmOF cellNodeSrc (C natEqF get_tag (constN 1)) opk t1O
      -- (3) cellNodeSrc opk = ap1cCell opk  (dtag-fire).
      derTag_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p))))
      derTag_ne = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (ap1 nIdx opk)) (ap1 Fst (dtag p))
                    (impLift (compose1U_eq Fst nIdx opk)) (impCong1 Fst (ap1 nIdx opk) (dtag p) (Hs.op_nIdx_imp p))
      derTagH : Deriv (imp HH (eqF (ap1 derTagIdx opk) (natCode 1)))
      derTagH = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) (natCode 1) (compI ne derTag_ne) (cnjR Hd2 htag)
      e3 : Deriv (imp HH (eqF (ap1 cellNodeSrc opk) (ap1 ap1cCell opk)))
      e3 = fork_true_to_fst_imp HH ap1cCell src_l2 (testTag 1) opk (natEqFire_imp HH derTagIdx 1 opk derTagH)
      -- (4) ap1cCell opk = rawCell  (mkAp1 raw, child opaque) -> tmAp1 (funP p)(srcL opk).
      cellRaw : Deriv (eqF (ap1 ap1cCell opk) rawCell)
      cellRaw = mkAp1_val bunF srcL opk (ap1 bunF opk) (ap1 srcL opk) (axRefl (ap1 bunF opk)) (axRefl (ap1 srcL opk))
      recBun_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 derBunIdx opk) (funP p)))
      recBun_ne = impEqTrans (ap1 derBunIdx opk) (ap1 Snd (ap1 nIdx opk)) (funP p)
                    (impLift (compose1U_eq Snd nIdx opk)) (impCong1 Snd (ap1 nIdx opk) (dtag p) (Hs.op_nIdx_imp p))
      cellRewrite : Deriv (imp HH (eqF rawCell rhs))
      cellRewrite = compI (compI ne recBun_ne)
                      (impCongR Pair (ap2 Pair (ap1 bunF opk) (ap1 srcL opk)) (ap2 Pair (funP p) (ap1 srcL opk)) tgAp1
                        (impCongL Pair (ap1 bunF opk) (funP p) (ap1 srcL opk) (identP (eqF (ap1 bunF opk) (funP p)))))
      e4 : Deriv (imp HH (eqF (ap1 ap1cCell opk) rhs))
      e4 = impEqTrans (ap1 ap1cCell opk) rawCell rhs (liftP HH cellRaw) cellRewrite
      chain : Deriv (imp HH (eqF (ap1 srcF p) rhs))
      chain = impEqTrans (ap1 srcF p) (ap1 srcStepU opk) rhs e1
                (impEqTrans (ap1 srcStepU opk) (ap1 cellNodeSrc opk) rhs e2
                  (impEqTrans (ap1 cellNodeSrc opk) (ap1 ap1cCell opk) rhs e3 e4))
  in cnjCurry chain

------------------------------------------------------------------------
-- srcF of an ap2c child (dtag = dgAp2c).  Both children kept opaque.

srcChildArgL : Term -> Term
srcChildArgL p = ap1 srcL (Hs.opkg p)
srcChildArgR : Term -> Term
srcChildArgR p = ap1 srcR (Hs.opkg p)

srcF_ap2c_himp : (p : Term) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 2))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (eqF (ap1 srcF p) (tmAp2 (funP p) (srcChildArgL p) (srcChildArgR p)))))
srcF_ap2c_himp p =
  let Hd2 = eqF (ap1 Fst p) (natCode 2)
      htag = eqF (ap1 Fst (dtag p)) dgAp2c
      HH = Cnj Hd2 htag
      opk = Hs.opkg p
      ne : Deriv (imp HH (neg (eqF p O)))
      ne = compI (cnjL Hd2 htag) (ne_from_head2 p)
      rhs = tmAp2 (funP p) (ap1 srcL opk) (ap1 srcR opk)
      rawCell = tmAp2 (ap1 bunF opk) (ap1 srcL opk) (ap1 srcR opk)
      op_tag_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 get_tag opk) (ap1 Fst p)))
      op_tag_ne = impEqTrans (ap1 get_tag opk) (ap1 Fst (ap1 get_newK opk)) (ap1 Fst p)
                    (impLift (compose1U_eq Fst get_newK opk)) (impCong1 Fst (ap1 get_newK opk) p (Hs.op_newK_imp p))
      gtag : Deriv (imp HH (eqF (ap1 get_tag opk) (natCode 2)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 2) (compI ne op_tag_ne) (cnjL Hd2 htag)
      e1 : Deriv (imp HH (eqF (ap1 srcF p) (ap1 srcStepU opk)))
      e1 = compI ne (Hs.opUnfold_imp p)
      t1O : Deriv (imp HH (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
      t1O = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk) (ap2 natEqF (ap1 get_tag opk) (natCode 1)) O
              (impLift (ruleTrans (ax_C natEqF get_tag (constN 1) opk) (congR natEqF (ap1 get_tag opk) (constN_eq 1 opk))))
              (impEqTrans (ap2 natEqF (ap1 get_tag opk) (natCode 1)) (ap2 natEqF (natCode 2) (natCode 1)) O
                (impCongL natEqF (ap1 get_tag opk) (natCode 2) (natCode 1) gtag)
                (impLift (natEqF_at_neq 2 1 (wn 2 1 (\ ())))))
      e2 : Deriv (imp HH (eqF (ap1 srcStepU opk) (ap1 cellNodeSrc opk)))
      e2 = fork_false_to_snd_imp HH tmOF cellNodeSrc (C natEqF get_tag (constN 1)) opk t1O
      derTag_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p))))
      derTag_ne = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (ap1 nIdx opk)) (ap1 Fst (dtag p))
                    (impLift (compose1U_eq Fst nIdx opk)) (impCong1 Fst (ap1 nIdx opk) (dtag p) (Hs.op_nIdx_imp p))
      derTagH : Deriv (imp HH (eqF (ap1 derTagIdx opk) (natCode 2)))
      derTagH = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) (natCode 2) (compI ne derTag_ne) (cnjR Hd2 htag)
      skip1 : Deriv (imp HH (eqF (ap1 cellNodeSrc opk) (ap1 src_l2 opk)))
      skip1 = fork_false_to_snd_imp HH ap1cCell src_l2 (testTag 1) opk
                (natEqSkip_imp HH derTagIdx 2 1 opk (wn 2 1 (\ ())) derTagH)
      fire2 : Deriv (imp HH (eqF (ap1 src_l2 opk) (ap1 ap2cCell opk)))
      fire2 = fork_true_to_fst_imp HH ap2cCell src_l3 (testTag 2) opk (natEqFire_imp HH derTagIdx 2 opk derTagH)
      e3 : Deriv (imp HH (eqF (ap1 cellNodeSrc opk) (ap1 ap2cCell opk)))
      e3 = impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 ap2cCell opk) skip1 fire2
      cellRaw : Deriv (eqF (ap1 ap2cCell opk) rawCell)
      cellRaw = mkAp2_val bunF srcL srcR opk (ap1 bunF opk) (ap1 srcL opk) (ap1 srcR opk)
                  (axRefl (ap1 bunF opk)) (axRefl (ap1 srcL opk)) (axRefl (ap1 srcR opk))
      recBun_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 derBunIdx opk) (funP p)))
      recBun_ne = impEqTrans (ap1 derBunIdx opk) (ap1 Snd (ap1 nIdx opk)) (funP p)
                    (impLift (compose1U_eq Snd nIdx opk)) (impCong1 Snd (ap1 nIdx opk) (dtag p) (Hs.op_nIdx_imp p))
      cellRewrite : Deriv (imp HH (eqF rawCell rhs))
      cellRewrite = compI (compI ne recBun_ne)
                      (impCongR Pair (ap2 Pair (ap1 bunF opk) (ap2 Pair (ap1 srcL opk) (ap1 srcR opk)))
                                     (ap2 Pair (funP p) (ap2 Pair (ap1 srcL opk) (ap1 srcR opk))) tgAp2
                        (impCongL Pair (ap1 bunF opk) (funP p) (ap2 Pair (ap1 srcL opk) (ap1 srcR opk))
                          (identP (eqF (ap1 bunF opk) (funP p)))))
      e4 : Deriv (imp HH (eqF (ap1 ap2cCell opk) rhs))
      e4 = impEqTrans (ap1 ap2cCell opk) rawCell rhs (liftP HH cellRaw) cellRewrite
      chain : Deriv (imp HH (eqF (ap1 srcF p) rhs))
      chain = impEqTrans (ap1 srcF p) (ap1 srcStepU opk) rhs e1
                (impEqTrans (ap1 srcStepU opk) (ap1 cellNodeSrc opk) rhs e2
                  (impEqTrans (ap1 cellNodeSrc opk) (ap1 ap2cCell opk) rhs e3 e4))
  in cnjCurry chain

------------------------------------------------------------------------
-- Shared cores for the redex src-head lifts (factor the prefix).

private
  -- srcF p = cellNodeSrc opk  over  HH = Cnj (Fst p=2) htag  (opUnfold + leaf-skip).
  toCellNode : (p : Term) (htag : Formula) ->
    Deriv (imp (Cnj (eqF (ap1 Fst p) (natCode 2)) htag) (eqF (ap1 srcF p) (ap1 cellNodeSrc (Hs.opkg p))))
  toCellNode p htag =
    let Hd2 = eqF (ap1 Fst p) (natCode 2)
        HH = Cnj Hd2 htag
        opk = Hs.opkg p
        ne = compI (cnjL Hd2 htag) (ne_from_head2 p)
        op_tag_ne = impEqTrans (ap1 get_tag opk) (ap1 Fst (ap1 get_newK opk)) (ap1 Fst p)
                      (impLift (compose1U_eq Fst get_newK opk)) (impCong1 Fst (ap1 get_newK opk) p (Hs.op_newK_imp p))
        gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 2) (compI ne op_tag_ne) (cnjL Hd2 htag)
        e1 = compI ne (Hs.opUnfold_imp p)
        t1O = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk) (ap2 natEqF (ap1 get_tag opk) (natCode 1)) O
                (impLift (ruleTrans (ax_C natEqF get_tag (constN 1) opk) (congR natEqF (ap1 get_tag opk) (constN_eq 1 opk))))
                (impEqTrans (ap2 natEqF (ap1 get_tag opk) (natCode 1)) (ap2 natEqF (natCode 2) (natCode 1)) O
                  (impCongL natEqF (ap1 get_tag opk) (natCode 2) (natCode 1) gtag)
                  (impLift (natEqF_at_neq 2 1 (wn 2 1 (\ ())))))
        e2 = fork_false_to_snd_imp HH tmOF cellNodeSrc (C natEqF get_tag (constN 1)) opk t1O
    in impEqTrans (ap1 srcF p) (ap1 srcStepU opk) (ap1 cellNodeSrc opk) e1 e2

  -- derTagIdx opk = natCode k  over  HH = Cnj (Fst p=2) (Fst(dtag p)=natCode k).
  derTagAt : (p : Term) (k : Nat) ->
    Deriv (imp (Cnj (eqF (ap1 Fst p) (natCode 2)) (eqF (ap1 Fst (dtag p)) (natCode k)))
               (eqF (ap1 derTagIdx (Hs.opkg p)) (natCode k)))
  derTagAt p k =
    let Hd2 = eqF (ap1 Fst p) (natCode 2)
        htag = eqF (ap1 Fst (dtag p)) (natCode k)
        opk = Hs.opkg p
        ne = compI (cnjL Hd2 htag) (ne_from_head2 p)
        derTag_ne = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (ap1 nIdx opk)) (ap1 Fst (dtag p))
                      (impLift (compose1U_eq Fst nIdx opk)) (impCong1 Fst (ap1 nIdx opk) (dtag p) (Hs.op_nIdx_imp p))
    in impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) (natCode k) (compI ne derTag_ne) (cnjR Hd2 htag)

-- srcF of an rO (o-redex) child:  srcF p = tmAp1 cZero (srcChildArg p)  (cZero concrete).
srcF_rO_himp : (p : Term) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 2))
             (imp (eqF (ap1 Fst (dtag p)) dgRo) (eqF (ap1 srcF p) (tmAp1 cZero (srcChildArg p)))))
srcF_rO_himp p =
  let htag = eqF (ap1 Fst (dtag p)) dgRo
      HH = Cnj (eqF (ap1 Fst p) (natCode 2)) htag
      opk = Hs.opkg p
      rhs = tmAp1 cZero (ap1 srcL opk)
      derTagH = derTagAt p 3
      skip1 = fork_false_to_snd_imp HH ap1cCell src_l2 (testTag 1) opk (natEqSkip_imp HH derTagIdx 3 1 opk (wn 3 1 (\ ())) derTagH)
      skip2 = fork_false_to_snd_imp HH ap2cCell src_l3 (testTag 2) opk (natEqSkip_imp HH derTagIdx 3 2 opk (wn 3 2 (\ ())) derTagH)
      fire3 = fork_true_to_fst_imp HH rOCell src_l4 (testTag 3) opk (natEqFire_imp HH derTagIdx 3 opk derTagH)
      e3 = impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rOCell opk) skip1
             (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rOCell opk) skip2 fire3)
      cellVal = mkAp1_val cZeroF srcL opk cZero (ap1 srcL opk) (cZeroF_val opk) (axRefl (ap1 srcL opk))
      e4 = impEqTrans (ap1 cellNodeSrc opk) (ap1 rOCell opk) rhs e3 (liftP HH cellVal)
  in cnjCurry (impEqTrans (ap1 srcF p) (ap1 cellNodeSrc opk) rhs (toCellNode p htag) e4)

-- srcF of a u-redex child:  srcF p = tmAp1 cId (srcChildArg p).
srcF_rU_himp : (p : Term) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 2))
             (imp (eqF (ap1 Fst (dtag p)) dgRu) (eqF (ap1 srcF p) (tmAp1 cId (srcChildArg p)))))
srcF_rU_himp p =
  let htag = eqF (ap1 Fst (dtag p)) dgRu
      HH = Cnj (eqF (ap1 Fst p) (natCode 2)) htag
      opk = Hs.opkg p
      rhs = tmAp1 cId (ap1 srcL opk)
      derTagH = derTagAt p 4
      skip1 = fork_false_to_snd_imp HH ap1cCell src_l2 (testTag 1) opk (natEqSkip_imp HH derTagIdx 4 1 opk (wn 4 1 (\ ())) derTagH)
      skip2 = fork_false_to_snd_imp HH ap2cCell src_l3 (testTag 2) opk (natEqSkip_imp HH derTagIdx 4 2 opk (wn 4 2 (\ ())) derTagH)
      skip3 = fork_false_to_snd_imp HH rOCell src_l4 (testTag 3) opk (natEqSkip_imp HH derTagIdx 4 3 opk (wn 4 3 (\ ())) derTagH)
      fire4 = fork_true_to_fst_imp HH rUCell src_l5 (testTag 4) opk (natEqFire_imp HH derTagIdx 4 opk derTagH)
      e3 = impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rUCell opk) skip1
             (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rUCell opk) skip2
               (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rUCell opk) skip3 fire4))
      cellVal = mkAp1_val cIdF srcL opk cId (ap1 srcL opk) (cIdF_val opk) (axRefl (ap1 srcL opk))
      e4 = impEqTrans (ap1 cellNodeSrc opk) (ap1 rUCell opk) rhs e3 (liftP HH cellVal)
  in cnjCurry (impEqTrans (ap1 srcF p) (ap1 cellNodeSrc opk) rhs (toCellNode p htag) e4)

-- srcF of a v-redex child:  srcF p = tmAp2 cProj (srcChildArgL p) (srcChildArgR p).
srcF_rV_himp : (p : Term) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 2))
             (imp (eqF (ap1 Fst (dtag p)) dgRv) (eqF (ap1 srcF p) (tmAp2 cProj (srcChildArgL p) (srcChildArgR p)))))
srcF_rV_himp p =
  let htag = eqF (ap1 Fst (dtag p)) dgRv
      HH = Cnj (eqF (ap1 Fst p) (natCode 2)) htag
      opk = Hs.opkg p
      rhs = tmAp2 cProj (ap1 srcL opk) (ap1 srcR opk)
      derTagH = derTagAt p 5
      skip1 = fork_false_to_snd_imp HH ap1cCell src_l2 (testTag 1) opk (natEqSkip_imp HH derTagIdx 5 1 opk (wn 5 1 (\ ())) derTagH)
      skip2 = fork_false_to_snd_imp HH ap2cCell src_l3 (testTag 2) opk (natEqSkip_imp HH derTagIdx 5 2 opk (wn 5 2 (\ ())) derTagH)
      skip3 = fork_false_to_snd_imp HH rOCell src_l4 (testTag 3) opk (natEqSkip_imp HH derTagIdx 5 3 opk (wn 5 3 (\ ())) derTagH)
      skip4 = fork_false_to_snd_imp HH rUCell src_l5 (testTag 4) opk (natEqSkip_imp HH derTagIdx 5 4 opk (wn 5 4 (\ ())) derTagH)
      fire5 = fork_true_to_fst_imp HH rVCell src_l6 (testTag 5) opk (natEqFire_imp HH derTagIdx 5 opk derTagH)
      e3 = impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rVCell opk) skip1
             (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rVCell opk) skip2
               (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rVCell opk) skip3
                 (impEqTrans (ap1 src_l4 opk) (ap1 src_l5 opk) (ap1 rVCell opk) skip4 fire5)))
      cellVal = mkAp2_val cProjF srcL srcR opk cProj (ap1 srcL opk) (ap1 srcR opk) (cProjF_val opk) (axRefl (ap1 srcL opk)) (axRefl (ap1 srcR opk))
      e4 = impEqTrans (ap1 cellNodeSrc opk) (ap1 rVCell opk) rhs e3 (liftP HH cellVal)
  in cnjCurry (impEqTrans (ap1 srcF p) (ap1 cellNodeSrc opk) rhs (toCellNode p htag) e4)
