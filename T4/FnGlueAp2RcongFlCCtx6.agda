{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnGlueAp2RcongFlCCtx6 -- the ap2-flN-Rcong leaf (fun-head 8 = R, but the
-- recursion child develops to a STUCK R -- neither Rb nor Rs -- so a pure
-- congruence) in the FULL depth-6 CtxKit context the inner mb caseElim delivers:
-- [neg-mbfunh3, neg-mbhead0, funh8, flag(flN), tag(=2), PA].  Node stays flN;
-- mcontract folds through tmAp2 and BOTH child triangles are threaded (tmAp2c2Arg6).
-- The RHS's erased R-node is NOT a redex (redexErasedRcongO via the erase-projection
-- bridges + shape caseElim), so markAll flags flN too.  Binary-node R analog of
-- T4.FnGlueAp2CongCtx5.
--
--   leaf_ap2_flC_Rcong :
--     imp (neg X_mbf3) (imp (neg X_mbh0) (imp X8 (imp Xflag (imp X2 (imp PA (Q sk))))))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnGlueAp2RcongFlCCtx6 where

open import T4.Base

open import T4.PrCodeObj using ( tmAp2 ; tgAp2 )
open import T4.FnMark using ( mAp2 ; flN ; flC ; mFun ; mMa ; mMb )
open import T4.FnMcontract using ( mcontract ; mcontract_ap2_cong )
open import T4.FnErase using ( erase )
open import T4.FnResidual using ( residual )
open import T4.FnMarkAll using ( markAll ; markAll_ap2 )
open import T4.FnTerm using ( redexHere )
open import T4.FnTriStep using ( Q )
open import T4.FnWfMarked2 using ( wfMarkedF )
open import T4.FnQCheck using ( qcheckFn )

open import T4.FnResidualOpaque2Imp using ( residual_op_ap2_flC_Rcong_neg_chain )
open import T4.FnFlcExtract2 using ( flC_extract_chain_ap2 )
open import T4.FnEraseOpaqueImp using ( erase_op_ap2_imp )
open import T4.FnGlueAp2RcongRedex using ( redexErasedRcongO )
open import T4.FnWfChildImp2 using ( wfF_child_ap2_ma_imp ; wfF_child_ap2_mb_imp )
open import T4.FnNodeNe using ( FstO )

open import T4.FnQCheckProj using ( PhiKFn ; QofChildFn )
open import T4.FnEraseOpaque using ( mMa_bound ; mMb_bound )
open import T4.BoundedConj using ( bigC )
open import T4.DescSnd using ( posNeqO )
open import BRA3.Church using ( sigma ; sub ; predecessor ; T_p_S_v0 )
open import BRA3.ChurchLeq using ( leq ; T76 )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import T4.SigmaZeroN using ( sigmaZeroL ; sigmaZeroR )
open import BRA3.Contrapositive using ( compI ; identP )
open import BRA3.Classical using ( axContrapos )
open import BRA3.Logic using ( eqSymImp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 )
open import T4.CtxKit
  using ( lift4 ; ap4c ; lift5 ; ap5c
        ; lift6 ; get6a ; get6b ; get6c ; get6d ; get6e ; get6f ; ap6c ; trans6c )

------------------------------------------------------------------------
-- Shared codes  sk = s (var 0)  and the depth-6 context
-- [Ga,Gb,Gc,Gd,Ge,Gf] = [neg-mbfunh3, neg-mbhead0, funh8, flag(flN), tag, PA].

sk : Term
sk = ap1 s (var 0)

g : Term
g = mFun sk

ma : Term
ma = mMa sk

mb : Term
mb = mMb sk

bigK : Term
bigK = ap2 (bigC qcheckFn) O (var 0)

Aform : Formula
Aform = eqF (ap1 wfMarkedF sk) O

Ga : Formula                                   -- neg mbfunhead 3
Ga = neg (eqF (ap1 Fst (ap1 Fst (ap1 Snd (ap1 Snd (mMb sk))))) (natCode 3))

Gb : Formula                                   -- neg mbhead 0
Gb = neg (eqF (ap1 Fst (mMb sk)) (natCode 0))

Gc : Formula                                   -- funhead 8
Gc = eqF (ap1 Fst (mFun sk)) (natCode 8)

Gd : Formula                                   -- neg flN
Gd = neg (eqF (ap1 Fst (ap1 Snd sk)) flN)

Ge : Formula                                   -- tag 2
Ge = eqF (ap1 Fst sk) (natCode 2)

Gf : Formula                                   -- PA
Gf = eqF (ap2 sigma bigK (ap1 wfMarkedF sk)) O

ne_sk : Deriv (neg (eqF sk O))
ne_sk = posNeqO sk (mp (ruleInst2 0 O 1 (var 0) refl T78) (ruleInst 0 (var 0) T76))

------------------------------------------------------------------------
-- Depth-6 helpers over [Ga..Gf].

c6 : (h : Fun1) (a b : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF a b))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF (ap1 h a) (ap1 h b))))))))
c6 h a b e = ap6c (lift6 Ga Gb Gc Gd Ge Gf (ax_eqCong1 h a b)) e

cR6 : (h : Fun2) (a b c : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF a b))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF (ap2 h c a) (ap2 h c b))))))))
cR6 h a b c e = ap6c (lift6 Ga Gb Gc Gd Ge Gf (ax_eqCongR h a b c)) e

cL6 : (h : Fun2) (a b c : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF a b))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF (ap2 h a c) (ap2 h b c))))))))
cL6 h a b c e = ap6c (lift6 Ga Gb Gc Gd Ge Gf (ax_eqCongL h a b c)) e

sym6 : (a b : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF a b))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF b a)))))))
sym6 a b e = ap6c (lift6 Ga Gb Gc Gd Ge Gf (eqSymImp a b)) e

emb6F : {X : Formula} -> Deriv (imp Gf X) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf X))))))
emb6F p = ap6c (lift6 Ga Gb Gc Gd Ge Gf p) (get6f Ga Gb Gc Gd Ge Gf)

emb6E : {X : Formula} -> Deriv (imp Ge X) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf X))))))
emb6E p = ap6c (lift6 Ga Gb Gc Gd Ge Gf p) (get6e Ga Gb Gc Gd Ge Gf)

-- weaken a depth-5 [Ga..Ge] proof to depth-6 (add Gf innermost).
wk56 : {X : Formula} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge X))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf X))))))
wk56 {X} p = ap5c (lift5 Ga Gb Gc Gd Ge (axK X Gf)) p

-- depth-6 congruence on BOTH tmAp2 arguments (threads both child triangles).
tmAp2c2Arg6 : {A A' B B' : Term} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF A A'))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF B B'))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
          (eqF (tmAp2 g A B) (tmAp2 g A' B'))))))))
tmAp2c2Arg6 {A} {A'} {B} {B'} ea eb =
  cR6 Pair (ap2 Pair g (ap2 Pair A B)) (ap2 Pair g (ap2 Pair A' B')) tgAp2
    (cR6 Pair (ap2 Pair A B) (ap2 Pair A' B') g
      (trans6c (ap2 Pair A B) (ap2 Pair A' B) (ap2 Pair A' B')
         (cL6 Pair A A' B ea)
         (cR6 Pair B B' A' eb)))

-- depth-6 flag rewrite on a marked ap2 node.
mAp2cFlag6 : (gg maa mbb : Term) {fl fl' : Term} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF fl fl'))))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
          (eqF (mAp2 fl gg maa mbb) (mAp2 fl' gg maa mbb))))))))
mAp2cFlag6 gg maa mbb {fl} {fl'} e =
  cR6 Pair (ap2 Pair fl (ap2 Pair gg (ap2 Pair maa mbb)))
           (ap2 Pair fl' (ap2 Pair gg (ap2 Pair maa mbb))) tgAp2
    (cL6 Pair fl fl' (ap2 Pair gg (ap2 Pair maa mbb)) e)

------------------------------------------------------------------------
-- neg (Fst c = 0)  =>  neg (c = O)  (imp-form; via Fst O = natCode 0).

ne_from_neg_head0 : (c : Term) ->
  Deriv (imp (neg (eqF (ap1 Fst c) (natCode 0))) (neg (eqF c O)))
ne_from_neg_head0 c =
  mp (axContrapos (eqF c O) (eqF (ap1 Fst c) (natCode 0)))
     (impEqTrans (ap1 Fst c) (ap1 Fst O) (natCode 0)
        (impCong1 Fst c O (identP (eqF c O)))
        (impLift {eqF c O} FstO))

------------------------------------------------------------------------
-- Child bounds + child triangles Q (mMa sk) / Q (mMb sk) (over PA = Gf).

rebound : (c : Term) ->
  Deriv (leq c (ap1 predecessor sk)) -> Deriv (leq c (var 0))
rebound c d =
  ruleTrans (congR sub c (ruleSym (ruleInst 0 (var 0) T_p_S_v0))) d

qChildA : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (Q ma)))))))
qChildA =
  let pa2phik : Deriv (imp Gf PhiKFn)
      pa2phik = sigmaZeroL bigK (ap1 wfMarkedF sk)
      pa2a : Deriv (imp Gf Aform)
      pa2a = sigmaZeroR bigK (ap1 wfMarkedF sk)
      childT : Deriv (imp Gf (imp (eqF (ap1 wfMarkedF ma) O) (Q ma)))
      childT = compI pa2phik (QofChildFn ma (rebound ma (mMa_bound sk ne_sk)))
      wcI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
              (imp Aform (eqF (ap1 wfMarkedF ma) O))))))))
      wcI = emb6E (wfF_child_ap2_ma_imp Ge sk ne_sk (identP Ge))
      aI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Aform))))))
      aI = emb6F pa2a
      childvalid : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF (ap1 wfMarkedF ma) O)))))))
      childvalid = ap6c wcI aI
  in ap6c (emb6F childT) childvalid

qChildB : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (Q mb)))))))
qChildB =
  let pa2phik : Deriv (imp Gf PhiKFn)
      pa2phik = sigmaZeroL bigK (ap1 wfMarkedF sk)
      pa2a : Deriv (imp Gf Aform)
      pa2a = sigmaZeroR bigK (ap1 wfMarkedF sk)
      childT : Deriv (imp Gf (imp (eqF (ap1 wfMarkedF mb) O) (Q mb)))
      childT = compI pa2phik (QofChildFn mb (rebound mb (mMb_bound sk ne_sk)))
      wcI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
              (imp Aform (eqF (ap1 wfMarkedF mb) O))))))))
      wcI = emb6E (wfF_child_ap2_mb_imp Ge sk ne_sk (identP Ge))
      aI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Aform))))))
      aI = emb6F pa2a
      childvalid : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF (ap1 wfMarkedF mb) O)))))))
      childvalid = ap6c wcI aI
  in ap6c (emb6F childT) childvalid

------------------------------------------------------------------------
-- The erased R-node is not a redex, in the depth-6 context (redexErasedRcongO
-- fed NE from Gb, F8 = Gc, NF = Ga).

redexErasedI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
                 (eqF (ap1 redexHere (tmAp2 g (ap1 erase ma) (ap1 erase mb))) O)))))))
redexErasedI =
  let neI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (neg (eqF mb O))))))))
      neI = ap6c (lift6 Ga Gb Gc Gd Ge Gf (ne_from_neg_head0 mb)) (get6b Ga Gb Gc Gd Ge Gf)
      f8I : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Gc))))))
      f8I = get6c Ga Gb Gc Gd Ge Gf
      nfI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Ga))))))
      nfI = get6a Ga Gb Gc Gd Ge Gf
  in ap6c (ap6c (ap6c (lift6 Ga Gb Gc Gd Ge Gf (redexErasedRcongO g ma mb)) neI) f8I) nfI

------------------------------------------------------------------------
-- DERIVED flC flag (via flC_extract_chain_ap2 fed tag = Ge, neg-flN = Gd, Aform).

avalI6 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Aform))))))
avalI6 = emb6F (sigmaZeroR bigK (ap1 wfMarkedF sk))

flcI6 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
          (eqF (ap1 Fst (ap1 Snd sk)) flC)))))))
flcI6 =
  ap6c (ap6c (ap6c (lift6 Ga Gb Gc Gd Ge Gf (flC_extract_chain_ap2 sk ne_sk))
             (get6e Ga Gb Gc Gd Ge Gf)) (get6d Ga Gb Gc Gd Ge Gf)) avalI6

------------------------------------------------------------------------
-- The leaf.

leaf_ap2_flC_Rcong :
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (Q sk)))))))
leaf_ap2_flC_Rcong =
  let residE : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
                 (eqF (ap1 residual sk)
                      (mAp2 flN g (ap1 residual ma) (ap1 residual mb)))))))))
      residE = ap6c (ap6c (ap6c (ap6c (ap6c
                 (lift6 Ga Gb Gc Gd Ge Gf (residual_op_ap2_flC_Rcong_neg_chain sk ne_sk))
                 (get6e Ga Gb Gc Gd Ge Gf)) flcI6) (get6c Ga Gb Gc Gd Ge Gf))
                 (get6b Ga Gb Gc Gd Ge Gf)) (get6a Ga Gb Gc Gd Ge Gf)
      lhsI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
               (eqF (ap1 mcontract (ap1 residual sk))
                    (tmAp2 g (ap1 mcontract (ap1 residual ma))
                             (ap1 mcontract (ap1 residual mb))))))))))
      lhsI = trans6c (ap1 mcontract (ap1 residual sk))
               (ap1 mcontract (mAp2 flN g (ap1 residual ma) (ap1 residual mb)))
               (tmAp2 g (ap1 mcontract (ap1 residual ma)) (ap1 mcontract (ap1 residual mb)))
               (c6 mcontract (ap1 residual sk)
                  (mAp2 flN g (ap1 residual ma) (ap1 residual mb)) residE)
               (lift6 Ga Gb Gc Gd Ge Gf (mcontract_ap2_cong g (ap1 residual ma) (ap1 residual mb)))
      eraseE : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
                 (eqF (ap1 erase sk) (tmAp2 g (ap1 erase ma) (ap1 erase mb)))))))))
      eraseE = emb6E (erase_op_ap2_imp Ge sk ne_sk (identP Ge))
      rhsFlagI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
                   (eqF (ap1 markAll (ap1 erase sk))
                        (mAp2 flN g (ap1 markAll (ap1 erase ma))
                                    (ap1 markAll (ap1 erase mb))))))))))
      rhsFlagI = trans6c (ap1 markAll (ap1 erase sk))
                   (ap1 markAll (tmAp2 g (ap1 erase ma) (ap1 erase mb)))
                   (mAp2 flN g (ap1 markAll (ap1 erase ma)) (ap1 markAll (ap1 erase mb)))
                   (c6 markAll (ap1 erase sk) (tmAp2 g (ap1 erase ma) (ap1 erase mb)) eraseE)
                   (trans6c (ap1 markAll (tmAp2 g (ap1 erase ma) (ap1 erase mb)))
                      (mAp2 (ap1 redexHere (tmAp2 g (ap1 erase ma) (ap1 erase mb))) g
                            (ap1 markAll (ap1 erase ma)) (ap1 markAll (ap1 erase mb)))
                      (mAp2 flN g (ap1 markAll (ap1 erase ma)) (ap1 markAll (ap1 erase mb)))
                      (lift6 Ga Gb Gc Gd Ge Gf (markAll_ap2 g (ap1 erase ma) (ap1 erase mb)))
                      (mAp2cFlag6 g (ap1 markAll (ap1 erase ma)) (ap1 markAll (ap1 erase mb)) redexErasedI))
      rhsI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf
               (eqF (ap1 mcontract (ap1 markAll (ap1 erase sk)))
                    (tmAp2 g (ap1 mcontract (ap1 markAll (ap1 erase ma)))
                             (ap1 mcontract (ap1 markAll (ap1 erase mb)))))))))))
      rhsI = trans6c (ap1 mcontract (ap1 markAll (ap1 erase sk)))
               (ap1 mcontract (mAp2 flN g (ap1 markAll (ap1 erase ma))
                                          (ap1 markAll (ap1 erase mb))))
               (tmAp2 g (ap1 mcontract (ap1 markAll (ap1 erase ma)))
                        (ap1 mcontract (ap1 markAll (ap1 erase mb))))
               (c6 mcontract (ap1 markAll (ap1 erase sk))
                  (mAp2 flN g (ap1 markAll (ap1 erase ma)) (ap1 markAll (ap1 erase mb))) rhsFlagI)
               (lift6 Ga Gb Gc Gd Ge Gf
                  (mcontract_ap2_cong g (ap1 markAll (ap1 erase ma)) (ap1 markAll (ap1 erase mb))))
  in trans6c (ap1 mcontract (ap1 residual sk))
       (tmAp2 g (ap1 mcontract (ap1 residual ma)) (ap1 mcontract (ap1 residual mb)))
       (ap1 mcontract (ap1 markAll (ap1 erase sk)))
       lhsI
       (trans6c (tmAp2 g (ap1 mcontract (ap1 residual ma)) (ap1 mcontract (ap1 residual mb)))
          (tmAp2 g (ap1 mcontract (ap1 markAll (ap1 erase ma)))
                   (ap1 mcontract (ap1 markAll (ap1 erase mb))))
          (ap1 mcontract (ap1 markAll (ap1 erase sk)))
          (tmAp2c2Arg6 qChildA qChildB)
          (sym6 (ap1 mcontract (ap1 markAll (ap1 erase sk)))
                (tmAp2 g (ap1 mcontract (ap1 markAll (ap1 erase ma)))
                         (ap1 mcontract (ap1 markAll (ap1 erase mb)))) rhsI))
