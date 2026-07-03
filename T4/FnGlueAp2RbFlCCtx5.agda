{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnGlueAp2RbFlCCtx5 -- the ap2-flC-Rb leaf (flag flC, fun-head 8 = R, mb-head
-- 0 = base case Rb) in the depth-5 context the inner dispatch delivers for the flC
-- branch: [funhead(=8), mbhead(=0), neg-flN, tag(=2), PA].  The flag flC is DERIVED
-- in-context via T4.FnFlcExtract2.flC_extract_chain_ap2, then fed to the ap2 flC-Rb
-- residual chain (residual d = mAp1 flN g0 (residual ma) directly, NO mAp2 node).
-- The recursion child mMb sk is reconstructed (= mO) as in the flN-Rb leaf; the RHS
-- (markAll o erase) side is flag-independent and reuses the flN-Rb twins verbatim.
--
--   leaf_ap2_flC_Rb :
--     imp X8 (imp Xmb0 (imp (neg Xflag) (imp X2 (imp PA (Q sk)))))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnGlueAp2RbFlCCtx5 where

open import T4.Base

open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; tgAp1 ; tgAp2 )
open import T4.FnMark using ( mAp1 ; mAp2 ; flN ; flC ; mFun ; mMa ; mMb ) renaming ( mO to mOt )
open import T4.FnMcontract using ( mcontract ; mcontract_mO ; mcontract_ap1_cong )
open import T4.FnErase using ( erase ; erase_mO )
open import T4.FnResidual using ( residual ; residual_mO )
open import T4.FnMarkAll using ( markAll ; markAll_mO ; markAll_ap2 )
open import T4.FnTerm using ( redexHere )
open import T4.FnTriStep using ( Q )
open import T4.FnWfMarked2 using ( wfMarkedF )
open import T4.FnQCheck using ( qcheckFn )

open import T4.FnResidualOpaque2Imp using ( residual_op_ap2_flC_Rb_chain )
open import T4.FnFlcExtract2 using ( flC_extract_chain_ap2 )
open import T4.FnEraseOpaqueImp using ( erase_op_ap2_imp )
open import T4.FnGlueAp2RbHelpers using ( mcontract_ap2_Rb_imp ; redex_ap2_Rb_imp )
open import T4.FnWfChildImp2 using ( wfF_child_ap2_ma_imp ; wfF_child_ap2_mb_imp )
open import T4.FnReconMb using ( reconTag0 )

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
open import BRA3.Logic using ( eqSymImp )
open import T4.DevF using ( pi_O_O )
open import T4.Thm12.ImpHelpers using ( impLift )
open import T4.CtxKit
  using ( lift4 ; ap4c
        ; lift5 ; get5a ; get5b ; get5c ; get5d ; get5e ; ap5c ; trans5c )

------------------------------------------------------------------------
-- Shared codes  sk = s (var 0)  and the depth-5 context
-- [Ga,Gb,Gc,Gd,Ge] = [funhead(=8), mbhead(=0), neg-flN, tag(=2), PA].

sk : Term
sk = ap1 s (var 0)

g : Term
g = mFun sk

ma : Term
ma = mMa sk

mb : Term
mb = mMb sk

g0 : Term
g0 = ap1 Fst (ap1 Snd g)

bigK : Term
bigK = ap2 (bigC qcheckFn) O (var 0)

Aform : Formula
Aform = eqF (ap1 wfMarkedF sk) O

Ga : Formula                                   -- funhead 8
Ga = eqF (ap1 Fst (mFun sk)) (natCode 8)

Gb : Formula                                   -- mbhead 0
Gb = eqF (ap1 Fst (mMb sk)) (natCode 0)

Gc : Formula                                   -- neg flN
Gc = neg (eqF (ap1 Fst (ap1 Snd sk)) flN)

Gd : Formula                                   -- tag 2
Gd = eqF (ap1 Fst sk) (natCode 2)

Ge : Formula                                   -- PA
Ge = eqF (ap2 sigma bigK (ap1 wfMarkedF sk)) O

ne_sk : Deriv (neg (eqF sk O))
ne_sk = posNeqO sk (mp (ruleInst2 0 O 1 (var 0) refl T78) (ruleInst 0 (var 0) T76))

------------------------------------------------------------------------
-- Depth-5 helpers over [Ga,Gb,Gc,Gd,Ge].

c5 : (h : Fun1) (a b : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF a b)))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF (ap1 h a) (ap1 h b)))))))
c5 h a b e = ap5c (lift5 Ga Gb Gc Gd Ge (ax_eqCong1 h a b)) e

cR5 : (h : Fun2) (a b c : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF a b)))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF (ap2 h c a) (ap2 h c b)))))))
cR5 h a b c e = ap5c (lift5 Ga Gb Gc Gd Ge (ax_eqCongR h a b c)) e

sym5 : (a b : Term) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF a b)))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF b a))))))
sym5 a b e = ap5c (lift5 Ga Gb Gc Gd Ge (eqSymImp a b)) e

emb5A : {X : Formula} -> Deriv (imp Ga X) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge X)))))
emb5A p = ap5c (lift5 Ga Gb Gc Gd Ge p) (get5a Ga Gb Gc Gd Ge)

emb5D : {X : Formula} -> Deriv (imp Gd X) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge X)))))
emb5D p = ap5c (lift5 Ga Gb Gc Gd Ge p) (get5d Ga Gb Gc Gd Ge)

emb5E : {X : Formula} -> Deriv (imp Ge X) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge X)))))
emb5E p = ap5c (lift5 Ga Gb Gc Gd Ge p) (get5e Ga Gb Gc Gd Ge)

-- projections of the ambient facts.
funhI5 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Ga)))))
funhI5 = get5a Ga Gb Gc Gd Ge

mbhI5 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Gb)))))
mbhI5 = get5b Ga Gb Gc Gd Ge

nfI5 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Gc)))))
nfI5 = get5c Ga Gb Gc Gd Ge

tagI5 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Gd)))))
tagI5 = get5d Ga Gb Gc Gd Ge

avalI5 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Aform)))))
avalI5 = emb5E (sigmaZeroR bigK (ap1 wfMarkedF sk))

flcI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF (ap1 Fst (ap1 Snd sk)) flC))))))
flcI =
  ap5c (ap5c (ap5c (lift5 Ga Gb Gc Gd Ge (flC_extract_chain_ap2 sk ne_sk)) tagI5) nfI5) avalI5

-- weaken a depth-4 [Ga,Gb,Gc,Gd] proof to depth-5.
wk45 : {X : Formula} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd X)))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge X)))))
wk45 {X} p = ap4c (lift4 Ga Gb Gc Gd (axK X Ge)) p

-- depth-5 congruence on the mb child (3rd arg) of a marked ap2 node.
mAp2cB5 : (fl gg aa : Term) {b b' : Term} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF b b')))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
          (eqF (mAp2 fl gg aa b) (mAp2 fl gg aa b')))))))
mAp2cB5 fl gg aa {b} {b'} e =
  cR5 Pair (ap2 Pair fl (ap2 Pair gg (ap2 Pair aa b)))
           (ap2 Pair fl (ap2 Pair gg (ap2 Pair aa b'))) tgAp2
    (cR5 Pair (ap2 Pair gg (ap2 Pair aa b)) (ap2 Pair gg (ap2 Pair aa b')) fl
      (cR5 Pair (ap2 Pair aa b) (ap2 Pair aa b') gg
        (cR5 Pair b b' aa e)))

-- depth-5 flag rewrite on a marked ap2 node.
mAp2cFlag5 : (gg maa mbb : Term) {fl fl' : Term} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF fl fl')))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
          (eqF (mAp2 fl gg maa mbb) (mAp2 fl' gg maa mbb)))))))
mAp2cFlag5 gg maa mbb {fl} {fl'} e =
  cR5 Pair (ap2 Pair fl (ap2 Pair gg (ap2 Pair maa mbb)))
           (ap2 Pair fl' (ap2 Pair gg (ap2 Pair maa mbb))) tgAp2
    (ap5c (lift5 Ga Gb Gc Gd Ge (ax_eqCongL Pair fl fl' (ap2 Pair gg (ap2 Pair maa mbb)))) e)

-- depth-5 congruence on the argument of tmAp1.
tmAp1cArg5 : (f : Term) {X Y : Term} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF X Y)))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF (tmAp1 f X) (tmAp1 f Y)))))))
tmAp1cArg5 f {X} {Y} e =
  cR5 Pair (ap2 Pair f X) (ap2 Pair f Y) tgAp1 (cR5 Pair X Y f e)

-- depth-5 congruence on the 3rd tmAp2 argument.
tmAp2cB5 : (gg aa : Term) {b b' : Term} ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF b b')))))) ->
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
          (eqF (tmAp2 gg aa b) (tmAp2 gg aa b')))))))
tmAp2cB5 gg aa {b} {b'} e =
  cR5 Pair (ap2 Pair gg (ap2 Pair aa b)) (ap2 Pair gg (ap2 Pair aa b')) tgAp2
    (cR5 Pair (ap2 Pair aa b) (ap2 Pair aa b') gg
      (cR5 Pair b b' aa e))

------------------------------------------------------------------------
-- Child bound + child triangle Q (mMa sk) (over PA = Ge).

rebound : (c : Term) ->
  Deriv (leq c (ap1 predecessor sk)) -> Deriv (leq c (var 0))
rebound c d =
  ruleTrans (congR sub c (ruleSym (ruleInst 0 (var 0) T_p_S_v0))) d

qChildA : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (Q ma))))))
qChildA =
  let pa2phik : Deriv (imp Ge PhiKFn)
      pa2phik = sigmaZeroL bigK (ap1 wfMarkedF sk)
      pa2a : Deriv (imp Ge Aform)
      pa2a = sigmaZeroR bigK (ap1 wfMarkedF sk)
      childT : Deriv (imp Ge (imp (eqF (ap1 wfMarkedF ma) O) (Q ma)))
      childT = compI pa2phik (QofChildFn ma (rebound ma (mMa_bound sk ne_sk)))
      wcI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
              (imp Aform (eqF (ap1 wfMarkedF ma) O)))))))
      wcI = emb5D (wfF_child_ap2_ma_imp Gd sk ne_sk (identP Gd))
      aI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Aform)))))
      aI = emb5E pa2a
      childvalid : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF (ap1 wfMarkedF ma) O))))))
      childvalid = ap5c wcI aI
  in ap5c (emb5E childT) childvalid

------------------------------------------------------------------------
-- Reconstruction  mMb sk = mO  from mb-head-0 (Gb) and child-validity (from Ge).

mbValid : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF (ap1 wfMarkedF mb) O))))))
mbValid =
  let pa2a : Deriv (imp Ge Aform)
      pa2a = sigmaZeroR bigK (ap1 wfMarkedF sk)
      wcI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
              (imp Aform (eqF (ap1 wfMarkedF mb) O)))))))
      wcI = emb5D (wfF_child_ap2_mb_imp Gd sk ne_sk (identP Gd))
      aI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Aform)))))
      aI = emb5E pa2a
  in ap5c wcI aI

mbEqmO : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF mb mOt))))))
mbEqmO =
  let reconD : Deriv (imp Gb (imp (eqF (ap1 wfMarkedF mb) O) (eqF mb O)))
      reconD = reconTag0 mb
      liftedRecon : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                      (imp Gb (imp (eqF (ap1 wfMarkedF mb) O) (eqF mb O))))))))
      liftedRecon = lift5 Ga Gb Gc Gd Ge reconD
      step1 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                (imp (eqF (ap1 wfMarkedF mb) O) (eqF mb O)))))))
      step1 = ap5c liftedRecon mbhI5
      mbEqO : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF mb O))))))
      mbEqO = ap5c step1 mbValid
  in trans5c mb O mOt mbEqO (lift5 Ga Gb Gc Gd Ge (ruleSym pi_O_O))

------------------------------------------------------------------------
-- The leaf.

leaf_ap2_flC_Rb :
  Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (Q sk))))))
leaf_ap2_flC_Rb =
  let ha : Deriv (imp Ga Ga)
      ha = identP Ga
      -- LHS:  residual sk = mAp1 flN g0 (residual ma)  (flC-Rb chain, DERIVED flC),
      -- then mcontract_ap1_cong -> tmAp1 g0 (mcontract (residual ma)).
      residChainI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                      (eqF (ap1 residual sk) (mAp1 flN g0 (ap1 residual ma))))))))
      residChainI =
        ap5c (ap5c (ap5c (ap5c (lift5 Ga Gb Gc Gd Ge (residual_op_ap2_flC_Rb_chain sk ne_sk))
                               tagI5) flcI) funhI5) mbhI5
      lhsI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
               (eqF (ap1 mcontract (ap1 residual sk))
                    (tmAp1 g0 (ap1 mcontract (ap1 residual ma)))))))))
      lhsI = trans5c (ap1 mcontract (ap1 residual sk))
               (ap1 mcontract (mAp1 flN g0 (ap1 residual ma)))
               (tmAp1 g0 (ap1 mcontract (ap1 residual ma)))
               (c5 mcontract (ap1 residual sk) (mAp1 flN g0 (ap1 residual ma)) residChainI)
               (lift5 Ga Gb Gc Gd Ge (mcontract_ap1_cong g0 (ap1 residual ma)))
      -- RHS: identical to flN-Rb (flag-independent).
      eraseE : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                 (eqF (ap1 erase sk) (tmAp2 g (ap1 erase ma) (ap1 erase mb))))))))
      eraseE = emb5D (erase_op_ap2_imp Gd sk ne_sk (identP Gd))
      eraseMbTmO : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                     (eqF (ap1 erase mb) tmO))))))
      eraseMbTmO = trans5c (ap1 erase mb) (ap1 erase mOt) tmO
                     (c5 erase mb mOt mbEqmO)
                     (lift5 Ga Gb Gc Gd Ge erase_mO)
      eraseE2 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                  (eqF (ap1 erase sk) (tmAp2 g (ap1 erase ma) tmO)))))))
      eraseE2 = trans5c (ap1 erase sk)
                  (tmAp2 g (ap1 erase ma) (ap1 erase mb))
                  (tmAp2 g (ap1 erase ma) tmO)
                  eraseE
                  (tmAp2cB5 g (ap1 erase ma) eraseMbTmO)
      redexE : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                 (eqF (ap1 redexHere (tmAp2 g (ap1 erase ma) tmO)) (natCode 1)))))))
      redexE = emb5A (redex_ap2_Rb_imp Ga g (ap1 erase ma) ha)
      rhsFlagI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
                   (eqF (ap1 markAll (ap1 erase sk))
                        (mAp2 flC g (ap1 markAll (ap1 erase ma)) tmO)))))))
      rhsFlagI = trans5c (ap1 markAll (ap1 erase sk))
                   (ap1 markAll (tmAp2 g (ap1 erase ma) tmO))
                   (mAp2 flC g (ap1 markAll (ap1 erase ma)) tmO)
                   (c5 markAll (ap1 erase sk) (tmAp2 g (ap1 erase ma) tmO) eraseE2)
                   (trans5c (ap1 markAll (tmAp2 g (ap1 erase ma) tmO))
                      (mAp2 (ap1 redexHere (tmAp2 g (ap1 erase ma) tmO)) g
                            (ap1 markAll (ap1 erase ma)) (ap1 markAll tmO))
                      (mAp2 flC g (ap1 markAll (ap1 erase ma)) tmO)
                      (lift5 Ga Gb Gc Gd Ge (markAll_ap2 g (ap1 erase ma) tmO))
                      (trans5c (mAp2 (ap1 redexHere (tmAp2 g (ap1 erase ma) tmO)) g
                                     (ap1 markAll (ap1 erase ma)) (ap1 markAll tmO))
                         (mAp2 flC g (ap1 markAll (ap1 erase ma)) (ap1 markAll tmO))
                         (mAp2 flC g (ap1 markAll (ap1 erase ma)) tmO)
                         (mAp2cFlag5 g (ap1 markAll (ap1 erase ma)) (ap1 markAll tmO) redexE)
                         (mAp2cB5 flC g (ap1 markAll (ap1 erase ma))
                            (lift5 Ga Gb Gc Gd Ge markAll_mO))))
      rhsI : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge
               (eqF (ap1 mcontract (ap1 markAll (ap1 erase sk)))
                    (tmAp1 g0 (ap1 mcontract (ap1 markAll (ap1 erase ma))))))))))
      rhsI = trans5c (ap1 mcontract (ap1 markAll (ap1 erase sk)))
               (ap1 mcontract (mAp2 flC g (ap1 markAll (ap1 erase ma)) tmO))
               (tmAp1 g0 (ap1 mcontract (ap1 markAll (ap1 erase ma))))
               (c5 mcontract (ap1 markAll (ap1 erase sk))
                  (mAp2 flC g (ap1 markAll (ap1 erase ma)) tmO) rhsFlagI)
               (emb5A (mcontract_ap2_Rb_imp Ga g (ap1 markAll (ap1 erase ma)) tmO ha
                         (impLift {Ga} mcontract_mO)))
  in trans5c (ap1 mcontract (ap1 residual sk))
       (tmAp1 g0 (ap1 mcontract (ap1 residual ma)))
       (ap1 mcontract (ap1 markAll (ap1 erase sk)))
       lhsI
       (trans5c (tmAp1 g0 (ap1 mcontract (ap1 residual ma)))
          (tmAp1 g0 (ap1 mcontract (ap1 markAll (ap1 erase ma))))
          (ap1 mcontract (ap1 markAll (ap1 erase sk)))
          (tmAp1cArg5 g0 qChildA)
          (sym5 (ap1 mcontract (ap1 markAll (ap1 erase sk)))
                (tmAp1 g0 (ap1 mcontract (ap1 markAll (ap1 erase ma)))) rhsI))
