{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.GLCodePDefN -- the number-code re-pointing of T4.GLCodePDef.SizeDef : the
-- symbolic node-accounting + fixed point for the honest p<N / runProgN diagonal.
-- Mirrors GLCodePDef VERBATIM, swapping the szLeqApp guard for the leq/predNof
-- guard ( handle pieceN / Cform'N / H'N from T4.GLCodeNodesN ) and runProg for
-- runProgN ( inner4DefN ).  Everything stays SYMBOLIC ( tc abstract, abstract
-- refl bridges ) -- nodes never normalises the program/thmT skeleton.

module T4.GLCodePDefN where

open import T4.Base
open import T4.Tags using
  ( tag_C ; tag_R ; tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import T4.Code using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import T4.ProgEnc using ( nodes ; addN_assoc )
open import T4.ParseN using ( runProgN )
open import T4.Thm12.ConstTermFun1 using ( constTermFun1 )
open import T4.ProgNodes using
  ( Ctx ; hole ; inAp1 ; inAp2L ; inAp2R ; plug ; nodesCtx ; nodes_plug )
open import T4.EvalU using ( mcode1 ; mcode2 ; mcodeMu ; tag_mu )
open import T4.KOut using ( sndProj )
open import T4.Exp using ( exp2 ; powN )
open import T4.Num using ( num )
open import T4.CountingObj using ( eqIndF )
open import T4.Decode using ( decode )
open import T4.GLCodeNodes using ( W ; Wctx ; W_plug )
open import T4.GLCodeNodesN using
  ( predNof ; pieceN ; CsN ; pieceN_suc ; Cform'N ; Cform'N_eq
  ; H'N ; deltaN ; nodes_H'N_suc )

import T4.KdefN

open import T4.NatExp using ( dom ; Sg ; mkSg ; fst ; snd )

open import BRA3.Church using ( pi ; isZero ; sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.Fan using ( Lift1 ; compose1U )
open import BRA3.Code.Tag using ( addN )
open import BRA3.Code.NatLemmas using ( addN_suc_right )
open import BRA3.RuleInst2 using ( NatLe )

module SizeDefN (tc : Fun1) where

  --------------------------------------------------------------------
  -- SECTION 1.  The diagonal construction, parametric in the threshold
  -- term  predN  and the abstract checker  tc .

  projKdefN : Term -> Fun1
  projKdefN predN = sndProj (T4.KdefN.kdefConstsN predN)

  KcodeN' : Term -> Fun1
  KcodeN' predN = T4.KdefN.KcodeN predN

  outKdefNP : Term -> Fun1
  outKdefNP predN = compose1U decode (compose1U (projKdefN predN) tc)

  gCodeOfDefNP : Term -> Term
  gCodeOfDefNP predN = mcode2 (Lift1 (outKdefNP predN))

  hitKdefNP : Term -> Fun1 -> Fun1
  hitKdefNP predN out = C eqIndF tc (compose1U (KcodeN' predN) out)

  predFlipDefNP : Term -> Fun1
  predFlipDefNP predN = compose1U isZero (hitKdefNP predN (outKdefNP predN))

  gLcodeDefNP : Term -> Term
  gLcodeDefNP predN =
    ap2 pi (natCode tag_C)
      (ap2 pi (gCodeOfDefNP predN)
        (ap2 pi (mcodeMu (mcode1 (predFlipDefNP predN))) (mcode1 u)))

  --------------------------------------------------------------------
  -- SECTION 2.  The mcode path  CmcodeDefN  ( runProgN in inner4 ).

  inner4DefN : Fun1
  inner4DefN =
    C Pair (constTermFun1 (natCode tag_neg))
      (C Pair (constTermFun1 (natCode tag_eq))
        (C Pair (constTermFun1 (codeTerm (ap2 runProgN (var 0) (var 1))))
          (C Pair (constTermFun1 (natCode tag_ap1))
            (C Pair (constTermFun1 (codeFun1 s)) num))))

  Cm_c2DefN : Ctx
  Cm_c2DefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2L pi hole (mcode1 inner4DefN)))

  Cm_c1DefN : Ctx
  Cm_c1DefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_imp))) Cm_c2DefN))

  Cm_RDefN : Ctx
  Cm_RDefN =
    inAp2R pi (natCode tag_R)
      (inAp2L pi Cm_c1DefN (ap2 pi (mcode2 v) (mcode2 v)))

  Cm_C2DefN : Ctx
  Cm_C2DefN =
    inAp2R pi (natCode tag_C)
      (inAp2L pi Cm_RDefN (ap2 pi (mcode1 (outKdefNP O)) (mcode1 u)))

  Cm_hitKDefN : Ctx
  Cm_hitKDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 eqIndF)
        (inAp2R pi (mcode1 tc) Cm_C2DefN))

  Cm_predFlipDefN : Ctx
  Cm_predFlipDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 (R isZero v v))
        (inAp2L pi Cm_hitKDefN (mcode1 u)))

  Cm_muDefN : Ctx
  Cm_muDefN = inAp2R pi (natCode tag_mu) Cm_predFlipDefN

  CmcodeDefN : Ctx
  CmcodeDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (gCodeOfDefNP O)
        (inAp2L pi Cm_muDefN (mcode1 u)))

  abstract
    CmcodeDefN_eq :
      (k : Nat) ->
      Eq (gLcodeDefNP (predNof k))
         (plug CmcodeDefN (W (codeFormula (leq (var zero) (predNof k)))))
    CmcodeDefN_eq k = refl

  --------------------------------------------------------------------
  -- SECTION 3.  CmcodebDefN = CmcodeDefN with  Wctx Cform'N  inlined.

  Cm_c2bDefN : Ctx
  Cm_c2bDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2L pi (Wctx Cform'N) (mcode1 inner4DefN)))

  Cm_c1bDefN : Ctx
  Cm_c1bDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_imp))) Cm_c2bDefN))

  Cm_RbDefN : Ctx
  Cm_RbDefN =
    inAp2R pi (natCode tag_R)
      (inAp2L pi Cm_c1bDefN (ap2 pi (mcode2 v) (mcode2 v)))

  Cm_C2bDefN : Ctx
  Cm_C2bDefN =
    inAp2R pi (natCode tag_C)
      (inAp2L pi Cm_RbDefN (ap2 pi (mcode1 (outKdefNP O)) (mcode1 u)))

  Cm_hitKbDefN : Ctx
  Cm_hitKbDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 eqIndF)
        (inAp2R pi (mcode1 tc) Cm_C2bDefN))

  Cm_predFlipbDefN : Ctx
  Cm_predFlipbDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 (R isZero v v))
        (inAp2L pi Cm_hitKbDefN (mcode1 u)))

  Cm_mubDefN : Ctx
  Cm_mubDefN = inAp2R pi (natCode tag_mu) Cm_predFlipbDefN

  CmcodebDefN : Ctx
  CmcodebDefN =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (gCodeOfDefNP O)
        (inAp2L pi Cm_mubDefN (mcode1 u)))

  size_decDefN :
    (k : Nat) ->
    Eq (nodes (plug CmcodebDefN (H'N k))) (addN (nodesCtx CmcodebDefN) (nodes (H'N k)))
  size_decDefN k = nodes_plug CmcodebDefN (H'N k)

  --------------------------------------------------------------------
  -- SECTION 4.  The size recurrence + exp-domination fixed point.

  commuteFront : (c d Y : Nat) -> Eq (addN c (addN d Y)) (addN d (addN c Y))
  commuteFront c zero     Y = refl
  commuteFront c (suc d') Y =
    eqTrans (addN_suc_right c (addN d' Y))
            (eqCong suc (commuteFront c d' Y))

  abstract
    nodes_plug_shift :
      (C : Ctx) (d : Nat) (X : Nat -> Term) ->
      ((k : Nat) -> Eq (nodes (X (suc k))) (addN d (nodes (X k)))) ->
      (k : Nat) -> Eq (nodes (plug C (X (suc k)))) (addN d (nodes (plug C (X k))))
    nodes_plug_shift hole          d X rec k = rec k
    nodes_plug_shift (inAp1 f c)   d X rec k =
      eqTrans (eqCong suc (nodes_plug_shift c d X rec k))
              (eqSym (addN_suc_right d (nodes (plug c (X k)))))
    nodes_plug_shift (inAp2L g c b) d X rec k =
      eqTrans (eqCong (\ z -> suc (addN z (nodes b))) (nodes_plug_shift c d X rec k))
        (eqTrans (eqCong suc (eqSym (addN_assoc d (nodes (plug c (X k))) (nodes b))))
                 (eqSym (addN_suc_right d (addN (nodes (plug c (X k))) (nodes b)))))
    nodes_plug_shift (inAp2R g a c) d X rec k =
      eqTrans (eqCong (\ z -> suc (addN (nodes a) z)) (nodes_plug_shift c d X rec k))
        (eqTrans (eqCong suc (commuteFront (nodes a) d (nodes (plug c (X k)))))
                 (eqSym (addN_suc_right d (addN (nodes a) (nodes (plug c (X k)))))))

  size_recDefN :
    (k : Nat) ->
    Eq (nodes (plug CmcodebDefN (H'N (suc k))))
       (addN deltaN (nodes (plug CmcodebDefN (H'N k))))
  size_recDefN k = nodes_plug_shift CmcodebDefN deltaN H'N nodes_H'N_suc k

  abstract
    dom_plug :
      (cx : Ctx) (d : Nat) (Hf : Nat -> Term) ->
      ((k : Nat) -> Eq (nodes (plug cx (Hf (suc k)))) (addN d (nodes (plug cx (Hf k))))) ->
      Sg Nat (\ k -> NatLe (nodes (plug cx (Hf k))) (powN k))
    dom_plug cx d Hf rec = dom d (\ k -> nodes (plug cx (Hf k))) rec

  boundDefN : Sg Nat (\ k -> NatLe (nodes (plug CmcodebDefN (H'N k))) (powN k))
  boundDefN = dom_plug CmcodebDefN deltaN H'N size_recDefN

  --------------------------------------------------------------------
  -- SECTION 5.  The canonical number-code threshold.   ( bridge kept
  --  abstract so transports stay neutral. )

  LstarN : Term
  LstarN = ap1 exp2 (natCode (fst boundDefN))

  abstract
    bridgeDefN :
      Eq (gLcodeDefNP (predNof (fst boundDefN)))
         (plug CmcodebDefN (H'N (fst boundDefN)))
    bridgeDefN = refl
