{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.GLCodePDef -- the Kdef-shape parallel of BRA4.GLCodeP.Size .
--
-- BRA4.GLCodeP.Size builds the size accounting + dLen for the Kgt-shape
-- diagonal program  gLcodeP tc  (= KDiag.gLcode  at  tc := thmT ).  This
-- file does the same for the Kdef-shape diagonal program
--  gLcodeDefP tc  (= KdefDiag.gLcodeDef  at  tc := thmT ).
--
-- Same parametrization-in-tc trick: tc is a module parameter so the deep
-- thmT skeleton is NEUTRAL during type-checking; instantiating at thmT
-- recovers the real  gLcodeDef  definitionally.
--
-- The H/Csmall/piece/Wctx/Cform infrastructure from GLCodeNodes is reused
-- VERBATIM because:
--   * Kdef's antecedent  pKdefAnt L = eqF (szLeqApp L (var 0)) (ap1 s O)
--     is SYNTACTICALLY the same as  pKgt L  (BRA4.KFormula);
--   * the threshold-numeral handle  H k  is shared (it lives inside the
--     codeFormula at L = exp2(natCode k), which is the same formula).
--
-- The Cmcode / Cmcodeb / inner4 contexts here are structurally SMALLER
-- than their GLCodeP counterparts (2 outer wrapL layers instead of 4,
-- inner4Def uses runProg instead of evalU∘parse).  This yields a
-- separate  boundDef  with a (possibly smaller) k witness; the canonical
-- Kdef threshold is  LstarDef := exp2 (natCode (fst boundDef)) .

module BRA4.GLCodePDef where

open import BRA4.Base
open import BRA4.Tags using
  ( tag_C ; tag_R ; tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import BRA4.Code using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import BRA4.ProgEnc using ( nodes ; addN_assoc ; enc ; lenR_enc )
open import BRA4.LenR using ( lenR )
open import BRA4.KFormula using ( szLeqApp ; pKgt )
open import BRA4.Kdef using ( runProg ; Kcode )
open import BRA4.KdefDiag using ( gLcodeDef ; gCodeOfDef ; predFlipDef )
open import BRA4.KdefRecog using ( hitKdef ; outKdef ; projKdef )
open import BRA4.SubLeq using ( sub_exp2_le )
open import BRA4.Thm12.ConstTermFun1 using
  ( NoVar ; NoVar_natCode ; constTermFun1 ; constTermFun1_eq )
open import BRA4.ProgNodes using
  ( Ctx ; hole ; inAp1 ; inAp2L ; inAp2R ; plug ; nodesCtx ; nodes_plug )
open import BRA4.EvalU using ( mcode1 ; mcode2 ; mcodeMu ; tag_mu )
open import BRA4.KOut using ( sndProj )
open import BRA4.Exp using ( exp2 ; powN )
open import BRA4.Num using ( num )
open import BRA4.EvalUEval using ( evalU )
open import BRA4.ProgParse using ( parse )
open import BRA4.CountingObj using ( eqIndF )
open import BRA4.GLCodeNodes using
  ( W ; Wctx ; W_plug ; Cform ; Cform_eq ; piece ; Csmall ; piece_suc ; H )

open import BRA4.NatExp using ( dom ; Sg ; mkSg ; fst ; snd )

open import BRA3.Church using ( pi ; isZero ; sub ; TisZeroZ )
open import BRA3.Fan using ( Lift1 ; compose1U ; compose1U_eq )
open import BRA3.Code.Tag using ( addN )
open import BRA3.Code.NatLemmas using ( addN_suc_right )
open import BRA3.RuleInst2 using ( NatLe )

module SizeDef (tc : Fun1) where

  --------------------------------------------------------------------
  -- SECTION 1.  The Kdef-shape diagonal construction, checker abstracted
  -- to  tc .   gLcodeDefP thmT  is definitionally  KdefDiag.gLcodeDef .

  outKdefP : Term -> Fun1
  outKdefP L = compose1U decode (compose1U (projKdef L) tc)
    where open import BRA4.Decode using ( decode )

  gCodeOfDefP : Term -> Term
  gCodeOfDefP L = mcode2 (Lift1 (outKdefP L))

  hitKdefP : Term -> Fun1 -> Fun1
  hitKdefP L out = C eqIndF tc (compose1U (Kcode L) out)

  predFlipDefP : Term -> Fun1
  predFlipDefP L = compose1U isZero (hitKdefP L (outKdefP L))

  gLcodeDefP : Term -> Term
  gLcodeDefP L =
    ap2 pi (natCode tag_C)
      (ap2 pi (gCodeOfDefP L)
        (ap2 pi (mcodeMu (mcode1 (predFlipDefP L))) (mcode1 u)))

  --------------------------------------------------------------------
  -- SECTION 2.  The mcode path  CmcodeDef  (siblings carry  tc , hence
  -- neutral).
  --
  -- The Kdef-shape wrapL chain has only 2 OUTER layers above the hole
  -- (kdefConsts entries 1 = tag_imp ; 2 = codeFormula(pKdefAnt L) = hole)
  -- and 5 inner layers (entries 3..7 = tag_neg, tag_eq,
  -- codeTerm(runProg v0 v1), tag_ap1, codeFun1 s).

  inner4Def : Fun1
  inner4Def =
    C Pair (constTermFun1 (natCode tag_neg))
      (C Pair (constTermFun1 (natCode tag_eq))
        (C Pair (constTermFun1 (codeTerm (ap2 runProg (var 0) (var 1))))
          (C Pair (constTermFun1 (natCode tag_ap1))
            (C Pair (constTermFun1 (codeFun1 s)) num))))

  -- Cm_c2Def : the wrapL layer at the HOLE position (entry 2 of kdefConsts).
  Cm_c2Def : Ctx
  Cm_c2Def =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2L pi hole (mcode1 inner4Def)))

  -- Cm_c1Def : the OUTER wrapL layer (entry 1 = tag_imp).
  Cm_c1Def : Ctx
  Cm_c1Def =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_imp))) Cm_c2Def))

  -- Cm_RDef : walks into  mcode2 (Lift1 (Kcode L))  via the Lift1 = R _ v v
  -- structure.
  Cm_RDef : Ctx
  Cm_RDef =
    inAp2R pi (natCode tag_R)
      (inAp2L pi Cm_c1Def (ap2 pi (mcode2 v) (mcode2 v)))

  -- Cm_C2Def : walks into  mcode1 (compose1U (Kcode L) (outKdefP L))  via
  -- compose1U = C (Lift1 _) _ u .   The  outKdefP O  sibling is L-free
  -- (projKdef depends on the LENGTH of kdefConsts only, not on L).
  Cm_C2Def : Ctx
  Cm_C2Def =
    inAp2R pi (natCode tag_C)
      (inAp2L pi Cm_RDef (ap2 pi (mcode1 (outKdefP O)) (mcode1 u)))

  -- Cm_hitKDef : walks into  mcode1 (hitKdefP L _) = mcode1 (C eqIndF tc
  -- (compose1U (Kcode L) _)) .
  Cm_hitKDef : Ctx
  Cm_hitKDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 eqIndF)
        (inAp2R pi (mcode1 tc) Cm_C2Def))

  -- Cm_predFlipDef : walks into  mcode1 (predFlipDefP L) = mcode1
  -- (compose1U isZero (hitKdefP L _)) .
  Cm_predFlipDef : Ctx
  Cm_predFlipDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 (R isZero v v))
        (inAp2L pi Cm_hitKDef (mcode1 u)))

  -- Cm_muDef : walks into  mcodeMu (mcode1 (predFlipDefP L)) = pi tag_mu (...).
  Cm_muDef : Ctx
  Cm_muDef = inAp2R pi (natCode tag_mu) Cm_predFlipDef

  -- CmcodeDef : the full context from the gLcodeDefP root down to the
  -- L-dependent hole at codeFormula(pKdefAnt L) = codeFormula(pKgt L).
  CmcodeDef : Ctx
  CmcodeDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (gCodeOfDefP O)
        (inAp2L pi Cm_muDef (mcode1 u)))

  -- RAW refl bridge.  Kept abstract so transports along it stay neutral.
  abstract
    CmcodeDef_eq :
      (k : Nat) ->
      Eq (gLcodeDefP (ap1 exp2 (natCode k)))
         (plug CmcodeDef (W (codeFormula (pKgt (ap1 exp2 (natCode k))))))
    CmcodeDef_eq k = refl

  --------------------------------------------------------------------
  -- SECTION 3.  CmcodebDef = CmcodeDef with  Wctx Cform  inlined at the
  -- hole.  One direct  nodes_plug  for the size additivity.

  Cm_c2bDef : Ctx
  Cm_c2bDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2L pi (Wctx Cform) (mcode1 inner4Def)))

  Cm_c1bDef : Ctx
  Cm_c1bDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_imp))) Cm_c2bDef))

  Cm_RbDef : Ctx
  Cm_RbDef =
    inAp2R pi (natCode tag_R)
      (inAp2L pi Cm_c1bDef (ap2 pi (mcode2 v) (mcode2 v)))

  Cm_C2bDef : Ctx
  Cm_C2bDef =
    inAp2R pi (natCode tag_C)
      (inAp2L pi Cm_RbDef (ap2 pi (mcode1 (outKdefP O)) (mcode1 u)))

  Cm_hitKbDef : Ctx
  Cm_hitKbDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 eqIndF)
        (inAp2R pi (mcode1 tc) Cm_C2bDef))

  Cm_predFlipbDef : Ctx
  Cm_predFlipbDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 (R isZero v v))
        (inAp2L pi Cm_hitKbDef (mcode1 u)))

  Cm_mubDef : Ctx
  Cm_mubDef = inAp2R pi (natCode tag_mu) Cm_predFlipbDef

  CmcodebDef : Ctx
  CmcodebDef =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (gCodeOfDefP O)
        (inAp2L pi Cm_mubDef (mcode1 u)))

  -- DIRECT additivity at  CmcodebDef .
  size_decDef :
    (k : Nat) ->
    Eq (nodes (plug CmcodebDef (H k))) (addN (nodesCtx CmcodebDef) (nodes (H k)))
  size_decDef k = nodes_plug CmcodebDef (H k)

  --------------------------------------------------------------------
  -- SECTION 4.  The H-recurrence is INHERITED from GLCodeNodes / GLCodeP
  -- (Csmall, piece, piece_suc, H are k-only; the program structure plays
  -- no role).  We restate the needed delta/recurrence here locally.

  delta : Nat
  delta = nodesCtx (Wctx Csmall)

  nodes_H_suc : (k : Nat) -> Eq (nodes (H (suc k))) (addN delta (nodes (H k)))
  nodes_H_suc k =
    eqSubst (\ z -> Eq (nodes (W z)) (addN delta (nodes (H k))))
            (eqSym (piece_suc k))
            (eqTrans (eqCong nodes (W_plug Csmall (piece k)))
                     (nodes_plug (Wctx Csmall) (W (piece k))))

  --------------------------------------------------------------------
  -- SECTION 5.  The size recurrence and the exp-domination bound for
  --  CmcodebDef .  Identical body to GLCodeP.Size (parametric in the
  -- context); kept local so  CmcodebDef  appears in the declared types
  -- and is never compared against the GLCodeP.Size  Cmcodeb .

  sizeDef : Nat -> Nat
  sizeDef k = nodes (plug CmcodebDef (H k))

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

  size_recDef :
    (k : Nat) ->
    Eq (nodes (plug CmcodebDef (H (suc k))))
       (addN delta (nodes (plug CmcodebDef (H k))))
  size_recDef k = nodes_plug_shift CmcodebDef delta H nodes_H_suc k

  abstract
    dom_plug :
      (cx : Ctx) (d : Nat) (Hf : Nat -> Term) ->
      ((k : Nat) -> Eq (nodes (plug cx (Hf (suc k)))) (addN d (nodes (plug cx (Hf k))))) ->
      Sg Nat (\ k -> NatLe (nodes (plug cx (Hf k))) (powN k))
    dom_plug cx d Hf rec = dom d (\ k -> nodes (plug cx (Hf k))) rec

  boundDef : Sg Nat (\ k -> NatLe (nodes (plug CmcodebDef (H k))) (powN k))
  boundDef = dom_plug CmcodebDef delta H size_recDef

  --------------------------------------------------------------------
  -- SECTION 6.  dLen for the canonical Kdef threshold
  --  LstarDef := exp2 (natCode (fst boundDef)) .   Identical body to
  -- GLCodeP.Size.dLen_gen / dLenAt / dLen (parametric in the size constant
  -- + program code + bound); kept local so the declared types reference
  --  CmcodebDef , not  Cmcodeb .

  szLeqApp_eval :
    (L e : Term) -> NoVar L ->
    Deriv (eqF (szLeqApp L e) (ap1 isZero (ap2 sub (ap1 lenR e) L)))
  szLeqApp_eval L e nvL =
    ruleTrans (compose1U_eq isZero (C sub lenR (constTermFun1 L)) e)
      (cong1 isZero
        (ruleTrans (ax_C sub lenR (constTermFun1 L) e)
                   (congR sub (ap1 lenR e) (constTermFun1_eq L nvL e))))

  abstract
    dLen_gen :
      (n k : Nat) (e : Term) ->
      Deriv (eqF (ap1 lenR e) (natCode n)) ->
      NatLe n (powN k) ->
      Deriv (eqF (szLeqApp (ap1 exp2 (natCode k)) e) (ap1 s O))
    dLen_gen n k e lenRe le =
      let L : Term
          L = ap1 exp2 (natCode k)
          subEq : Deriv (eqF (ap2 sub (ap1 lenR e) L) O)
          subEq = ruleTrans (congL sub L lenRe) (sub_exp2_le n k le)
      in ruleTrans (szLeqApp_eval L e (NoVar_natCode k))
                   (ruleTrans (cong1 isZero subEq) TisZeroZ)

    dLenAtDef :
      (k : Nat) ->
      NatLe (nodes (plug CmcodebDef (H k))) (powN k) ->
      Deriv (eqF (szLeqApp (ap1 exp2 (natCode k)) (enc (plug CmcodebDef (H k))))
                 (ap1 s O))
    dLenAtDef k le =
      dLen_gen (nodes (plug CmcodebDef (H k))) k (enc (plug CmcodebDef (H k)))
               (lenR_enc (plug CmcodebDef (H k))) le

  -- dLen for the canonical Kdef program  plug CmcodebDef (H (fst boundDef))
  -- (= gLcodeDefP (exp2 (natCode (fst boundDef)))  definitionally, via the
  -- bridge in BRA4.KGodel1BridgeDef).
  dLenDef :
    Deriv (eqF (szLeqApp (ap1 exp2 (natCode (fst boundDef)))
                         (enc (plug CmcodebDef (H (fst boundDef)))))
               (ap1 s O))
  dLenDef = dLenAtDef (fst boundDef) (snd boundDef)
