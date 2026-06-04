{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.GLCodeP -- Phase R5, step (3)+(5): the size accounting + dLen, PARAMETRIC
-- over an abstract proof-checker  tc : Fun1  (module  Size ).
--
-- The diagonal program embeds the checker  thmT  (via  hitK  and  out_L ).  We
-- mirror the construction with  tc  in place of  thmT ; since  tc  is a module
-- PARAMETER (a variable), Agda cannot unfold it, so  mcode1 tc  is NEUTRAL and
-- nodes (gLcodeP tc L)  stays SYMBOLIC -- the additivity goes through with NO
-- normalisation of the (huge) checker.  Instantiating  tc := thmT  at the end
-- is a stuck application:  gLcodeP thmT L  is definitionally the real  gLcode L
-- (so T4.KDiag sets  gLcode := gLcodeP thmT ), and nothing forces  thmT .

module T4.GLCodeP where

open import T4.Base
open import T4.Tags using ( tag_C ; tag_R ; tag_neg ; tag_imp ; tag_eq ; tag_ap1 )
open import T4.Code using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import T4.ProgEnc using ( nodes ; addN_assoc ; enc ; lenR_enc )
open import T4.LenR using ( lenR )
open import T4.KFormula using ( szLeqApp )
open import T4.SubLeq using ( sub_exp2_le )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; NoVar_natCode ; constTermFun1_eq )
open import T4.ProgNodes using ( Ctx ; hole ; inAp1 ; inAp2L ; inAp2R ; plug ; nodesCtx ; nodes_plug )
open import T4.Thm12.ConstTermFun1 using ( constTermFun1 )
open import T4.EvalU using ( mcode1 ; mcode2 ; mcodeMu ; tag_mu )
open import T4.KFormula using ( pKgt ; negKgtCodeOf )
open import T4.KOut using ( proj_L )
open import T4.Decode using ( decode )
open import T4.Exp using ( exp2 ; powN )
open import T4.Num using ( num )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.CountingObj using ( eqIndF )
open import T4.GLCodeNodes using ( W ; Wctx ; W_plug ; Cform ; Cform_eq ; piece ; Csmall ; piece_suc ; H )

open import T4.NatExp using ( dom ; Sg ; mkSg ; fst ; snd )

open import BRA3.Church using ( pi ; isZero ; sub ; TisZeroZ )
open import BRA3.Fan using ( Lift1 ; compose1U ; compose1U_eq )
open import BRA3.Code.Tag using ( addN )
open import BRA3.Code.NatLemmas using ( addN_suc_right )
open import BRA3.RuleInst2 using ( NatLe )

module Size (tc : Fun1) where

  --------------------------------------------------------------------
  -- SECTION 1.  The diagonal construction, checker abstracted to  tc .
  --   gLcodeP thmT  is definitionally  KDiag.gLcode .

  out_Lp : Term -> Fun1
  out_Lp L = compose1U decode (compose1U (proj_L L) tc)

  gCodeOfp : Term -> Term
  gCodeOfp L = mcode2 (Lift1 (out_Lp L))

  hitKp : Term -> Fun1 -> Fun1
  hitKp L out = C eqIndF tc (compose1U (negKgtCodeOf L) out)

  predFlipp : Term -> Fun1
  predFlipp L = compose1U isZero (hitKp L (out_Lp L))

  gLcodeP : Term -> Term
  gLcodeP L =
    ap2 pi (natCode tag_C)
      (ap2 pi (gCodeOfp L)
        (ap2 pi (mcodeMu (mcode1 (predFlipp L))) (mcode1 u)))

  --------------------------------------------------------------------
  -- SECTION 2.  The mcode path Cmcode (siblings carry  tc , hence neutral).

  inner4 : Fun1
  inner4 =
    C Pair (constTermFun1 (natCode tag_neg))
      (C Pair (constTermFun1 (natCode tag_eq))
        (C Pair (constTermFun1 (codeTerm (ap2 evalU (ap1 parse (var 0)) (var 1))))
          (C Pair (constTermFun1 (natCode tag_ap1))
            (C Pair (constTermFun1 (codeFun1 s)) num))))

  Cm_c4 : Ctx
  Cm_c4 =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2L pi hole (mcode1 inner4)))

  Cm_c3 : Ctx
  Cm_c3 =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_imp))) Cm_c4))
  Cm_c2 : Ctx
  Cm_c2 =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_neg))) Cm_c3))
  Cm_c1 : Ctx
  Cm_c1 =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_neg))) Cm_c2))

  Cm_R : Ctx
  Cm_R =
    inAp2R pi (natCode tag_R)
      (inAp2L pi Cm_c1 (ap2 pi (mcode2 v) (mcode2 v)))

  Cm_C2 : Ctx
  Cm_C2 =
    inAp2R pi (natCode tag_C)
      (inAp2L pi Cm_R (ap2 pi (mcode1 (out_Lp O)) (mcode1 u)))

  Cm_hitK : Ctx
  Cm_hitK =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 eqIndF)
        (inAp2R pi (mcode1 tc) Cm_C2))

  Cm_predFlip : Ctx
  Cm_predFlip =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 (R isZero v v))
        (inAp2L pi Cm_hitK (mcode1 u)))

  Cm_mu : Ctx
  Cm_mu = inAp2R pi (natCode tag_mu) Cm_predFlip

  Cmcode : Ctx
  Cmcode =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (gCodeOfp O)
        (inAp2L pi Cm_mu (mcode1 u)))

  -- RAW refl (tc abstract => cheap; tc siblings matched syntactically).
  abstract
    Cmcode_eq :
      (k : Nat) ->
      Eq (gLcodeP (ap1 exp2 (natCode k)))
         (plug Cmcode (W (codeFormula (pKgt (ap1 exp2 (natCode k))))))
    Cmcode_eq k = refl

  --------------------------------------------------------------------
  -- SECTION 3.  The size, DEFINED as a plug-form so the additivity is the
  -- DIRECT  nodes_plug  (no eqCong/conversion that would normalise the huge
  -- skeleton).  Cbig = Cmcode then Wctx Cform; the threshold numeral handle
  --  H k = W (piece k)  sits in the hole.  gCanon k is definitionally the real
  -- diagonal  gLcodeP (exp2 (natCode k))  (via plug_comp/W_plug/Cform_eq/Cmcode_eq).

  -- ONE full context  Cmcodeb  = Cmcode with  Wctx Cform  inlined at the hole;
  -- a SINGLE direct nodes_plug (testA-style), so nodesCtx appears once and is
  -- never compared/forced.  Re-states the chain with the deepest filler.
  Cm_c4b : Ctx
  Cm_c4b =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2L pi (Wctx Cform) (mcode1 inner4)))
  Cm_c3b : Ctx
  Cm_c3b =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_imp))) Cm_c4b))
  Cm_c2b : Ctx
  Cm_c2b =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_neg))) Cm_c3b))
  Cm_c1b : Ctx
  Cm_c1b =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 Pair)
        (inAp2R pi (mcode1 (constTermFun1 (natCode tag_neg))) Cm_c2b))
  Cm_Rb : Ctx
  Cm_Rb =
    inAp2R pi (natCode tag_R)
      (inAp2L pi Cm_c1b (ap2 pi (mcode2 v) (mcode2 v)))
  Cm_C2b : Ctx
  Cm_C2b =
    inAp2R pi (natCode tag_C)
      (inAp2L pi Cm_Rb (ap2 pi (mcode1 (out_Lp O)) (mcode1 u)))
  Cm_hitKb : Ctx
  Cm_hitKb =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 eqIndF)
        (inAp2R pi (mcode1 tc) Cm_C2b))
  Cm_predFlipb : Ctx
  Cm_predFlipb =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (mcode2 (R isZero v v))
        (inAp2L pi Cm_hitKb (mcode1 u)))
  Cm_mub : Ctx
  Cm_mub = inAp2R pi (natCode tag_mu) Cm_predFlipb
  Cmcodeb : Ctx
  Cmcodeb =
    inAp2R pi (natCode tag_C)
      (inAp2R pi (gCodeOfp O)
        (inAp2L pi Cm_mub (mcode1 u)))

  -- DIRECT additivity: ONE nodes_plug, declared type = lemma type SYNTACTICALLY
  -- (no gCanon/c0 def to unfold), so nodesCtx Cmcodeb is never normalised.
  size_dec :
    (k : Nat) ->
    Eq (nodes (plug Cmcodeb (H k))) (addN (nodesCtx Cmcodeb) (nodes (H k)))
  size_dec k = nodes_plug Cmcodeb (H k)

  --------------------------------------------------------------------
  -- SECTION 4.  The H-recurrence (H = W o piece is SMALL: numeral coding, no
  -- thmT / evalU), so these transports are cheap.

  delta : Nat
  delta = nodesCtx (Wctx Csmall)

  nodes_H_suc : (k : Nat) -> Eq (nodes (H (suc k))) (addN delta (nodes (H k)))
  nodes_H_suc k =
    eqSubst (\ z -> Eq (nodes (W z)) (addN delta (nodes (H k))))
            (eqSym (piece_suc k))
            (eqTrans (eqCong nodes (W_plug Csmall (piece k)))
                     (nodes_plug (Wctx Csmall) (W (piece k))))

  --------------------------------------------------------------------
  -- SECTION 5.  The size recurrence and the exp-domination bound.
  --   size k = nodes (gCanon k) = nodes (plug Cmcodeb (H k)) .
  -- nodesCtx Cmcodeb is kept LITERAL (no def) so it is never normalised.

  size : Nat -> Nat
  size k = nodes (plug Cmcodeb (H k))

  -- generic c+(d+Y) = d+(c+Y), recursion on d (small); applied at the huge
  -- c := nodesCtx Cmcodeb as a STUCK term (c never matched).
  commuteFront : (c d Y : Nat) -> Eq (addN c (addN d Y)) (addN d (addN c Y))
  commuteFront c zero     Y = refl
  commuteFront c (suc d') Y =
    eqTrans (addN_suc_right c (addN d' Y))
            (eqCong suc (commuteFront c d' Y))

  -- GENERIC: a per-step recurrence on the HOLE lifts to the whole plug,
  -- proven by induction on the (abstract) context C.  SEALED (abstract) so that
  -- at  C := Cmcodeb  the application is NEUTRAL (not reduced) -- otherwise the
  -- evaluation would run  commuteFront (nodes a) ...  on the concrete siblings
  -- and force the huge skeleton (decode/thmT).
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

  -- literal type (= nodes_plug_shift's type at Cmcodeb), so it is ASSIGNED
  -- directly (no conversion normalising nodes(plug Cmcodeb ...)).
  size_rec :
    (k : Nat) ->
    Eq (nodes (plug Cmcodeb (H (suc k))))
       (addN delta (nodes (plug Cmcodeb (H k))))
  size_rec k = nodes_plug_shift Cmcodeb delta H nodes_H_suc k

  -- dom specialised to a plug-form size, GENERIC over the context C / hole Hf
  -- and SEALED, so its premise matches  size_rec  LITERALLY (no conversion that
  -- would normalise  nodes (plug C ...) ) and at  C := Cmcodeb  it is neutral.
  abstract
    dom_plug :
      (cx : Ctx) (d : Nat) (Hf : Nat -> Term) ->
      ((k : Nat) -> Eq (nodes (plug cx (Hf (suc k)))) (addN d (nodes (plug cx (Hf k))))) ->
      Sg Nat (\ k -> NatLe (nodes (plug cx (Hf k))) (powN k))
    dom_plug cx d Hf rec = dom d (\ k -> nodes (plug cx (Hf k))) rec

  -- the exp-domination witness:  kk  with  nodes (plug Cmcodeb (H kk)) <= powN kk .
  bound : Sg Nat (\ k -> NatLe (nodes (plug Cmcodeb (H k))) (powN k))
  bound = dom_plug Cmcodeb delta H size_rec

  --------------------------------------------------------------------
  -- SECTION 6.  dLen for the canonical threshold  L := exp2 (natCode kk) .
  -- szLeqApp L e  reduces (object) to  isZero (sub (lenR e) L) ; with
  --  e := enc (gCanon kk) ,  lenR e = natCode (nodes (gCanon kk))  [lenR_enc]
  -- and the bound gives  sub (..) L = O , so  szLeqApp = isZero O = s O .
  -- Everything below is OBJECT Derivs over the STUCK  natCode (nodes (..)) ;
  -- nothing normalises the program.

  szLeqApp_eval :
    (L e : Term) -> NoVar L ->
    Deriv (eqF (szLeqApp L e) (ap1 isZero (ap2 sub (ap1 lenR e) L)))
  szLeqApp_eval L e nvL =
    ruleTrans (compose1U_eq isZero (C sub lenR (constTermFun1 L)) e)
      (cong1 isZero
        (ruleTrans (ax_C sub lenR (constTermFun1 L) e)
                   (congR sub (ap1 lenR e) (constTermFun1_eq L nvL e))))

  -- GENERIC dLen over an ABSTRACT size  n  (so  natCode n  is neutral and the
  -- ruleTrans middles never normalise it).  SEALED, so at  n := nodes (plug ..)
  -- it is a neutral application -- the program is never normalised.
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

    -- dLen at the plug-form program, with  k  kept a PARAMETER (so the size
    -- value  nodes (plug Cmcodeb (H k))  is compared under a binder, syntactic
    -- fast-path -- as in  bound ), then instantiated at the witness  fst bound .
    dLenAt :
      (k : Nat) ->
      NatLe (nodes (plug Cmcodeb (H k))) (powN k) ->
      Deriv (eqF (szLeqApp (ap1 exp2 (natCode k)) (enc (plug Cmcodeb (H k))))
                 (ap1 s O))
    dLenAt k le =
      dLen_gen (nodes (plug Cmcodeb (H k))) k (enc (plug Cmcodeb (H k)))
               (lenR_enc (plug Cmcodeb (H k))) le

  -- dLen for the canonical program  plug Cmcodeb (H (fst bound))  (definitionally
  -- the real diagonal  gLcodeP (exp2 (natCode (fst bound))) ).
  dLen :
    Deriv (eqF (szLeqApp (ap1 exp2 (natCode (fst bound)))
                         (enc (plug Cmcodeb (H (fst bound)))))
               (ap1 s O))
  dLen = dLenAt (fst bound) (snd bound)


