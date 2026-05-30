{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.GLCodeNodes -- Phase R5, step (3): the thmT-FREE structural pieces of the
-- node accounting (CHAITIN-G1-FAITHFUL-BLUEPRINT.md S5bis R4).
--
-- These do NOT mention the proof-checker  thmT  or the full diagonal  gLcode ;
-- they are about the K-formula code  codeFormula (pKgt L) , the threshold
-- numeral handle  piece k = codeFun1 (constTermFun1 (natCode k)) , and the
-- embedded-constant coder  W = mcode1 o constTermFun1 .  The thmT-bearing mcode
-- path (Cmcode), the size additivity and dLen are in BRA4.GLCodeP, PARAMETRIC
-- over an abstract checker  tc : Fun1  (so  nodes  never normalises  thmT ).

module BRA4.GLCodeNodes where

open import BRA4.Base
open import BRA4.Tags using ( tag_C ; tag_eq ; tag_ap1 )
open import BRA4.Code using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import BRA4.ProgEnc using ( nodes )
open import BRA4.ProgNodes using ( Ctx ; hole ; inAp1 ; inAp2L ; inAp2R ; plug ; nodesCtx ; nodes_plug )
open import BRA4.Thm12.ConstTermFun1 using ( constTermFun1 )
open import BRA4.EvalU using ( mcode1 ; mcode2 )
open import BRA4.KFormula using ( pKgt )
open import BRA4.Exp using ( exp2 )
open import BRA4.LenR using ( lenR )

open import BRA3.Church using ( pi ; isZero ; sub )
open import BRA3.Code.Tag using ( addN )

------------------------------------------------------------------------
-- SECTION 1.  The k-varying handle  piece  and its one-step context  Csmall .
--   piece k = codeFun1 (constTermFun1 (natCode k))
-- constTermFun1 (natCode (suc k)) = compose1U s (constTermFun1 (natCode k))
--                                 = C (R s v v) (constTermFun1 (natCode k)) u ,
-- so  codeFun1  of it is a fixed 3-Pair wrap of  piece k .

piece : Nat -> Term
piece k = codeFun1 (constTermFun1 (natCode k))

Csmall : Ctx
Csmall =
  inAp2R Pair (natCode tag_C)
    (inAp2R Pair (codeFun2 (R s v v))
      (inAp2L Pair hole (codeFun1 u)))

-- RAW refl:  piece (suc k) = plug Csmall (piece k) .  Kept OPAQUE (abstract)
-- so transports along it stay neutral (avoid normalising the embedded code).
abstract
  piece_suc : (k : Nat) -> Eq (piece (suc k)) (plug Csmall (piece k))
  piece_suc k = refl

------------------------------------------------------------------------
-- SECTION 2.  W = mcode1 o constTermFun1 (the embedded-constant coder), and
-- its commutation with plugging:  W (plug C t) = plug (Wctx C) (W t) .
-- Each constructor turns one  ap2 g / ap1 f  into the fixed  C-combinator
-- mcode (a 3-pi cell), so W is a structure-preserving image and  Wctx  is its
-- per-node lift.  Proved generically, by induction on the context.

W : Term -> Term
W t = mcode1 (constTermFun1 t)

Wctx : Ctx -> Ctx
Wctx hole           = hole
Wctx (inAp1 f c)    =
  inAp2R pi (natCode tag_C)
    (inAp2R pi (mcode2 (R f v v))
      (inAp2L pi (Wctx c) (mcode1 u)))
Wctx (inAp2L g c b) =
  inAp2R pi (natCode tag_C)
    (inAp2R pi (mcode2 g)
      (inAp2L pi (Wctx c) (W b)))
Wctx (inAp2R g a c) =
  inAp2R pi (natCode tag_C)
    (inAp2R pi (mcode2 g)
      (inAp2R pi (W a) (Wctx c)))

-- Kept OPAQUE (abstract): the commutation holds by a refl-chain, but is hidden
-- so  eqCong nodes (W_plug ...)  stays neutral (no normalising the coded formula).
abstract
  W_plug : (c : Ctx) (t : Term) -> Eq (W (plug c t)) (plug (Wctx c) (W t))
  W_plug hole           t = refl
  W_plug (inAp1 f c)    t =
    eqCong (\ z -> ap2 pi (natCode tag_C) (ap2 pi (mcode2 (R f v v)) (ap2 pi z (mcode1 u))))
           (W_plug c t)
  W_plug (inAp2L g c b) t =
    eqCong (\ z -> ap2 pi (natCode tag_C) (ap2 pi (mcode2 g) (ap2 pi z (W b))))
           (W_plug c t)
  W_plug (inAp2R g a c) t =
    eqCong (\ z -> ap2 pi (natCode tag_C) (ap2 pi (mcode2 g) (ap2 pi (W a) z)))
           (W_plug c t)

-- the embedded numeral handle (= W (piece k)), thmT-free.
H : Nat -> Term
H k = W (piece k)

------------------------------------------------------------------------
-- SECTION 3.  Cform : the (small, k-free) Pair-context inside
-- codeFormula (pKgt L)  reaching  piece k  (L = exp2 (natCode k)).
--   codeFormula (pKgt L)
--     = Pair tag_eq (Pair (codeTerm (szLeqApp L (var0))) (codeTerm (s O)))
--   codeTerm (szLeqApp L v0) = Pair tag_ap1 (Pair (codeFun1 (szLeqFun L)) (codeTerm v0))
--   codeFun1 (szLeqFun L)    = Pair tag_C (Pair (codeFun2 (R isZero v v))
--                                (Pair (codeFun1 (C sub lenR (constTermFun1 L))) (codeFun1 u)))
--   codeFun1 (C sub lenR (constTermFun1 L))
--                            = Pair tag_C (Pair (codeFun2 sub)
--                                (Pair (codeFun1 lenR) (codeFun1 (constTermFun1 L))))
--   codeFun1 (constTermFun1 L) = codeFun1 (C (R exp2 v v) (constTermFun1 (natCode k)) u)
--                            = Pair tag_C (Pair (codeFun2 (R exp2 v v))
--                                (Pair (piece k) (codeFun1 u)))

Cinner1 : Ctx
Cinner1 =
  inAp2R Pair (natCode tag_C)
    (inAp2R Pair (codeFun2 (R exp2 v v))
      (inAp2L Pair hole (codeFun1 u)))

Cinner2 : Ctx
Cinner2 =
  inAp2R Pair (natCode tag_C)
    (inAp2R Pair (codeFun2 sub)
      (inAp2R Pair (codeFun1 lenR) Cinner1))

Cinner3 : Ctx
Cinner3 =
  inAp2R Pair (natCode tag_C)
    (inAp2R Pair (codeFun2 (R isZero v v))
      (inAp2L Pair Cinner2 (codeFun1 u)))

Cinner4 : Ctx
Cinner4 =
  inAp2R Pair (natCode tag_ap1)
    (inAp2L Pair Cinner3 (codeTerm (var 0)))

Cform : Ctx
Cform =
  inAp2R Pair (natCode tag_eq)
    (inAp2L Pair Cinner4 (codeTerm (ap1 s O)))

abstract
  Cform_eq :
    (k : Nat) ->
    Eq (codeFormula (pKgt (ap1 exp2 (natCode k)))) (plug Cform (piece k))
  Cform_eq k = refl
