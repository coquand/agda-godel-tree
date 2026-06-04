{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CKRecog -- surprise-GII task (b): the re-pointed recogniser at the
-- single-atom characteristic-function shape  cNeg (cEqTm (cAp2f CK . .) O) .
--
-- The CK-route analog of  T4.KdefConjRecog , re-pointed from the  cAnd -spine
-- big conjunction to the single negated atom.   The recogniser machinery is
-- GENERIC in the code-builder ( KcodeCK : Fun1 ) and the projector ( out :
-- Fun1 ); the only shape-specific ingredients are  KcodeCK / projCK / outCK .
--
--   * projCK  : the "cEqTm -> cAp2f CK -> first-arg" projector ( clos §4(b) ),
--     path  Snd;Snd;Fst;Snd;Snd;Fst  ( vs  KdefConjRecog.projAtom 's final
--     Snd , because the subject is the FIRST  cAp2f  argument here ).
--   * KcodeCK : Fun1   ( = compile of an  AbsFun1.Exp ),  ap1 KcodeCK a =
--     cNeg (cEqTm (cAp2f CK (ap1 num a) (cVarc i1)) O)  ( PROVED ) -- the closed
--     code-builder the recogniser indicator needs ( cf.  KcodeConj N ).
--   * outCK = decode . projCK . thmT ;  outCK_correct  reads  a  NUM-RAW.
--   * hitCK / *_eval / *_le_one / dNeg_from_hitCK / hitCK_fires -- the
--     recogniser, verbatim from  KdefConjRecog  ( generic in  KcodeCK / out ).
--
-- Parametric in  CK : Fun2  ( = T4.CKMargin.CKr r k )  and the run-length
-- variable index  i1 : Nat  ( the coded  cVarc i1  slot ).

module T4.CKRecog where

open import T4.Base
open import T4.Tags using ( tag_neg ; tag_eq ; tag_ap2 ; tag_var )
open import T4.Code using ( codeFun2 )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.Decode using ( decode ; decode_num_id_at )
open import T4.DefWit using ( cEqTm ; cNeg )
open import T4.CgiClash using ( cAp2f ; cVarc )
open import T4.AbsFun1 using ( Exp ; evar ; econst ; eap1 ; eap2 ; denote
                             ; compile ; compile_eq )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; NoVar_natCode ; mkAnd )
open import T4.DoubleCodeNum using ( NoVar_codeFun2L )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_le_one )
open import T4.Bridge      using ( eqInd_sound )
open import T4.KFire       using ( eqInd_at_eq )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

-- CK : the closed characteristic ( = CKMargin.CKr r k );  i1 : run-length var.
module _ (CK : Fun2) (i1 : Nat) where

  ------------------------------------------------------------------------
  -- SECTION 0.  The atom / negated-atom code terms.

  atomCKcode : Term -> Term -> Term
  atomCKcode subj run = cEqTm (cAp2f CK subj run) O

  negCKcode : Term -> Term -> Term
  negCKcode subj run = cNeg (atomCKcode subj run)

  ------------------------------------------------------------------------
  -- SECTION 1.  The projector  projCK : Fun1  ( clos §4(b) ).

  projCK : Fun1
  projCK =
    compose1U Fst
      (compose1U Snd
        (compose1U Snd
          (compose1U Fst
            (compose1U Snd Snd))))

  projCK_at :
    (subj run : Term) ->
    Deriv (eqF (ap1 projCK (negCKcode subj run)) subj)
  projCK_at subj run =
    let t0 : Term
        t0 = negCKcode subj run

        L : Term
        L = ap2 Pair (natCode tag_ap2)
              (ap2 Pair (codeFun2 CK) (ap2 Pair subj run))
        Prun : Term
        Prun = ap2 Pair subj run
        Pcf : Term
        Pcf = ap2 Pair (codeFun2 CK) Prun
        Einner : Term
        Einner = ap2 Pair L O
        Eq2 : Term
        Eq2 = ap2 Pair (natCode tag_eq) Einner

        inner1 : Fun1
        inner1 = compose1U Snd Snd
        c3 : Fun1
        c3 = compose1U Fst inner1
        c4 : Fun1
        c4 = compose1U Snd c3
        c5 : Fun1
        c5 = compose1U Snd c4

        inner1_eq : Deriv (eqF (ap1 inner1 t0) Einner)
        inner1_eq =
          ruleTrans (compose1U_eq Snd Snd t0)
            (ruleTrans (cong1 Snd (axSnd (natCode tag_neg) Eq2))
                       (axSnd (natCode tag_eq) Einner))

        c3_eq : Deriv (eqF (ap1 c3 t0) L)
        c3_eq =
          ruleTrans (compose1U_eq Fst inner1 t0)
            (ruleTrans (cong1 Fst inner1_eq) (axFst L O))

        c4_eq : Deriv (eqF (ap1 c4 t0) Pcf)
        c4_eq =
          ruleTrans (compose1U_eq Snd c3 t0)
            (ruleTrans (cong1 Snd c3_eq) (axSnd (natCode tag_ap2) Pcf))

        c5_eq : Deriv (eqF (ap1 c5 t0) Prun)
        c5_eq =
          ruleTrans (compose1U_eq Snd c4 t0)
            (ruleTrans (cong1 Snd c4_eq) (axSnd (codeFun2 CK) Prun))
    in ruleTrans (compose1U_eq Fst c5 t0)
         (ruleTrans (cong1 Fst c5_eq) (axFst subj run))

  ------------------------------------------------------------------------
  -- SECTION 2.  The closed code-builder  KcodeCK : Fun1  (via AbsFun1).
  --   ap1 KcodeCK a = cNeg (cEqTm (cAp2f CK (ap1 num a) (cVarc i1)) O)  (PROVED).
  --   Only  num a  depends on  a  ( the  eap1 num evar  leaf ); everything else
  --   is a  NoVar  constant ( natCode tags, codeFun2 CK, cVarc i1, O ).

  -- single-var smart constructors (mirror ConjCodeExp's  enat2 / ecNeg2 / ...).
  enatE : Nat -> Exp
  enatE n = econst (natCode n) (NoVar_natCode n)

  epairE : Exp -> Exp -> Exp
  epairE a b = eap2 Pair a b

  -- NoVar (cVarc i1) = NoVar (Pair (natCode tag_var) (natCode i1)).
  nv_cVarc : NoVar (cVarc i1)
  nv_cVarc = mkAnd (NoVar_natCode tag_var) (NoVar_natCode i1)

  KExpCK : Exp
  KExpCK =
    epairE (enatE tag_neg)
      (epairE (enatE tag_eq)
        (epairE
          (epairE (enatE tag_ap2)
            (epairE (econst (codeFun2 CK) (NoVar_codeFun2L CK))
              (epairE (eap1 num evar) (econst (cVarc i1) nv_cVarc))))
          (econst O tt)))

  KcodeCK : Fun1
  KcodeCK = compile KExpCK

  -- denote KExpCK a  is DEFINITIONALLY  negCKcode (ap1 num a) (cVarc i1) .
  KcodeCK_eval :
    (a : Term) ->
    Deriv (eqF (ap1 KcodeCK a) (negCKcode (ap1 num a) (cVarc i1)))
  KcodeCK_eval a = compile_eq KExpCK a

  ------------------------------------------------------------------------
  -- SECTION 3.  The subject projector  outCK  and its NUM-RAW correctness.

  outCK : Fun1
  outCK = compose1U decode (compose1U projCK thmT)

  -- code-term form (run-length generic).
  outCK_correct :
    (w x0 run : Term) ->
    Deriv (eqF (ap1 thmT w) (negCKcode (ap1 num x0) run)) ->
    Deriv (eqF (ap1 outCK w) x0)
  outCK_correct w x0 run matched =
    let e1 : Deriv (eqF (ap1 outCK w)
                        (ap1 decode (ap1 (compose1U projCK thmT) w)))
        e1 = compose1U_eq decode (compose1U projCK thmT) w

        e2 : Deriv (eqF (ap1 (compose1U projCK thmT) w) (ap1 projCK (ap1 thmT w)))
        e2 = compose1U_eq projCK thmT w

        e3 : Deriv (eqF (ap1 projCK (ap1 thmT w)) (ap1 num x0))
        e3 = ruleTrans (cong1 projCK matched) (projCK_at (ap1 num x0) run)

        e4 : Deriv (eqF (ap1 decode (ap1 num x0)) x0)
        e4 = decode_num_id_at x0
    in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

  -- KcodeCK ( Fun1 ) form -- the shape the generic recogniser consumes.
  outCK_correct_K :
    (w x0 : Term) ->
    Deriv (eqF (ap1 thmT w) (ap1 KcodeCK x0)) ->
    Deriv (eqF (ap1 outCK w) x0)
  outCK_correct_K w x0 h =
    outCK_correct w x0 (cVarc i1) (ruleTrans h (KcodeCK_eval x0))

  ------------------------------------------------------------------------
  -- SECTION 4.  The recogniser indicator (verbatim from KdefConjRecog,
  --   generic in  KcodeCK / out ).

  hitCK : Fun1 -> Fun1
  hitCK out = C eqIndF thmT (compose1U KcodeCK out)

  hitCK_eval :
    (out : Fun1) (w : Term) ->
    Deriv (eqF (ap1 (hitCK out) w)
               (eqInd (ap1 thmT w) (ap1 KcodeCK (ap1 out w))))
  hitCK_eval out w =
    ruleTrans (ax_C eqIndF thmT (compose1U KcodeCK out) w)
      (ruleTrans (congR eqIndF (ap1 thmT w) (axComp KcodeCK out w))
                 (eqIndF_eq (ap1 thmT w) (ap1 KcodeCK (ap1 out w))))

  hitCK_le_one :
    (out : Fun1) (w : Term) ->
    Deriv (leq (ap1 (hitCK out) w) (ap1 s O))
  hitCK_le_one out w =
    let c0 : Term
        c0 = ap1 (hitCK out) w
        c1 : Term
        c1 = eqInd (ap1 thmT w) (ap1 KcodeCK (ap1 out w))
        rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
        rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
               (congL sub (ap1 s O) (hitCK_eval out w))
    in mp rw (eqInd_le_one (ap1 thmT w) (ap1 KcodeCK (ap1 out w)))

  dNeg_from_hitCK :
    (out : Fun1) (w0 : Term) ->
    Deriv (eqF (ap1 (hitCK out) w0) (ap1 s O)) ->
    Deriv (eqF (ap1 thmT w0) (ap1 KcodeCK (ap1 out w0)))
  dNeg_from_hitCK out w0 h =
    let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 KcodeCK (ap1 out w0)))
                           (ap1 s O))
        match = ruleTrans (ruleSym (hitCK_eval out w0)) h
    in eqInd_sound (ap1 thmT w0) (ap1 KcodeCK (ap1 out w0)) match

  hitCK_fires :
    (w x0 : Term) ->
    Deriv (eqF (ap1 thmT w) (ap1 KcodeCK x0)) ->
    Deriv (eqF (ap1 (hitCK outCK) w) (ap1 s O))
  hitCK_fires w x0 hyp =
    let A : Term
        A = ap1 thmT w
        B : Term
        B = ap1 KcodeCK (ap1 outCK w)
        bIsKx : Deriv (eqF B (ap1 KcodeCK x0))
        bIsKx = cong1 KcodeCK (outCK_correct_K w x0 hyp)
    in ruleTrans (hitCK_eval outCK w)
         (ruleTrans (ruleSym (eqIndF_eq A B))
           (ruleTrans (congL eqIndF B hyp)
             (ruleTrans (congR eqIndF (ap1 KcodeCK x0) bIsKx)
               (ruleTrans (eqIndF_eq (ap1 KcodeCK x0) (ap1 KcodeCK x0))
                 (eqInd_at_eq (ap1 KcodeCK x0))))))
