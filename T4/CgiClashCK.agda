{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashCK -- surprise-GII task (b): the characteristic-function-shape
-- Chaitin clash + its re-pointed recogniser projector.
--
-- This is the CK-route analog of  T4.CgiClash , re-pointed from the OLD
-- single-conjunct  Kdef L x = imp (szLeq p = 1) (neg (definable p x n))  shape
-- ( two free object vars  p / n , a size antecedent ) to the clos-corrected.md
-- SINGLE-ATOM characteristic-function shape:  the stage predicate is
--
--   S(r) := neg (eqF (ap2 CK (var x0) (var x1)) O)
--
-- whose code is  cNeg (cEqTm (cAp2f CK (..x0..) (cVarc x1)) O)  ( T4.CKMargin 's
-- charNegR ).  This route is STRUCTURALLY SIMPLER than  CgiClash :
--   * NO size predicate / no  encoded_mp  to strip an antecedent ;
--   * NO free program variable to substitute ( CK : Fun2  is a CLOSED
--     combinator , the subject  x0  already num-raw from Step 2 ) ;
--   * the ONLY substitution is the diagonal's  ruleInst  of the coded
--     run-length  cVarc x1 ↦ nTerm  ( concrete halting fuel ) at the clash.
--
-- TWO deliverables, both verified :
--   (1) the re-pointed RECOGNISER PROJECTOR  outCK : Fun1  ( the literal
--       "cEqTm → cAp2f CK → first-arg" projector of clos-corrected.md §4(b) ) +
--       outCK_correct  ( reads  x0  back NUM-RAW :  decode (ap1 num x0) = x0 ) ;
--   (2) the clash  cgiClashCK , around the shipped  T4.ChaitinG1
--       .chaitin_G1_assembly , riding on  thmT_at_sb / sbt_at_var_match  for the
--       run-length instantiation and  encoded_exfalso  for the ex-falso leg.
--
-- Parametric in the closed characteristic  CK : Fun2  ( supplied as
-- T4.CKMargin 's  CKr r k  downstream ).  The positive leg  dPos  ( the
-- diagonal actually defines  x0  at fuel  nT ) and the recogniser-firing
-- dNeg  are inputs ( as in  CgiClash ) -- the enum-identification / run facts
-- that produce them are Steps 1-6 content ( task (d) ), supplied by the
-- re-pointed discharge/chain.

module T4.CgiClashCK where

open import T4.Base
open import T4.Tags using ( tag_sb ; tag_neg ; tag_eq ; tag_ap2 )
open import T4.Code using ( codeFun2 ; codeFalse )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.Decode using ( decode ; decode_num_id_at )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt )
open import T4.SbtAtVar using ( sbt_at_var_match )
open import T4.NumInert using ( sbt_num_inert )
open import T4.SbStep using
  ( sbf_step_atomic ; sbf_step_neg ; sbt_step_ap2 ; NumCode ; ncO
  ; sbt_inert_NumCode )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.ConInj using ( cmp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.ChaitinG1 using ( chaitin_G1_assembly )
open import T4.CgiClash using ( cAp2f ; cVarc ; SomeProof ; mkProof )
open import T4.CKRecog using ( KcodeCK ; KcodeCK_eval )

open import BRA3.Church      using ( pi )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

-- CK : the closed characteristic program ( = T4.CKMargin.CKr r k ).
module _ (CK : Fun2) where

  ------------------------------------------------------------------------
  -- SECTION 0.  The atom / negated-atom code terms.
  --   atomCKcode subj run = cEqTm (cAp2f CK subj run) O      -- "CK subj run = O"
  --   negCKcode  subj run = cNeg (atomCKcode subj run)       -- its negation

  atomCKcode : Term -> Term -> Term
  atomCKcode subj run = cEqTm (cAp2f CK subj run) O

  negCKcode : Term -> Term -> Term
  negCKcode subj run = cNeg (atomCKcode subj run)

  ------------------------------------------------------------------------
  -- SECTION 1.  The re-pointed projector  projCK : Fun1  ( clos §4(b) ).
  --   negCKcode subj run = cNeg (cEqTm (cAp2f CK subj run) O)
  --     = Pair(tag_neg, Pair(tag_eq, Pair( Pair(tag_ap2, Pair(cf2, Pair(subj,run))), O )))
  --   so the path to the FIRST argument  subj  is  Snd ; Snd ; Fst ; Snd ; Snd ; Fst
  --   ( cf. KdefConjRecog.projAtom 's  Snd;Snd;Fst;Snd;Snd;Snd , whose subject was
  --     the SECOND  cAp2f  argument -- the final  Snd  becomes  Fst  here ).

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

        L : Term                          -- cAp2f CK subj run
        L = ap2 Pair (natCode tag_ap2)
              (ap2 Pair (codeFun2 CK) (ap2 Pair subj run))
        Prun : Term                       -- Pair(subj, run)
        Prun = ap2 Pair subj run
        Pcf : Term                        -- Pair(codeFun2 CK, Prun)
        Pcf = ap2 Pair (codeFun2 CK) Prun
        Einner : Term                     -- Pair(L, O)
        Einner = ap2 Pair L O
        Eq2 : Term                        -- Pair(tag_eq, Einner)  = cEqTm L O
        Eq2 = ap2 Pair (natCode tag_eq) Einner

        inner1 : Fun1
        inner1 = compose1U Snd Snd
        c3 : Fun1
        c3 = compose1U Fst inner1
        c4 : Fun1
        c4 = compose1U Snd c3
        c5 : Fun1
        c5 = compose1U Snd c4

        -- op1,op2:  strip cNeg, strip tag_eq  ->  Einner = Pair(L,O).
        inner1_eq : Deriv (eqF (ap1 inner1 t0) Einner)
        inner1_eq =
          ruleTrans (compose1U_eq Snd Snd t0)
            (ruleTrans (cong1 Snd (axSnd (natCode tag_neg) Eq2))
                       (axSnd (natCode tag_eq) Einner))

        -- op3:  Fst  ->  L .
        c3_eq : Deriv (eqF (ap1 c3 t0) L)
        c3_eq =
          ruleTrans (compose1U_eq Fst inner1 t0)
            (ruleTrans (cong1 Fst inner1_eq)
                       (axFst L O))

        -- op4:  Snd  ->  Pcf = Pair(codeFun2 CK, Prun) .
        c4_eq : Deriv (eqF (ap1 c4 t0) Pcf)
        c4_eq =
          ruleTrans (compose1U_eq Snd c3 t0)
            (ruleTrans (cong1 Snd c3_eq)
                       (axSnd (natCode tag_ap2) Pcf))

        -- op5:  Snd  ->  Prun = Pair(subj, run) .
        c5_eq : Deriv (eqF (ap1 c5 t0) Prun)
        c5_eq =
          ruleTrans (compose1U_eq Snd c4 t0)
            (ruleTrans (cong1 Snd c4_eq)
                       (axSnd (codeFun2 CK) Prun))
    in ruleTrans (compose1U_eq Fst c5 t0)
         (ruleTrans (cong1 Fst c5_eq)
                    (axFst subj run))

  ------------------------------------------------------------------------
  -- SECTION 2.  The subject projector  outCK  and its NUM-RAW correctness.
  --   outCK = decode . projCK . thmT ;  reads  x0  out of the num-raw slot.

  outCK : Fun1
  outCK = compose1U decode (compose1U projCK thmT)

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

  ------------------------------------------------------------------------
  -- SECTION 3.  The single substitution pass over  negCKcode .
  --   sbf spec (cNeg (cEqTm (cAp2f CK subj run) O))
  --     = cNeg (cEqTm (cAp2f CK subj' run') O)
  --   ( O  is inert by  ncO ; the functor code  codeFun2 CK  stays opaque ).

  passCK :
    (k : Nat) (S subj subj' run run' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) subj) subj') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) run) run') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (negCKcode subj run))
                (negCKcode subj' run'))
  passCK k S subj subj' run run' eSubj eRun =
    let spec : Term
        spec = ap2 Pair (natCode k) S

        e_atomL : Deriv (eqF (ap2 sbt spec (cAp2f CK subj run))
                              (cAp2f CK subj' run'))
        e_atomL = sbt_step_ap2 k S CK subj run subj' run' eSubj eRun

        e_O : Deriv (eqF (ap2 sbt spec O) O)
        e_O = sbt_inert_NumCode O ncO k S

        e_atom : Deriv (eqF (ap2 sbf spec (atomCKcode subj run))
                             (atomCKcode subj' run'))
        e_atom = sbf_step_atomic k S (cAp2f CK subj run) O
                   (cAp2f CK subj' run') O e_atomL e_O
    in sbf_step_neg k S (atomCKcode subj run) (atomCKcode subj' run') e_atom

  ------------------------------------------------------------------------
  -- SECTION 4.  The clash.
  --   Inputs ( as in  CgiClash ) :
  --     dNeg : T proves  neg(CK x0 x1 = O)  with the run-length still the CODED
  --            variable  cVarc i1  ( the open derivation = "forall run-length" );
  --     dPos : T proves  CK x0 nT = O  at the diagonal's CONCRETE halting fuel
  --            nT  ( the diagonal defines  x0  -- Steps 1/4/6, thm13/dPos ).
  --   Body: instantiate  cVarc i1 ↦ nT  by  thmT_at_sb + sbt_at_var_match
  --   ( the subject  num x0  stays inert ), then  chaitin_G1_assembly .

  cgiClashCK :
    (x0 nT w0 cPos : Term) (i1 : Nat) ->
    Deriv (eqF (ap1 thmT w0)   (negCKcode (ap1 num x0) (cVarc i1))) ->
    Deriv (eqF (ap1 thmT cPos) (atomCKcode (ap1 num x0) nT)) ->
    SomeProof
  cgiClashCK x0 nT w0 cPos i1 dNeg dPos =
    let spec1 : Term
        spec1 = ap2 Pair (natCode i1) nT

        Dpos : Term                                   -- the positive atom at fuel nT
        Dpos = atomCKcode (ap1 num x0) nT

        -- instantiate the coded run-length  cVarc i1 ↦ nT  ( subject num-raw inert ).
        subEq : Deriv (eqF (ap2 sbf spec1 (negCKcode (ap1 num x0) (cVarc i1)))
                            (cNeg Dpos))
        subEq =
          passCK i1 nT (ap1 num x0) (ap1 num x0) (cVarc i1) nT
            (sbt_num_inert i1 nT x0)
            (sbt_at_var_match i1 nT)

        wrap : Term
        wrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)

        dNegFinal : Deriv (eqF (ap1 thmT wrap) (cNeg Dpos))
        dNegFinal =
          ruleTrans (thmT_at_sb spec1 w0)
            (ruleTrans (congR sbf spec1 dNeg) subEq)

        dExF : Deriv (eqF (ap1 thmT (exfProof Dpos codeFalse))
                           (cImp Dpos (cImp (cNeg Dpos) codeFalse)))
        dExF = encoded_exfalso Dpos codeFalse

        final : Deriv (eqF (ap1 thmT
                             (cmp (cmp (exfProof Dpos codeFalse) cPos) wrap))
                            codeFalse)
        final = chaitin_G1_assembly Dpos cPos (exfProof Dpos codeFalse) wrap
                  dPos dNegFinal dExF
    in mkProof
         (cmp (cmp (exfProof Dpos codeFalse) cPos) wrap)
         final

  ------------------------------------------------------------------------
  -- SECTION 5.  The clash in the  KcodeCK  ( discharge-output ) form.
  --   T4.DischargeCK.dNeg_at_kmax  delivers  dNeg  as  thmT w0 = ap1 (KcodeCK
  --   CK i1) x0 ;  KcodeCK_eval  rewrites it to the  negCKcode  form  cgiClashCK
  --   consumes ( the two  negCKcode  defs are definitionally identical ).  So
  --   the discharge feeds this directly ( w0 := k_max , x0 := x' ).

  cgiClashCK_K :
    (x0 nT w0 cPos : Term) (i1 : Nat) ->
    Deriv (eqF (ap1 thmT w0)   (ap1 (KcodeCK CK i1) x0)) ->
    Deriv (eqF (ap1 thmT cPos) (atomCKcode (ap1 num x0) nT)) ->
    SomeProof
  cgiClashCK_K x0 nT w0 cPos i1 dNegK dPos =
    cgiClashCK x0 nT w0 cPos i1
      (ruleTrans dNegK (KcodeCK_eval CK i1 x0)) dPos
