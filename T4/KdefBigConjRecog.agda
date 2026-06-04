{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefBigConjRecog -- the recognition bridge at the FRAMEWORK's
-- KdefBigConj  big-conjunction shape (T4.SurpriseG2.KdefBigConj), the
-- subject sitting in the  ap1 s -OUTPUT slot ( day-incompressibility,
-- Kritchman-Raz "K(r) > L" ), NOT the  ap1 num -DATA slot of the block-4
-- DefinePExp  Kfunctor  shape.
--
-- =====================================================================
-- WHY A FRESH RECOGNISER (plan B).
-- =====================================================================
--
-- The shipped block-4 recogniser ( T4.KdefConjRecog ) reads the subject
-- out of the  ap2 runProg _ (num a)  data slot, with output  s (natCode j)
-- VARYING per conjunct index  j .   The framework's  KdefBigConj M enum
-- subject  has the subject in the  ap1 s subject  OUTPUT slot ( CONSTANT
-- across all  M+1  conjuncts ) and the data slot holds the free fuel
-- var 0 .   These are structurally different formulas, so the block-4
-- recogniser does NOT apply by a bridge ( see SURPRISE-GII-DAYCLASH-
-- HANDOFF.md "block-4 does NOT bridge to KdefBigConj" ).
--
-- This file ships the recogniser at the  KdefBigConj  shape : the
-- recogniser machinery of  T4.KdefConjRecog / T4.CKRecog  is GENERIC in
-- the code-builder  ( KcodeBC M : Fun1 )  and the projector  ( out :
-- Fun1 ); the only shape-specific ingredients are  KcodeBC / projConjBC /
-- outBC_correct , so we ship exactly those and re-derive the four
-- recogniser facts verbatim.
--
--   * KcodeBC M : Fun1   -- the NUM-RAW conjunction code-builder ( via
--       AbsFun1 ).   ap1 (KcodeBC M) a = KBCcode M a , the right-nested
--        cAnd  of  M+1  per-program negs, each with  ap1 num a  in the
--        ap1 s -OUTPUT slot ( recogniser-readable ).
--   * projConjBC M : Fun1 = projAtomBC  ( N=0 )  /  projAtomBC . headProj
--       ( N=suc )  reads the subject  num a  back out of the FIRST
--       ( highest-index ) conjunct's  ap1 s -slot.
--   * outBC M = decode . projConjBC M . thmT .
--   * outBC_correct : thmT w = ap1 (KcodeBC M) x'  ==>  outBC M w = x'
--       ( num-raw, via  decode_num_id_at ).
--   * hitBC / *_eval / *_le_one / dNeg_from_hitBC / hitBC_fires .
--
-- The subject the framework actually proves about is the numeral
--  natCode r ; the bridge  codeFormula (KdefBigConj M enum (natCode r)) =
-- ap1 (KcodeBC M) (natCode r)  ( the  num_eq_code  install at the numeral
-- subject ) is shipped separately ( T4.KdefBigConjNumBridge ).

module T4.KdefBigConjRecog where

open import T4.Base
open import T4.Tags using ( tag_neg ; tag_eq ; tag_imp ; tag_ap1 ; tag_ap2
                          ; tag_var ; tag_s )
open import T4.Code using ( codeTerm ; codeFun1 ; codeFun2 )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.Kdef using ( runProg )
open import T4.Decode using ( decode ; decode_num_id_at )
open import T4.AbsFun1 using ( Exp ; evar ; econst ; eap1 ; eap2 ; denote
                             ; compile ; compile_eq )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; NoVarAnd ; mkAnd ; NoVar_natCode )
open import T4.DoubleCodeNum using ( NoVar_codeFun1L ; NoVar_codeFun2L )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_le_one )
open import T4.Bridge      using ( eqInd_sound )
open import T4.KFire       using ( eqInd_at_eq )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( Pair ; compose1U ; compose1U_eq ; axComp )

------------------------------------------------------------------------
-- SECTION 0.  NoVar (codeTerm t)  for ANY  t  ( codeTerm is a pure code ).

NoVar_codeTerm : (t : Term) -> NoVar (codeTerm t)
NoVar_codeTerm O           = tt
NoVar_codeTerm (var k)     = mkAnd (NoVar_natCode tag_var) (NoVar_natCode k)
NoVar_codeTerm (ap1 f t)   =
  mkAnd (NoVar_natCode tag_ap1)
    (mkAnd (NoVar_codeFun1L f) (NoVar_codeTerm t))
NoVar_codeTerm (ap2 g a b) =
  mkAnd (NoVar_natCode tag_ap2)
    (mkAnd (NoVar_codeFun2L g)
      (mkAnd (NoVar_codeTerm a) (NoVar_codeTerm b)))

-- enum : the enumerator of Berry's finite program set.
-- fuel : the fuel term in the  runProg  slot ( = var 0 for the framework's
--   open  KdefBigConj ; = a closed common fuel  F  for the instantiated
--   clash ).   The recogniser/projector are OBLIVIOUS to its value -- it
--   sits in  lhsCode , a NoVar constant the projector skips -- so the whole
--   stack is generic in  fuel .
module _ (enum : Fun1) (fuel : Term) where

  ----------------------------------------------------------------------
  -- SECTION 1.  The num-raw code terms ( mirror KdefBigConj.perProgNeg /
  --   KdefBigConj , with the subject  num a  in the  ap1 s -output slot ).

  -- the LHS  ap2 runProg (ap1 enum (natCode k)) fuel  code ( NoVar const ).
  lhsCode : Nat -> Term
  lhsCode k = codeTerm (ap2 runProg (ap1 enum (natCode k)) fuel)

  NoVar_lhsCode : (k : Nat) -> NoVar (lhsCode k)
  NoVar_lhsCode k =
    NoVar_codeTerm (ap2 runProg (ap1 enum (natCode k)) fuel)

  -- the  ap1 s a  output slot ( num-raw :  ap1 num a ).
  outSlot : Term -> Term
  outSlot a = ap2 Pair (natCode tag_ap1) (ap2 Pair (natCode tag_s) (ap1 num a))

  -- codeFormula (perProgNeg enum a k) , num-raw at the subject.
  perProgNegCodeBC : Term -> Nat -> Term
  perProgNegCodeBC a k =
    ap2 Pair (natCode tag_neg)
      (ap2 Pair (natCode tag_eq)
        (ap2 Pair (lhsCode k) (outSlot a)))

  -- the standard And-encoding  conjF X Y = neg (imp X (neg Y)) , coded.
  cAndBC : Term -> Term -> Term
  cAndBC X Y =
    ap2 Pair (natCode tag_neg)
      (ap2 Pair (natCode tag_imp)
        (ap2 Pair X (ap2 Pair (natCode tag_neg) Y)))

  -- codeFormula (KdefBigConj M enum a) , num-raw at the subject.
  KBCcode : Nat -> Term -> Term
  KBCcode zero    a = perProgNegCodeBC a zero
  KBCcode (suc M) a = cAndBC (perProgNegCodeBC a (suc M)) (KBCcode M a)

  ----------------------------------------------------------------------
  -- SECTION 2.  The closed code-builder  KcodeBC M : Fun1  (via AbsFun1).

  enatE : Nat -> Exp
  enatE n = econst (natCode n) (NoVar_natCode n)

  epair : Exp -> Exp -> Exp
  epair a b = eap2 Pair a b

  -- the  ap1 s (num evar)  output slot, with the subject leaf  eap1 num evar .
  outSlotExp : Exp
  outSlotExp = epair (enatE tag_ap1) (epair (enatE tag_s) (eap1 num evar))

  lhsExp : Nat -> Exp
  lhsExp k = econst (lhsCode k) (NoVar_lhsCode k)

  perProgNegExpBC : Nat -> Exp
  perProgNegExpBC k =
    epair (enatE tag_neg)
      (epair (enatE tag_eq)
        (epair (lhsExp k) outSlotExp))

  cAndExp : Exp -> Exp -> Exp
  cAndExp X Y =
    epair (enatE tag_neg)
      (epair (enatE tag_imp)
        (epair X (epair (enatE tag_neg) Y)))

  KExpBC : Nat -> Exp
  KExpBC zero    = perProgNegExpBC zero
  KExpBC (suc M) = cAndExp (perProgNegExpBC (suc M)) (KExpBC M)

  -- denote KExpBC M a  is  KBCcode M a  ( base by refl, step by congruence ).
  KExpBC_pin :
    (M : Nat) (a : Term) -> Eq (denote (KExpBC M) a) (KBCcode M a)
  KExpBC_pin zero    a = refl
  KExpBC_pin (suc M) a =
    eqCong (\ z -> cAndBC (perProgNegCodeBC a (suc M)) z) (KExpBC_pin M a)

  KcodeBC : Nat -> Fun1
  KcodeBC M = compile (KExpBC M)

  KcodeBC_eval :
    (M : Nat) (a : Term) ->
    Deriv (eqF (ap1 (KcodeBC M) a) (KBCcode M a))
  KcodeBC_eval M a =
    eqSubst (\ z -> Deriv (eqF (ap1 (KcodeBC M) a) z))
            (KExpBC_pin M a)
            (compile_eq (KExpBC M) a)

  ----------------------------------------------------------------------
  -- SECTION 3.  The atom projector  projAtomBC  ( to  num a  under  ap1 s ).
  --   perProgNegCodeBC a k =
  --     Pair tag_neg (Pair tag_eq (Pair (lhsCode k)
  --        (Pair tag_ap1 (Pair tag_s (num a))))) ,
  --   so the path to  num a  is  Snd ; Snd ; Snd ; Snd ; Snd .

  projAtomBC : Fun1
  projAtomBC =
    compose1U Snd
      (compose1U Snd
        (compose1U Snd
          (compose1U Snd Snd)))

  projAtomBC_at :
    (a : Term) (k : Nat) ->
    Deriv (eqF (ap1 projAtomBC (perProgNegCodeBC a k)) (ap1 num a))
  projAtomBC_at a k =
    let t0 : Term
        t0 = perProgNegCodeBC a k

        Pinner : Term                        -- Pair tag_s (num a)
        Pinner = ap2 Pair (natCode tag_s) (ap1 num a)
        Pout : Term                          -- outSlot a = Pair tag_ap1 Pinner
        Pout = ap2 Pair (natCode tag_ap1) Pinner
        Pbody : Term                         -- Pair (lhsCode k) (outSlot a)
        Pbody = ap2 Pair (lhsCode k) Pout
        Peq : Term                           -- Pair tag_eq Pbody
        Peq = ap2 Pair (natCode tag_eq) Pbody

        c1 : Fun1                            -- innermost: Snd ; Snd
        c1 = compose1U Snd Snd
        c2 : Fun1
        c2 = compose1U Snd c1
        c3 : Fun1
        c3 = compose1U Snd c2

        -- c1 t0 = Pbody  (strip tag_neg, strip tag_eq).
        c1_eq : Deriv (eqF (ap1 c1 t0) Pbody)
        c1_eq =
          ruleTrans (compose1U_eq Snd Snd t0)
            (ruleTrans (cong1 Snd (axSnd (natCode tag_neg) Peq))
                       (axSnd (natCode tag_eq) Pbody))

        -- c2 t0 = outSlot a  (take the eqF RHS).
        c2_eq : Deriv (eqF (ap1 c2 t0) Pout)
        c2_eq =
          ruleTrans (compose1U_eq Snd c1 t0)
            (ruleTrans (cong1 Snd c1_eq) (axSnd (lhsCode k) Pout))

        -- c3 t0 = Pinner  (strip tag_ap1).
        c3_eq : Deriv (eqF (ap1 c3 t0) Pinner)
        c3_eq =
          ruleTrans (compose1U_eq Snd c2 t0)
            (ruleTrans (cong1 Snd c2_eq) (axSnd (natCode tag_ap1) Pinner))
    in ruleTrans (compose1U_eq Snd c3 t0)
         (ruleTrans (cong1 Snd c3_eq) (axSnd (natCode tag_s) (ap1 num a)))

  ----------------------------------------------------------------------
  -- SECTION 4.  The conjunction head projector  headProj  ( verbatim from
  --   KdefConjRecog : cAndBC X Y -> X ,  path  Fst ; Snd ; Snd ).

  headProj : Fun1
  headProj = compose1U Fst (compose1U Snd Snd)

  headProj_at :
    (X Y : Term) ->
    Deriv (eqF (ap1 headProj (cAndBC X Y)) X)
  headProj_at X Y =
    let cAndXY : Term
        cAndXY = cAndBC X Y
        Z : Term
        Z = ap2 Pair (natCode tag_imp) (ap2 Pair X (ap2 Pair (natCode tag_neg) Y))
        W : Term
        W = ap2 Pair X (ap2 Pair (natCode tag_neg) Y)

        ssEq : Deriv (eqF (ap1 (compose1U Snd Snd) cAndXY) W)
        ssEq = ruleTrans (compose1U_eq Snd Snd cAndXY)
                 (ruleTrans (cong1 Snd (axSnd (natCode tag_neg) Z))
                            (axSnd (natCode tag_imp) W))
    in ruleTrans (compose1U_eq Fst (compose1U Snd Snd) cAndXY)
         (ruleTrans (cong1 Fst ssEq)
                    (axFst X (ap2 Pair (natCode tag_neg) Y)))

  projConjBC : Nat -> Fun1
  projConjBC zero    = projAtomBC
  projConjBC (suc n) = compose1U projAtomBC headProj

  projConjBC_at :
    (M : Nat) (a : Term) ->
    Deriv (eqF (ap1 (projConjBC M) (KBCcode M a)) (ap1 num a))
  projConjBC_at zero    a = projAtomBC_at a zero
  projConjBC_at (suc n) a =
    ruleTrans (compose1U_eq projAtomBC headProj (KBCcode (suc n) a))
      (ruleTrans (cong1 projAtomBC
                    (headProj_at (perProgNegCodeBC a (suc n)) (KBCcode n a)))
                 (projAtomBC_at a (suc n)))

  ----------------------------------------------------------------------
  -- SECTION 5.  The subject projector  outBC  and its num-raw correctness.

  outBC : Nat -> Fun1
  outBC M = compose1U decode (compose1U (projConjBC M) thmT)

  outBC_correct :
    (M : Nat) (w x' : Term) ->
    Deriv (eqF (ap1 thmT w) (ap1 (KcodeBC M) x')) ->
    Deriv (eqF (ap1 (outBC M) w) x')
  outBC_correct M w x' matched =
    let e1 : Deriv (eqF (ap1 (outBC M) w)
                        (ap1 decode (ap1 (compose1U (projConjBC M) thmT) w)))
        e1 = compose1U_eq decode (compose1U (projConjBC M) thmT) w

        e2 : Deriv (eqF (ap1 (compose1U (projConjBC M) thmT) w)
                        (ap1 (projConjBC M) (ap1 thmT w)))
        e2 = compose1U_eq (projConjBC M) thmT w

        e3 : Deriv (eqF (ap1 (projConjBC M) (ap1 thmT w)) (ap1 num x'))
        e3 = ruleTrans (cong1 (projConjBC M)
                          (ruleTrans matched (KcodeBC_eval M x')))
                       (projConjBC_at M x')

        e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
        e4 = decode_num_id_at x'
    in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

  ----------------------------------------------------------------------
  -- SECTION 6.  The recogniser indicator ( generic; verbatim from
  --   KdefConjRecog / CKRecog , in  KcodeBC M / out ).

  hitBC : Nat -> Fun1 -> Fun1
  hitBC M out = C eqIndF thmT (compose1U (KcodeBC M) out)

  hitBC_eval :
    (M : Nat) (out : Fun1) (w : Term) ->
    Deriv (eqF (ap1 (hitBC M out) w)
               (eqInd (ap1 thmT w) (ap1 (KcodeBC M) (ap1 out w))))
  hitBC_eval M out w =
    ruleTrans (ax_C eqIndF thmT (compose1U (KcodeBC M) out) w)
      (ruleTrans (congR eqIndF (ap1 thmT w) (axComp (KcodeBC M) out w))
                 (eqIndF_eq (ap1 thmT w) (ap1 (KcodeBC M) (ap1 out w))))

  hitBC_le_one :
    (M : Nat) (out : Fun1) (w : Term) ->
    Deriv (leq (ap1 (hitBC M out) w) (ap1 s O))
  hitBC_le_one M out w =
    let c0 : Term
        c0 = ap1 (hitBC M out) w
        c1 : Term
        c1 = eqInd (ap1 thmT w) (ap1 (KcodeBC M) (ap1 out w))
        rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
        rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
               (congL sub (ap1 s O) (hitBC_eval M out w))
    in mp rw (eqInd_le_one (ap1 thmT w) (ap1 (KcodeBC M) (ap1 out w)))

  dNeg_from_hitBC :
    (M : Nat) (out : Fun1) (w0 : Term) ->
    Deriv (eqF (ap1 (hitBC M out) w0) (ap1 s O)) ->
    Deriv (eqF (ap1 thmT w0) (ap1 (KcodeBC M) (ap1 out w0)))
  dNeg_from_hitBC M out w0 h =
    let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 (KcodeBC M) (ap1 out w0)))
                           (ap1 s O))
        match = ruleTrans (ruleSym (hitBC_eval M out w0)) h
    in eqInd_sound (ap1 thmT w0) (ap1 (KcodeBC M) (ap1 out w0)) match

  hitBC_fires :
    (M : Nat) (w x : Term) ->
    Deriv (eqF (ap1 thmT w) (ap1 (KcodeBC M) x)) ->
    Deriv (eqF (ap1 (hitBC M (outBC M)) w) (ap1 s O))
  hitBC_fires M w x hyp =
    let A : Term
        A = ap1 thmT w
        B : Term
        B = ap1 (KcodeBC M) (ap1 (outBC M) w)
        bIsKx : Deriv (eqF B (ap1 (KcodeBC M) x))
        bIsKx = cong1 (KcodeBC M) (outBC_correct M w x hyp)
    in ruleTrans (hitBC_eval M (outBC M) w)
         (ruleTrans (ruleSym (eqIndF_eq A B))
           (ruleTrans (congL eqIndF B hyp)
             (ruleTrans (congR eqIndF (ap1 (KcodeBC M) x) bIsKx)
               (ruleTrans (eqIndF_eq (ap1 (KcodeBC M) x) (ap1 (KcodeBC M) x))
                 (eqInd_at_eq (ap1 (KcodeBC M) x))))))
