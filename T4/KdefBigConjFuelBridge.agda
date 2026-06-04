{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefBigConjFuelBridge -- the fuel-instantiated numeral bridge.
--
-- =====================================================================
-- WHY.
-- =====================================================================
--
-- The clash must instantiate the shared fuel  var 0  to a concrete common
-- fuel  F  ( >= all picks halting times AND the diagonal's nTerm ) BEFORE
-- the Sigma_1-lift, because  dKrest  ("T proves K_rest") is NOT a theorem
-- at open  var 0  ( T does not prove  forall x. K_rest(x) ).   So the input
-- D : imp K_rest (KdefBigConj M enum (natCode r))  is used via
-- ruleInst 0 F D , producing  substF zero F (KdefBigConj M enum (natCode r))
-- as the consequent.   To feed this to the ( now fuel-parametrised )
-- recogniser  KdefBigConjRecog  at  fuel := F , we need
--
--   numBridgeF :
--     Deriv (eqF (codeFormula (substF zero F (KdefBigConj M enum (natCode r))))
--                (ap1 (KcodeBC enum F M) (natCode r)))
--
-- Two pieces, both mechanical:
--   * distKBC : substF zero F (KdefBigConj M enum (natCode r))
--             = KdefBigConjF M (natCode r)   ( the explicit fuel-F framework
--     formula )  -- a META Eq by induction on M, using  substT_NoVar  on the
--     closed  natCode  sub-terms ( which  substT zero F  leaves fixed but does
--     NOT reduce on, since  natCode k  is stuck for a variable index ).
--   * numBridgeF_at : codeFormula (KdefBigConjF M (natCode r))
--                   = ap1 (KcodeBC enum F M) (natCode r)   -- the  numBridge
--     proof verbatim at fuel  F  ( the subject leaf  num_eq_code  congruence ).

module T4.KdefBigConjFuelBridge where

open import T4.Base
open import T4.Tags using ( tag_neg ; tag_eq ; tag_imp ; tag_ap1 ; tag_s )
open import T4.Code using ( codeFormula ; codeTerm )
open import T4.Num  using ( num )
open import T4.Kdef using ( runProg )
open import T4.IsNat using ( num_eq_code )
open import T4.NumContract using ( isNat_natCode )
open import T4.SubstNoVar using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import T4.SurpriseG2.KdefBigConj using ( KdefBigConj ; perProgNeg )
open import T4.KdefBigConjRecog
  using ( KBCcode ; perProgNegCodeBC ; lhsCode ; KcodeBC ; KcodeBC_eval )

open import BRA3.PairAlgebra using ( Pair )

module _ (enum : Fun1) (F : Term) where

  ----------------------------------------------------------------------
  -- The explicit fuel-F framework formula ( mirror of KdefBigConj, with
  -- the  runProg  fuel slot  F  in place of  var 0 ).

  perProgNegF : Term -> Nat -> Formula
  perProgNegF subj k =
    neg (eqF (ap2 runProg (ap1 enum (natCode k)) F) (ap1 s subj))

  KdefBigConjF : Nat -> Term -> Formula
  KdefBigConjF zero    subj = perProgNegF subj zero
  KdefBigConjF (suc M) subj =
    neg (imp (perProgNegF subj (suc M)) (neg (KdefBigConjF M subj)))

  ----------------------------------------------------------------------
  -- SECTION 1.  Distribution :  substF zero F (KdefBigConj M enum (natCode r))
  --   = KdefBigConjF M (natCode r) .   The fuel slot  var 0  becomes  F  (by
  --   reduction), the closed  natCode k / natCode r  sub-terms are fixed by
  --   substT_NoVar  ( they do NOT reduce, being stuck on a variable index ).

  -- per-conjunct distribution.
  distPP :
    (r k : Nat) ->
    Eq (substF zero F (perProgNeg enum (natCode r) k))
       (perProgNegF (natCode r) k)
  distPP r k =
    eqTrans
      (eqCong (\ X -> neg (eqF (ap2 runProg (ap1 enum X) F)
                                (ap1 s (substT zero F (natCode r)))))
              (substT_NoVar zero F (natCode k) (NoVar_natCode k)))
      (eqCong (\ Y -> neg (eqF (ap2 runProg (ap1 enum (natCode k)) F)
                                (ap1 s Y)))
              (substT_NoVar zero F (natCode r) (NoVar_natCode r)))

  distKBC :
    (M r : Nat) ->
    Eq (substF zero F (KdefBigConj M enum (natCode r)))
       (KdefBigConjF M (natCode r))
  distKBC zero    r = distPP r zero
  distKBC (suc M) r =
    eqTrans
      (eqCong (\ H -> neg (imp H
                            (neg (substF zero F (KdefBigConj M enum (natCode r))))))
              (distPP r (suc M)))
      (eqCong (\ T -> neg (imp (perProgNegF (natCode r) (suc M)) (neg T)))
              (distKBC M r))

  ----------------------------------------------------------------------
  -- SECTION 2.  numBridge at fuel  F  ( the  numBridge  proof verbatim, with
  --   F  in the fuel slot -- the subject-leaf  num_eq_code  congruence ).

  subjEq : (r : Nat) -> Deriv (eqF (codeTerm (natCode r)) (ap1 num (natCode r)))
  subjEq r = ruleSym (num_eq_code (natCode r) (isNat_natCode r))

  perProgBridgeF :
    (r k : Nat) ->
    Deriv (eqF (codeFormula (perProgNegF (natCode r) k))
               (perProgNegCodeBC enum F (natCode r) k))
  perProgBridgeF r k =
    congR Pair (natCode tag_neg)
      (congR Pair (natCode tag_eq)
        (congR Pair (lhsCode enum F k)
          (congR Pair (natCode tag_ap1)
            (congR Pair (natCode tag_s) (subjEq r)))))

  codeFormToKBCF :
    (M r : Nat) ->
    Deriv (eqF (codeFormula (KdefBigConjF M (natCode r)))
               (KBCcode enum F M (natCode r)))
  codeFormToKBCF zero    r = perProgBridgeF r zero
  codeFormToKBCF (suc M) r =
    let a : Term
        a = natCode r

        e_head : Deriv (eqF (codeFormula (perProgNegF a (suc M)))
                            (perProgNegCodeBC enum F a (suc M)))
        e_head = perProgBridgeF r (suc M)

        e_tail : Deriv (eqF (codeFormula (KdefBigConjF M a))
                            (KBCcode enum F M a))
        e_tail = codeFormToKBCF M r

        TT : Term
        TT = ap2 Pair (natCode tag_neg) (codeFormula (KdefBigConjF M a))

        innerHead :
          Deriv (eqF (ap2 Pair (codeFormula (perProgNegF a (suc M))) TT)
                     (ap2 Pair (perProgNegCodeBC enum F a (suc M)) TT))
        innerHead = congL Pair TT e_head

        innerTail :
          Deriv (eqF (ap2 Pair (perProgNegCodeBC enum F a (suc M)) TT)
                     (ap2 Pair (perProgNegCodeBC enum F a (suc M))
                        (ap2 Pair (natCode tag_neg) (KBCcode enum F M a))))
        innerTail =
          congR Pair (perProgNegCodeBC enum F a (suc M))
            (congR Pair (natCode tag_neg) e_tail)

        inner :
          Deriv (eqF (ap2 Pair (codeFormula (perProgNegF a (suc M))) TT)
                     (ap2 Pair (perProgNegCodeBC enum F a (suc M))
                        (ap2 Pair (natCode tag_neg) (KBCcode enum F M a))))
        inner = ruleTrans innerHead innerTail
    in congR Pair (natCode tag_neg)
         (congR Pair (natCode tag_imp) inner)

  numBridgeF_at :
    (M r : Nat) ->
    Deriv (eqF (codeFormula (KdefBigConjF M (natCode r)))
               (ap1 (KcodeBC enum F M) (natCode r)))
  numBridgeF_at M r =
    ruleTrans (codeFormToKBCF M r) (ruleSym (KcodeBC_eval enum F M (natCode r)))

  ----------------------------------------------------------------------
  -- SECTION 3.  The headline fuel-F bridge ( from the  substF -instantiated
  --   consequent of  ruleInst 0 F D  to the recogniser shape ).

  numBridgeF :
    (M r : Nat) ->
    Deriv (eqF (codeFormula (substF zero F (KdefBigConj M enum (natCode r))))
               (ap1 (KcodeBC enum F M) (natCode r)))
  numBridgeF M r =
    eqSubst (\ P -> Deriv (eqF (codeFormula P)
                               (ap1 (KcodeBC enum F M) (natCode r))))
            (eqSym (distKBC M r))
            (numBridgeF_at M r)
