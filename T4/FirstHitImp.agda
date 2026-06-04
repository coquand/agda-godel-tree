{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FirstHitImp -- Carneiro-lifted (imp Rf) version of FirstHit's
-- least-number lemma.
--
-- In T4/FirstHit.agda the module Search exports
--   least_hit  : (B : Term) -> Deriv (eqF (ap1 p B) (ap1 s O))
--                            -> Deriv (eqF (ap1 p (g (s B))) (ap1 s O))
--   least_first : closed
--   leastNumber : record-package
--
-- Among these, only  least_hit  is h-DEPENDENT (it consumes the firing
-- witness ).   least_first  is closed.   We provide the Carneiro-lifted
--   imp_least_hit  +  imp_LeastNumber  (record-package with imp-lifted
-- isHit field; isFirst stays closed).

module T4.FirstHitImp where

open import T4.Base
open import T4.Code        using ( falseF )
open import T4.ImpExtras   using ( imp_byCases ; imp_compI )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impCong1 ; impRuleSym )

open import T4.ExistsHit using ( le_one_neq_zero )

open import BRA3.ChurchT80 using ( exFalsoFromSO )
open import BRA3.Contrapositive using ( compI ; bComb ; identP ; liftP )
open import BRA3.Logic          using ( prependEqLeft ; appendEqRight
                                       ; impTrans ; eqSymImp )
open import BRA3.ChurchLeq      using ( leq )

import T4.FirstHit

------------------------------------------------------------------------
-- imp-lifted Search module.   Parametric in the same  (p, p_le_one) .

module SearchImp
  (p : Fun1)
  (p_le_one : (r : Term) -> Deriv (leq (ap1 p r) (ap1 s O)))
  where

  open T4.FirstHit.Search p p_le_one
    using ( g ; gRec ; gStep ; compInv ; gSuccHit ; firstnessU ; least_first )

  ----------------------------------------------------------------------
  -- imp_least_hit -- the Carneiro-lifted least-hit lemma.
  --
  -- Replays the body of  least_hit  with the  witness  step
  --   prependEqLeft (s O) (p B) O (ruleSym witness)
  -- lifted under  imp Rf .

  imp_least_hit :
    (Rf : Formula) (B : Term) ->
    Deriv (imp Rf (eqF (ap1 p B) (ap1 s O))) ->
    Deriv (imp Rf (eqF (ap1 p (g (ap1 s B))) (ap1 s O)))
  imp_least_hit Rf B witness_imp =
    let Goal : Formula
        Goal = eqF (ap1 p (g (ap1 s B))) (ap1 s O)

        ----------------------------------------------------------------
        -- imp_missCase :  imp Rf (imp (p (g B) = O) Goal) .

        d_gBB : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (g B) B))
        d_gBB = compInv B
        d_pBeq : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (ap1 p (g B)) (ap1 p B)))
        d_pBeq = compI d_gBB (ax_eqCong1 p (g B) B)
        d_pBO : Deriv (imp (eqF (ap1 p (g B)) O) (eqF (ap1 p B) O))
        d_pBO = bComb (compI d_pBeq (ax_eqTrans (ap1 p (g B)) (ap1 p B) O))
                      (identP (eqF (ap1 p (g B)) O))

        -- imp-lifted  prependEqLeft (s O) (p B) O (ruleSym witness)  step.
        -- prependEqLeft a b c eqAB = mp (ax_eqTrans b a c) (ruleSym eqAB) .
        -- Here a := s O, b := p B, c := O, eqAB := ruleSym witness.
        --
        -- imp_prependEqLeft applied to witness_imp:
        witness_sym_imp :
          Deriv (imp Rf (eqF (ap1 s O) (ap1 p B)))
        witness_sym_imp = impRuleSym {Rf} witness_imp

        ax_eqT_inst :
          Deriv (imp (eqF (ap1 p B) (ap1 s O))
                     (imp (eqF (ap1 p B) O) (eqF (ap1 s O) O)))
        ax_eqT_inst = ax_eqTrans (ap1 p B) (ap1 s O) O

        prep_imp :
          Deriv (imp Rf (imp (eqF (ap1 p B) O) (eqF (ap1 s O) O)))
        prep_imp = impMp {Rf} (impLift {Rf} ax_eqT_inst) witness_imp

        -- d_pBO is closed:  imp (p (g B) = O) (p B = O) .
        -- prep_imp under imp Rf:  imp Rf (imp (p B = O) (s O = O)) .
        -- Combine via  imp_compI :  imp Rf (imp (p (g B) = O) (s O = O)) .
        d_pBO_imp : Deriv (imp Rf (imp (eqF (ap1 p (g B)) O) (eqF (ap1 p B) O)))
        d_pBO_imp = impLift {Rf} d_pBO

        e_sOO_imp : Deriv (imp Rf (imp (eqF (ap1 p (g B)) O) (eqF (ap1 s O) O)))
        e_sOO_imp = imp_compI {Rf} d_pBO_imp prep_imp

        -- exFalsoFromSO Goal : imp (s O = O) Goal   -- closed.
        exF : Deriv (imp (eqF (ap1 s O) O) Goal)
        exF = exFalsoFromSO Goal

        imp_missCase : Deriv (imp Rf (imp (eqF (ap1 p (g B)) O) Goal))
        imp_missCase = imp_compI {Rf} e_sOO_imp (impLift {Rf} exF)

        ----------------------------------------------------------------
        -- imp_hitCase :  imp Rf (imp (neg (p (g B) = O)) Goal) .
        --
        -- hitCase is CLOSED (independent of witness).  Build via FirstHit's
        -- own body, then impLift under  Rf .

        d_eq : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                          (eqF (ap1 p (g (ap1 s B))) (ap1 p (g B))))
        d_eq = compI (gSuccHit B) (ax_eqCong1 p (g (ap1 s B)) (g B))

        d_sO : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                          (eqF (ap1 p (g B)) (ap1 s O)))
        d_sO = le_one_neq_zero (ap1 p (g B)) (p_le_one (g B))

        d_eqSym : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                             (eqF (ap1 p (g B)) (ap1 p (g (ap1 s B)))))
        d_eqSym = compI d_eq (eqSymImp (ap1 p (g (ap1 s B))) (ap1 p (g B)))

        t1 : Deriv (imp (neg (eqF (ap1 p (g B)) O))
                        (imp (eqF (ap1 p (g B)) (ap1 s O)) Goal))
        t1 = compI d_eqSym
               (ax_eqTrans (ap1 p (g B)) (ap1 p (g (ap1 s B))) (ap1 s O))

        hitCase_closed : Deriv (imp (neg (eqF (ap1 p (g B)) O)) Goal)
        hitCase_closed = bComb t1 d_sO

        imp_hitCase : Deriv (imp Rf (imp (neg (eqF (ap1 p (g B)) O)) Goal))
        imp_hitCase = impLift {Rf} hitCase_closed

    in imp_byCases Rf (eqF (ap1 p (g B)) O) Goal imp_missCase imp_hitCase

  ----------------------------------------------------------------------
  -- ImpLeastNumber -- the Carneiro-lifted record package.
  --
  -- Same shape as  FirstHit.Search.LeastNumber  but the  isHit  Deriv
  -- is wrapped in  imp Rf .   The  w1  field stays a CLOSED Term
  -- ( w1 := g (s B) ), and  isFirst  is closed already.

  record ImpLeastNumber (Rf : Formula) (B : Term) : Set where
    constructor mkImpLeast
    field
      w1     : Term
      isHit  : Deriv (imp Rf (eqF (ap1 p w1) (ap1 s O)))
      isFirst : (x : Term) ->
                Deriv (imp (leq (ap1 s x) w1) (eqF (ap1 p x) O))

  imp_leastNumber :
    (Rf : Formula) (B : Term) ->
    Deriv (imp Rf (eqF (ap1 p B) (ap1 s O))) ->
    ImpLeastNumber Rf B
  imp_leastNumber Rf B witness_imp =
    mkImpLeast (g (ap1 s B))
               (imp_least_hit Rf B witness_imp)
               (least_first B)
