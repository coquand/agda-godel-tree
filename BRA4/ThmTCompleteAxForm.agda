{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTCompleteAxForm -- completeness for the formula-only axioms
-- axS and axNeg.
--
-- These axioms have NO Term parameters ; their  extra  bundle is
-- Pair codeA (Pair codeB codeC)  (axS) or  Pair codeA codeB  (axNeg) ;
-- the closure's output has  Fst / Snd  projections of  extra  which
-- reduce via axFst / axSnd to the corresponding codeFormulas.

module BRA4.ThmTCompleteAxForm where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Encode
open import BRA4.ThmT      using ( thmT )

open import BRA4.ThmTAtAx12 using ( thmT_at_axN12 )
open import BRA4.ThmTAtAx13 using ( thmT_at_axN13 )

open import BRA3.Church      using ( pi )
open import BRA3.PairAlgebra using ( axFst ; axSnd )

------------------------------------------------------------------------
-- axS A B C  :  P = imp (imp A (imp B C)) (imp (imp A B) (imp A C)) .
-- encode (axS A B C) = packAx 12 (pi codeA (pi codeB codeC)) .
-- thmT_at_axN12 output :
--   outputRHS (pi codeA (pi codeB codeC))
--     = pi tag_imp (pi impA_impBC impAB_impAC)
-- with the inner three uses of   ap1 Fst / ap1 Snd  on  extra  unfolded.
-- We reduce each projection via axFst / axSnd.

thmT_complete_axS :
  (A B Cf : Formula) ->
  Deriv (eqF (ap1 thmT (encode (axS A B Cf)))
              (codeFormula (imp (imp A (imp B Cf)) (imp (imp A B) (imp A Cf)))))
thmT_complete_axS A B Cf =
  let cA : Term
      cA = codeFormula A
      cB : Term
      cB = codeFormula B
      cC : Term
      cC = codeFormula Cf
      extra : Term
      extra = ap2 Pair cA (ap2 Pair cB cC)

      raw : Deriv (eqF (ap1 thmT (encode (axS A B Cf)))
                    (ap2 pi (natCode tag_imp)
                      (ap2 pi
                        (ap2 pi (natCode tag_imp)
                          (ap2 pi (ap1 Fst extra)
                            (ap2 pi (natCode tag_imp)
                              (ap2 pi (ap1 Fst (ap1 Snd extra))
                                       (ap1 Snd (ap1 Snd extra))))))
                        (ap2 pi (natCode tag_imp)
                          (ap2 pi
                            (ap2 pi (natCode tag_imp)
                              (ap2 pi (ap1 Fst extra) (ap1 Fst (ap1 Snd extra))))
                            (ap2 pi (natCode tag_imp)
                              (ap2 pi (ap1 Fst extra) (ap1 Snd (ap1 Snd extra)))))))))
      raw = thmT_at_axN12 extra

      eq_A : Deriv (eqF (ap1 Fst extra) cA)
      eq_A = axFst cA (ap2 Pair cB cC)

      eq_Snd : Deriv (eqF (ap1 Snd extra) (ap2 Pair cB cC))
      eq_Snd = axSnd cA (ap2 Pair cB cC)

      eq_B : Deriv (eqF (ap1 Fst (ap1 Snd extra)) cB)
      eq_B = ruleTrans (cong1 Fst eq_Snd) (axFst cB cC)

      eq_C : Deriv (eqF (ap1 Snd (ap1 Snd extra)) cC)
      eq_C = ruleTrans (cong1 Snd eq_Snd) (axSnd cB cC)

      -- Use Eq.subst three times to rewrite  Fst extra , Fst (Snd extra) ,
      -- Snd (Snd extra)  into  cA , cB , cC  in the displayed Term.
      -- This is heavy ; we leverage the eqSubst-via-congRule pattern.

      cBImpC : Term
      cBImpC = ap2 pi (natCode tag_imp) (ap2 pi cB cC)

      cAImpBImpC : Term
      cAImpBImpC = ap2 pi (natCode tag_imp) (ap2 pi cA cBImpC)

      cAImpB : Term
      cAImpB = ap2 pi (natCode tag_imp) (ap2 pi cA cB)

      cAImpC : Term
      cAImpC = ap2 pi (natCode tag_imp) (ap2 pi cA cC)

      cAB_AC : Term
      cAB_AC = ap2 pi (natCode tag_imp) (ap2 pi cAImpB cAImpC)

      -- Build the target piece by piece via cong-chains.

      step_left_BC :
        Deriv (eqF
          (ap2 pi (natCode tag_imp)
            (ap2 pi (ap1 Fst (ap1 Snd extra)) (ap1 Snd (ap1 Snd extra))))
          cBImpC)
      step_left_BC =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap1 Snd (ap1 Snd extra)) eq_B)
                     (congR pi cB eq_C))

      step_left_ABImpC :
        Deriv (eqF
          (ap2 pi (natCode tag_imp)
            (ap2 pi (ap1 Fst extra)
              (ap2 pi (natCode tag_imp)
                (ap2 pi (ap1 Fst (ap1 Snd extra))
                         (ap1 Snd (ap1 Snd extra))))))
          cAImpBImpC)
      step_left_ABImpC =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi (ap1 Fst (ap1 Snd extra))
                                                (ap1 Snd (ap1 Snd extra))))
                              eq_A)
                     (congR pi cA step_left_BC))

      step_right_AB :
        Deriv (eqF
          (ap2 pi (natCode tag_imp)
            (ap2 pi (ap1 Fst extra) (ap1 Fst (ap1 Snd extra))))
          cAImpB)
      step_right_AB =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap1 Fst (ap1 Snd extra)) eq_A)
                     (congR pi cA eq_B))

      step_right_AC :
        Deriv (eqF
          (ap2 pi (natCode tag_imp)
            (ap2 pi (ap1 Fst extra) (ap1 Snd (ap1 Snd extra))))
          cAImpC)
      step_right_AC =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap1 Snd (ap1 Snd extra)) eq_A)
                     (congR pi cA eq_C))

      step_right :
        Deriv (eqF
          (ap2 pi (natCode tag_imp)
            (ap2 pi
              (ap2 pi (natCode tag_imp)
                (ap2 pi (ap1 Fst extra) (ap1 Fst (ap1 Snd extra))))
              (ap2 pi (natCode tag_imp)
                (ap2 pi (ap1 Fst extra) (ap1 Snd (ap1 Snd extra))))))
          cAB_AC)
      step_right =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi (ap1 Fst extra)
                                                (ap1 Snd (ap1 Snd extra))))
                              step_right_AB)
                     (congR pi cAImpB step_right_AC))

      total :
        Deriv (eqF
          (ap2 pi (natCode tag_imp)
            (ap2 pi
              (ap2 pi (natCode tag_imp)
                (ap2 pi (ap1 Fst extra)
                  (ap2 pi (natCode tag_imp)
                    (ap2 pi (ap1 Fst (ap1 Snd extra))
                             (ap1 Snd (ap1 Snd extra))))))
              (ap2 pi (natCode tag_imp)
                (ap2 pi
                  (ap2 pi (natCode tag_imp)
                    (ap2 pi (ap1 Fst extra) (ap1 Fst (ap1 Snd extra))))
                  (ap2 pi (natCode tag_imp)
                    (ap2 pi (ap1 Fst extra) (ap1 Snd (ap1 Snd extra))))))))
          (codeFormula (imp (imp A (imp B Cf)) (imp (imp A B) (imp A Cf)))))
      total =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi
                                         (ap2 pi (natCode tag_imp)
                                           (ap2 pi (ap1 Fst extra) (ap1 Fst (ap1 Snd extra))))
                                         (ap2 pi (natCode tag_imp)
                                           (ap2 pi (ap1 Fst extra) (ap1 Snd (ap1 Snd extra))))))
                              step_left_ABImpC)
                     (congR pi cAImpBImpC step_right))
  in ruleTrans raw total

------------------------------------------------------------------------
-- axNeg A B  :  P = imp (imp (neg A) (neg B)) (imp B A) .
-- extra = Pair cA cB ; outputRHS uses  Fst extra = cA ,  Snd extra = cB .

thmT_complete_axNeg :
  (A B : Formula) ->
  Deriv (eqF (ap1 thmT (encode (axNeg A B)))
              (codeFormula (imp (imp (neg A) (neg B)) (imp B A))))
thmT_complete_axNeg A B =
  let cA : Term
      cA = codeFormula A
      cB : Term
      cB = codeFormula B
      extra : Term
      extra = ap2 Pair cA cB

      raw : Deriv (eqF (ap1 thmT (encode (axNeg A B)))
                    (ap2 pi (natCode tag_imp)
                      (ap2 pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi (ap2 pi (natCode tag_neg) (ap1 Fst extra))
                                                (ap2 pi (natCode tag_neg) (ap1 Snd extra))))
                              (ap2 pi (natCode tag_imp)
                                (ap2 pi (ap1 Snd extra) (ap1 Fst extra))))))
      raw = thmT_at_axN13 extra

      eq_A : Deriv (eqF (ap1 Fst extra) cA)
      eq_A = axFst cA cB
      eq_B : Deriv (eqF (ap1 Snd extra) cB)
      eq_B = axSnd cA cB

      -- pi tag_neg (Fst extra) -> pi tag_neg cA  =  codeFormula (neg A).
      step_negA :
        Deriv (eqF (ap2 pi (natCode tag_neg) (ap1 Fst extra)) (codeFormula (neg A)))
      step_negA = congR pi (natCode tag_neg) eq_A
      step_negB :
        Deriv (eqF (ap2 pi (natCode tag_neg) (ap1 Snd extra)) (codeFormula (neg B)))
      step_negB = congR pi (natCode tag_neg) eq_B

      -- pi tag_imp (pi (neg A) (neg B))   =  codeFormula (imp (neg A) (neg B)).
      step_impNegs :
        Deriv (eqF (ap2 pi (natCode tag_imp)
                     (ap2 pi (ap2 pi (natCode tag_neg) (ap1 Fst extra))
                              (ap2 pi (natCode tag_neg) (ap1 Snd extra))))
                    (codeFormula (imp (neg A) (neg B))))
      step_impNegs =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap2 pi (natCode tag_neg) (ap1 Snd extra)) step_negA)
                     (congR pi (codeFormula (neg A)) step_negB))

      -- pi tag_imp (pi (Snd extra) (Fst extra))   =  codeFormula (imp B A).
      step_impBA :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))
                    (codeFormula (imp B A)))
      step_impBA =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap1 Fst extra) eq_B)
                     (congR pi cB eq_A))

      total :
        Deriv (eqF (ap2 pi (natCode tag_imp)
                     (ap2 pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi (ap2 pi (natCode tag_neg) (ap1 Fst extra))
                                                (ap2 pi (natCode tag_neg) (ap1 Snd extra))))
                              (ap2 pi (natCode tag_imp)
                                (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))))
                    (codeFormula (imp (imp (neg A) (neg B)) (imp B A))))
      total =
        congR pi (natCode tag_imp)
          (ruleTrans (congL pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))
                              step_impNegs)
                     (congR pi (codeFormula (imp (neg A) (neg B))) step_impBA))
  in ruleTrans raw total
