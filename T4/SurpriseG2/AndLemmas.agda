{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.AndLemmas --
--
-- Formula-level And introduction / projection / Carneiro-LIFTED variants
-- at  conjF A B = neg (imp A (neg B))  (BRA's standard encoding) .
--
-- These let the formula-level  S(r) = Deriv (neg BigConjFormula)  unfold
-- via classical Hilbert equivalences ( `neg (A /\ B) = imp B (neg A)` ,
-- And-elim from a hypothetical conjunction ) WITHOUT a meta deduction
-- theorem  ( see [[feedback_no_meta_to_imp_primitive_needed]] ) .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * `fstAndImp A B : Deriv (imp (conjF A B) A)`
-- * `sndAndImp A B : Deriv (imp (conjF A B) B)`
--     The classical projections .   Proofs via axExFalso + flipImp
--     ( T4.mario ) + axContrapos + DNE + impTrans .
--
-- * `negConjToImpRtoNegL  A B : Deriv (imp (neg (conjF A B)) (imp B (neg A)))`
-- * `negConjToImpLtoNegR  A B : Deriv (imp (neg (conjF A B)) (imp A (neg B)))`
--     The classical neg-of-conj equivalences :  `neg (A /\ B) ↔ A → ¬B`
--     and  `neg (A /\ B) ↔ B → ¬A` .   These are the FORMULA-LEVEL
--     deduction-theorem stand-ins .
--
-- * `liftedAndIntro X A B : Deriv (imp X A) -> Deriv (imp X B) -> Deriv (imp X (conjF A B))`
--     The Carneiro-LIFTED andIntro :   under a common hypothesis  X .
--     Used in the inductive step body to aggregate per-k per-program
--     negations into a lifted K-formula  Deriv (imp X (KdefBigConj ...)) .
--
-- * `axExFalsoToNeg X : Deriv (imp falseF X)  +  Deriv falseF -> Deriv X`
--     ( the FALSE-introduction lift via  axExFalso  +  liftP ) .

module T4.SurpriseG2.AndLemmas where

open import T4.Base
open import BRA3.Logic           using ( impTrans )
open import BRA3.Contrapositive
  using ( DNE ; Q_to_dNeg ; liftP ; bComb ; bCombTwo ; axContrapos ; axExFalso
        ; compI ; identP )
open import T4.mario           using ( flipImp )

open import T4.SurpriseG2.BigConjFormula  using ( conjF )

------------------------------------------------------------------------
-- The classical projection  conjF A B -> A  ( and -> B ) , as a closed
-- implication Deriv .

fstAndImp : (A B : Formula) -> Deriv (imp (conjF A B) A)
fstAndImp A B =
  let step1 : Deriv (imp A (imp (neg A) (neg B)))
      step1 = axExFalso A (neg B)
      step2 : Deriv (imp (imp A (imp (neg A) (neg B)))
                           (imp (neg A) (imp A (neg B))))
      step2 = flipImp A (neg A) (neg B)
      step3 : Deriv (imp (neg A) (imp A (neg B)))
      step3 = mp step2 step1
      step4 : Deriv (imp (imp (neg A) (imp A (neg B)))
                           (imp (neg (imp A (neg B))) (neg (neg A))))
      step4 = axContrapos (neg A) (imp A (neg B))
      step5 : Deriv (imp (neg (imp A (neg B))) (neg (neg A)))
      step5 = mp step4 step3
      step6 : Deriv (imp (neg (neg A)) A)
      step6 = DNE A
  in impTrans step5 step6

sndAndImp : (A B : Formula) -> Deriv (imp (conjF A B) B)
sndAndImp A B =
  let -- Strategy :  B is the "second conjunct" .   The neg-of-imp equivalence
      -- gives us  ¬(A → ¬B) → A ∧ ¬¬B ;  proceed similarly to fstAndImp .
      --
      -- Inner :  imp (neg B) (imp A (neg B)) :=  axK (neg B) A .
      step1 : Deriv (imp (neg B) (imp A (neg B)))
      step1 = axK (neg B) A
      step2 : Deriv (imp (imp (neg B) (imp A (neg B)))
                           (imp (neg (imp A (neg B))) (neg (neg B))))
      step2 = axContrapos (neg B) (imp A (neg B))
      step3 : Deriv (imp (neg (imp A (neg B))) (neg (neg B)))
      step3 = mp step2 step1
      step4 : Deriv (imp (neg (neg B)) B)
      step4 = DNE B
  in impTrans step3 step4

------------------------------------------------------------------------
-- The classical neg-of-conj equivalences .   These are the FORMULA-LEVEL
-- deduction-theorem stand-ins :
--   `neg (A /\ B) -> A -> neg B`   ( direct from And-encoding via DNE )
--   `neg (A /\ B) -> B -> neg A`   ( via axContrapos + DNE ) .

-- neg (conjF A B) = neg (neg (imp A (neg B))) ; DNE gives the body .
negConjToImpLtoNegR :
  (A B : Formula) -> Deriv (imp (neg (conjF A B)) (imp A (neg B)))
negConjToImpLtoNegR A B = DNE (imp A (neg B))

-- Then flip via axContrapos + DNE .
negConjToImpRtoNegL :
  (A B : Formula) -> Deriv (imp (neg (conjF A B)) (imp B (neg A)))
negConjToImpRtoNegL A B =
  let P : Formula
      P = imp A (neg B)

      cp : Deriv (imp P (imp (neg (neg B)) (neg A)))
      cp = axContrapos A (neg B)

      qd : Deriv (imp B (neg (neg B)))
      qd = Q_to_dNeg B

      -- Carneiro-lift cp to insert B between P and its body .
      lifted_cp : Deriv (imp P (imp B (imp (neg (neg B)) (neg A))))
      lifted_cp =
        bComb (liftP P (axK (imp (neg (neg B)) (neg A)) B)) cp

      lifted_qd : Deriv (imp P (imp B (neg (neg B))))
      lifted_qd = liftP P qd

      inner : Deriv (imp P (imp B (neg A)))
      inner = bCombTwo {P} {B} {neg (neg B)} {neg A} lifted_cp lifted_qd
  in impTrans (negConjToImpLtoNegR A B) inner

------------------------------------------------------------------------
-- Carneiro-LIFTED andIntro :  from  Deriv (imp X A)  and  Deriv (imp X B)  ,
-- derive  Deriv (imp X (conjF A B)) .
--
-- Mirrors  T4.CompressCanonical.andIntro  but everything lifted under  X .

liftedAndIntro :
  (X A B : Formula) -> Deriv (imp X A) -> Deriv (imp X B) -> Deriv (imp X (conjF A B))
liftedAndIntro X A B dXA dXB =
  let -- Mirror andIntro's structure but with all steps lifted under X .
      -- Let  Y = imp A (neg B) ( = the inner imp of  conjF A B ) .
      Y : Formula
      Y = imp A (neg B)

      -- We want  Deriv (imp X (neg Y))  =  Deriv (imp X (conjF A B)) .
      --
      -- Strategy ( same as andIntro , lifted ) :
      --   D1 := (imp X (imp Y A))      = liftP X (axK A Y) o dXA
      --                                 actually simpler : liftP X (Hilbert lemma).
      --   D2 := (imp X (imp Y (neg B))) , obtained from Y as the imp .
      --   D3 := (imp X (neg (neg B))) , from dXB via lifted Q_to_dNeg .
      --
      -- And conclude via lifted axContrapos .

      -- D1 :  imp X (imp Y A) ,  via  liftP Y dXA .
      dXY_A : Deriv (imp X (imp Y A))
      dXY_A = bComb (liftP X (axK A Y)) dXA

      -- D2 :  imp X (imp Y (neg B)) .   Y = imp A (neg B) , so
      --       imp Y (neg B)  by  bComb (identP Y) (... project A from Y? )
      --       This is :  ( Y -> Y )  +  ( Y -> A )  -> ( Y -> neg B ) by bComb .
      --   To project  A  from  Y = imp A (neg B) -- no, A is the antecedent, we
      --   have it from dXA under X .
      --   Actually  Y = imp A (neg B) ; from Y and A get neg B (mp at imp) .
      --   So  imp Y (imp A (neg B)) = identP Y , and combined with imp X A  via
      --   bComb under nested context .

      -- Y = imp A (neg B) ;  identP Y : imp Y Y = imp Y (imp A (neg B)) .
      -- liftP X : imp X (imp Y (imp A (neg B))) .   Combine with dXY_A
      -- via bCombTwo to get imp X (imp Y (neg B)) .
      dXY_negB : Deriv (imp X (imp Y (neg B)))
      dXY_negB =
        let s1 : Deriv (imp X (imp Y (imp A (neg B))))
            s1 = liftP X (identP Y)
            s2 : Deriv (imp X (imp Y (neg B)))
            s2 = bCombTwo {X} {Y} {A} {neg B} s1 dXY_A
        in s2

      -- D3 :  imp X (neg (neg B)) .   Lift Q_to_dNeg B + dXB via bComb .
      dX_nnB : Deriv (imp X (neg (neg B)))
      dX_nnB = bComb (liftP X (Q_to_dNeg B)) dXB

      -- D4 :  imp X (imp Y (neg B))  ->  imp X (imp (neg (neg B)) (neg Y))  via lifted axContrapos .
      lifted_cp : Deriv (imp X (imp (imp Y (neg B)) (imp (neg (neg B)) (neg Y))))
      lifted_cp = liftP X (axContrapos Y (neg B))

      -- Simpler :  just bComb lifted_cp at the X level with dXY_negB .
      dX_negY : Deriv (imp X (neg Y))
      dX_negY = bComb (bComb lifted_cp dXY_negB) dX_nnB
  in dX_negY
