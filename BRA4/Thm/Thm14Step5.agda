{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14Step5 -- Step 5 of Guard's Theorem 14 proof in BRA4 ,
-- EXACTLY matching guard15.pdf p.17 line 5) :
--
--     th(x) = j   ⊃   th(big_term(x))  =  "0 = 1"   ,    by mp on 3) , 4) , 5a) .
--
-- BRA4 form (non-parametric ;  F  fixed in BRA4.Thm.Thm14F ).
-- Universal in  x : Term .
--
--     step5 :  (x : Term) ->
--              Deriv (imp (P_x x)
--                      (eqF (ap1 thmT (big_term x))
--                            (codeFormula falseF)))
--
-- Construction.  Two encoded modus-ponens applications, both via
--  BRA4.Thm12.EncodedMp.imp_encoded_mp  (Carneiro-lifted) .
--
--   Set  A x  =  encEqF (encThm (code x)) (encSub (code i) (code i))  -- "th(x_) = sub(i,i)" .
--   Set  notA x =  encNeg (A x)                                        -- "th(x_) ≠ sub(i,i)" .
--
--   Inner mp  (impl = h_part x , ant = g x) :
--     ih_imp : thmT (h_part x)  =  encImp (A x) (encImp (notA x) (codeFormula falseF))
--                                              [from thmT_h_part , impLifted]
--     ih_a   : thmT (g x)       =  A x        [step3 x , already conditional]
--     -->     thmT (Pair tag_mp (Pair (h_part x) (g x)))  =  encImp (notA x) (codeFormula falseF) .
--
--   Outer mp  (impl = inner_mp_term x , ant = K_part x) :
--     ih_imp : thmT (inner_mp_term x)  =  encImp (notA x) (codeFormula falseF)  [from inner]
--     ih_a   : thmT (K_part x)         =  notA x                                [step4 x]
--     -->     thmT (big_term x)        =  codeFormula falseF .

module BRA4.Thm.Thm14Step5 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFormula ; falseF )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.EncodedMp   using ( imp_encoded_mp )
open import BRA4.Thm12.ImpHelpers  using ( impLift )
open import BRA4.Thm.Thm14F
  using ( i ; code ; encEqF ; encThm ; encSub ; encNeg )
open import BRA4.Thm.Thm14Step1    using ( P_x )
open import BRA4.Thm.Thm14Step3    using ( g ; step3 )
open import BRA4.Thm.Thm14Step4    using ( K_part ; step4 )
open import BRA4.Thm.Thm14HPart
  using ( h_part ; thmT_h_part ; Y0 ; Y1 ; encImp )

------------------------------------------------------------------------
-- The shorthand decoded formulas .

A_ : Term -> Term
A_ x = encEqF (Y0 x) Y1                                  -- "th(x_) = sub(i,i)"

notA_ : Term -> Term
notA_ x = encNeg (A_ x)                                  -- "th(x_) ≠ sub(i,i)"

------------------------------------------------------------------------
-- inner_mp_term x  =  Pair tag_mp (Pair (h_part x) (g x))  -- "mp(h(x), g(x))"
--    with BRA4 convention "Pair tag_mp (Pair impl ant)" :
--      impl-slot = h_part x ;  ant-slot = g x .

inner_mp_term : Term -> Term
inner_mp_term x = ap2 Pair (natCode tag_mp) (ap2 Pair (h_part x) (g x))

------------------------------------------------------------------------
-- big_term x  =  Pair tag_mp (Pair (inner_mp_term x) (K_part x))
--    = Guard's "4J[4J(J(num x,1),x)+1, 4J(gx,hx)+2]+2  = mp(K(x), mp(g(x), h(x)))" .

big_term : Term -> Term
big_term x = ap2 Pair (natCode tag_mp) (ap2 Pair (inner_mp_term x) (K_part x))

------------------------------------------------------------------------
-- Step 5 .  Guard 's "th(x) = j ⊃ th(big_term(x)) = '0 = 1'" EXACTLY .

step5 :
  (x : Term) ->
  Deriv (imp (P_x x)
              (eqF (ap1 thmT (big_term x))
                    (codeFormula falseF)))
step5 x =
  let
    P : Formula
    P = P_x x

    --------------------------------------------------------------------
    -- Inner mp .  ih_imp from thmT_h_part (impLifted) ; ih_a from step3 .

    imp_ih_imp_inner :
      Deriv (imp P (eqF (ap1 thmT (h_part x))
                         (ap2 Pair (natCode tag_imp)
                           (ap2 Pair (A_ x)
                             (encImp (notA_ x) (codeFormula falseF))))))
    imp_ih_imp_inner = impLift {P} (thmT_h_part x)

    imp_ih_a_inner :
      Deriv (imp P (eqF (ap1 thmT (g x)) (A_ x)))
    imp_ih_a_inner = step3 x

    inner_result :
      Deriv (imp P (eqF (ap1 thmT (inner_mp_term x))
                         (encImp (notA_ x) (codeFormula falseF))))
    inner_result =
      imp_encoded_mp P (h_part x) (g x)
                       (A_ x) (encImp (notA_ x) (codeFormula falseF))
                       imp_ih_imp_inner imp_ih_a_inner

    --------------------------------------------------------------------
    -- Outer mp .  ih_imp = inner_result ; ih_a from step4 .

    imp_ih_imp_outer :
      Deriv (imp P (eqF (ap1 thmT (inner_mp_term x))
                         (ap2 Pair (natCode tag_imp)
                           (ap2 Pair (notA_ x) (codeFormula falseF)))))
    imp_ih_imp_outer = inner_result

    imp_ih_a_outer :
      Deriv (imp P (eqF (ap1 thmT (K_part x)) (notA_ x)))
    imp_ih_a_outer = step4 x

  in imp_encoded_mp P (inner_mp_term x) (K_part x)
                       (notA_ x) (codeFormula falseF)
                       imp_ih_imp_outer imp_ih_a_outer
