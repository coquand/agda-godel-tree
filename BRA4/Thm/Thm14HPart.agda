{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14HPart -- Step 5a of Guard's Theorem 14 proof in BRA4 .
--
-- Builds  h(x) , Guard's  "sb2 spec2 t'"  encoded Term (guard15.pdf p.17) ,
-- where  spec2  packages the two simultaneous substitutions
--    var 0  :=  encThm (code x)        -- Guard's  "th(x_)"
--    var 1  :=  encSub (code i) (code i) -- Guard's  "sub(i, i)"
-- and  t'  is the encoded derivation of Guard's schema
--    F'  =  (x_0 = x_1)  ⊃  (x_0 ≠ x_1)  ⊃  0 = 1 .
--
-- Output :
--
--     thmT_h_part :  (x : Term) ->
--       Deriv (eqF (ap1 thmT (h_part x))
--                   (encImp (encEqF (encThm (code x)) (encSub (code i) (code i)))
--                           (encImp (encNeg (encEqF (encThm (code x)) (encSub (code i) (code i))))
--                                   (codeFormula falseF))))
--
-- Proof chain :
--   (A)  thmT (h_part x)
--          =Deriv=  sbf2 (spec2 x) (ap1 thmT t_prime)      [thmT_at_sb2]
--          =Deriv=  sbf2 (spec2 x) (codeFormula F_prime)   [congR sbf2 + thmT_t_prime]
--   (B)  Unfold  codeFormula F_prime  =
--          Pair tag_imp (Pair (codeFormula A_eq)
--            (Pair tag_imp (Pair (codeFormula (neg A_eq)) (codeFormula falseF))))
--        via  sbf2_at_imp  (twice) , then  sbf2_at_atomic / sbf2_at_neg .
--   (C)  Substituent slots :
--          sbt2 spec2 (codeTerm (var 0))  =Deriv=  encThm (code x)   [sbt2_at_var_match_one]
--          sbt2 spec2 (codeTerm (var 1))  =Deriv=  encSub (code i) (code i) [sbt2_at_var_match_two]
--   (D)  codeFormula falseF  =  atomic (eqn O (ap1 s O))  has only  O ,
--        natCode 1 = ap1 s O  inside .  Both leaves are closed and traversed
--        by  sbt2  to themselves via  sbt2_codeTerm_natCode_eq  (mirror of
--         BRA4.Thm.Thm14Step4.sbt_codeTerm_natCode_eq ).

module BRA4.Thm.Thm14HPart where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula
                                          ; falseF )
open import BRA4.Num               using ( num )
open import BRA4.SbT2              using ( sbt2 )
open import BRA4.SbF2              using ( sbf2 )
open import BRA4.SbContract2       using ( SbContract2 ; sbContract2 )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb2         using ( thmT_at_sb2 )
open import BRA4.Sub               using ( sub )
open import BRA4.NumContract       using ( numContract ; module NumContract )
open import BRA4.Thm.Thm14F
  using ( i ; iNat ; code ; encEqF ; encThm ; encSub ; encNeg )
open import BRA4.Thm.Thm14TPrime
  using ( t_prime ; F_prime ; A_eq ; thmT_t_prime )

open SbContract2 sbContract2
open NumContract numContract using ( numEq )

------------------------------------------------------------------------
-- encImp .  Guard's encoded "P ⊃ Q" .

encImp : Term -> Term -> Term
encImp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

------------------------------------------------------------------------
-- spec2 x  -- the 2-variable substitution spec :
--    var 0  :=  encThm (code x)
--    var 1  :=  encSub (code i) (code i)

Y0 : Term -> Term
Y0 x = encThm (code x)                       -- "th(x_)"

Y1 : Term
Y1 = encSub (code i) (code i)                -- "sub(i, i)"

spec2 : Term -> Term
spec2 x = ap2 Pair (ap2 Pair (natCode zero) (Y0 x))
                   (ap2 Pair (natCode (suc zero)) Y1)

------------------------------------------------------------------------
-- h_part x  =  Pair tag_sb2 (Pair (spec2 x) t_prime) .

h_part : Term -> Term
h_part x = ap2 Pair (natCode tag_sb2) (ap2 Pair (spec2 x) t_prime)

------------------------------------------------------------------------
-- Helper :  sbt2  on  codeTerm (natCode n)  is identity .
--
-- For any  spec = spec2 x ,  sbt2 spec (codeTerm (natCode n)) =Deriv=
--  codeTerm (natCode n) , by meta-induction on  n .
--   n = 0 :  codeTerm O = O .  sbt2_at_O .
--   n = suc m :  codeTerm (ap1 s (natCode m)) = Pair tag_ap1 (Pair (codeFun1 s)
--               (codeTerm (natCode m))) .  sbt2_at_ap1 + IH .

sbt2_codeTerm_natCode_eq :
  (x : Term) (n : Nat) ->
  Deriv (eqF (ap2 sbt2 (spec2 x) (codeTerm (natCode n)))
              (codeTerm (natCode n)))
sbt2_codeTerm_natCode_eq x zero =
  sbt2_at_O (spec2 x)
sbt2_codeTerm_natCode_eq x (suc n) =
  let
    spec : Term
    spec = spec2 x

    step1 :
      Deriv (eqF (ap2 sbt2 spec (codeTerm (ap1 s (natCode n))))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 s)
                      (ap2 sbt2 spec (codeTerm (natCode n))))))
    step1 = sbt2_at_ap1 zero (suc zero) (Y0 x) Y1 s (codeTerm (natCode n))

    ih :
      Deriv (eqF (ap2 sbt2 spec (codeTerm (natCode n)))
                  (codeTerm (natCode n)))
    ih = sbt2_codeTerm_natCode_eq x n

    step2 :
      Deriv (eqF (ap2 Pair (codeFun1 s) (ap2 sbt2 spec (codeTerm (natCode n))))
                  (ap2 Pair (codeFun1 s) (codeTerm (natCode n))))
    step2 = congR Pair (codeFun1 s) ih

    step3 :
      Deriv (eqF (ap2 Pair (natCode tag_ap1)
                   (ap2 Pair (codeFun1 s) (ap2 sbt2 spec (codeTerm (natCode n)))))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 s) (codeTerm (natCode n)))))
    step3 = congR Pair (natCode tag_ap1) step2
  in ruleTrans step1 step3

------------------------------------------------------------------------
-- sbt2  at the var 0 slot inside  codeTerm (var 0) .
--    codeTerm (var 0) = Pair (natCode tag_var) (natCode 0)
--    sbt2_at_var_match_one (k1=0, k2=1) gives  Y0 x .

sbt2_at_codeTerm_var0 :
  (x : Term) ->
  Deriv (eqF (ap2 sbt2 (spec2 x) (codeTerm (var zero))) (Y0 x))
sbt2_at_codeTerm_var0 x =
  sbt2_at_var_match_one zero (suc zero) (Y0 x) Y1

------------------------------------------------------------------------
-- sbt2  at the var 1 slot inside  codeTerm (var 1) .
--    codeTerm (var 1) = Pair (natCode tag_var) (natCode 1)
--    sbt2_at_var_match_two (k1=0, k2=1, k1!=k2) gives  Y1 .

sbt2_at_codeTerm_var1 :
  (x : Term) ->
  Deriv (eqF (ap2 sbt2 (spec2 x) (codeTerm (var (suc zero)))) Y1)
sbt2_at_codeTerm_var1 x =
  sbt2_at_var_match_two zero (suc zero) (Y0 x) Y1 refl

------------------------------------------------------------------------
-- sbf2  on  codeFormula A_eq  =  Pair tag_eq (Pair (codeTerm (var 0)) (codeTerm (var 1))) .
-- Unfolds via  sbf2_at_atomic  then plops Y0 x , Y1 via the two var lemmas .
--
-- Output : encEqF (Y0 x) Y1 .

sbf2_at_A_eq :
  (x : Term) ->
  Deriv (eqF (ap2 sbf2 (spec2 x) (codeFormula A_eq))
              (encEqF (Y0 x) Y1))
sbf2_at_A_eq x =
  let
    spec : Term
    spec = spec2 x

    -- codeFormula A_eq = Pair tag_eq (Pair (codeTerm (var 0)) (codeTerm (var 1)))
    step_atom :
      Deriv (eqF (ap2 sbf2 spec (codeFormula A_eq))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair
                      (ap2 sbt2 spec (codeTerm (var zero)))
                      (ap2 sbt2 spec (codeTerm (var (suc zero)))))))
    step_atom = sbf2_at_atomic zero (suc zero) (Y0 x) Y1
                  (codeTerm (var zero)) (codeTerm (var (suc zero)))

    sbt2_v0 :
      Deriv (eqF (ap2 sbt2 spec (codeTerm (var zero))) (Y0 x))
    sbt2_v0 = sbt2_at_codeTerm_var0 x

    sbt2_v1 :
      Deriv (eqF (ap2 sbt2 spec (codeTerm (var (suc zero)))) Y1)
    sbt2_v1 = sbt2_at_codeTerm_var1 x

    step_inner :
      Deriv (eqF (ap2 Pair (ap2 sbt2 spec (codeTerm (var zero)))
                             (ap2 sbt2 spec (codeTerm (var (suc zero)))))
                  (ap2 Pair (Y0 x) Y1))
    step_inner =
      ruleTrans
        (congL Pair (ap2 sbt2 spec (codeTerm (var (suc zero)))) sbt2_v0)
        (congR Pair (Y0 x) sbt2_v1)

    step_outer :
      Deriv (eqF (ap2 Pair (natCode tag_eq)
                   (ap2 Pair (ap2 sbt2 spec (codeTerm (var zero)))
                             (ap2 sbt2 spec (codeTerm (var (suc zero))))))
                  (encEqF (Y0 x) Y1))
    step_outer = congR Pair (natCode tag_eq) step_inner
  in ruleTrans step_atom step_outer

------------------------------------------------------------------------
-- sbf2  on  codeFormula (neg A_eq)  =  Pair tag_neg (codeFormula A_eq) .
-- Unfolds via  sbf2_at_neg  + congR sbf2_at_A_eq .
--
-- Output : encNeg (encEqF (Y0 x) Y1) .

sbf2_at_negA_eq :
  (x : Term) ->
  Deriv (eqF (ap2 sbf2 (spec2 x) (codeFormula (neg A_eq)))
              (encNeg (encEqF (Y0 x) Y1)))
sbf2_at_negA_eq x =
  let
    spec : Term
    spec = spec2 x

    step_neg :
      Deriv (eqF (ap2 sbf2 spec (codeFormula (neg A_eq)))
                  (ap2 Pair (natCode tag_neg)
                    (ap2 sbf2 spec (codeFormula A_eq))))
    step_neg = sbf2_at_neg zero (suc zero) (Y0 x) Y1 (codeFormula A_eq)

    step_inner :
      Deriv (eqF (ap2 Pair (natCode tag_neg)
                   (ap2 sbf2 spec (codeFormula A_eq)))
                  (ap2 Pair (natCode tag_neg)
                    (encEqF (Y0 x) Y1)))
    step_inner = congR Pair (natCode tag_neg) (sbf2_at_A_eq x)
  in ruleTrans step_neg step_inner

------------------------------------------------------------------------
-- sbf2  on  codeFormula falseF  =  Pair tag_eq (Pair (codeTerm O) (codeTerm (ap1 s O))) .
-- codeTerm O = O ; codeTerm (ap1 s O) = Pair tag_ap1 (Pair (codeFun1 s) O) .
-- Both are closed numerals (natCode 0 = O , natCode 1 = ap1 s O) , so the
-- sbt2_codeTerm_natCode_eq helper applies to each .
--
-- Output : codeFormula falseF  (unchanged) .

sbf2_at_falseF :
  (x : Term) ->
  Deriv (eqF (ap2 sbf2 (spec2 x) (codeFormula falseF))
              (codeFormula falseF))
sbf2_at_falseF x =
  let
    spec : Term
    spec = spec2 x

    -- codeFormula falseF = Pair tag_eq (Pair (codeTerm O) (codeTerm (ap1 s O))) .
    --   codeTerm O      = O                 (= natCode 0)
    --   codeTerm (ap1 s O) = Pair tag_ap1 (Pair (codeFun1 s) O)
    --                       = codeTerm (natCode 1) .

    step_atom :
      Deriv (eqF (ap2 sbf2 spec (codeFormula falseF))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair
                      (ap2 sbt2 spec (codeTerm O))
                      (ap2 sbt2 spec (codeTerm (ap1 s O))))))
    step_atom = sbf2_at_atomic zero (suc zero) (Y0 x) Y1
                  (codeTerm O) (codeTerm (ap1 s O))

    sbt2_O : Deriv (eqF (ap2 sbt2 spec (codeTerm O)) (codeTerm O))
    sbt2_O = sbt2_codeTerm_natCode_eq x zero

    sbt2_sO : Deriv (eqF (ap2 sbt2 spec (codeTerm (ap1 s O))) (codeTerm (ap1 s O)))
    sbt2_sO = sbt2_codeTerm_natCode_eq x (suc zero)

    step_inner :
      Deriv (eqF (ap2 Pair (ap2 sbt2 spec (codeTerm O))
                             (ap2 sbt2 spec (codeTerm (ap1 s O))))
                  (ap2 Pair (codeTerm O) (codeTerm (ap1 s O))))
    step_inner =
      ruleTrans
        (congL Pair (ap2 sbt2 spec (codeTerm (ap1 s O))) sbt2_O)
        (congR Pair (codeTerm O) sbt2_sO)

    step_outer :
      Deriv (eqF (ap2 Pair (natCode tag_eq)
                   (ap2 Pair (ap2 sbt2 spec (codeTerm O))
                             (ap2 sbt2 spec (codeTerm (ap1 s O)))))
                  (codeFormula falseF))
    step_outer = congR Pair (natCode tag_eq) step_inner
  in ruleTrans step_atom step_outer

------------------------------------------------------------------------
-- sbf2  on  codeFormula (imp (neg A_eq) falseF) :  inner imp .
--   sbf2_at_imp + congR/congL with the two sub-results .
--
-- Output : encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF) .

sbf2_at_inner_imp :
  (x : Term) ->
  Deriv (eqF (ap2 sbf2 (spec2 x) (codeFormula (imp (neg A_eq) falseF)))
              (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF)))
sbf2_at_inner_imp x =
  let
    spec : Term
    spec = spec2 x

    step_imp :
      Deriv (eqF (ap2 sbf2 spec (codeFormula (imp (neg A_eq) falseF)))
                  (ap2 Pair (natCode tag_imp)
                    (ap2 Pair
                      (ap2 sbf2 spec (codeFormula (neg A_eq)))
                      (ap2 sbf2 spec (codeFormula falseF)))))
    step_imp = sbf2_at_imp zero (suc zero) (Y0 x) Y1
                 (codeFormula (neg A_eq)) (codeFormula falseF)

    step_inner :
      Deriv (eqF (ap2 Pair
                   (ap2 sbf2 spec (codeFormula (neg A_eq)))
                   (ap2 sbf2 spec (codeFormula falseF)))
                  (ap2 Pair (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF)))
    step_inner =
      ruleTrans
        (congL Pair (ap2 sbf2 spec (codeFormula falseF)) (sbf2_at_negA_eq x))
        (congR Pair (encNeg (encEqF (Y0 x) Y1)) (sbf2_at_falseF x))

    step_outer :
      Deriv (eqF (ap2 Pair (natCode tag_imp)
                   (ap2 Pair
                     (ap2 sbf2 spec (codeFormula (neg A_eq)))
                     (ap2 sbf2 spec (codeFormula falseF))))
                  (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF)))
    step_outer = congR Pair (natCode tag_imp) step_inner
  in ruleTrans step_imp step_outer

------------------------------------------------------------------------
-- sbf2  on  codeFormula F_prime  =  codeFormula (imp A_eq (imp (neg A_eq) falseF)) .
-- Outer imp via  sbf2_at_imp .
--
-- Output : encImp (encEqF (Y0 x) Y1) (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF)) .

sbf2_at_F_prime :
  (x : Term) ->
  Deriv (eqF (ap2 sbf2 (spec2 x) (codeFormula F_prime))
              (encImp (encEqF (Y0 x) Y1)
                      (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))))
sbf2_at_F_prime x =
  let
    spec : Term
    spec = spec2 x

    step_imp :
      Deriv (eqF (ap2 sbf2 spec (codeFormula F_prime))
                  (ap2 Pair (natCode tag_imp)
                    (ap2 Pair
                      (ap2 sbf2 spec (codeFormula A_eq))
                      (ap2 sbf2 spec (codeFormula (imp (neg A_eq) falseF))))))
    step_imp = sbf2_at_imp zero (suc zero) (Y0 x) Y1
                 (codeFormula A_eq) (codeFormula (imp (neg A_eq) falseF))

    step_inner :
      Deriv (eqF (ap2 Pair
                   (ap2 sbf2 spec (codeFormula A_eq))
                   (ap2 sbf2 spec (codeFormula (imp (neg A_eq) falseF))))
                  (ap2 Pair (encEqF (Y0 x) Y1)
                       (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))))
    step_inner =
      ruleTrans
        (congL Pair (ap2 sbf2 spec (codeFormula (imp (neg A_eq) falseF)))
                     (sbf2_at_A_eq x))
        (congR Pair (encEqF (Y0 x) Y1) (sbf2_at_inner_imp x))

    step_outer :
      Deriv (eqF (ap2 Pair (natCode tag_imp)
                   (ap2 Pair
                     (ap2 sbf2 spec (codeFormula A_eq))
                     (ap2 sbf2 spec (codeFormula (imp (neg A_eq) falseF)))))
                  (encImp (encEqF (Y0 x) Y1)
                          (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))))
    step_outer = congR Pair (natCode tag_imp) step_inner
  in ruleTrans step_imp step_outer

------------------------------------------------------------------------
-- Main theorem :  thmT (h_part x)  =Deriv=  encImp (...) (encImp (encNeg (...)) (codeFormula falseF)) .
--
-- Chain :
--   thmT (h_part x)
--     =Deriv=  sbf2 (spec2 x) (ap1 thmT t_prime)            [thmT_at_sb2]
--     =Deriv=  sbf2 (spec2 x) (codeFormula F_prime)         [congR sbf2 + thmT_t_prime]
--     =Deriv=  encImp (encEqF (Y0 x) Y1) (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))  [sbf2_at_F_prime]

thmT_h_part :
  (x : Term) ->
  Deriv (eqF (ap1 thmT (h_part x))
              (encImp (encEqF (Y0 x) Y1)
                      (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))))
thmT_h_part x =
  let
    spec : Term
    spec = spec2 x

    step_A :
      Deriv (eqF (ap1 thmT (h_part x))
                  (ap2 sbf2 spec (ap1 thmT t_prime)))
    step_A = thmT_at_sb2 spec t_prime

    step_B :
      Deriv (eqF (ap2 sbf2 spec (ap1 thmT t_prime))
                  (ap2 sbf2 spec (codeFormula F_prime)))
    step_B = congR sbf2 spec thmT_t_prime

    step_C :
      Deriv (eqF (ap2 sbf2 spec (codeFormula F_prime))
                  (encImp (encEqF (Y0 x) Y1)
                          (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))))
    step_C = sbf2_at_F_prime x
  in ruleTrans step_A (ruleTrans step_B step_C)
