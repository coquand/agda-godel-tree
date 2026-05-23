{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14HPart -- Step 5a of Guard's Theorem 14 proof in BRA4 ,
-- now via a NESTED single-variable sb-wrap (no sbt2/sbf2).
--
-- Builds  h(x) , Guard's encoded Term (guard15.pdf p.17) , where the two
-- simultaneous substitutions
--    var 0  :=  encThm (code x)          -- Guard's  "th(x_)"
--    var 1  :=  encSub (code i) (code i)  -- Guard's  "sub(i, i)"
-- are realised as TWO nested  tag_sb  wraps (var 0 outermost, var 1
-- innermost) of  t' , the encoded derivation of Guard's schema
--    F'  =  (x_0 = x_1)  >  ((x_0 ≠ x_1)  >  0 = 1) .
--
-- Since  code t = num t  (BRA4.Thm.Thm14F) , both substituents are
--  num-based  composites :
--    encThm (code x) = Pair tag_ap1 (Pair (codeFun1 thmT) (num x))
--    encSub (code i)(code i)
--      = Pair tag_ap2 (Pair (codeFun2 sub) (Pair (num i) (num i)))
-- hence  InertU  via  NumCode  (BRA4.SbStep).  The inner-planted
--  encSub (code i)(code i)  is re-scanned by the outer (var 0) pass and
-- discharged by its inertness; the var-0 substituent is fresh-planted last.
--
--   thmT_h_part :  (x : Term) ->
--     Deriv (eqF (ap1 thmT (h_part x))
--                 (encImp (encEqF (encThm (code x)) (encSub (code i) (code i)))
--                         (encImp (encNeg (encEqF (encThm (code x)) (encSub (code i) (code i))))
--                                 (codeFormula falseF))))

module BRA4.Thm.Thm14HPart where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula
                                          ; falseF )
open import BRA4.Num               using ( num )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.Sub               using ( sub )
open import BRA4.Thm.Thm14F
  using ( i ; code ; encEqF ; encThm ; encSub ; encNeg )
open import BRA4.Thm.Thm14TPrime
  using ( t_prime ; F_prime ; A_eq ; thmT_t_prime )

------------------------------------------------------------------------
-- encImp .  Guard's encoded "P > Q" .

encImp : Term -> Term -> Term
encImp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

------------------------------------------------------------------------
-- The two substituents.

Y0 : Term -> Term
Y0 x = encThm (code x)                       -- "th(x_)"  = encThm (num x)

Y1 : Term
Y1 = encSub (code i) (code i)                -- "sub(i, i)"

-- NumCode witnesses (code t = num t , so both are num-based).
ncY0 : (x : Term) -> NumCode (Y0 x)
ncY0 x = ncAp1 thmT (code x) (ncNum x)

ncY1 : NumCode Y1
ncY1 = ncAp2 sub (code i) (code i) (ncNum i) (ncNum i)

------------------------------------------------------------------------
-- Var-leaf codes and the encoded skeleton  FormHP x0 x1  =  codeFormula
--  F_prime  with the two var-leaves replaced by  x0 / x1 .

private
  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cFalse : Term
  cFalse = codeFormula falseF

  FormHP : Term -> Term -> Term
  FormHP x0 x1 =
    encImp (encEqF x0 x1)
           (encImp (encNeg (encEqF x0 x1)) cFalse)

  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

------------------------------------------------------------------------
-- h_part x  =  nested sb-wrap of  t' .

h_part : Term -> Term
h_part x =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_at (Y0 x))
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_at Y1) t_prime)))

------------------------------------------------------------------------
-- The closed  falseF  code is inert under every single-variable
-- substitution :  codeFormula falseF = Pair tag_eq (Pair (codeTerm O)
--  (codeTerm (s O))) , both leaves num-based.

private
  falseInert :
    (k : Nat) (S : Term) ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) cFalse) cFalse)
  falseInert k S =
    sbf_step_atomic k S
      (codeTerm O) (codeTerm (ap1 s O))
      (codeTerm O) (codeTerm (ap1 s O))
      (sbt_inert_NumCode (codeTerm O) ncO k S)
      (sbt_inert_NumCode (codeTerm (ap1 s O)) (ncAp1 s O ncO) k S)

------------------------------------------------------------------------
-- One pass of  sbf  over the FormHP skeleton.

private
  onePassHP :
    (k : Nat) (S : Term) (x0 x1 x0' x1' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x0) x0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x1) x1') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormHP x0 x1))
                (FormHP x0' x1'))
  onePassHP k S x0 x1 x0' x1' e0 e1 =
    sbf_step_imp k S
      (encEqF x0 x1) (encImp (encNeg (encEqF x0 x1)) cFalse)
      (encEqF x0' x1') (encImp (encNeg (encEqF x0' x1')) cFalse)
      (sbf_step_atomic k S x0 x1 x0' x1' e0 e1)
      (sbf_step_imp k S
        (encNeg (encEqF x0 x1)) cFalse
        (encNeg (encEqF x0' x1')) cFalse
        (sbf_step_neg k S (encEqF x0 x1) (encEqF x0' x1')
          (sbf_step_atomic k S x0 x1 x0' x1' e0 e1))
        (falseInert k S))

------------------------------------------------------------------------
-- Main theorem.

thmT_h_part :
  (x : Term) ->
  Deriv (eqF (ap1 thmT (h_part x))
              (encImp (encEqF (Y0 x) Y1)
                      (encImp (encNeg (encEqF (Y0 x) Y1)) (codeFormula falseF))))
thmT_h_part x =
  let spec0 : Term
      spec0 = spec0_at (Y0 x)
      spec1 : Term
      spec1 = spec1_at Y1

      innerCode : Term
      innerCode = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 t_prime)

      -- thmT (h_part x) = sbf spec0 (thmT innerCode)   [thmT_at_sb].
      e1 : Deriv (eqF (ap1 thmT (h_part x))
                       (ap2 sbf spec0 (ap1 thmT innerCode)))
      e1 = thmT_at_sb spec0 innerCode

      -- thmT innerCode = sbf spec1 (thmT t_prime)       [thmT_at_sb].
      e2 : Deriv (eqF (ap1 thmT innerCode) (ap2 sbf spec1 (ap1 thmT t_prime)))
      e2 = thmT_at_sb spec1 t_prime

      -- thmT t_prime = codeFormula F_prime = FormHP cV0 cV1.
      e3 : Deriv (eqF (ap1 thmT t_prime) (FormHP cV0 cV1))
      e3 = thmT_t_prime

      -- inner pass (var 1 := Y1).
      innerPass :
        Deriv (eqF (ap2 sbf spec1 (FormHP cV0 cV1)) (FormHP cV0 Y1))
      innerPass =
        onePassHP (suc zero) Y1 cV0 cV1 cV0 Y1
          (sbt_at_var_nomatch (suc zero) zero Y1 refl)
          (sbt_at_var_match (suc zero) Y1)

      -- outer pass (var 0 := Y0 x) ; Y1 inert (num-based).
      outerPass :
        Deriv (eqF (ap2 sbf spec0 (FormHP cV0 Y1)) (FormHP (Y0 x) Y1))
      outerPass =
        onePassHP zero (Y0 x) cV0 Y1 (Y0 x) Y1
          (sbt_at_var_match zero (Y0 x))
          (sbt_inert_NumCode Y1 ncY1 zero (Y0 x))

  in ruleTrans e1
       (ruleTrans (congR sbf spec0 e2)
         (ruleTrans (congR sbf spec0 (congR sbf spec1 e3))
           (ruleTrans (congR sbf spec0 innerPass)
                      outerPass)))
