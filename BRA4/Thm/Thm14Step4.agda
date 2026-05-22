{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14Step4 -- Step 4 of Guard's Theorem 14 proof in BRA4 ,
-- EXACTLY matching guard15.pdf p.17 line 4) :
--
--     th(x) = j   ⊃   th(K_part(x))  =  "th(x_) ≠ sub(i,i)"  ,    by the definition of j.
--
-- BRA4 form (non-parametric ;  F  fixed in BRA4.Thm.Thm14F ; sub-form
-- diagonal:  G = neg(eqF(thmT(var 1))(ap2 sub i i)) ).
-- Universal in  x : Term .  With Guard 's helpers  code , encEqF , encThm ,
--  encSub , encNeg  ( in BRA4.Thm.Thm14F ) :
--
--     step4 :  (x : Term) ->
--              Deriv (imp (P_x x)
--                      (eqF (ap1 thmT (K_part x))
--                            (encNeg (encEqF (encThm (code x))
--                                            (encSub (code i) (code i))))))
--                                                       -- "th(x_) ≠ sub(i,i)"
--
-- Construction.  K_part  uses BRA4's encoded-substitution constructor
--  (tag_sb)  with substitution spec  Pair (natCode 1) (code x)  ( = Pair 1 num x ,
-- DIRECT , NOT codeTerm-wrapped) .  The key primitive is  thmT_at_sb :
--    thmT (sb cSpec cProofIdx)  =Deriv=  sbf cSpec (thmT cProofIdx) .
-- Under  P_x  (thmT x = j)  we get  sbf cSpec j  =Deriv= sbf cSpec (codeFormula G)
--  ( via codeFormulaG_eq_j ) .  Then  sbf cSpec (codeFormula G)  evaluates by
-- the per-shape closures  sbf_at_neg / sbf_at_atomic / sbt_at_ap1 / sbt_at_var_match /
--  sbt_at_ap2 / (sbt-on-codeTerm-of-numeral helper)  to the Guard-target form .
-- Final bridges via  numEq  on the two  code i  slots .

module BRA4.Thm.Thm14Step4 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import BRA4.Num               using ( num )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.NumContract       using ( numContract ; module NumContract )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.Sub               using ( sub )
open import BRA4.SbContract        using ( SbContract ; module SbContract )
open import BRA4.Thm12.ImpHelpers
  using ( impLift ; impRefl ; impCongR ; impEqTrans )
open import BRA4.Thm.Thm14F
  using ( i ; iNat ; j ; G ; code ; encEqF ; encThm ; encSub ; encNeg
        ; codeFormulaG_eq_j )
open import BRA4.Thm.Thm14Step1    using ( P_x )

open SbContract sbContract
open NumContract numContract using ( numEq )

------------------------------------------------------------------------
-- Helper :  sbt at  codeTerm (natCode n)  =Deriv=  codeTerm (natCode n) .
--
-- For any  cSpec = Pair (natCode k) S , by meta-induction on  n :
--   n = 0 :  sbt cSpec O = O  via sbt_at_O .
--   n = suc m :  codeTerm (natCode (suc m)) = Pair tag_ap1 (Pair (codeFun1 s) (codeTerm (natCode m))) ;
--               sbt_at_ap1 + IH .

sbt_codeTerm_natCode_eq :
  (k : Nat) (S : Term) (n : Nat) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm (natCode n)))
              (codeTerm (natCode n)))
sbt_codeTerm_natCode_eq k S zero =
  sbt_at_O (ap2 Pair (natCode k) S)
sbt_codeTerm_natCode_eq k S (suc n) =
  let
    spec : Term
    spec = ap2 Pair (natCode k) S

    -- (1)  sbt spec (codeTerm (ap1 s (natCode n)))
    --        =Deriv= Pair tag_ap1 (Pair (codeFun1 s) (sbt spec (codeTerm (natCode n)))) .
    step1 :
      Deriv (eqF (ap2 sbt spec (codeTerm (ap1 s (natCode n))))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 s)
                      (ap2 sbt spec (codeTerm (natCode n))))))
    step1 = sbt_at_ap1 k S s (codeTerm (natCode n))

    -- IH
    ih :
      Deriv (eqF (ap2 sbt spec (codeTerm (natCode n)))
                  (codeTerm (natCode n)))
    ih = sbt_codeTerm_natCode_eq k S n

    -- (2) Push IH inside the Pair structure .
    step2 :
      Deriv (eqF (ap2 Pair (codeFun1 s) (ap2 sbt spec (codeTerm (natCode n))))
                  (ap2 Pair (codeFun1 s) (codeTerm (natCode n))))
    step2 = congR Pair (codeFun1 s) ih

    step3 :
      Deriv (eqF (ap2 Pair (natCode tag_ap1)
                   (ap2 Pair (codeFun1 s) (ap2 sbt spec (codeTerm (natCode n)))))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 s) (codeTerm (natCode n)))))
    step3 = congR Pair (natCode tag_ap1) step2

  in ruleTrans step1 step3

------------------------------------------------------------------------
-- The substitution specification :  Pair (natCode 1) (code x) .
--
-- Note :  S = code x = ap1 num x  is the BRA-runtime substituent
-- DIRECTLY -- NOT  codeTerm  - wrapped .  This is what makes the
-- sbt_at_var_match closure produce exactly  code x  (= Guard's "x_") .

cSpec_x : Term -> Term
cSpec_x x = ap2 Pair (natCode (suc zero)) (code x)

------------------------------------------------------------------------
-- K_part x  =  Pair tag_sb (Pair (cSpec_x x) x)  -- the encoded sb-
-- substitution Term .  The proof-index slot is  x  itself .

K_part : Term -> Term
K_part x = ap2 Pair (natCode tag_sb) (ap2 Pair (cSpec_x x) x)

------------------------------------------------------------------------
-- Step 4 .  Guard's "th(x) = j ⊃ th(K_part(x)) = 'th(x_) ≠ sub(i,i)'" .

step4 :
  (x : Term) ->
  Deriv (imp (P_x x)
              (eqF (ap1 thmT (K_part x))
                    (encNeg (encEqF (encThm (code x))
                                     (encSub (code i) (code i))))))
step4 x =
  let
    P : Formula
    P = P_x x

    cSpec : Term
    cSpec = cSpec_x x

    --------------------------------------------------------------------
    -- (A)  thmT (K_part x)  =Deriv=  sbf cSpec (thmT x)
    --       [thmT_at_sb] , impLifted .
    step_A_uc :
      Deriv (eqF (ap1 thmT (K_part x))
                  (ap2 sbf cSpec (ap1 thmT x)))
    step_A_uc = thmT_at_sb cSpec x

    step_A_imp :
      Deriv (imp P (eqF (ap1 thmT (K_part x))
                         (ap2 sbf cSpec (ap1 thmT x))))
    step_A_imp = impLift {P} step_A_uc

    --------------------------------------------------------------------
    -- (B)  Under  P_x  (thmT x = j) :
    --        sbf cSpec (thmT x)  =Deriv=  sbf cSpec j .
    hyp_imp : Deriv (imp P (eqF (ap1 thmT x) j))
    hyp_imp = impRefl P

    step_B_imp :
      Deriv (imp P (eqF (ap2 sbf cSpec (ap1 thmT x))
                         (ap2 sbf cSpec j)))
    step_B_imp = impCongR {P} sbf (ap1 thmT x) j cSpec hyp_imp

    --------------------------------------------------------------------
    -- (C)  j  =Deriv=  codeFormula G   [via codeFormulaG_eq_j sym] ;
    --       sbf cSpec j  =Deriv=  sbf cSpec (codeFormula G) .
    j_eq_codeFG : Deriv (eqF j (codeFormula G))
    j_eq_codeFG = ruleSym codeFormulaG_eq_j

    step_C_uc :
      Deriv (eqF (ap2 sbf cSpec j) (ap2 sbf cSpec (codeFormula G)))
    step_C_uc = congR sbf cSpec j_eq_codeFG

    step_C_imp :
      Deriv (imp P (eqF (ap2 sbf cSpec j) (ap2 sbf cSpec (codeFormula G))))
    step_C_imp = impLift {P} step_C_uc

    --------------------------------------------------------------------
    -- (D)  Unfold  sbf cSpec (codeFormula G)  through  G 's Formula
    --       structure via per-shape closures .
    --
    -- G  =  neg ( atomic ( eqn (ap1 thmT (var 1)) (ap2 sub i i) ) ) .
    -- codeFormula G  =  Pair tag_neg ( Pair tag_eq ( Pair (codeTerm(ap1 thmT (var 1))) (codeTerm(ap2 sub i i)) ) ) .

    eqInner : Term
    eqInner =
      ap2 Pair (natCode tag_eq)
        (ap2 Pair (codeTerm (ap1 thmT (var (suc zero))))
                  (codeTerm (ap2 sub i i)))

    -- sbf_at_neg :  sbf cSpec (Pair tag_neg cP)  =Deriv=  Pair tag_neg (sbf cSpec cP) .
    step_D1 :
      Deriv (eqF (ap2 sbf cSpec (codeFormula G))
                  (ap2 Pair (natCode tag_neg)
                    (ap2 sbf cSpec eqInner)))
    step_D1 = sbf_at_neg (suc zero) (code x) eqInner

    -- sbf_at_atomic :  sbf cSpec (Pair tag_eq (Pair a b))
    --   =Deriv=  Pair tag_eq (Pair (sbt cSpec a) (sbt cSpec b)) .
    step_D2 :
      Deriv (eqF (ap2 sbf cSpec eqInner)
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair
                      (ap2 sbt cSpec (codeTerm (ap1 thmT (var (suc zero)))))
                      (ap2 sbt cSpec (codeTerm (ap2 sub i i))))))
    step_D2 = sbf_at_atomic (suc zero) (code x)
                (codeTerm (ap1 thmT (var (suc zero))))
                (codeTerm (ap2 sub i i))

    --------------------------------------------------------------------
    -- LHS slot :  sbt cSpec (codeTerm (ap1 thmT (var 1)))
    --   =Deriv=  Pair tag_ap1 (Pair (codeFun1 thmT) (sbt cSpec (codeTerm (var 1))))  [sbt_at_ap1]
    --   =Deriv=  Pair tag_ap1 (Pair (codeFun1 thmT) (code x))                          [sbt_at_var_match]
    --   =        encThm (code x) .

    step_E1 :
      Deriv (eqF (ap2 sbt cSpec (codeTerm (ap1 thmT (var (suc zero)))))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 thmT)
                      (ap2 sbt cSpec (codeTerm (var (suc zero)))))))
    step_E1 = sbt_at_ap1 (suc zero) (code x) thmT (codeTerm (var (suc zero)))

    step_E2 :
      Deriv (eqF (ap2 sbt cSpec (codeTerm (var (suc zero)))) (code x))
    step_E2 = sbt_at_var_match (suc zero) (code x)

    step_E :
      Deriv (eqF (ap2 sbt cSpec (codeTerm (ap1 thmT (var (suc zero)))))
                  (encThm (code x)))
    step_E =
      ruleTrans step_E1
        (congR Pair (natCode tag_ap1)
          (congR Pair (codeFun1 thmT) step_E2))

    --------------------------------------------------------------------
    -- RHS slot :  sbt cSpec (codeTerm (ap2 sub i i))
    --   =Deriv=  Pair tag_ap2 (Pair (codeFun2 sub) (Pair (sbt cSpec (codeTerm i)) (sbt cSpec (codeTerm i))))   [sbt_at_ap2]
    --   =Deriv=  Pair tag_ap2 (Pair (codeFun2 sub) (Pair (codeTerm i) (codeTerm i)))                            [sbt_codeTerm_natCode_eq]
    --   =Deriv=  Pair tag_ap2 (Pair (codeFun2 sub) (Pair (code i) (code i)))                                    [numEq iNat , sym , twice]
    --   =        encSub (code i) (code i) .

    step_F1 :
      Deriv (eqF (ap2 sbt cSpec (codeTerm (ap2 sub i i)))
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 sub)
                      (ap2 Pair
                        (ap2 sbt cSpec (codeTerm i))
                        (ap2 sbt cSpec (codeTerm i))))))
    step_F1 = sbt_at_ap2 (suc zero) (code x) sub (codeTerm i) (codeTerm i)

    sbt_i_eq : Deriv (eqF (ap2 sbt cSpec (codeTerm i)) (codeTerm i))
    sbt_i_eq = sbt_codeTerm_natCode_eq (suc zero) (code x) iNat

    code_i_eq : Deriv (eqF (codeTerm i) (code i))
    code_i_eq = ruleSym (numEq iNat)

    -- Combined: sbt cSpec (codeTerm i)  =Deriv=  code i .
    sbt_i_to_code : Deriv (eqF (ap2 sbt cSpec (codeTerm i)) (code i))
    sbt_i_to_code = ruleTrans sbt_i_eq code_i_eq

    step_F2 :
      Deriv (eqF (ap2 Pair
                    (ap2 sbt cSpec (codeTerm i))
                    (ap2 sbt cSpec (codeTerm i)))
                  (ap2 Pair (code i) (code i)))
    step_F2 =
      ruleTrans (congL Pair (ap2 sbt cSpec (codeTerm i)) sbt_i_to_code)
                (congR Pair (code i) sbt_i_to_code)

    step_F :
      Deriv (eqF (ap2 sbt cSpec (codeTerm (ap2 sub i i)))
                  (encSub (code i) (code i)))
    step_F =
      ruleTrans step_F1
        (congR Pair (natCode tag_ap2)
          (congR Pair (codeFun2 sub) step_F2))

    --------------------------------------------------------------------
    -- Combine step_D2 + step_E + step_F to get :
    --   sbf cSpec eqInner  =Deriv=  encEqF (encThm (code x)) (encSub (code i) (code i)) .
    step_D_combined :
      Deriv (eqF (ap2 sbf cSpec eqInner)
                  (encEqF (encThm (code x)) (encSub (code i) (code i))))
    step_D_combined =
      ruleTrans step_D2
        (congR Pair (natCode tag_eq)
          (ruleTrans
            (congL Pair (ap2 sbt cSpec (codeTerm (ap2 sub i i))) step_E)
            (congR Pair (encThm (code x)) step_F)))

    -- Now combine step_D1 + step_D_combined :
    --   sbf cSpec (codeFormula G)  =Deriv=  encNeg (encEqF (encThm (code x)) (encSub (code i) (code i))) .
    step_D :
      Deriv (eqF (ap2 sbf cSpec (codeFormula G))
                  (encNeg (encEqF (encThm (code x))
                                   (encSub (code i) (code i)))))
    step_D =
      ruleTrans step_D1
        (congR Pair (natCode tag_neg) step_D_combined)

    step_D_imp :
      Deriv (imp P (eqF (ap2 sbf cSpec (codeFormula G))
                         (encNeg (encEqF (encThm (code x))
                                          (encSub (code i) (code i))))))
    step_D_imp = impLift {P} step_D

    --------------------------------------------------------------------
    -- Chain everything via impEqTrans .

    step_AB :
      Deriv (imp P (eqF (ap1 thmT (K_part x))
                         (ap2 sbf cSpec j)))
    step_AB =
      impEqTrans {P}
        (ap1 thmT (K_part x))
        (ap2 sbf cSpec (ap1 thmT x))
        (ap2 sbf cSpec j)
        step_A_imp step_B_imp

    step_ABC :
      Deriv (imp P (eqF (ap1 thmT (K_part x))
                         (ap2 sbf cSpec (codeFormula G))))
    step_ABC =
      impEqTrans {P}
        (ap1 thmT (K_part x))
        (ap2 sbf cSpec j)
        (ap2 sbf cSpec (codeFormula G))
        step_AB step_C_imp

  in impEqTrans {P}
       (ap1 thmT (K_part x))
       (ap2 sbf cSpec (codeFormula G))
       (encNeg (encEqF (encThm (code x))
                        (encSub (code i) (code i))))
       step_ABC step_D_imp
