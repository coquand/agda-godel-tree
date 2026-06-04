{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashImp -- Carneiro-lifted (imp Rf) variant of T4.CgiClash.
--
-- Discovery:  thmT_at_sb  does NOT need its own imp-lift -- it consumes
-- only closed Terms (no Deriv argument), so the resulting closed Deriv
-- can be  impLift -ed.  Same for  encoded_exfalso  and  passK .
--
-- The h-dependencies that DO need lifting are confined to:
--   * dNeg (= imp_dNeg_at_kmax from DischargeKdefImp)
--   * run  (= imp_dEval_witness from ChainKdefImp, fed into dPos via
--             runProg_eq + thm13_binary)
--   * the encoded_mp / chaitin_G1_assembly chain that consumes the
--     above.
--
-- For encoded_mp we already have  T4.Thm12.EncodedMp.imp_encoded_mp .
-- thm13_binary and dPos we re-derive locally under  imp Rf .

module T4.CgiClashImp where

open import T4.Base
open import T4.Tags using
  ( tag_sb ; tag_ap1 ; tag_ap2 ; tag_eq ; tag_var )
open import T4.Code using ( codeFun2 ; codeFalse )
open import T4.Num  using ( num ; num_at_S )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp ; imp_encoded_mp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.KFormula using ( szLeqFun )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.Kdef using ( runProg ; runProg_eq ; Kcode ; Kcode_eval )
open import T4.CgiDPos using ( D )
open import T4.CgiClash using ( SomeProof ; mkProof ; cgiClash
                                ; passK ; cAp1f ; cAp2f ; szAtomT
                                ; KT ; defEqT ; cVarc )
open import T4.Thm12.All using ( thm12 ; thm12_Fun2 ; fst ; snd )
open import T4.Thm12.Thm13 using ( codeFXeqY2 ; thm13_binary )
open import T4.Thm12.CodeFTeq using ( codeFTeq2 )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impEqTrans ; impCong1 ; impCongL ; impCongR )
open import T4.ImpExtras
  using ( imp_eqTrans_imp )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- imp_thm13_binary -- Carneiro-lifted  thm13_binary .

imp_thm13_binary :
  (Rf : Formula) (g : Fun2) (x1 x2 y : Term) ->
  Deriv (imp Rf (eqF (ap2 g x1 x2) y)) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 g)) x1 x2))
                      (codeFXeqY2 g x1 x2 y)))
imp_thm13_binary Rf g x1 x2 y h_imp =
  let p_g = thm12_Fun2 g
      Df = fst p_g

      e_thm12 : Deriv (eqF (ap1 thmT (ap2 Df x1 x2)) (codeFTeq2 g x1 x2))
      e_thm12 = snd p_g x1 x2

      imp_num_bridge :
        Deriv (imp Rf (eqF (ap1 num (ap2 g x1 x2)) (ap1 num y)))
      imp_num_bridge = impCong1 num (ap2 g x1 x2) y h_imp

      codeApSlot : Term
      codeApSlot =
        ap2 Pair (natCode tag_ap2)
          (ap2 Pair (codeFun2 g) (ap2 Pair (ap1 num x1) (ap1 num x2)))

      imp_inner_pair :
        Deriv (imp Rf (eqF (ap2 Pair codeApSlot (ap1 num (ap2 g x1 x2)))
                            (ap2 Pair codeApSlot (ap1 num y))))
      imp_inner_pair = impCongR Pair (ap1 num (ap2 g x1 x2)) (ap1 num y)
                          codeApSlot imp_num_bridge

      imp_outer_bridge :
        Deriv (imp Rf (eqF (codeFTeq2 g x1 x2) (codeFXeqY2 g x1 x2 y)))
      imp_outer_bridge = impCongR Pair
        (ap2 Pair codeApSlot (ap1 num (ap2 g x1 x2)))
        (ap2 Pair codeApSlot (ap1 num y))
        (natCode tag_eq) imp_inner_pair

  in impEqTrans (ap1 thmT (ap2 Df x1 x2)) (codeFTeq2 g x1 x2)
       (codeFXeqY2 g x1 x2 y) (impLift {Rf} e_thm12) imp_outer_bridge

------------------------------------------------------------------------
-- imp_dPos -- Carneiro-lifted  CgiDPos.dPos .
--
-- Original:
--   dPos gL n0 x' rf =
--     let run = ruleTrans (runProg_eq gL n0) rf
--         d1 = thm13_binary runProg gL n0 (s x') run
--         bridge = closed
--     in ruleTrans d1 bridge

imp_dPos :
  (Rf : Formula) (gL n0 x' : Term) ->
  Deriv (imp Rf (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x'))) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProg)) gL n0))
                      (D gL n0 x')))
imp_dPos Rf gL n0 x' imp_rf =
  let run_eq : Deriv (eqF (ap2 runProg gL n0) (ap2 evalU (ap1 parse gL) n0))
      run_eq = runProg_eq gL n0

      imp_run : Deriv (imp Rf (eqF (ap2 runProg gL n0) (ap1 s x')))
      imp_run = impEqTrans (ap2 runProg gL n0) (ap2 evalU (ap1 parse gL) n0)
                  (ap1 s x') (impLift {Rf} run_eq) imp_rf

      imp_d1 : Deriv (imp Rf (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProg)) gL n0))
                                   (codeFXeqY2 runProg gL n0 (ap1 s x'))))
      imp_d1 = imp_thm13_binary Rf runProg gL n0 (ap1 s x') imp_run

      bridge : Deriv (eqF (codeFXeqY2 runProg gL n0 (ap1 s x')) (D gL n0 x'))
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp2f runProg (ap1 num gL) (ap1 num n0))
                   (num_at_S x'))

  in impEqTrans (ap1 thmT (ap2 (fst (thm12_Fun2 runProg)) gL n0))
       (codeFXeqY2 runProg gL n0 (ap1 s x')) (D gL n0 x')
       imp_d1 (impLift {Rf} bridge)

------------------------------------------------------------------------
-- imp_chaitin_G1_assembly -- Carneiro-lifted  chaitin_G1_assembly .

imp_chaitin_G1_assembly :
  (Rf : Formula) (P cPos cExF w0 : Term) ->
  Deriv (imp Rf (eqF (ap1 thmT cPos) P)) ->
  Deriv (imp Rf (eqF (ap1 thmT w0)  (cNeg P))) ->
  Deriv (imp Rf (eqF (ap1 thmT cExF) (cImp P (cImp (cNeg P) codeFalse)))) ->
  Deriv (imp Rf (eqF (ap1 thmT (cmp (cmp cExF cPos) w0)) codeFalse))
imp_chaitin_G1_assembly Rf P cPos cExF w0 imp_dPos imp_dNeg imp_dExF =
  let imp_mp1 :
        Deriv (imp Rf (eqF (ap1 thmT (cmp cExF cPos)) (cImp (cNeg P) codeFalse)))
      imp_mp1 = imp_encoded_mp Rf cExF cPos P (cImp (cNeg P) codeFalse)
                  imp_dExF imp_dPos

      imp_mp2 :
        Deriv (imp Rf (eqF (ap1 thmT (cmp (cmp cExF cPos) w0)) codeFalse))
      imp_mp2 = imp_encoded_mp Rf (cmp cExF cPos) w0 (cNeg P) codeFalse
                  imp_mp1 imp_dNeg
  in imp_mp2

------------------------------------------------------------------------
-- The integrated imp-lifted clash.
--
-- Mirrors  T4.CgiClash.cgiClash  with h-dependent inputs (dNeg, run)
-- replaced by their imp-lifted versions.
--
-- Output:  pf : Term  (identical to closed cgiClash's pf -- h-independent
-- Term construction);  imp_isPf : Deriv (imp Rf (eqF (ap1 thmT pf) codeFalse)) .

-- ImpSomeProof  :  Sigma type alias instead of a dependent record
-- (per feedback_specialised_record_typecheck_blowup -- dependent records
-- with Deriv fields over thmT cause 30-60s typecheck blowup).

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst

ImpSomeProof : Formula -> Set
ImpSomeProof Rf =
  Sigma Term (\ pf -> Deriv (imp Rf (eqF (ap1 thmT pf) codeFalse)))

mkImpProof :
  {Rf : Formula} (pf : Term) ->
  Deriv (imp Rf (eqF (ap1 thmT pf) codeFalse)) ->
  ImpSomeProof Rf
mkImpProof pf d = mkSigma pf d

------------------------------------------------------------------------
-- Body of the imp-lifted clash as a PARAMETRIC MODULE -- matches the
-- `module _ (L gL n0 x' : Term) where` pattern of the original CgiClash,
-- avoiding a 100-binding let-pile that Agda's elaborator struggles with.

module ClashBody
  (Rf : Formula) (L gL n0 x' w0 cSize : Term)
  (imp_dNeg : Deriv (imp Rf (eqF (ap1 thmT w0) (ap1 (Kcode L) x'))))
  (dSize    : Deriv (eqF (ap1 thmT cSize)
                          (szAtomT L gL n0 x' (ap1 num gL))))
  (imp_run  : Deriv (imp Rf (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x'))))
  where

  S0 : Term
  S0 = ap1 num gL
  S1 : Term
  S1 = ap1 num n0
  spec0 : Term
  spec0 = ap2 Pair (natCode zero) S0
  spec1 : Term
  spec1 = ap2 Pair (natCode (suc zero)) S1

  KOpen : Term
  KOpen = KT L gL n0 x' (cVarc zero) (cVarc (suc zero))
  KMid : Term
  KMid  = KT L gL n0 x' (cVarc zero) (ap1 num n0)
  KClosed : Term
  KClosed = KT L gL n0 x' (ap1 num gL) (ap1 num n0)

  innerEq : Deriv (eqF (ap2 sbf spec1 KOpen) KMid)
  innerEq =
    passK L gL n0 x' (suc zero) S1
      (cVarc zero) (cVarc zero) (cVarc (suc zero)) (ap1 num n0)
      (sbt_at_var_nomatch (suc zero) zero S1 refl)
      (sbt_at_var_match (suc zero) S1)

  outerEq : Deriv (eqF (ap2 sbf spec0 KMid) KClosed)
  outerEq =
    passK L gL n0 x' zero S0
      (cVarc zero) (ap1 num gL) (ap1 num n0) (ap1 num n0)
      (sbt_at_var_match zero S0)
      (sbt_num_inert zero S0 n0)

  substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KOpen)) KClosed)
  substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

  imp_dNegOpen : Deriv (imp Rf (eqF (ap1 thmT w0) KOpen))
  imp_dNegOpen = imp_eqTrans_imp imp_dNeg (impLift {Rf} (Kcode_eval L x'))

  innerWrap : Term
  innerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)
  outerWrap : Term
  outerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

  imp_congR_inner :
    Deriv (imp Rf (eqF (ap2 sbf spec1 (ap1 thmT w0)) (ap2 sbf spec1 KOpen)))
  imp_congR_inner = impCongR sbf (ap1 thmT w0) KOpen spec1 imp_dNegOpen

  imp_dInner :
    Deriv (imp Rf (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen)))
  imp_dInner = imp_eqTrans_imp (impLift {Rf} (thmT_at_sb spec1 w0))
                               imp_congR_inner

  imp_congR_outer :
    Deriv (imp Rf (eqF (ap2 sbf spec0 (ap1 thmT innerWrap))
                        (ap2 sbf spec0 (ap2 sbf spec1 KOpen))))
  imp_congR_outer = impCongR sbf (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen)
                      spec0 imp_dInner

  imp_d_to_substBoth :
    Deriv (imp Rf (eqF (ap1 thmT outerWrap)
                        (ap2 sbf spec0 (ap2 sbf spec1 KOpen))))
  imp_d_to_substBoth =
    imp_eqTrans_imp (impLift {Rf} (thmT_at_sb spec0 innerWrap))
                    imp_congR_outer

  imp_dInst : Deriv (imp Rf (eqF (ap1 thmT outerWrap) KClosed))
  imp_dInst = imp_eqTrans_imp imp_d_to_substBoth (impLift {Rf} substBoth)

  imp_dNegFinal :
    Deriv (imp Rf (eqF (ap1 thmT (cmp outerWrap cSize)) (cNeg (D gL n0 x'))))
  imp_dNegFinal =
    imp_encoded_mp Rf outerWrap cSize
      (szAtomT L gL n0 x' (ap1 num gL))
      (cNeg (D gL n0 x'))
      imp_dInst (impLift {Rf} dSize)

  cPos : Term
  cPos = ap2 (fst (thm12_Fun2 runProg)) gL n0

  imp_dPosD : Deriv (imp Rf (eqF (ap1 thmT cPos) (D gL n0 x')))
  imp_dPosD = imp_dPos Rf gL n0 x' imp_run

  imp_dExF :
    Deriv (imp Rf (eqF (ap1 thmT (exfProof (D gL n0 x') codeFalse))
                        (cImp (D gL n0 x') (cImp (cNeg (D gL n0 x')) codeFalse))))
  imp_dExF = impLift {Rf} (encoded_exfalso (D gL n0 x') codeFalse)

  pf : Term
  pf = cmp (cmp (exfProof (D gL n0 x') codeFalse) cPos)
           (cmp outerWrap cSize)

  imp_final : Deriv (imp Rf (eqF (ap1 thmT pf) codeFalse))
  imp_final =
    imp_chaitin_G1_assembly Rf (D gL n0 x') cPos
      (exfProof (D gL n0 x') codeFalse) (cmp outerWrap cSize)
      imp_dPosD imp_dNegFinal imp_dExF

imp_cgiClash :
  (Rf : Formula) (L gL n0 x' w0 cSize : Term) ->
  Deriv (imp Rf (eqF (ap1 thmT w0) (ap1 (Kcode L) x'))) ->
  Deriv (eqF (ap1 thmT cSize) (szAtomT L gL n0 x' (ap1 num gL))) ->
  Deriv (imp Rf (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x'))) ->
  ImpSomeProof Rf
imp_cgiClash Rf L gL n0 x' w0 cSize imp_dNeg dSize imp_run =
  let open ClashBody Rf L gL n0 x' w0 cSize imp_dNeg dSize imp_run
  in mkImpProof pf imp_final
