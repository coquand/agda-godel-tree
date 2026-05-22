{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedReflVar0 -- the encoded reflexivity at the SPECIFIC
-- value  var 0 .
--
-- z_axRefl_v0 : Term
-- thmT_eq_z_axRefl_v0 : Deriv (eqF (ap1 thmT z_axRefl_v0) (codeFormula (atomic (eqn (var 0) (var 0)))))
--
-- Construction follows the BRA-Deriv proof  axRefl (var 0)
--    = mp (mp (ax_eqTrans (u (var 0)) (var 0) (var 0)) (ax_u (var 0))) (ax_u (var 0))
-- but at the encoded level :
--
--   (1) The ax_eqTrans-instance is encoded via a 5-sb-wrap using two
--       FRESH variable indices  c1 = 3 , c2 = 4 .  These are above
--       maxVarT (u (var 0)) = maxVarT (var 0) = 1 .  The fresh-c trick
--       (Church Standard Metatheorem VII style, see BRA4.RuleInst2)
--       avoids the  Closed  premises of the standard
--       thmT_complete_ax_eqTrans by renaming v1 -> v3 and v2 -> v4
--       BEFORE substituting v0 -> u(var 0) , v3 -> var 0 , v4 -> var 0 .
--       Because  c1 = 3 , c2 = 4  are concrete Nats, ALL natEq reductions
--       inside substF chains reduce definitionally in Agda.
--
--   (2) The two ax_u encodings use the standard  encode_sb 0 (codeTerm (var 0)) (packAx 2 O) .
--
--   (3) The two mp wraps use  thmT_at_mp_codeF .

module BRA4.Thm12.EncodedReflVar0 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.SbContract
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.SbDerived         using ( module Derive )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx2         using ( thmT_at_axN2 )
open import BRA4.ThmTAtAx4         using ( thmT_at_axN4 )
open import BRA4.ThmTAtMp          using ( thmT_at_mp_codeF )
open import BRA4.ThmTCompleteAxClosedFree using ( thmT_complete_ax_u )

open import BRA3.Church            using ( pi )

open SbContract sbContract
open Derive sbt sbf sbContract

------------------------------------------------------------------------
-- step_sb_wrap : sb-wrap a code whose thmT-eval is known to be a
-- codeFormula.  Output is the substituted codeFormula.

private
  step_sb_wrap :
    (k : Nat) (t : Term)
    (inputCode : Term) (schemaCarrier : Formula)
    (inner_eq : Deriv (eqF (ap1 thmT inputCode) (codeFormula schemaCarrier))) ->
    Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb)
                                  (ap2 pi (ap2 pi (natCode k) (codeTerm t)) inputCode)))
                (codeFormula (substF k t schemaCarrier)))
  step_sb_wrap k t inputCode schemaCarrier inner_eq =
    let spec : Term
        spec = ap2 Pair (natCode k) (codeTerm t)
        e_sb = thmT_at_sb spec inputCode
        e_lift = congR sbf spec inner_eq
        e_codeF = sbfEq_codeFormula k t schemaCarrier
    in ruleTrans e_sb (ruleTrans e_lift e_codeF)

------------------------------------------------------------------------
-- Fresh variable indices c1, c2 with c1 = 3, c2 = 4.  Both > 2 (so
-- distinct from schema vars 0, 1, 2) and > maxVarT (var 0) = 1.

private
  c1 : Nat
  c1 = suc (suc (suc zero))

  c2 : Nat
  c2 = suc (suc (suc (suc zero)))

------------------------------------------------------------------------
-- The axN4 schema as a Formula.

private
  axN4_F : Formula
  axN4_F = imp (atomic (eqn (var zero) (var (suc zero))))
                (imp (atomic (eqn (var zero) (var (suc (suc zero)))))
                      (atomic (eqn (var (suc zero)) (var (suc (suc zero))))))

packAx4_O : Term
packAx4_O = ap2 Pair (natCode tag_ax) (ap2 Pair (natCode (suc (suc (suc (suc zero))))) O)

packAx2_O : Term
packAx2_O = ap2 Pair (natCode tag_ax) (ap2 Pair (natCode (suc (suc zero))) O)

------------------------------------------------------------------------
-- 5-sb-wrap step formulas (intermediate substF results).
-- Each form below is the EXPECTED reduced form ; Agda checks via
-- normalization (all natEq operations are on concrete Nats).

private
  -- After substF 1 (var c1) axN4_F :
  -- imp (eqn v0 (var c1)) (imp (eqn v0 v2) (eqn (var c1) v2))
  F1 : Formula
  F1 = substF (suc zero) (var c1) axN4_F

  -- After substF 2 (var c2) F1 :
  -- imp (eqn v0 (var c1)) (imp (eqn v0 (var c2)) (eqn (var c1) (var c2)))
  F2 : Formula
  F2 = substF (suc (suc zero)) (var c2) F1

  -- After substF 0 (u (var 0)) F2 :
  -- imp (eqn (u v0) (var c1)) (imp (eqn (u v0) (var c2)) (eqn (var c1) (var c2)))
  F3 : Formula
  F3 = substF zero (ap1 u (var zero)) F2

  -- After substF c1 (var 0) F3 :
  -- imp (eqn (u v0) v0) (imp (eqn (u v0) (var c2)) (eqn v0 (var c2)))
  F4 : Formula
  F4 = substF c1 (var zero) F3

  -- After substF c2 (var 0) F4 :
  -- imp (eqn (u v0) v0) (imp (eqn (u v0) v0) (eqn v0 v0))
  --  =  P_imp_imp_Q   where  P = (atomic (eqn (u v0) v0)) , Q = atomic (eqn v0 v0).
  F5 : Formula
  F5 = substF c2 (var zero) F4

------------------------------------------------------------------------
-- 5-sb-wrap construction of encoded ax_eqTrans (u v0) v0 v0.

-- Layer 1 : sb at var 1 with substituent (var c1).
layer1_code : Term
layer1_code = ap2 pi (natCode tag_sb)
                (ap2 pi (ap2 pi (natCode (suc zero)) (codeTerm (var c1)))
                        packAx4_O)

-- Layer 2 : sb at var 2 with substituent (var c2).
layer2_code : Term
layer2_code = ap2 pi (natCode tag_sb)
                (ap2 pi (ap2 pi (natCode (suc (suc zero))) (codeTerm (var c2)))
                        layer1_code)

-- Layer 3 : sb at var 0 with substituent (u (var 0)).
layer3_code : Term
layer3_code = ap2 pi (natCode tag_sb)
                (ap2 pi (ap2 pi (natCode zero) (codeTerm (ap1 u (var zero))))
                        layer2_code)

-- Layer 4 : sb at var c1 with substituent (var 0).
layer4_code : Term
layer4_code = ap2 pi (natCode tag_sb)
                (ap2 pi (ap2 pi (natCode c1) (codeTerm (var zero)))
                        layer3_code)

-- Layer 5 : sb at var c2 with substituent (var 0).
layer5_code : Term
layer5_code = ap2 pi (natCode tag_sb)
                (ap2 pi (ap2 pi (natCode c2) (codeTerm (var zero)))
                        layer4_code)

private
  layer1_eq :
    Deriv (eqF (ap1 thmT layer1_code) (codeFormula F1))
  layer1_eq = step_sb_wrap (suc zero) (var c1) packAx4_O axN4_F (thmT_at_axN4 O)

  layer2_eq :
    Deriv (eqF (ap1 thmT layer2_code) (codeFormula F2))
  layer2_eq = step_sb_wrap (suc (suc zero)) (var c2) layer1_code F1 layer1_eq

  layer3_eq :
    Deriv (eqF (ap1 thmT layer3_code) (codeFormula F3))
  layer3_eq = step_sb_wrap zero (ap1 u (var zero)) layer2_code F2 layer2_eq

  layer4_eq :
    Deriv (eqF (ap1 thmT layer4_code) (codeFormula F4))
  layer4_eq = step_sb_wrap c1 (var zero) layer3_code F3 layer3_eq

  layer5_eq :
    Deriv (eqF (ap1 thmT layer5_code) (codeFormula F5))
  layer5_eq = step_sb_wrap c2 (var zero) layer4_code F4 layer4_eq

------------------------------------------------------------------------
-- F5 has the form  imp P (imp P Q)  where P = atomic (eqn (u v0) v0)
-- and Q = atomic (eqn v0 v0) .  We need Agda to verify this.

private
  P_form : Formula
  P_form = atomic (eqn (ap1 u (var zero)) (var zero))

  Q_form : Formula
  Q_form = atomic (eqn (var zero) (var zero))

  -- Definitional check: F5 = imp P_form (imp P_form Q_form).
  -- All natEq reductions involve concrete Nats (0, 1, 2, c1=3, c2=4) so
  -- Agda computes everything.
  F5_eq : Eq F5 (imp P_form (imp P_form Q_form))
  F5_eq = refl

------------------------------------------------------------------------
-- Now apply two thmT_at_mp_codeF's with thmT_complete_ax_u (var 0).

-- z_axU_v0 = encode (ax_u (var 0))
z_axU_v0 : Term
z_axU_v0 = ap2 pi (natCode tag_sb)
             (ap2 pi (ap2 pi (natCode zero) (codeTerm (var zero)))
                     packAx2_O)

-- Inner mp : combine layer5 with z_axU_v0 via thmT_at_mp_codeF.
inner_mp_code : Term
inner_mp_code = ap2 pi (natCode tag_mp) (ap2 pi layer5_code z_axU_v0)

-- Outer mp : combine inner_mp_code with z_axU_v0 again.
outer_mp_code : Term
outer_mp_code = ap2 pi (natCode tag_mp) (ap2 pi inner_mp_code z_axU_v0)

private
  z_axU_v0_eq :
    Deriv (eqF (ap1 thmT z_axU_v0) (codeFormula P_form))
  z_axU_v0_eq = thmT_complete_ax_u (var zero)

  layer5_eq_renamed :
    Deriv (eqF (ap1 thmT layer5_code) (codeFormula (imp P_form (imp P_form Q_form))))
  layer5_eq_renamed =
    eqSubst (\ G -> Deriv (eqF (ap1 thmT layer5_code) (codeFormula G)))
            F5_eq
            layer5_eq

  inner_mp_eq :
    Deriv (eqF (ap1 thmT inner_mp_code) (codeFormula (imp P_form Q_form)))
  inner_mp_eq =
    thmT_at_mp_codeF layer5_code z_axU_v0 P_form (imp P_form Q_form)
                      layer5_eq_renamed z_axU_v0_eq

------------------------------------------------------------------------
-- The encoded refl at var 0.

z_axRefl_v0 : Term
z_axRefl_v0 = outer_mp_code

thmT_eq_z_axRefl_v0 :
  Deriv (eqF (ap1 thmT z_axRefl_v0) (codeFormula Q_form))
thmT_eq_z_axRefl_v0 =
  thmT_at_mp_codeF inner_mp_code z_axU_v0 P_form Q_form
                    inner_mp_eq z_axU_v0_eq
