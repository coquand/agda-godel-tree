{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.NoVarZ -- the NoVar witness for z_axRefl_v0 .
--
-- z_axRefl_v0 (defined in BRA4.Thm12.EncodedReflVar0) is built entirely
-- from O, ap1 s (inside natCode), and ap2 pi  -- no  var k  constructor.
-- This module discharges that fact, enabling constTermFun1 to bake
-- z_axRefl_v0 into a proper Fun1.

module BRA4.Thm12.NoVarZ where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Thm12.EncodedReflVar0
open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; NoVar_natCode ; NoVarAnd ; mkAnd )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- NoVar witnesses for the intermediate constants.

NoVar_codeTerm_var :
  (n : Nat) -> NoVar (ap2 pi (natCode tag_var) (natCode n))
NoVar_codeTerm_var n = mkAnd (NoVar_natCode tag_var) (NoVar_natCode n)

NoVar_codeTerm_u_var_zero :
  NoVar (ap2 pi (natCode tag_ap1)
                (ap2 pi (natCode tag_u)
                        (ap2 pi (natCode tag_var) (natCode zero))))
NoVar_codeTerm_u_var_zero =
  mkAnd (NoVar_natCode tag_ap1)
        (mkAnd (NoVar_natCode tag_u) (NoVar_codeTerm_var zero))

NoVar_packAx :
  (k : Nat) -> NoVar (ap2 pi (natCode tag_ax) (ap2 pi (natCode k) O))
NoVar_packAx k =
  mkAnd (NoVar_natCode tag_ax)
        (mkAnd (NoVar_natCode k) tt)

NoVar_packAx4_O : NoVar packAx4_O
NoVar_packAx4_O = NoVar_packAx (suc (suc (suc (suc zero))))

NoVar_packAx2_O : NoVar packAx2_O
NoVar_packAx2_O = NoVar_packAx (suc (suc zero))

------------------------------------------------------------------------
-- Layer-by-layer.

NoVar_layer1 : NoVar layer1_code
NoVar_layer1 =
  mkAnd (NoVar_natCode tag_sb)
        (mkAnd (mkAnd (NoVar_natCode (suc zero))
                       (NoVar_codeTerm_var (suc (suc (suc zero)))))
               NoVar_packAx4_O)

NoVar_layer2 : NoVar layer2_code
NoVar_layer2 =
  mkAnd (NoVar_natCode tag_sb)
        (mkAnd (mkAnd (NoVar_natCode (suc (suc zero)))
                       (NoVar_codeTerm_var (suc (suc (suc (suc zero))))))
               NoVar_layer1)

NoVar_layer3 : NoVar layer3_code
NoVar_layer3 =
  mkAnd (NoVar_natCode tag_sb)
        (mkAnd (mkAnd (NoVar_natCode zero)
                       NoVar_codeTerm_u_var_zero)
               NoVar_layer2)

NoVar_layer4 : NoVar layer4_code
NoVar_layer4 =
  mkAnd (NoVar_natCode tag_sb)
        (mkAnd (mkAnd (NoVar_natCode (suc (suc (suc zero))))
                       (NoVar_codeTerm_var zero))
               NoVar_layer3)

NoVar_layer5 : NoVar layer5_code
NoVar_layer5 =
  mkAnd (NoVar_natCode tag_sb)
        (mkAnd (mkAnd (NoVar_natCode (suc (suc (suc (suc zero)))))
                       (NoVar_codeTerm_var zero))
               NoVar_layer4)

NoVar_z_axU_v0 : NoVar z_axU_v0
NoVar_z_axU_v0 =
  mkAnd (NoVar_natCode tag_sb)
        (mkAnd (mkAnd (NoVar_natCode zero)
                       (NoVar_codeTerm_var zero))
               NoVar_packAx2_O)

NoVar_inner_mp : NoVar inner_mp_code
NoVar_inner_mp =
  mkAnd (NoVar_natCode tag_mp)
        (mkAnd NoVar_layer5 NoVar_z_axU_v0)

NoVar_z_axRefl_v0 : NoVar z_axRefl_v0
NoVar_z_axRefl_v0 =
  mkAnd (NoVar_natCode tag_mp)
        (mkAnd NoVar_inner_mp NoVar_z_axU_v0)
