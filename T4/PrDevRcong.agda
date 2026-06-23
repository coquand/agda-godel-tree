{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrDevRcong -- the R-congruence equation of  devF  (deferred from PrDev):
--   devF (tmAp2 (cRec g h1 h2) a b) = tmAp2 (cRec g h1 h2) (devF a) (devF b)
-- whenever the recursion argument  b  is NOT  tmO  (Fst b != 0) and NOT
-- s-headed (Fst (Fst (Snd b)) != 3) -- i.e. neither an Rb nor an Rs redex.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrDevRcong where

open import T4.Base

open import T4.PrCodeObj using ( tmAp2 ; cRec )
open import T4.PrDev

open import T4.DerSrc using ( fork_false_to_snd )

open import BRA3.Church       using ( pi )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( decideNatNeq )

devF_R_cong : (g h1 h2 a b : Term) (mb mf : Nat) ->
  Deriv (eqF (ap1 Fst b) (natCode mb)) -> ((Eq mb 0) -> Empty) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd b))) (natCode mf)) -> ((Eq mf 3) -> Empty) ->
  Deriv (eqF (ap1 devF (tmAp2 (cRec g h1 h2) a b))
             (tmAp2 (cRec g h1 h2) (ap1 devF a) (ap1 devF b)))
devF_R_cong g h1 h2 a b mb mf hb mb0 hbf mf3 =
  let open Rec g h1 h2 a b
      headB_v : Deriv (eqF (ap1 headB input_pkg) (natCode mb))
      headB_v = ruleTrans (compose1U_eq Fst apB input_pkg)
                  (ruleTrans (cong1 Fst apB_eq) hb)
      fstSndB : Deriv (eqF (ap1 (compose1U Fst bSnd) input_pkg) (ap1 Fst (ap1 Snd b)))
      fstSndB = ruleTrans (compose1U_eq Fst bSnd input_pkg)
                  (cong1 Fst (ruleTrans (compose1U_eq Snd apB input_pkg) (cong1 Snd apB_eq)))
      headBFun_v : Deriv (eqF (ap1 headBFun input_pkg) (natCode mf))
      headBFun_v = ruleTrans (compose1U_eq Fst (compose1U Fst bSnd) input_pkg)
                     (ruleTrans (cong1 Fst fstSndB) hbf)
      fires : Deriv (eqF (ap1 R_disp input_pkg) (ap1 br_Rcong input_pkg))
      fires =
        ruleTrans (fork_false_to_snd br_Rb R_lvl2 (C natEqF headB (constN 0)) input_pkg
                     (idxTest_skip headB mb 0 input_pkg (decideNatNeq mb 0 mb0) headB_v))
                  (fork_false_to_snd br_Rs br_Rcong (C natEqF headBFun (constN 3)) input_pkg
                     (idxTest_skip headBFun mf 3 input_pkg (decideNatNeq mf 3 mf3) headBFun_v))
      val : Deriv (eqF (ap1 br_Rcong input_pkg)
                       (tmAp2 (cRec g h1 h2) (ap1 devF a) (ap1 devF b)))
      val = mkAp2_val (mkRec bG0 bH1 bH2) devA devB input_pkg
              (cRec g h1 h2) (ap1 devF a) (ap1 devF b)
              (mkRec_val bG0 bH1 bH2 input_pkg g h1 h2 bG0_eq bH1_eq bH2_eq) recA recB
  in ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val))
