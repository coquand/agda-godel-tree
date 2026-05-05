{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12LiftComp
--
-- Theorem 12 (asymmetric) for the COMPOSITION cases  Lift f  (Fun2)
-- and  Comp f g  (Fun1), parametric in IHs for the sub-functors.
--
-- Generalises BRA.Thm12LiftI (Lift at f = I): the Lift case here
-- accepts an IH for ANY f : Fun1 at the substituted variable (cor v1).
-- Comp accepts IHs for both f and g.
--
-- The IHs are supplied as universal Deriv-functions (over arbitrary
-- input Term).  This matches the natural "structural recursion over
-- Fun1/Fun2" pattern: when Phase-7 glue is built, each sub-functor
-- IH is the recursive call into thm12_F1 / thm12_F2 .
--
-- Pattern (each composition case):
--   1. Use the per-axiom dispatcher (parDispAxLift / parDispAxComp /
--      ...) to encode the defining axiom at sub-functor IHs.
--   2. Use thmTDispRuleTrans_param to chain with the IHs.
--   3. Bridge the final  cor  -side via cong1 cor + the defining axiom.
--
-- No new infrastructure beyond what was used in Thm12LiftI.

module BRA.Thm12LiftComp where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axLift ; tagCode_axComp ; tagCode_axPost
  ; tagCode_axComp2 ; tagCode_axFan
  ; tagCode_ruleTrans ; tagCode_cong1 ; tagCode_congL ; tagCode_congR
  ; thmTDispAxLift_param ; thmTDispAxComp_param ; thmTDispAxPost_param
  ; thmTDispAxComp2_param ; thmTDispAxFan_param
  ; thmTDispRuleTrans_param ; thmTDispCong1_param
  ; thmTDispCongL_param ; thmTDispCongR_param )

------------------------------------------------------------------------
-- Universal asymmetric IH type for a Fun1 / Fun2.

UnivIH1 : Fun1 -> Set
UnivIH1 f = (x : Term) ->
  Sigma Term (\ Df ->
    Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq1Asym f x))))

UnivIH2 : Fun2 -> Set
UnivIH2 g = (x v : Term) ->
  Sigma Term (\ Dg ->
    Deriv (atomic (eqn (ap1 thmT Dg) (codeFTeq2Asym g x v))))

------------------------------------------------------------------------
-- Lift case: given UnivIH1 f, build thm12 for Lift f at v1, v2.

module LiftCase (f : Fun1) (IH_f : UnivIH1 f) (v1 v2 : Nat) where

  v1T : Term
  v1T = var v1

  v2T : Term
  v2T = var v2

  -- Sub-derivation 1: Lift f's defining axiom encoded at  aT = cor v1 ,  bT = cor v2 .

  Df_lift_ax : Term
  Df_lift_ax = ap2 Pair tagCode_axLift
                   (ap2 Pair (reify (codeF1 f))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  -- mid: encoded RHS of axLift (Lift f) (cor v1) (cor v2) = f (cor v1) ;
  -- it equals codeFTeq1Asym f v1T's LHS subterm.
  mid : Term
  mid = ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 f)) (ap1 cor v1T))

  -- LHS subterm of disp_lift's RHS-image: encoded ap2 (Lift f) (cor v1) (cor v2).
  lift_lhs : Term
  lift_lhs = ap2 Pair (reify tagAp2)
                 (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Lift I))))
                                      (reify (codeF1 f)))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  disp_lift : Deriv (atomic (eqn (ap1 thmT Df_lift_ax)
                                  (ap2 Pair lift_lhs mid)))
  disp_lift = thmTDispAxLift_param f (ap1 cor v1T) (ap1 cor v2T)

  -- Sub-derivation 2: IH for  f  at v1.
  -- IH_f v1T : Sigma Term (\Df_f -> Deriv (eqn (thmT Df_f) (codeFTeq1Asym f v1T))).
  -- codeFTeq1Asym f v1T = Pair (mkAp1T (codeF1 f) (cor v1T)) (cor (ap1 f v1T))
  --                    = Pair mid (cor (ap1 f v1T))   -- middle term matches!

  Df_IH : Term
  Df_IH = fst (IH_f v1T)

  ih_at_v1 : Deriv (atomic (eqn (ap1 thmT Df_IH) (codeFTeq1Asym f v1T)))
  ih_at_v1 = snd (IH_f v1T)

  -- Head-shape proof on Df_lift_ax for thmTDispRuleTrans_param.
  -- tagCode_axLift = reify (natCode tagAxLift) = ap2 Pair O (rest), so
  -- Fst (Pair tagCode_axLift _) = tagCode_axLift = Pair O (rest).
  shape_proof : Deriv (atomic (eqn (ap1 Fst Df_lift_ax)
                                    (ap2 Pair O
                                      (reify (natCode (suc (suc (suc (suc (suc (suc zero)))))))))))
  shape_proof = axFst tagCode_axLift _

  -- thmTDispRuleTrans_param chains disp_lift with ih_at_v1.

  cor_f_v1 : Term
  cor_f_v1 = ap1 cor (ap1 f v1T)

  Df_term : Term
  Df_term = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_lift_ax Df_IH)

  merged : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (ap2 Pair lift_lhs cor_f_v1)))
  merged = thmTDispRuleTrans_param Df_lift_ax Df_IH
            lift_lhs mid mid cor_f_v1
            _ _ shape_proof
            disp_lift ih_at_v1

  -- Bridge:  cor (f v1) -> cor (Lift f v1 v2)  via  cong1 cor + axLift.
  bridge_RHS : Deriv (atomic (eqn cor_f_v1
                                   (ap1 cor (ap2 (Lift f) v1T v2T))))
  bridge_RHS = cong1 cor (ruleSym (axLift f v1T v2T))

  bridge : Deriv (atomic (eqn (ap2 Pair lift_lhs cor_f_v1)
                               (codeFTeq2Asym (Lift f) v1T v2T)))
  bridge = congR Pair lift_lhs bridge_RHS

  thm12_Lift_f_param :
    Sigma Term (\ Df ->
      Deriv (atomic (eqn (ap1 thmT Df)
                          (codeFTeq2Asym (Lift f) v1T v2T))))
  thm12_Lift_f_param = mkSigma Df_term (ruleTrans merged bridge)

------------------------------------------------------------------------
-- Comp case: given UnivIH1 f and UnivIH1 g, build thm12 for Comp f g at v1.

module CompCase (f g : Fun1)
                (IH_f : UnivIH1 f) (IH_g : UnivIH1 g)
                (v1 : Nat) where

  v1T : Term
  v1T = var v1

  -- Comp f g's defining axiom:  (Comp f g)(x) = f (g x) .
  -- Encoded at xT = cor v1:
  --   parDispAxComp gives Pair (mkAp1T (codeF1 (Comp f g)) (cor v1))
  --                            (mkAp1T (codeF1 f) (mkAp1T (codeF1 g) (cor v1)))
  -- LHS subterm matches codeFTeq1Asym (Comp f g) v1T's LHS.
  -- RHS subterm:  f (g (cor v1))  encoded.  We need to bridge to  cor (f (g v1)) .

  Df_comp_ax : Term
  Df_comp_ax = ap2 Pair tagCode_axComp
                   (ap2 Pair (reify (codeF1 f))
                              (ap2 Pair (reify (codeF1 g)) (ap1 cor v1T)))

  -- LHS subterm of comp dispatch RHS = encoded  Comp f g (cor v1) .
  comp_lhs : Term
  comp_lhs = ap2 Pair (reify tagAp1)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp I I))))
                                       (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))))
                             (ap1 cor v1T))

  -- Mid 1: encoded  f (g (cor v1)) .  After axComp dispatch, the RHS subterm
  -- is  mkAp1T (codeF1 f) (mkAp1T (codeF1 g) (cor v1)) .
  comp_mid : Term
  comp_mid = ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 f))
                             (ap2 Pair (reify tagAp1)
                                       (ap2 Pair (reify (codeF1 g)) (ap1 cor v1T))))

  disp_comp : Deriv (atomic (eqn (ap1 thmT Df_comp_ax)
                                  (ap2 Pair comp_lhs comp_mid)))
  disp_comp = thmTDispAxComp_param f g (ap1 cor v1T)

  -- Now we need to bridge comp_mid -> cor (Comp f g (v1)) at the RHS.
  --
  -- comp_mid's structure is the encoded form of  f (g (cor v1)) .
  -- We want  cor (Comp f g v1) = cor (f (g v1))  by axComp + cong1 cor .
  --
  -- The IHs give us at the encoded level:
  --   IH_g at v1T : encoded  g (cor v1) = cor (g v1)
  --                = mkEqT (mkAp1T (codeF1 g) (cor v1)) (cor (g v1))
  --   IH_f at (g v1T) : encoded  f (cor (g v1)) = cor (f (g v1))
  --                  = mkEqT (mkAp1T (codeF1 f) (cor (g v1))) (cor (f (g v1)))
  --
  -- To use IH_f at  cor (g v1) , we need  mkAp1T (codeF1 f) (cor (g v1))
  -- as the LHS subterm.  But comp_mid has  mkAp1T (codeF1 f) (mkAp1T (codeF1 g) (cor v1))
  -- on the RHS subterm.  These differ in the inner  cor (g v1)  vs
  --  mkAp1T (codeF1 g) (cor v1)  -- this is exactly what IH_g says equal
  -- (modulo direction).
  --
  -- Strategy: chain via parEncCong1 + IH_g + IH_f, sequentially.
  -- We use parEncRuleTrans (= thmTDispRuleTrans_param) twice and
  -- parEncCong1 once.  This is the standard 3-fold composition pattern.
  --
  -- For brevity we implement it directly using thmTDispRuleTrans_param
  -- twice; cong1 at the encoded level uses thmTDispCong1_param.

  -- IH_g at v1T:
  Df_IH_g : Term
  Df_IH_g = fst (IH_g v1T)

  ih_g : Deriv (atomic (eqn (ap1 thmT Df_IH_g) (codeFTeq1Asym g v1T)))
  ih_g = snd (IH_g v1T)

  -- IH_f at (g v1T):
  Df_IH_f : Term
  Df_IH_f = fst (IH_f (ap1 g v1T))

  ih_f : Deriv (atomic (eqn (ap1 thmT Df_IH_f) (codeFTeq1Asym f (ap1 g v1T))))
  ih_f = snd (IH_f (ap1 g v1T))

  -- We use thmTDispCong1_param to lift IH_g into a cong1-form usable inside
  -- the encoded Pair structure.
  -- thmTDispCong1_param f y_h_T u1 u2 d_h
  --   : Deriv (eqn (thmT (Pair tagCode_cong1 (Pair (codeF1 f) y_h_T)))
  --                (Pair (mkAp1T (codeF1 f) u1)
  --                      (mkAp1T (codeF1 f) u2)))
  -- where d_h : Deriv (eqn (thmT y_h_T) (Pair u1 u2)).
  --
  -- Apply with f = f (the outer Fun1), y_h_T = Df_IH_g, u1 = mkAp1T (codeF1 g) (cor v1),
  -- u2 = cor (g v1).  Then we get encoded  f (g (cor v1)) = f (cor (g v1)) .

  -- Step A: lift IH_g via thmTDispCong1_param at outer f.
  --
  -- IH_g at v1T : thmT(Df_IH_g) = mkEqT (mkAp1T (codeF1 g) (cor v1)) (cor (g v1)).
  -- thmTDispCong1_param f Df_IH_g (mkAp1T (codeF1 g) (cor v1)) (cor (g v1)) ih_g
  --   : thmT(Pair tagCode_cong1 (Pair (codeF1 f) Df_IH_g))
  --       = Pair (mkAp1T (codeF1 f) (mkAp1T (codeF1 g) (cor v1)))
  --              (mkAp1T (codeF1 f) (cor (g v1)))

  -- Sub-Term shorthands.
  ih_g_LHS : Term
  ih_g_LHS = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 g)) (ap1 cor v1T))

  ih_g_RHS : Term
  ih_g_RHS = ap1 cor (ap1 g v1T)

  Df_cong_g : Term
  Df_cong_g = ap2 Pair tagCode_cong1
                   (ap2 Pair (reify (codeF1 f)) Df_IH_g)

  -- u1, u2 of cong-lifted IH_g.
  cong_u1 : Term
  cong_u1 = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) ih_g_LHS)

  cong_u2 : Term
  cong_u2 = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) ih_g_RHS)

  cong_g : Deriv (atomic (eqn (ap1 thmT Df_cong_g)
                               (ap2 Pair cong_u1 cong_u2)))
  cong_g = thmTDispCong1_param f Df_IH_g ih_g_LHS ih_g_RHS ih_g

  -- Step B: chain disp_comp + cong_g via thmTDispRuleTrans_param.
  -- disp_comp's RHS u2 = comp_mid = cong_u1 (definitionally).

  shape_comp_ax : Deriv (atomic (eqn (ap1 Fst Df_comp_ax)
                                      (ap2 Pair O
                                        (reify (natCode (suc (suc (suc (suc zero)))))))))
  shape_comp_ax = axFst tagCode_axComp _

  Df_step1 : Term
  Df_step1 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_comp_ax Df_cong_g)

  step1 : Deriv (atomic (eqn (ap1 thmT Df_step1)
                              (ap2 Pair comp_lhs cong_u2)))
  step1 = thmTDispRuleTrans_param Df_comp_ax Df_cong_g
            comp_lhs comp_mid cong_u1 cong_u2
            _ _ shape_comp_ax
            disp_comp cong_g

  -- Step C: chain step1 + ih_f via thmTDispRuleTrans_param.
  -- ih_f's LHS u3 = mkAp1T (codeF1 f) (cor (g v1)) = cong_u2 (definitionally).

  -- Head-shape of Df_step1 (which starts with tagCode_ruleTrans).
  -- We don't pin down x', y'; thmTDispRuleTrans_param takes them as
  -- explicit Term args, but we let Agda infer via _.

  shape_step1_RAW : Deriv (atomic (eqn (ap1 Fst Df_step1) tagCode_ruleTrans))
  shape_step1_RAW = axFst tagCode_ruleTrans _

  cor_fg_v1 : Term
  cor_fg_v1 = ap1 cor (ap1 f (ap1 g v1T))

  Df_term : Term
  Df_term = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_step1 Df_IH_f)

  merged : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (ap2 Pair comp_lhs cor_fg_v1)))
  merged = thmTDispRuleTrans_param Df_step1 Df_IH_f
            comp_lhs cong_u2 cong_u2 cor_fg_v1
            _ _ shape_step1_RAW
            step1 ih_f

  -- Step D: Bridge cor (f (g v1)) -> cor (Comp f g v1) via axComp + cong1 cor.
  bridge_RHS : Deriv (atomic (eqn cor_fg_v1
                                   (ap1 cor (ap1 (Comp f g) v1T))))
  bridge_RHS = cong1 cor (ruleSym (axComp f g v1T))

  bridge : Deriv (atomic (eqn (ap2 Pair comp_lhs cor_fg_v1)
                               (codeFTeq1Asym (Comp f g) v1T)))
  bridge = congR Pair comp_lhs bridge_RHS

  thm12_Comp_param :
    Sigma Term (\ Df ->
      Deriv (atomic (eqn (ap1 thmT Df)
                          (codeFTeq1Asym (Comp f g) v1T))))
  thm12_Comp_param = mkSigma Df_term (ruleTrans merged bridge)

------------------------------------------------------------------------
-- Post case: given UnivIH1 f and UnivIH2 h, build thm12 for Post f h
-- at v1, v2.

module PostCase (f : Fun1) (h : Fun2)
                (IH_f : UnivIH1 f) (IH_h : UnivIH2 h)
                (v1 v2 : Nat) where

  v1T : Term
  v1T = var v1

  v2T : Term
  v2T = var v2

  -- Post f h's defining axiom: Post f h (a, b) = f (h a b).
  -- thmTDispAxPost_param f h (cor v1) (cor v2) gives:
  --   thmT(Df_post_ax) = Pair post_lhs post_mid
  -- where post_lhs = encoded (Post f h)(cor v1, cor v2),
  --       post_mid = encoded f (h (cor v1) (cor v2))
  --                = mkAp1T (codeF1 f) (mkAp2T (codeF2 h) (cor v1) (cor v2)).

  Df_post_ax : Term
  Df_post_ax = ap2 Pair tagCode_axPost
                   (ap2 Pair (reify (codeF1 f))
                              (ap2 Pair (reify (codeF2 h))
                                         (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))

  post_lhs : Term
  post_lhs = ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Post I IfLf))))
                                       (ap2 Pair (reify (codeF1 f))
                                                  (reify (codeF2 h))))
                             (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  post_mid : Term
  post_mid = ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 f))
                             (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 h))
                                                   (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))

  disp_post : Deriv (atomic (eqn (ap1 thmT Df_post_ax)
                                  (ap2 Pair post_lhs post_mid)))
  disp_post = thmTDispAxPost_param f h (ap1 cor v1T) (ap1 cor v2T)

  -- IH_h at (v1T, v2T) gives: thmT(Df_IH_h) = encoded (h cor v1 cor v2 = cor (h v1 v2)).
  Df_IH_h : Term
  Df_IH_h = fst (IH_h v1T v2T)

  ih_h : Deriv (atomic (eqn (ap1 thmT Df_IH_h) (codeFTeq2Asym h v1T v2T)))
  ih_h = snd (IH_h v1T v2T)

  -- IH_f at (h v1T v2T):
  Df_IH_f : Term
  Df_IH_f = fst (IH_f (ap2 h v1T v2T))

  ih_f : Deriv (atomic (eqn (ap1 thmT Df_IH_f)
                             (codeFTeq1Asym f (ap2 h v1T v2T))))
  ih_f = snd (IH_f (ap2 h v1T v2T))

  -- Lift IH_h via thmTDispCong1_param at outer f.

  ih_h_LHS : Term
  ih_h_LHS = ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))

  ih_h_RHS : Term
  ih_h_RHS = ap1 cor (ap2 h v1T v2T)

  Df_cong_h : Term
  Df_cong_h = ap2 Pair tagCode_cong1
                   (ap2 Pair (reify (codeF1 f)) Df_IH_h)

  cong_u1 : Term
  cong_u1 = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) ih_h_LHS)

  cong_u2 : Term
  cong_u2 = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) ih_h_RHS)

  cong_h : Deriv (atomic (eqn (ap1 thmT Df_cong_h)
                               (ap2 Pair cong_u1 cong_u2)))
  cong_h = thmTDispCong1_param f Df_IH_h ih_h_LHS ih_h_RHS ih_h

  -- Chain disp_post + cong_h via thmTDispRuleTrans_param.

  shape_post_ax : Deriv (atomic (eqn (ap1 Fst Df_post_ax) tagCode_axPost))
  shape_post_ax = axFst tagCode_axPost _

  Df_step1 : Term
  Df_step1 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_post_ax Df_cong_h)

  step1 : Deriv (atomic (eqn (ap1 thmT Df_step1)
                              (ap2 Pair post_lhs cong_u2)))
  step1 = thmTDispRuleTrans_param Df_post_ax Df_cong_h
            post_lhs post_mid cong_u1 cong_u2
            _ _ shape_post_ax
            disp_post cong_h

  -- Chain step1 + ih_f via thmTDispRuleTrans_param.

  shape_step1 : Deriv (atomic (eqn (ap1 Fst Df_step1) tagCode_ruleTrans))
  shape_step1 = axFst tagCode_ruleTrans _

  cor_f_h_v1v2 : Term
  cor_f_h_v1v2 = ap1 cor (ap1 f (ap2 h v1T v2T))

  Df_term : Term
  Df_term = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_step1 Df_IH_f)

  merged : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (ap2 Pair post_lhs cor_f_h_v1v2)))
  merged = thmTDispRuleTrans_param Df_step1 Df_IH_f
            post_lhs cong_u2 cong_u2 cor_f_h_v1v2
            _ _ shape_step1
            step1 ih_f

  -- Bridge cor (f (h v1 v2)) -> cor (Post f h v1 v2) via cong1 cor + axPost.

  bridge_RHS : Deriv (atomic (eqn cor_f_h_v1v2
                                   (ap1 cor (ap2 (Post f h) v1T v2T))))
  bridge_RHS = cong1 cor (ruleSym (axPost f h v1T v2T))

  bridge : Deriv (atomic (eqn (ap2 Pair post_lhs cor_f_h_v1v2)
                               (codeFTeq2Asym (Post f h) v1T v2T)))
  bridge = congR Pair post_lhs bridge_RHS

  thm12_Post_param :
    Sigma Term (\ Df ->
      Deriv (atomic (eqn (ap1 thmT Df)
                          (codeFTeq2Asym (Post f h) v1T v2T))))
  thm12_Post_param = mkSigma Df_term (ruleTrans merged bridge)
