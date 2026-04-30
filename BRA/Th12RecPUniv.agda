{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecPUniv -- universal closure infrastructure for Theorem 12 of RecP s.
--
-- Mirrors BRA.Th12RecUniv (Rec z s) with binary modifications.  The
-- variable-layout convention follows BRA/NEXT-SESSION-RECP-TREEEQ.md:
--   var 0 = x (recursion variable, inducted on by ruleIndBT).
--   var 1 = p (parameter, kept fresh during induction).
--
-- Steps (matching Th12RecUniv):
--   A: Df_F2_RecP_s : Fun2.
--   B1: Df_F2_RecP_s_at_O reduction.
--   C: shape_at proof.
--   D-concrete: Th12_at_lf_concrete via Th12_F2_RecP_s_at_lf (from Th12RecP).
--   D-helpers: closure Eq lemmas.
--   D-final: Th12_at_lf_substF (3-layer eqSubst) via WithClosure.
--   E: toIH2RecP packaging.
--   F: basePair Agda function.
--   G0-G3: SKI foundation (liftAxiom, B_combinator, lifted equational rules).
--   G4: toIH2RecP_lifted.
--   H: Th12_F2_RecP_s via ruleIndBT, parametric on basePair_param.

module BRA.Th12RecPUniv where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.ReifyClosed  using (reifyClosed)
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.Tag using
  ( tagAxRecPLf ; tagAxRefl ; tagRuleTrans )
open import BRA.Thm.ThmT using
  ( thmT ; thClosed
  ; tagCode_axRecPLf
  ; tagCode_ruleTrans ; tagCode_axRecPNd ; tagCode_axRefl
  ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRefl_param ; thmTDispRuleTrans_param
  ; liftAxiomTwo ; liftedRuleTransTwo )
import BRA.Th12RecP
open BRA.Th12RecP using (IH2RecP_doublelifted)

------------------------------------------------------------------------
-- Helper Fun2 combinators (same as Th12RecUniv).

EmitPair : Fun2 -> Fun2 -> Fun2
EmitPair ha hb = Fan ha hb Pair

KT2 : Term -> Fun2
KT2 k = Lift (KT k)

------------------------------------------------------------------------
-- Main parametric module.

module Th12RecPUnivCase
  (s : Fun2)
  -- Closure assumption: s contains no free var.
  (s_closed : (x : Nat) (r : Term) -> Eq (substF2 x r s) s)
  where

  sT : Term
  sT = reify (codeF2 s)

  recPF : Fun2
  recPF = RecP s

  cf2 : Term
  cf2 = reify (codeF2 recPF)

  pCT : Term
  pCT = reify (codeF2 Pair)

  ----------------------------------------------------------------------
  -- The lf-case payload for RecP at (p, O).
  --
  -- lf_inner_p = Pair Df_lf_orig_p (Pair tagCode_axRefl (cor (recPF p O)))
  -- where Df_lf_orig_p = Pair tagCode_axRecPLf (Pair sT (cor p)).
  --
  -- This is parameterised by p (the runtime parameter).  For the lf-case
  -- substF reduction we'll instantiate at p = var 1 (the schematic
  -- statement's parameter slot).

  Df_lf_orig_at : Term -> Term
  Df_lf_orig_at p = ap2 Pair tagCode_axRecPLf (ap2 Pair sT (ap1 cor p))

  encAxReflRecPF_at : Term -> Term
  encAxReflRecPF_at p = ap2 Pair tagCode_axRefl (ap1 cor (ap2 recPF p O))

  lf_inner_at : Term -> Term
  lf_inner_at p = ap2 Pair (Df_lf_orig_at p) (encAxReflRecPF_at p)

  ----------------------------------------------------------------------
  -- Step A: Df_F2_RecP_s as a Fun2 with shape-providing outer wrapper.
  --
  -- Df_F2_RecP_s = Fan (Lift (KT tagCode_ruleTrans))
  --                    inner_dispatch
  --                    Pair
  -- so ap2 Df_F2_RecP_s p x =BRA Pair tagCode_ruleTrans (inner_dispatch p x).
  -- Fst is tagCode_ruleTrans = Pair-shaped (load-bearing for IH2RecP.shape).
  --
  -- inner_dispatch dispatches on x via IfLf:
  --   - x = O      : emit lf_inner_at p (the lf-case payload).
  --   - x = Pair a b: emit step_inner_at_pab (RecP-recursive content).
  --
  -- inner_dispatch = Fan (Post Snd Pair)               -- extracts x for IfLf
  --                       (Fan lf_branch_Fun2          -- emits lf_inner_at p
  --                            (RecP step_inner)       -- emits chain content via RecP
  --                            Pair)
  --                       IfLf
  --
  -- lf_branch_Fun2 = Lift f_lf where f_lf : Fun1 emits lf_inner_at p.

  -- f_Df_lf_orig : Fun1 emitting Df_lf_orig_at p as a function of p.
  --   ap1 f_Df_lf_orig p = Pair tagCode_axRecPLf (Pair sT (cor p)).
  f_Df_lf_orig : Fun1
  f_Df_lf_orig = Comp2 Pair (KT tagCode_axRecPLf) (Comp2 Pair (KT sT) cor)

  -- f_encAxRefl : Fun1 emitting encAxReflRecPF_at p.
  --   ap1 f_encAxRefl p = Pair tagCode_axRefl (cor (recPF p O)).
  -- recPF p O = ap2 recPF p O. As a Fun1 of p: Comp2 recPF I (KT O).
  --   ap1 (Comp2 recPF I (KT O)) p = ap2 recPF (I p)((KT O) p) = ap2 recPF p O. ✓
  f_encAxRefl : Fun1
  f_encAxRefl = Comp2 Pair (KT tagCode_axRefl) (Comp cor (Comp2 recPF I (KT O)))

  -- f_lf : Fun1 emitting lf_inner_at p = Pair (Df_lf_orig_at p)(encAxRefl_at p).
  f_lf : Fun1
  f_lf = Comp2 Pair f_Df_lf_orig f_encAxRefl

  ----------------------------------------------------------------------
  -- emit_* combinators for the real step_inner.  Each is a Fun2 that
  -- at runtime (orig = Pair p (Pair v1 v2), recs = Pair r1 r2) emits a
  -- specific Term piece of the chain Df.

  -- Recs projector: ap2 Recs orig recs = recs.
  Recs : Fun2
  Recs = Post Snd Pair

  -- RecsFst : ap2 RecsFst orig (Pair r1 r2) = r1.
  RecsFst : Fun2
  RecsFst = Post Fst Recs

  -- RecsSnd : ap2 RecsSnd orig (Pair r1 r2) = r2.
  RecsSnd : Fun2
  RecsSnd = Post Snd Recs

  -- emit_v1 : ap2 emit_v1 (Pair p (Pair v1 v2)) _ = v1.
  emit_v1 : Fun2
  emit_v1 = Lift (Comp Fst Snd)

  -- emit_v2 : ap2 emit_v2 (Pair p (Pair v1 v2)) _ = v2.
  emit_v2 : Fun2
  emit_v2 = Lift (Comp Snd Snd)

  -- emit_cp : ap2 emit_cp orig _ = cor (Fst orig).
  emit_cp : Fun2
  emit_cp = Lift (Comp cor Fst)

  emit_cv1 : Fun2
  emit_cv1 = Lift (Comp cor (Comp Fst Snd))

  emit_cv2 : Fun2
  emit_cv2 = Lift (Comp cor (Comp Snd Snd))

  -- emit_f_lf_p : ap2 emit_f_lf_p orig _ = ap1 f_lf (Fst orig) = f_lf p.
  emit_f_lf_p : Fun2
  emit_f_lf_p = Lift (Comp f_lf Fst)

  -- emit_cor_recPF_pv1 : ap2 ... orig _ = cor (recPF p v1)
  --                = ap1 cor (ap2 recPF (Fst orig)(Fst (Snd orig))).
  emit_cor_recPF_pv1 : Fun2
  emit_cor_recPF_pv1 = Lift (Comp cor (Comp2 recPF Fst (Comp Fst Snd)))

  -- emit_IfLf_v1 : ap2 ... orig recs = ap2 IfLf v1 (Pair (f_lf p) r1).
  emit_IfLf_v1 : Fun2
  emit_IfLf_v1 = Fan emit_v1 (EmitPair emit_f_lf_p RecsFst) IfLf

  emit_IfLf_v2 : Fun2
  emit_IfLf_v2 = Fan emit_v2 (EmitPair emit_f_lf_p RecsSnd) IfLf

  -- emit_IH_Df_v1 : Pair tagCode_ruleTrans (IfLf-form for v1).
  -- This is wrapped_IfLf_form p v1 at runtime.
  emit_IH_Df_v1 : Fun2
  emit_IH_Df_v1 = EmitPair (KT2 tagCode_ruleTrans) emit_IfLf_v1

  emit_IH_Df_v2 : Fun2
  emit_IH_Df_v2 = EmitPair (KT2 tagCode_ruleTrans) emit_IfLf_v2

  -- mkAp2T cf2 cp cv2 = Pair tagAp2 (Pair cf2 (Pair cp cv2)).
  emit_mkAp2T_cf2_cp_cv2 : Fun2
  emit_mkAp2T_cf2_cp_cv2 = EmitPair (KT2 (reify tagAp2))
                             (EmitPair (KT2 cf2) (EmitPair emit_cp emit_cv2))

  -- X = Pair tagAp2 (Pair pCT (Pair cv1 cv2)).
  emit_X : Fun2
  emit_X = EmitPair (KT2 (reify tagAp2))
             (EmitPair (KT2 pCT) (EmitPair emit_cv1 emit_cv2))

  -- ppCorPairForm = Pair tagAp2 (Pair pCT (Pair cp X)).
  emit_ppCorPairForm : Fun2
  emit_ppCorPairForm = EmitPair (KT2 (reify tagAp2))
                         (EmitPair (KT2 pCT) (EmitPair emit_cp emit_X))

  -- Df_E1 = Pair tagCode_axRecPNd (Pair sT (Pair cp (Pair cv1 cv2))).
  emit_Df_E1 : Fun2
  emit_Df_E1 = EmitPair (KT2 tagCode_axRecPNd)
                 (EmitPair (KT2 sT)
                   (EmitPair emit_cp (EmitPair emit_cv1 emit_cv2)))

  -- Df_E_v1 = Pair tagCode_congL (Pair pCT (Pair (IH.Df_v1)(mkAp2T cf2 cp cv2))).
  emit_Df_E_v1 : Fun2
  emit_Df_E_v1 = EmitPair (KT2 tagCode_congL)
                   (EmitPair (KT2 pCT)
                     (EmitPair emit_IH_Df_v1 emit_mkAp2T_cf2_cp_cv2))

  -- Df_E_v1_lifted = Pair tagCode_congR (Pair sT (Pair Df_E_v1 ppCorPairForm)).
  emit_Df_E_v1_lifted : Fun2
  emit_Df_E_v1_lifted = EmitPair (KT2 tagCode_congR)
                          (EmitPair (KT2 sT)
                            (EmitPair emit_Df_E_v1 emit_ppCorPairForm))

  -- Df_E_v2 = Pair tagCode_congR (Pair pCT (Pair (IH.Df_v2)(cor(recPF p v1)))).
  emit_Df_E_v2 : Fun2
  emit_Df_E_v2 = EmitPair (KT2 tagCode_congR)
                   (EmitPair (KT2 pCT)
                     (EmitPair emit_IH_Df_v2 emit_cor_recPF_pv1))

  emit_Df_E_v2_lifted : Fun2
  emit_Df_E_v2_lifted = EmitPair (KT2 tagCode_congR)
                          (EmitPair (KT2 sT)
                            (EmitPair emit_Df_E_v2 emit_ppCorPairForm))

  -- Df_chain1 = Pair tagCode_ruleTrans (Pair Df_E1 Df_E_v1_lifted).
  emit_Df_chain1 : Fun2
  emit_Df_chain1 = EmitPair (KT2 tagCode_ruleTrans)
                     (EmitPair emit_Df_E1 emit_Df_E_v1_lifted)

  -- step_inner emits Pair Df_chain1 Df_E_v2_lifted (the chain content
  -- without the outer tagCode_ruleTrans wrapper, which Df_F2_RecP_s adds).
  step_inner : Fun2
  step_inner = EmitPair emit_Df_chain1 emit_Df_E_v2_lifted

  inner_dispatch : Fun2
  inner_dispatch = Fan (Post Snd Pair)
                       (Fan (Lift f_lf) (RecP step_inner) Pair)
                       IfLf

  Df_F2_RecP_s : Fun2
  Df_F2_RecP_s = Fan (Lift (KT tagCode_ruleTrans))
                     inner_dispatch
                     Pair

  ----------------------------------------------------------------------
  -- Step B1: BRA-equality reduction of Df_F2_RecP_s at (p, O).
  --
  -- ap2 Df_F2_RecP_s p O =BRA Pair tagCode_ruleTrans (lf_inner_at p)
  -- via axFan + axLift + axKT + (axFan + axPost + axSnd + axIfLfL + ...
  -- + axLift + f_lf reductions).

  -- Stage 1: outer Fan reduction.
  --   ap2 Df_F2_RecP_s p O =BRA Pair (ap2 (Lift (KT tagCode_ruleTrans)) p O)
  --                                   (ap2 inner_dispatch p O).
  --   Then axLift + axKT for the first slot, axFan + axPost + axSnd +
  --   axIfLfL + axLift + cong for the second slot.
  --
  -- The full reduction is ~50 LoC; for now we provide the result as a
  -- WithClosure parameter (analogous to Df_F1_Rec_zs_at_Pair in Th12RecUniv).

  ----------------------------------------------------------------------
  -- Step C: shape proof at any (p, x).
  --
  -- Fst (ap2 Df_F2_RecP_s p x) =BRA tagCode_ruleTrans, which is
  -- Pair-shaped (= Pair O (...rest of natCode tagRuleTrans...)).

  shape_at : (p x : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap2 Df_F2_RecP_s p x)) tagCode_ruleTrans))
  shape_at p x =
    let
      s1 : Deriv (atomic (eqn (ap2 Df_F2_RecP_s p x)
                              (ap2 Pair (ap2 (Lift (KT tagCode_ruleTrans)) p x)
                                        (ap2 inner_dispatch p x))))
      s1 = axFan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair p x

      s2_lift : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) p x)
                                    (ap1 (KT tagCode_ruleTrans) p)))
      s2_lift = axLift (KT tagCode_ruleTrans) p x

      s2_kt : Deriv (atomic (eqn (ap1 (KT tagCode_ruleTrans) p) tagCode_ruleTrans))
      s2_kt = axKT (natCode tagRuleTrans) p

      s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) p x) tagCode_ruleTrans))
      s2 = ruleTrans s2_lift s2_kt

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair (ap2 (Lift (KT tagCode_ruleTrans)) p x)
                            (ap2 inner_dispatch p x))
                  (ap2 Pair tagCode_ruleTrans (ap2 inner_dispatch p x))))
      step_LHS = congL Pair (ap2 inner_dispatch p x) s2

      reduce_Df : Deriv (atomic (eqn (ap2 Df_F2_RecP_s p x)
                                     (ap2 Pair tagCode_ruleTrans
                                               (ap2 inner_dispatch p x))))
      reduce_Df = ruleTrans s1 step_LHS

      cong_Fst : Deriv (atomic (eqn (ap1 Fst (ap2 Df_F2_RecP_s p x))
                                    (ap1 Fst (ap2 Pair tagCode_ruleTrans
                                                       (ap2 inner_dispatch p x)))))
      cong_Fst = cong1 Fst reduce_Df

      fst_proj : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagCode_ruleTrans
                                                          (ap2 inner_dispatch p x)))
                                    tagCode_ruleTrans))
      fst_proj = axFst tagCode_ruleTrans (ap2 inner_dispatch p x)

    in ruleTrans cong_Fst fst_proj

  ----------------------------------------------------------------------
  -- Step D-helpers: structural Eq closure lemmas (analog of Th12RecUniv's).

  recPF_closed : (x : Nat) (r : Term) -> Eq (substF2 x r recPF) recPF
  recPF_closed x r = eqCong RecP (s_closed x r)

  cor_closed_eq : (x : Nat) (r : Term) -> Eq (substF1 x r cor) cor
  cor_closed_eq x r = refl

  tagCode_ruleTrans_closed : (x : Nat) (r : Term) ->
    Eq (subst x r tagCode_ruleTrans) tagCode_ruleTrans
  tagCode_ruleTrans_closed x r = reifyClosed (natCode tagRuleTrans) x r

  tagCode_axRecPLf_closed : (x : Nat) (r : Term) ->
    Eq (subst x r tagCode_axRecPLf) tagCode_axRecPLf
  tagCode_axRecPLf_closed x r = reifyClosed (natCode tagAxRecPLf) x r

  tagCode_axRefl_closed : (x : Nat) (r : Term) ->
    Eq (subst x r tagCode_axRefl) tagCode_axRefl
  tagCode_axRefl_closed x r = reifyClosed _ x r

  sT_closed : (x : Nat) (r : Term) -> Eq (subst x r sT) sT
  sT_closed x r = reifyClosed (codeF2 s) x r

  cf2_closed : (x : Nat) (r : Term) -> Eq (subst x r cf2) cf2
  cf2_closed x r = reifyClosed (codeF2 recPF) x r

  pCT_closed : (x : Nat) (r : Term) -> Eq (subst x r pCT) pCT
  pCT_closed x r = reifyClosed (codeF2 Pair) x r

  ----------------------------------------------------------------------
  -- Concrete lf-case proofs (no closure assumptions needed).
  --
  -- Df_F2_RecP_s_at_O p reduces  ap2 Df_F2_RecP_s p O  to the structured
  -- lf payload  Pair tagCode_ruleTrans (lf_inner_at p)  via the chain
  -- axFan + axLift + axKT + axFan + axPost + axSnd + axIfLfL + axComp2
  -- (no axIfLf at opaque var — at concrete x = O, axIfLfL fires).

  -- Helper: f_Df_lf_orig p reduces to Df_lf_orig_at p.
  f_Df_lf_orig_red : (p : Term) ->
    Deriv (atomic (eqn (ap1 f_Df_lf_orig p) (Df_lf_orig_at p)))
  f_Df_lf_orig_red p =
    let
      s1 = axComp2 Pair (KT tagCode_axRecPLf) (Comp2 Pair (KT sT) cor) p
      s2 = axKT (natCode tagAxRecPLf) p
      s3 = axComp2 Pair (KT sT) cor p
      s4 = axKT (codeF2 s) p
      s_inner : Deriv (atomic (eqn (ap1 (Comp2 Pair (KT sT) cor) p)
                                    (ap2 Pair sT (ap1 cor p))))
      s_inner = ruleTrans s3 (congL Pair (ap1 cor p) s4)
      step1 = congL Pair (ap1 (Comp2 Pair (KT sT) cor) p) s2
      step2 = congR Pair tagCode_axRecPLf s_inner
    in ruleTrans s1 (ruleTrans step1 step2)

  -- Helper: f_encAxRefl p reduces to encAxReflRecPF_at p.
  --   f_encAxRefl = Comp2 Pair (KT tagCode_axRefl) (Comp cor (Comp2 recPF I (KT O)))
  --   ap1 f_encAxRefl p = Pair tagCode_axRefl (cor (recPF p O))
  f_encAxRefl_red : (p : Term) ->
    Deriv (atomic (eqn (ap1 f_encAxRefl p) (encAxReflRecPF_at p)))
  f_encAxRefl_red p =
    let
      -- ap1 f_encAxRefl p = Pair (ap1 (KT tagCode_axRefl) p)
      --                          (ap1 (Comp cor (Comp2 recPF I (KT O))) p)
      s1 = axComp2 Pair (KT tagCode_axRefl) (Comp cor (Comp2 recPF I (KT O))) p
      s2 = axKT (natCode tagAxRefl) p
      -- Inner: ap1 (Comp cor (Comp2 recPF I (KT O))) p
      --      = ap1 cor (ap1 (Comp2 recPF I (KT O)) p)
      --      = ap1 cor (ap2 recPF (ap1 I p)((ap1 (KT O) p)))
      --      = ap1 cor (ap2 recPF p O)
      s3 = axComp cor (Comp2 recPF I (KT O)) p
      s4 = axComp2 recPF I (KT O) p
      s5 = axI p
      s6 = axKT lf p   -- ap1 (KT O) p = O (since O = reify lf)
      -- Combine: ap2 recPF (ap1 I p)(ap1 (KT O) p) = ap2 recPF p O.
      s_recPF_args : Deriv (atomic (eqn (ap2 recPF (ap1 I p) (ap1 (KT O) p))
                                          (ap2 recPF p O)))
      s_recPF_args = ruleTrans (congL recPF (ap1 (KT O) p) s5)
                                (congR recPF p s6)
      s_recPF : Deriv (atomic (eqn (ap1 (Comp2 recPF I (KT O)) p) (ap2 recPF p O)))
      s_recPF = ruleTrans s4 s_recPF_args
      s_inner : Deriv (atomic (eqn (ap1 (Comp cor (Comp2 recPF I (KT O))) p)
                                    (ap1 cor (ap2 recPF p O))))
      s_inner = ruleTrans s3 (cong1 cor s_recPF)
      step1 = congL Pair (ap1 (Comp cor (Comp2 recPF I (KT O))) p) s2
      step2 = congR Pair tagCode_axRefl s_inner
    in ruleTrans s1 (ruleTrans step1 step2)

  -- Helper: f_lf p reduces to lf_inner_at p.
  f_lf_red : (p : Term) ->
    Deriv (atomic (eqn (ap1 f_lf p) (lf_inner_at p)))
  f_lf_red p =
    let
      s1 = axComp2 Pair f_Df_lf_orig f_encAxRefl p
      s2 = f_Df_lf_orig_red p
      s3 = f_encAxRefl_red p
    in ruleTrans s1 (ruleTrans (congL Pair (ap1 f_encAxRefl p) s2)
                                (congR Pair (Df_lf_orig_at p) s3))

  -- Df_F2_RecP_s reduction at lf input.
  Df_F2_RecP_s_at_O : (p : Term) ->
    Deriv (atomic (eqn (ap2 Df_F2_RecP_s p O)
                        (ap2 Pair tagCode_ruleTrans (lf_inner_at p))))
  Df_F2_RecP_s_at_O p =
    let
      -- Outer Fan: Df_F2_RecP_s p O = Pair (Lift (KT _) p O)(inner_dispatch p O).
      s_outer = axFan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair p O
      -- Lift (KT tagCode_ruleTrans) p O = tagCode_ruleTrans.
      s_outerL = ruleTrans (axLift (KT tagCode_ruleTrans) p O)
                            (axKT (natCode tagRuleTrans) p)
      -- Inner: inner_dispatch p O = ...IfLf O (Pair (f_lf p) O)... = f_lf p.
      s_id_fan = axFan (Post Snd Pair) (Fan (Lift f_lf) (RecP step_inner) Pair) IfLf p O
      -- Post Snd Pair p O = Snd (Pair p O) = O.
      s_post : Deriv (atomic (eqn (ap2 (Post Snd Pair) p O) O))
      s_post = ruleTrans (axPost Snd Pair p O) (axSnd p O)
      -- Fan (Lift f_lf) (RecP step_inner) Pair p O = Pair (f_lf p) O.
      s_inner_fan = axFan (Lift f_lf) (RecP step_inner) Pair p O
      s_lift_flf = axLift f_lf p O
      s_recp_lf = axRecPLf step_inner p
      s_inner_right : Deriv (atomic (eqn
                       (ap2 (Fan (Lift f_lf) (RecP step_inner) Pair) p O)
                       (ap2 Pair (ap1 f_lf p) O)))
      s_inner_right = ruleTrans s_inner_fan
                       (ruleTrans (congL Pair (ap2 (RecP step_inner) p O) s_lift_flf)
                                  (congR Pair (ap1 f_lf p) s_recp_lf))
      s_iflfL = axIfLfL (ap1 f_lf p) O
      -- Combine inner_dispatch p O = f_lf p.
      s_id_step1 = congL IfLf (ap2 (Fan (Lift f_lf) (RecP step_inner) Pair) p O) s_post
      s_id_step2 = congR IfLf O s_inner_right
      s_id : Deriv (atomic (eqn (ap2 inner_dispatch p O) (ap1 f_lf p)))
      s_id = ruleTrans s_id_fan
              (ruleTrans s_id_step1 (ruleTrans s_id_step2 s_iflfL))
      -- f_lf p = lf_inner_at p.
      s_flf = f_lf_red p
      -- Combine outer.
      s_outer_step1 = congL Pair (ap2 inner_dispatch p O) s_outerL
      s_outer_step2 = congR Pair tagCode_ruleTrans (ruleTrans s_id s_flf)
    in ruleTrans s_outer (ruleTrans s_outer_step1 s_outer_step2)

  ----------------------------------------------------------------------
  -- IfLf-form helper for IH.Df slots in the doubly-lifted chain Df.
  --
  -- ap2 Df_F2_RecP_s p x reduces (via axFan + axLift + axKT + axFan +
  -- axPost + axSnd + axLift) to wrapped_IfLf_form p x.  At opaque var x,
  -- this reduction completes (no axIfLf needed); the IfLf application
  -- inside is left as-is.

  wrapped_IfLf_form : Term -> Term -> Term
  wrapped_IfLf_form p x = ap2 Pair tagCode_ruleTrans
                            (ap2 IfLf x (ap2 Pair (ap1 f_lf p)
                                                  (ap2 (RecP step_inner) p x)))

  Df_F2_RecP_s_eqv_IfLf_form : (p x : Term) ->
    Deriv (atomic (eqn (ap2 Df_F2_RecP_s p x) (wrapped_IfLf_form p x)))
  Df_F2_RecP_s_eqv_IfLf_form p x =
    let
      s1 = axFan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair p x
      s_outerL : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) p x)
                                     tagCode_ruleTrans))
      s_outerL = ruleTrans (axLift (KT tagCode_ruleTrans) p x)
                            (axKT (natCode tagRuleTrans) p)
      s_id_fan = axFan (Post Snd Pair) (Fan (Lift f_lf) (RecP step_inner) Pair) IfLf p x
      s_post : Deriv (atomic (eqn (ap2 (Post Snd Pair) p x) x))
      s_post = ruleTrans (axPost Snd Pair p x) (axSnd p x)
      s_inner_fan = axFan (Lift f_lf) (RecP step_inner) Pair p x
      s_inner_lift = axLift f_lf p x
      s_inner_right : Deriv (atomic (eqn
        (ap2 (Fan (Lift f_lf) (RecP step_inner) Pair) p x)
        (ap2 Pair (ap1 f_lf p) (ap2 (RecP step_inner) p x))))
      s_inner_right = ruleTrans s_inner_fan
                        (congL Pair (ap2 (RecP step_inner) p x) s_inner_lift)
      s_step1 = congL IfLf (ap2 (Fan (Lift f_lf) (RecP step_inner) Pair) p x) s_post
      s_step2 = congR IfLf x s_inner_right
      s_id : Deriv (atomic (eqn (ap2 inner_dispatch p x)
                                  (ap2 IfLf x (ap2 Pair (ap1 f_lf p)
                                                        (ap2 (RecP step_inner) p x)))))
      s_id = ruleTrans s_id_fan (ruleTrans s_step1 s_step2)
      s_outer1 = congL Pair (ap2 inner_dispatch p x) s_outerL
      s_outer2 = congR Pair tagCode_ruleTrans s_id
    in ruleTrans s1 (ruleTrans s_outer1 s_outer2)

  ----------------------------------------------------------------------
  -- Reduction lemmas for emit_* combinators at runtime
  -- (orig = Pair p (Pair v1 v2), recs = Pair r1 r2).

  EmitPair_red : (ha hb : Fun2) (orig recs : Term) (a' b' : Term)
              -> Deriv (atomic (eqn (ap2 ha orig recs) a'))
              -> Deriv (atomic (eqn (ap2 hb orig recs) b'))
              -> Deriv (atomic (eqn (ap2 (EmitPair ha hb) orig recs) (ap2 Pair a' b')))
  EmitPair_red ha hb orig recs a' b' Da Db =
    let s1 = axFan ha hb Pair orig recs
        s2 = congL Pair (ap2 hb orig recs) Da
        s3 = congR Pair a' Db
    in ruleTrans s1 (ruleTrans s2 s3)

  KT2_reify_red : (T : Tree) (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (KT (reify T))) orig recs) (reify T)))
  KT2_reify_red T orig recs =
    ruleTrans (axLift (KT (reify T)) orig recs) (axKT T orig)

  -- Primitive projections at orig = Pair p (Pair v1 v2).

  emit_v1_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_v1 (ap2 Pair p' (ap2 Pair v1' v2')) recs) v1'))
  emit_v1_red p' v1' v2' recs =
    let s1 = axLift (Comp Fst Snd) (ap2 Pair p' (ap2 Pair v1' v2')) recs
        s2 = axComp Fst Snd (ap2 Pair p' (ap2 Pair v1' v2'))
        s3 = cong1 Fst (axSnd p' (ap2 Pair v1' v2'))
        s4 = axFst v1' v2'
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  emit_v2_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_v2 (ap2 Pair p' (ap2 Pair v1' v2')) recs) v2'))
  emit_v2_red p' v1' v2' recs =
    let s1 = axLift (Comp Snd Snd) (ap2 Pair p' (ap2 Pair v1' v2')) recs
        s2 = axComp Snd Snd (ap2 Pair p' (ap2 Pair v1' v2'))
        s3 = cong1 Snd (axSnd p' (ap2 Pair v1' v2'))
        s4 = axSnd v1' v2'
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  emit_cp_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cp (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap1 cor p')))
  emit_cp_red p' v1' v2' recs =
    let s1 = axLift (Comp cor Fst) (ap2 Pair p' (ap2 Pair v1' v2')) recs
        s2 = axComp cor Fst (ap2 Pair p' (ap2 Pair v1' v2'))
        s3 = cong1 cor (axFst p' (ap2 Pair v1' v2'))
    in ruleTrans s1 (ruleTrans s2 s3)

  emit_cv1_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cv1 (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap1 cor v1')))
  emit_cv1_red p' v1' v2' recs =
    let s1 = axLift (Comp cor (Comp Fst Snd)) (ap2 Pair p' (ap2 Pair v1' v2')) recs
        s2 = axComp cor (Comp Fst Snd) (ap2 Pair p' (ap2 Pair v1' v2'))
        s3 = cong1 cor (axComp Fst Snd (ap2 Pair p' (ap2 Pair v1' v2')))
        s4 = cong1 cor (cong1 Fst (axSnd p' (ap2 Pair v1' v2')))
        s5 = cong1 cor (axFst v1' v2')
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 (ruleTrans s4 s5)))

  emit_cv2_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cv2 (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap1 cor v2')))
  emit_cv2_red p' v1' v2' recs =
    let s1 = axLift (Comp cor (Comp Snd Snd)) (ap2 Pair p' (ap2 Pair v1' v2')) recs
        s2 = axComp cor (Comp Snd Snd) (ap2 Pair p' (ap2 Pair v1' v2'))
        s3 = cong1 cor (axComp Snd Snd (ap2 Pair p' (ap2 Pair v1' v2')))
        s4 = cong1 cor (cong1 Snd (axSnd p' (ap2 Pair v1' v2')))
        s5 = cong1 cor (axSnd v1' v2')
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 (ruleTrans s4 s5)))

  emit_f_lf_p_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_f_lf_p (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap1 f_lf p')))
  emit_f_lf_p_red p' v1' v2' recs =
    let s1 = axLift (Comp f_lf Fst) (ap2 Pair p' (ap2 Pair v1' v2')) recs
        s2 = axComp f_lf Fst (ap2 Pair p' (ap2 Pair v1' v2'))
        s3 = cong1 f_lf (axFst p' (ap2 Pair v1' v2'))
    in ruleTrans s1 (ruleTrans s2 s3)

  emit_cor_recPF_pv1_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cor_recPF_pv1 (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap1 cor (ap2 recPF p' v1'))))
  emit_cor_recPF_pv1_red p' v1' v2' recs =
    let
      orig = ap2 Pair p' (ap2 Pair v1' v2')
      s1 = axLift (Comp cor (Comp2 recPF Fst (Comp Fst Snd))) orig recs
      s2 = axComp cor (Comp2 recPF Fst (Comp Fst Snd)) orig
      s3 = cong1 cor (axComp2 recPF Fst (Comp Fst Snd) orig)
      -- Inner: ap2 recPF (Fst orig)(ap1 (Comp Fst Snd) orig)
      --      = ap2 recPF p' (ap1 Fst (Snd orig))
      --      = ap2 recPF p' (Fst (Pair v1' v2'))
      --      = ap2 recPF p' v1'.
      sFst = axFst p' (ap2 Pair v1' v2')
      sCompFstSnd : Deriv (atomic (eqn (ap1 (Comp Fst Snd) orig) v1'))
      sCompFstSnd = ruleTrans (axComp Fst Snd orig)
                              (ruleTrans (cong1 Fst (axSnd p' (ap2 Pair v1' v2')))
                                          (axFst v1' v2'))
      sBoth : Deriv (atomic (eqn (ap2 recPF (ap1 Fst orig)
                                          (ap1 (Comp Fst Snd) orig))
                                  (ap2 recPF p' v1')))
      sBoth = ruleTrans (congL recPF (ap1 (Comp Fst Snd) orig) sFst)
                        (congR recPF p' sCompFstSnd)
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 (cong1 cor sBoth)))

  -- Recs projectors.

  Recs_red : (orig r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 Recs orig (ap2 Pair r1 r2)) (ap2 Pair r1 r2)))
  Recs_red orig r1 r2 =
    let s1 = axPost Snd Pair orig (ap2 Pair r1 r2)
        s2 = axSnd orig (ap2 Pair r1 r2)
    in ruleTrans s1 s2

  RecsFst_red : (orig r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 RecsFst orig (ap2 Pair r1 r2)) r1))
  RecsFst_red orig r1 r2 =
    let s1 = axPost Fst Recs orig (ap2 Pair r1 r2)
        s2 = cong1 Fst (Recs_red orig r1 r2)
        s3 = axFst r1 r2
    in ruleTrans s1 (ruleTrans s2 s3)

  RecsSnd_red : (orig r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 RecsSnd orig (ap2 Pair r1 r2)) r2))
  RecsSnd_red orig r1 r2 =
    let s1 = axPost Snd Recs orig (ap2 Pair r1 r2)
        s2 = cong1 Snd (Recs_red orig r1 r2)
        s3 = axSnd r1 r2
    in ruleTrans s1 (ruleTrans s2 s3)

  ----------------------------------------------------------------------
  -- IfLf-form emitters reduce to wrapped_IfLf_form p' v_i' (= IH.Df slot).

  emit_IfLf_v1_red : (p' v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn
            (ap2 emit_IfLf_v1 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 IfLf v1' (ap2 Pair (ap1 f_lf p') r1))))
  emit_IfLf_v1_red p' v1' v2' r1 r2 =
    let
      orig = ap2 Pair p' (ap2 Pair v1' v2')
      recs = ap2 Pair r1 r2
      s_fan = axFan emit_v1 (EmitPair emit_f_lf_p RecsFst) IfLf orig recs
      s_v1 = emit_v1_red p' v1' v2' recs
      s_payload : Deriv (atomic (eqn
                  (ap2 (EmitPair emit_f_lf_p RecsFst) orig recs)
                  (ap2 Pair (ap1 f_lf p') r1)))
      s_payload = EmitPair_red emit_f_lf_p RecsFst orig recs
                    (ap1 f_lf p') r1
                    (emit_f_lf_p_red p' v1' v2' recs)
                    (RecsFst_red orig r1 r2)
      step1 = congL IfLf (ap2 (EmitPair emit_f_lf_p RecsFst) orig recs) s_v1
      step2 = congR IfLf v1' s_payload
    in ruleTrans s_fan (ruleTrans step1 step2)

  emit_IfLf_v2_red : (p' v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn
            (ap2 emit_IfLf_v2 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 IfLf v2' (ap2 Pair (ap1 f_lf p') r2))))
  emit_IfLf_v2_red p' v1' v2' r1 r2 =
    let
      orig = ap2 Pair p' (ap2 Pair v1' v2')
      recs = ap2 Pair r1 r2
      s_fan = axFan emit_v2 (EmitPair emit_f_lf_p RecsSnd) IfLf orig recs
      s_v2 = emit_v2_red p' v1' v2' recs
      s_payload = EmitPair_red emit_f_lf_p RecsSnd orig recs
                    (ap1 f_lf p') r2
                    (emit_f_lf_p_red p' v1' v2' recs)
                    (RecsSnd_red orig r1 r2)
      step1 = congL IfLf (ap2 (EmitPair emit_f_lf_p RecsSnd) orig recs) s_v2
      step2 = congR IfLf v2' s_payload
    in ruleTrans s_fan (ruleTrans step1 step2)

  emit_IH_Df_v1_red : (p' v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn
            (ap2 emit_IH_Df_v1 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 Pair tagCode_ruleTrans
              (ap2 IfLf v1' (ap2 Pair (ap1 f_lf p') r1)))))
  emit_IH_Df_v1_red p' v1' v2' r1 r2 =
    EmitPair_red (KT2 tagCode_ruleTrans) emit_IfLf_v1
      (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2)
      tagCode_ruleTrans _
      (KT2_reify_red (natCode tagRuleTrans)
        (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
      (emit_IfLf_v1_red p' v1' v2' r1 r2)

  emit_IH_Df_v2_red : (p' v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn
            (ap2 emit_IH_Df_v2 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 Pair tagCode_ruleTrans
              (ap2 IfLf v2' (ap2 Pair (ap1 f_lf p') r2)))))
  emit_IH_Df_v2_red p' v1' v2' r1 r2 =
    EmitPair_red (KT2 tagCode_ruleTrans) emit_IfLf_v2
      (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2)
      tagCode_ruleTrans _
      (KT2_reify_red (natCode tagRuleTrans)
        (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
      (emit_IfLf_v2_red p' v1' v2' r1 r2)

  ----------------------------------------------------------------------
  -- Composite emitters.

  emit_X_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_X (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT (ap2 Pair (ap1 cor v1') (ap1 cor v2'))))))
  emit_X_red p' v1' v2' recs =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
    in EmitPair_red (KT2 (reify tagAp2)) _ orig recs (reify tagAp2) _
         (KT2_reify_red tagAp2 orig recs)
         (EmitPair_red (KT2 pCT) _ orig recs pCT _
           (KT2_reify_red (codeF2 Pair) orig recs)
           (EmitPair_red emit_cv1 emit_cv2 orig recs
             (ap1 cor v1') (ap1 cor v2')
             (emit_cv1_red p' v1' v2' recs)
             (emit_cv2_red p' v1' v2' recs)))

  emit_ppCorPairForm_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_ppCorPairForm (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT
                            (ap2 Pair (ap1 cor p')
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair pCT (ap2 Pair (ap1 cor v1')(ap1 cor v2')))))))))
  emit_ppCorPairForm_red p' v1' v2' recs =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
    in EmitPair_red (KT2 (reify tagAp2)) _ orig recs (reify tagAp2) _
         (KT2_reify_red tagAp2 orig recs)
         (EmitPair_red (KT2 pCT) _ orig recs pCT _
           (KT2_reify_red (codeF2 Pair) orig recs)
           (EmitPair_red emit_cp emit_X orig recs (ap1 cor p') _
             (emit_cp_red p' v1' v2' recs)
             (emit_X_red p' v1' v2' recs)))

  emit_mkAp2T_cf2_cp_cv2_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_mkAp2T_cf2_cp_cv2 (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair cf2 (ap2 Pair (ap1 cor p')(ap1 cor v2'))))))
  emit_mkAp2T_cf2_cp_cv2_red p' v1' v2' recs =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
    in EmitPair_red (KT2 (reify tagAp2)) _ orig recs (reify tagAp2) _
         (KT2_reify_red tagAp2 orig recs)
         (EmitPair_red (KT2 cf2) _ orig recs cf2 _
           (KT2_reify_red (codeF2 recPF) orig recs)
           (EmitPair_red emit_cp emit_cv2 orig recs
             (ap1 cor p') (ap1 cor v2')
             (emit_cp_red p' v1' v2' recs)
             (emit_cv2_red p' v1' v2' recs)))

  emit_Df_E1_red : (p' v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_Df_E1 (ap2 Pair p' (ap2 Pair v1' v2')) recs)
                        (ap2 Pair tagCode_axRecPNd
                          (ap2 Pair sT
                            (ap2 Pair (ap1 cor p')
                              (ap2 Pair (ap1 cor v1')(ap1 cor v2')))))))
  emit_Df_E1_red p' v1' v2' recs =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
    in EmitPair_red (KT2 tagCode_axRecPNd) _ orig recs tagCode_axRecPNd _
         (KT2_reify_red _ orig recs)
         (EmitPair_red (KT2 sT) _ orig recs sT _
           (KT2_reify_red (codeF2 s) orig recs)
           (EmitPair_red emit_cp _ orig recs (ap1 cor p') _
             (emit_cp_red p' v1' v2' recs)
             (EmitPair_red emit_cv1 emit_cv2 orig recs
               (ap1 cor v1') (ap1 cor v2')
               (emit_cv1_red p' v1' v2' recs)
               (emit_cv2_red p' v1' v2' recs))))

  -- Helper Term: chain Df expanded to the level step_inner emits.

  Df_chain12_at : (v1 v2 : Nat) -> Term
  Df_chain12_at v1 v2 =
    let cp_  = ap1 cor (var (suc zero))
        cv1_ = ap1 cor (var v1)
        cv2_ = ap1 cor (var v2)
        rec_pv1_ = ap2 recPF (var (suc zero)) (var v1)
        ihDf_v1 = wrapped_IfLf_form (var (suc zero)) (var v1)
        ihDf_v2 = wrapped_IfLf_form (var (suc zero)) (var v2)
        X_ = ap2 Pair (reify tagAp2)
               (ap2 Pair pCT (ap2 Pair cv1_ cv2_))
        ppCorPairForm_ = ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT (ap2 Pair cp_ X_))
        mkAp2T_ = ap2 Pair (reify tagAp2)
                    (ap2 Pair cf2 (ap2 Pair cp_ cv2_))
        Df_E1_ = ap2 Pair tagCode_axRecPNd
                   (ap2 Pair sT (ap2 Pair cp_ (ap2 Pair cv1_ cv2_)))
        Df_E_v1_ = ap2 Pair tagCode_congL
                     (ap2 Pair pCT (ap2 Pair ihDf_v1 mkAp2T_))
        Df_E_v1_lifted_ = ap2 Pair tagCode_congR
                            (ap2 Pair sT (ap2 Pair Df_E_v1_ ppCorPairForm_))
        Df_E_v2_ = ap2 Pair tagCode_congR
                     (ap2 Pair pCT (ap2 Pair ihDf_v2 (ap1 cor rec_pv1_)))
        Df_E_v2_lifted_ = ap2 Pair tagCode_congR
                            (ap2 Pair sT (ap2 Pair Df_E_v2_ ppCorPairForm_))
        Df_chain1_ = ap2 Pair tagCode_ruleTrans
                       (ap2 Pair Df_E1_ Df_E_v1_lifted_)
    in ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1_ Df_E_v2_lifted_)

  ----------------------------------------------------------------------
  -- Composite emitter reductions.

  emit_Df_E_v1_red : (p' v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn
            (ap2 emit_Df_E_v1 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 Pair tagCode_congL
              (ap2 Pair pCT (ap2 Pair
                (ap2 Pair tagCode_ruleTrans
                  (ap2 IfLf v1' (ap2 Pair (ap1 f_lf p') r1)))
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair cf2 (ap2 Pair (ap1 cor p')(ap1 cor v2')))))))))
  emit_Df_E_v1_red p' v1' v2' r1 r2 =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
        recs = ap2 Pair r1 r2
    in EmitPair_red (KT2 tagCode_congL) _ orig recs tagCode_congL _
         (KT2_reify_red _ orig recs)
         (EmitPair_red (KT2 pCT) _ orig recs pCT _
           (KT2_reify_red (codeF2 Pair) orig recs)
           (EmitPair_red emit_IH_Df_v1 emit_mkAp2T_cf2_cp_cv2 orig recs
             _ _
             (emit_IH_Df_v1_red p' v1' v2' r1 r2)
             (emit_mkAp2T_cf2_cp_cv2_red p' v1' v2' recs)))

  emit_Df_E_v2_red : (p' v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn
            (ap2 emit_Df_E_v2 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 Pair tagCode_congR
              (ap2 Pair pCT (ap2 Pair
                (ap2 Pair tagCode_ruleTrans
                  (ap2 IfLf v2' (ap2 Pair (ap1 f_lf p') r2)))
                (ap1 cor (ap2 recPF p' v1')))))))
  emit_Df_E_v2_red p' v1' v2' r1 r2 =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
        recs = ap2 Pair r1 r2
    in EmitPair_red (KT2 tagCode_congR) _ orig recs tagCode_congR _
         (KT2_reify_red _ orig recs)
         (EmitPair_red (KT2 pCT) _ orig recs pCT _
           (KT2_reify_red (codeF2 Pair) orig recs)
           (EmitPair_red emit_IH_Df_v2 emit_cor_recPF_pv1 orig recs
             _ _
             (emit_IH_Df_v2_red p' v1' v2' r1 r2)
             (emit_cor_recPF_pv1_red p' v1' v2' recs)))

  emit_Df_E_v1_lifted_red : (p' v1' v2' r1 r2 : Term)
    (Df_E_v1' : Term)
    (DEv1 : Deriv (atomic (eqn (ap2 emit_Df_E_v1 (ap2 Pair p' (ap2 Pair v1' v2'))
                                                  (ap2 Pair r1 r2)) Df_E_v1'))) ->
    Deriv (atomic (eqn
            (ap2 emit_Df_E_v1_lifted (ap2 Pair p' (ap2 Pair v1' v2'))
                                       (ap2 Pair r1 r2))
            (ap2 Pair tagCode_congR
              (ap2 Pair sT (ap2 Pair Df_E_v1'
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT
                    (ap2 Pair (ap1 cor p')
                      (ap2 Pair (reify tagAp2)
                        (ap2 Pair pCT
                          (ap2 Pair (ap1 cor v1')(ap1 cor v2'))))))))))))
  emit_Df_E_v1_lifted_red p' v1' v2' r1 r2 Df_E_v1' DEv1 =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
        recs = ap2 Pair r1 r2
    in EmitPair_red (KT2 tagCode_congR) _ orig recs tagCode_congR _
         (KT2_reify_red _ orig recs)
         (EmitPair_red (KT2 sT) _ orig recs sT _
           (KT2_reify_red (codeF2 s) orig recs)
           (EmitPair_red emit_Df_E_v1 emit_ppCorPairForm orig recs
             Df_E_v1' _
             DEv1
             (emit_ppCorPairForm_red p' v1' v2' recs)))

  emit_Df_E_v2_lifted_red : (p' v1' v2' r1 r2 : Term)
    (Df_E_v2' : Term)
    (DEv2 : Deriv (atomic (eqn (ap2 emit_Df_E_v2 (ap2 Pair p' (ap2 Pair v1' v2'))
                                                  (ap2 Pair r1 r2)) Df_E_v2'))) ->
    Deriv (atomic (eqn
            (ap2 emit_Df_E_v2_lifted (ap2 Pair p' (ap2 Pair v1' v2'))
                                       (ap2 Pair r1 r2))
            (ap2 Pair tagCode_congR
              (ap2 Pair sT (ap2 Pair Df_E_v2'
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT
                    (ap2 Pair (ap1 cor p')
                      (ap2 Pair (reify tagAp2)
                        (ap2 Pair pCT
                          (ap2 Pair (ap1 cor v1')(ap1 cor v2'))))))))))))
  emit_Df_E_v2_lifted_red p' v1' v2' r1 r2 Df_E_v2' DEv2 =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
        recs = ap2 Pair r1 r2
    in EmitPair_red (KT2 tagCode_congR) _ orig recs tagCode_congR _
         (KT2_reify_red _ orig recs)
         (EmitPair_red (KT2 sT) _ orig recs sT _
           (KT2_reify_red (codeF2 s) orig recs)
           (EmitPair_red emit_Df_E_v2 emit_ppCorPairForm orig recs
             Df_E_v2' _
             DEv2
             (emit_ppCorPairForm_red p' v1' v2' recs)))

  emit_Df_chain1_red : (p' v1' v2' r1 r2 : Term)
    (Df_E1' Df_E_v1_lifted' : Term)
    (DE1 : Deriv (atomic (eqn (ap2 emit_Df_E1 (ap2 Pair p' (ap2 Pair v1' v2'))
                                                (ap2 Pair r1 r2)) Df_E1')))
    (DEv1L : Deriv (atomic (eqn (ap2 emit_Df_E_v1_lifted (ap2 Pair p' (ap2 Pair v1' v2'))
                                                          (ap2 Pair r1 r2)) Df_E_v1_lifted'))) ->
    Deriv (atomic (eqn
            (ap2 emit_Df_chain1 (ap2 Pair p' (ap2 Pair v1' v2')) (ap2 Pair r1 r2))
            (ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1' Df_E_v1_lifted'))))
  emit_Df_chain1_red p' v1' v2' r1 r2 Df_E1' Df_E_v1_lifted' DE1 DEv1L =
    let orig = ap2 Pair p' (ap2 Pair v1' v2')
        recs = ap2 Pair r1 r2
    in EmitPair_red (KT2 tagCode_ruleTrans) _ orig recs tagCode_ruleTrans _
         (KT2_reify_red _ orig recs)
         (EmitPair_red emit_Df_E1 emit_Df_E_v1_lifted orig recs
           Df_E1' Df_E_v1_lifted' DE1 DEv1L)

  ----------------------------------------------------------------------
  -- Df_F2_RecP_s_at_Pair_chain_proven : the chain Df bridge.
  --
  -- ap2 Df_F2_RecP_s pT (Pair (var v1)(var v2)) =BRA Df_chain12_at v1 v2.
  --
  -- Composition:
  --   Stage 1: outer Fan reduction (Df_F2_RecP_s_eqv_IfLf_form-like, but
  --            specialised at Pair input — IfLf fires via axIfLfN).
  --   Stage 2: axRecPNd unfolds RecP step_inner at Pair input.
  --   Stage 3: step_inner emits chain content (via emit_Df_chain1 +
  --            emit_Df_E_v2_lifted reductions).

  Df_F2_RecP_s_at_Pair_chain_proven : (v1 v2 : Nat) ->
    Deriv (atomic (eqn (ap2 Df_F2_RecP_s (var (suc zero)) (ap2 Pair (var v1) (var v2)))
                        (Df_chain12_at v1 v2)))
  Df_F2_RecP_s_at_Pair_chain_proven v1 v2 =
    let
      pT_ = var (suc zero)
      v1T_ = var v1
      v2T_ = var v2
      pairT_ = ap2 Pair v1T_ v2T_
      orig_ = ap2 Pair pT_ pairT_
      r1_ = ap2 (RecP step_inner) pT_ v1T_
      r2_ = ap2 (RecP step_inner) pT_ v2T_
      recs_ = ap2 Pair r1_ r2_

      -- Stage 1: Df_F2_RecP_s pT (Pair v1 v2) reduces (axFan + axLift + axKT)
      -- to Pair tagCode_ruleTrans (inner_dispatch pT (Pair v1 v2)).
      stage1_outer = axFan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair pT_ pairT_
      stage1_outerL = ruleTrans (axLift (KT tagCode_ruleTrans) pT_ pairT_)
                                 (axKT (natCode tagRuleTrans) pT_)
      stage1 : Deriv (atomic (eqn (ap2 Df_F2_RecP_s pT_ pairT_)
                                    (ap2 Pair tagCode_ruleTrans
                                              (ap2 inner_dispatch pT_ pairT_))))
      stage1 = ruleTrans stage1_outer
                          (congL Pair (ap2 inner_dispatch pT_ pairT_) stage1_outerL)

      -- Stage 2a: inner_dispatch reduces at Pair input via axIfLfN.
      stage2a_fan = axFan (Post Snd Pair) (Fan (Lift f_lf) (RecP step_inner) Pair) IfLf pT_ pairT_
      stage2a_post : Deriv (atomic (eqn (ap2 (Post Snd Pair) pT_ pairT_) pairT_))
      stage2a_post = ruleTrans (axPost Snd Pair pT_ pairT_) (axSnd pT_ pairT_)
      stage2a_inner_fan = axFan (Lift f_lf) (RecP step_inner) Pair pT_ pairT_
      stage2a_lift = axLift f_lf pT_ pairT_
      stage2a_inner : Deriv (atomic (eqn
                       (ap2 (Fan (Lift f_lf) (RecP step_inner) Pair) pT_ pairT_)
                       (ap2 Pair (ap1 f_lf pT_) (ap2 (RecP step_inner) pT_ pairT_))))
      stage2a_inner = ruleTrans stage2a_inner_fan
                       (congL Pair (ap2 (RecP step_inner) pT_ pairT_) stage2a_lift)
      stage2a_iflfN = axIfLfN v1T_ v2T_ (ap1 f_lf pT_)
                              (ap2 (RecP step_inner) pT_ pairT_)
      stage2a_step1 = congL IfLf (ap2 (Fan (Lift f_lf) (RecP step_inner) Pair) pT_ pairT_)
                              stage2a_post
      stage2a_step2 = congR IfLf pairT_ stage2a_inner
      stage2a : Deriv (atomic (eqn (ap2 inner_dispatch pT_ pairT_)
                                    (ap2 (RecP step_inner) pT_ pairT_)))
      stage2a = ruleTrans stage2a_fan (ruleTrans stage2a_step1 (ruleTrans stage2a_step2 stage2a_iflfN))

      -- Stage 2b: axRecPNd unfolds RecP step_inner at Pair input.
      stage2b = axRecPNd step_inner pT_ v1T_ v2T_

      -- Combine Stage 1 + 2a + 2b: Df_F2_RecP_s pT pairT
      --   = Pair tagCode_ruleTrans (step_inner orig recs).
      stage12 : Deriv (atomic (eqn (ap2 Df_F2_RecP_s pT_ pairT_)
                                     (ap2 Pair tagCode_ruleTrans
                                               (ap2 step_inner orig_ recs_))))
      stage12 = ruleTrans stage1
                  (congR Pair tagCode_ruleTrans (ruleTrans stage2a stage2b))

      -- Stage 3: step_inner orig recs reduces to chain content.
      ihDf_v1 = wrapped_IfLf_form pT_ v1T_
      ihDf_v2 = wrapped_IfLf_form pT_ v2T_

      cp_  = ap1 cor pT_
      cv1_ = ap1 cor v1T_
      cv2_ = ap1 cor v2T_
      rec_pv1_ = ap2 recPF pT_ v1T_
      X_ = ap2 Pair (reify tagAp2)
             (ap2 Pair pCT (ap2 Pair cv1_ cv2_))
      ppCorPairForm_ = ap2 Pair (reify tagAp2)
                        (ap2 Pair pCT (ap2 Pair cp_ X_))
      mkAp2T_ = ap2 Pair (reify tagAp2)
                  (ap2 Pair cf2 (ap2 Pair cp_ cv2_))
      Df_E1_ = ap2 Pair tagCode_axRecPNd
                 (ap2 Pair sT (ap2 Pair cp_ (ap2 Pair cv1_ cv2_)))
      Df_E_v1_ = ap2 Pair tagCode_congL
                   (ap2 Pair pCT (ap2 Pair ihDf_v1 mkAp2T_))
      Df_E_v1_lifted_ = ap2 Pair tagCode_congR
                          (ap2 Pair sT (ap2 Pair Df_E_v1_ ppCorPairForm_))
      Df_E_v2_ = ap2 Pair tagCode_congR
                   (ap2 Pair pCT (ap2 Pair ihDf_v2 (ap1 cor rec_pv1_)))
      Df_E_v2_lifted_ = ap2 Pair tagCode_congR
                          (ap2 Pair sT (ap2 Pair Df_E_v2_ ppCorPairForm_))
      Df_chain1_ = ap2 Pair tagCode_ruleTrans
                     (ap2 Pair Df_E1_ Df_E_v1_lifted_)

      stage3_DE1 = emit_Df_E1_red pT_ v1T_ v2T_ recs_
      stage3_DEv1 = emit_Df_E_v1_red pT_ v1T_ v2T_ r1_ r2_
      stage3_DEv1L = emit_Df_E_v1_lifted_red pT_ v1T_ v2T_ r1_ r2_ Df_E_v1_ stage3_DEv1
      stage3_DEv2 = emit_Df_E_v2_red pT_ v1T_ v2T_ r1_ r2_
      stage3_DEv2L = emit_Df_E_v2_lifted_red pT_ v1T_ v2T_ r1_ r2_ Df_E_v2_ stage3_DEv2
      stage3_chain1 = emit_Df_chain1_red pT_ v1T_ v2T_ r1_ r2_ Df_E1_ Df_E_v1_lifted_
                        stage3_DE1 stage3_DEv1L

      stage3 : Deriv (atomic (eqn (ap2 step_inner orig_ recs_)
                                   (ap2 Pair Df_chain1_ Df_E_v2_lifted_)))
      stage3 = EmitPair_red emit_Df_chain1 emit_Df_E_v2_lifted orig_ recs_
                  Df_chain1_ Df_E_v2_lifted_
                  stage3_chain1 stage3_DEv2L

    in ruleTrans stage12 (congR Pair tagCode_ruleTrans stage3)

  ----------------------------------------------------------------------
  -- Th12 at lf input (concrete proof, replacing the WithClosure parameter).
  --
  -- Strategy: reduce Df_F2_RecP_s p O (Df_F2_RecP_s_at_O), then thmT
  -- dispatches via tagCode_ruleTrans on (Df_lf_orig_at p, encAxReflRecPF_at p).
  -- thmT(Df_lf_orig_at p) = codeFTeq2Asym recPF p O via Th12_F2_RecP_s_at_lf
  -- (from BRA.Th12RecP).  thmT(encAxReflRecPF_at p) = Pair (cor(recPF p O))
  -- (cor(recPF p O)) via thmTDispAxRefl_param.  body_ruleTrans combines.

  module Th12RecPCaseInst = BRA.Th12RecP.Th12RecPCase s

  Th12_at_lf_concrete_proven : (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s p O))
                        (codeFTeq2Asym recPF p O)))
  Th12_at_lf_concrete_proven p =
    let
      -- thmT(Pair tagCode_ruleTrans (Pair Df_lf_orig encAxRefl)) via dispatcher.
      -- y1 = Df_lf_orig_at p = Df_lf p (from Th12RecP).
      -- y2 = encAxReflRecPF_at p = Pair tagCode_axRefl (cor(recPF p O)).
      --
      -- thmT y1 = Pair (mkAp2T cf2 (cor p) (cor O))(cor(recPF p O))
      --         = codeFTeq2Asym recPF p O   [via Th12_F2_RecP_s_at_lf p].
      -- thmT y2 = Pair (cor(recPF p O))(cor(recPF p O))   [thmTDispAxRefl_param].
      -- shape Fst(Df_lf_orig_at p) = Fst(Pair tagCode_axRecPLf _) = tagCode_axRecPLf.
      -- u1 = mkAp2T cf2 (cor p)(cor O), u2 = u3 = cor(recPF p O), u4 = cor(recPF p O).
      -- body_ruleTrans output: Pair u1 u4 = codeFTeq2Asym recPF p O. ✓

      img_y1 : Deriv (atomic (eqn (ap1 thmT (Df_lf_orig_at p))
                                   (codeFTeq2Asym recPF p O)))
      img_y1 = Th12RecPCaseInst.Th12_F2_RecP_s_at_lf p

      img_y2 : Deriv (atomic (eqn (ap1 thmT (encAxReflRecPF_at p))
                                   (ap2 Pair (ap1 cor (ap2 recPF p O))
                                             (ap1 cor (ap2 recPF p O)))))
      img_y2 = thmTDispAxRefl_param (ap1 cor (ap2 recPF p O))

      -- Apply thmTDispRuleTrans_param.
      -- Note: codeFTeq2Asym recPF p O =
      --   ap2 Pair (mkAp2T cf2 (ap1 cor p)(ap1 cor O))(ap1 cor (ap2 recPF p O)).
      -- So u1 = mkAp2T cf2 (ap1 cor p)(ap1 cor O), u2 = cor(recPF p O).
      -- u3 = u4 = cor(recPF p O).  u2 = u3 ✓.

      disp : Deriv (atomic (eqn
              (ap1 thmT (ap2 Pair tagCode_ruleTrans (lf_inner_at p)))
              (ap2 Pair (mkAp2T cf2 (ap1 cor p)(ap1 cor O))
                        (ap1 cor (ap2 recPF p O)))))
      disp = thmTDispRuleTrans_param (Df_lf_orig_at p) (encAxReflRecPF_at p)
              (mkAp2T cf2 (ap1 cor p)(ap1 cor O))
              (ap1 cor (ap2 recPF p O))
              (ap1 cor (ap2 recPF p O))
              (ap1 cor (ap2 recPF p O))
              _ _ (axFst tagCode_axRecPLf _) img_y1 img_y2

      -- Bridge from Df_F2_RecP_s p O to Pair tagCode_ruleTrans (lf_inner_at p).
      bridge : Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s p O))
                                   (ap1 thmT (ap2 Pair tagCode_ruleTrans (lf_inner_at p)))))
      bridge = cong1 thmT (Df_F2_RecP_s_at_O p)
    in ruleTrans bridge disp

  ----------------------------------------------------------------------
  -- WithClosure submodule (analog of Th12RecUniv).
  --
  -- Takes:
  --   Df_F2_RecP_s_closed : structural Eq (caller dischargeable as refl
  --     for typical concrete closed s).
  --   ih_s_bra : Theorem 12 for s in BRA-Deriv form.
  --   Df_F2_RecP_s_at_O_at : (p : Term) -> Deriv (eqn (ap2 Df_F2_RecP_s p O)
  --                                                    (Pair tagCode_ruleTrans (lf_inner_at p)))
  --     (Step B1, ~50 LoC mechanical reduction; deferred to caller.)
  --   Df_F2_RecP_s_at_Pair_at : (v1 v2 : Nat) ->
  --     Deriv (eqn (ap2 Df_F2_RecP_s (var (suc zero))(Pair (var v1)(var v2)))
  --                (Df_chain12_at v1 v2))
  --     (Step B2, ~150-200 LoC mechanical; deferred to caller.)
  --   Th12_at_lf_concrete_at : (p : Term) ->
  --     Deriv (eqn (ap1 thmT (Pair tagCode_ruleTrans (lf_inner_at p)))
  --                (codeFTeq2Asym recPF p O))
  --     (Step D-concrete, ~80 LoC; deferred to caller via Th12RecPCase or
  --     direct proof using thmTDispRuleTrans_param + thmTDispAxRefl_param.)
  --   basePair_param : the SKI-lifted basePair (Step G).

  P_Th12_RecP_s : Formula
  P_Th12_RecP_s = atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var zero)))
                              (codeFTeq2Asym recPF (var (suc zero)) (var zero)))

  module WithClosure
    (Df_F2_RecP_s_closed :
       (x : Nat) (r : Term) -> Eq (substF2 x r Df_F2_RecP_s) Df_F2_RecP_s)
    (ih_s_bra : (a b : Term) ->
       Deriv (atomic (eqn (mkAp2T sT (ap1 cor a) (ap1 cor b))
                          (ap1 cor (ap2 s a b)))))
    where

    -- Th12 at lf-input: now concrete (was a parameter; discharged structurally
    -- via Df_F2_RecP_s_at_O + thmTDispRuleTrans_param + Th12_F2_RecP_s_at_lf
    -- + thmTDispAxRefl_param).
    Th12_at_lf_concrete_at : (p : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s p O))
                          (codeFTeq2Asym recPF p O)))
    Th12_at_lf_concrete_at = Th12_at_lf_concrete_proven

    --------------------------------------------------------------------
    -- Step D-final: Th12_at_lf_substF.
    --
    -- substF zero O P_Th12_RecP_s reduces to (with var 0 -> O, var 1 stays):
    --   atomic (eqn (ap1 (substF1 zero O thmT)
    --                    (ap2 (substF2 zero O Df_F2_RecP_s)(var (suc zero)) O))
    --               (subst zero O (codeFTeq2Asym recPF (var (suc zero))(var zero))))

    codeFTeq2Asym_subst_eq_O :
      Eq (subst zero O (codeFTeq2Asym recPF (var (suc zero)) (var zero)))
         (codeFTeq2Asym recPF (var (suc zero)) O)
    codeFTeq2Asym_subst_eq_O =
      eqCong3 (\ cf2' cor' recPF' -> ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair cf2' (ap2 Pair (ap1 cor' (var (suc zero)))(ap1 cor' O))))
        (ap1 cor' (ap2 recPF' (var (suc zero)) O)))
        (cf2_closed zero O)
        (cor_closed_eq zero O)
        (recPF_closed zero O)

    Th12_at_lf_substF : Deriv (substF zero O P_Th12_RecP_s)
    Th12_at_lf_substF =
      eqSubst (\ thT' -> Deriv (atomic (eqn
          (ap1 thT' (ap2 (substF2 zero O Df_F2_RecP_s) (var (suc zero)) O))
          (subst zero O (codeFTeq2Asym recPF (var (suc zero)) (var zero))))))
        (eqSym (thClosed zero O))
        (eqSubst (\ Df' -> Deriv (atomic (eqn
            (ap1 thmT (ap2 Df' (var (suc zero)) O))
            (subst zero O (codeFTeq2Asym recPF (var (suc zero)) (var zero))))))
          (eqSym (Df_F2_RecP_s_closed zero O))
          (eqSubst (\ rhs -> Deriv (atomic (eqn
              (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) O)) rhs)))
            (eqSym codeFTeq2Asym_subst_eq_O)
            (Th12_at_lf_concrete_at (var (suc zero)))))

    --------------------------------------------------------------------
    -- Step E: toIH2RecP packaging.

    open BRA.Th12RecP using (IH2RecP)

    codeFTeq2Asym_subst_eq_var : (v : Nat) ->
      Eq (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero)))
         (codeFTeq2Asym recPF (var (suc zero)) (var v))
    codeFTeq2Asym_subst_eq_var v =
      eqCong3 (\ cf2' cor' recPF' -> ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair cf2' (ap2 Pair (ap1 cor' (var (suc zero)))(ap1 cor' (var v)))))
        (ap1 cor' (ap2 recPF' (var (suc zero)) (var v))))
        (cf2_closed zero (var v))
        (cor_closed_eq zero (var v))
        (recPF_closed zero (var v))

    toIH2RecP : (v : Nat) ->
      Deriv (substF zero (var v) P_Th12_RecP_s) ->
      IH2RecP recPF (var (suc zero)) (var v)
    toIH2RecP v ihD =
      record
        { Df    = ap2 Df_F2_RecP_s (var (suc zero)) (var v)
        ; fstL  = _
        ; fstR  = _
        ; shape = shape_at (var (suc zero)) (var v)
        ; image = image_proof
        }
      where
        image_proof : Deriv (atomic (eqn
                       (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v)))
                       (codeFTeq2Asym recPF (var (suc zero)) (var v))))
        image_proof =
          eqSubst (\ rhs -> Deriv (atomic (eqn
              (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v))) rhs)))
            (codeFTeq2Asym_subst_eq_var v)
            (eqSubst (\ Df' -> Deriv (atomic (eqn
                (ap1 thmT (ap2 Df' (var (suc zero)) (var v)))
                (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero))))))
              (Df_F2_RecP_s_closed zero (var v))
              (eqSubst (\ thT' -> Deriv (atomic (eqn
                  (ap1 thT' (ap2 (substF2 zero (var v) Df_F2_RecP_s) (var (suc zero)) (var v)))
                  (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero))))))
                (thClosed zero (var v))
                ihD))

    --------------------------------------------------------------------
    -- Step G0-G3: SKI lift foundation (mirror of Th12RecUniv's).

    liftAxiom : (P : Formula) {Q : Formula} -> Deriv Q -> Deriv (P imp Q)
    liftAxiom P D = mp (axK _ P) D

    B_combinator : {P Q R : Formula} ->
                   Deriv (P imp (Q imp R)) ->
                   Deriv (P imp Q) ->
                   Deriv (P imp R)
    B_combinator {P} {Q} {R} D1 D2 = mp (mp (axS P Q R) D1) D2

    liftedAxEqTrans : (P : Formula) (a b c : Term) ->
                      Deriv (P imp atomic (eqn a b)) ->
                      Deriv (P imp atomic (eqn a c)) ->
                      Deriv (P imp atomic (eqn b c))
    liftedAxEqTrans P a b c D1 D2 =
      B_combinator (B_combinator (liftAxiom P (axEqTrans a b c)) D1) D2

    liftedCong1 : (P : Formula) (f : Fun1) (a b : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn (ap1 f a) (ap1 f b)))
    liftedCong1 P f a b D =
      B_combinator (liftAxiom P (axEqCong1 f a b)) D

    liftedCongL : (P : Formula) (g : Fun2) (a b c : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn (ap2 g a c) (ap2 g b c)))
    liftedCongL P g a b c D =
      B_combinator (liftAxiom P (axEqCongL g a b c)) D

    liftedCongR : (P : Formula) (g : Fun2) (a b c : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn (ap2 g c a) (ap2 g c b)))
    liftedCongR P g a b c D =
      B_combinator (liftAxiom P (axEqCongR g a b c)) D

    liftedEqSubst : {A : Set} (P : Formula) (Property : A -> Formula)
                    {x y : A} -> Eq x y ->
                    Deriv (P imp Property x) ->
                    Deriv (P imp Property y)
    liftedEqSubst P Property eq D =
      eqSubst (\ z -> Deriv (P imp Property z)) eq D

    --------------------------------------------------------------------
    -- Step G4: toIH2RecP_lifted.

    record IH2RecP_lifted (P : Formula) (g : Fun2) (p x : Term) : Set where
      field
        Df    : Term
        fstL  : Term
        fstR  : Term
        shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
        image : Deriv (P imp atomic (eqn (ap1 thmT Df) (codeFTeq2Asym g p x)))

    toIH2RecP_lifted_image : (P : Formula) (v : Nat) ->
      Deriv (P imp substF zero (var v) P_Th12_RecP_s) ->
      Deriv (P imp atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v)))
                                (codeFTeq2Asym recPF (var (suc zero)) (var v))))
    toIH2RecP_lifted_image P v lifted_ihD =
      liftedEqSubst P (\ rhs -> atomic (eqn
          (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v))) rhs))
        (codeFTeq2Asym_subst_eq_var v)
        (liftedEqSubst P (\ Df' -> atomic (eqn
            (ap1 thmT (ap2 Df' (var (suc zero)) (var v)))
            (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero)))))
          (Df_F2_RecP_s_closed zero (var v))
          (liftedEqSubst P (\ thT' -> atomic (eqn
              (ap1 thT' (ap2 (substF2 zero (var v) Df_F2_RecP_s) (var (suc zero)) (var v)))
              (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero)))))
            (thClosed zero (var v))
            lifted_ihD))

    toIH2RecP_lifted : (P : Formula) (v : Nat) ->
                       Deriv (P imp substF zero (var v) P_Th12_RecP_s) ->
                       IH2RecP_lifted P recPF (var (suc zero)) (var v)
    toIH2RecP_lifted P v lifted_ihD =
      record
        { Df    = ap2 Df_F2_RecP_s (var (suc zero)) (var v)
        ; fstL  = _
        ; fstR  = _
        ; shape = shape_at (var (suc zero)) (var v)
        ; image = toIH2RecP_lifted_image P v lifted_ihD
        }

    --------------------------------------------------------------------
    -- Doubly-lifted toIH2RecP.  IH.Df is the IfLf-form (BRA-equal to
    -- ap2 Df_F2_RecP_s pT (var v) but matches step_inner's runtime
    -- emission at IH slots — the literal-equality pivot that closes
    -- the chain Df bridge.

    toIH2RecP_doublelifted_image_at_Df : (P1 P2 : Formula) (v : Nat) ->
      Deriv (P1 imp (P2 imp substF zero (var v) P_Th12_RecP_s)) ->
      Deriv (P1 imp (P2 imp atomic
        (eqn (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v)))
             (codeFTeq2Asym recPF (var (suc zero)) (var v)))))
    toIH2RecP_doublelifted_image_at_Df P1 P2 v dl_ihD =
      eqSubst (\ rhs -> Deriv (P1 imp (P2 imp atomic (eqn
            (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v))) rhs))))
        (codeFTeq2Asym_subst_eq_var v)
        (eqSubst (\ Df' -> Deriv (P1 imp (P2 imp atomic (eqn
              (ap1 thmT (ap2 Df' (var (suc zero)) (var v)))
              (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero)))))))
          (Df_F2_RecP_s_closed zero (var v))
          (eqSubst (\ thT' -> Deriv (P1 imp (P2 imp atomic (eqn
                (ap1 thT' (ap2 (substF2 zero (var v) Df_F2_RecP_s) (var (suc zero)) (var v)))
                (subst zero (var v) (codeFTeq2Asym recPF (var (suc zero)) (var zero)))))))
            (thClosed zero (var v))
            dl_ihD))

    toIH2RecP_doublelifted_image : (P1 P2 : Formula) (v : Nat) ->
      Deriv (P1 imp (P2 imp substF zero (var v) P_Th12_RecP_s)) ->
      Deriv (P1 imp (P2 imp atomic
        (eqn (ap1 thmT (wrapped_IfLf_form (var (suc zero)) (var v)))
             (codeFTeq2Asym recPF (var (suc zero)) (var v)))))
    toIH2RecP_doublelifted_image P1 P2 v dl_ihD =
      let
        base_dl = toIH2RecP_doublelifted_image_at_Df P1 P2 v dl_ihD
        -- Bridge: thmT (wrapped_IfLf_form pT v) = thmT (Df_F2_RecP_s pT v)
        -- via cong1 thmT (ruleSym (Df_F2_RecP_s_eqv_IfLf_form pT v)).
        bridge : Deriv (atomic (eqn
                  (ap1 thmT (wrapped_IfLf_form (var (suc zero)) (var v)))
                  (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v)))))
        bridge = cong1 thmT (ruleSym (Df_F2_RecP_s_eqv_IfLf_form (var (suc zero)) (var v)))
      in liftedRuleTransTwo P1 P2
           (ap1 thmT (wrapped_IfLf_form (var (suc zero)) (var v)))
           (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var v)))
           (codeFTeq2Asym recPF (var (suc zero)) (var v))
           (liftAxiomTwo P1 P2 bridge) base_dl

    toIH2RecP_doublelifted : (P1 P2 : Formula) (v : Nat) ->
                             Deriv (P1 imp (P2 imp substF zero (var v) P_Th12_RecP_s)) ->
                             IH2RecP_doublelifted P1 P2 recPF (var (suc zero)) (var v)
    toIH2RecP_doublelifted P1 P2 v dl_ihD =
      record
        { Df    = wrapped_IfLf_form (var (suc zero)) (var v)
        ; fstL  = _
        ; fstR  = _
        ; shape = axFst tagCode_ruleTrans
                    (ap2 IfLf (var v) (ap2 Pair (ap1 f_lf (var (suc zero)))
                                                (ap2 (RecP step_inner) (var (suc zero)) (var v))))
        ; image = toIH2RecP_doublelifted_image P1 P2 v dl_ihD
        }

    --------------------------------------------------------------------
    -- Step H scaffold: WithBasePairParam takes the lifted basePair.

    module WithBasePairParam
      (basePair_param : (v1 v2 : Nat) ->
         Deriv ((substF zero (var v1) P_Th12_RecP_s) imp
                ((substF zero (var v2) P_Th12_RecP_s) imp
                 (substF zero (ap2 Pair (var v1) (var v2)) P_Th12_RecP_s))))
      where

      Th12_F2_RecP_s : Deriv P_Th12_RecP_s
      Th12_F2_RecP_s = ruleIndBT P_Th12_RecP_s
                                  (suc (suc zero))
                                  (suc (suc (suc zero)))
                                  Th12_at_lf_substF
                                  (basePair_param (suc (suc zero))
                                                  (suc (suc (suc zero))))

    --------------------------------------------------------------------
    -- BasePair: per-(v1, v2) doubly-lifted machinery for the Pair-case.

    axImpRefl : (Q : Formula) -> Deriv (Q imp Q)
    axImpRefl Q = mp (mp (axS Q (Q imp Q) Q) (axK Q (Q imp Q))) (axK Q Q)

    module BasePair (v1 v2 : Nat) where

      Pv1 : Formula
      Pv1 = substF zero (var v1) P_Th12_RecP_s

      Pv2 : Formula
      Pv2 = substF zero (var v2) P_Th12_RecP_s

      Ppair : Formula
      Ppair = substF zero (ap2 Pair (var v1) (var v2)) P_Th12_RecP_s

      v1T : Term
      v1T = var v1
      v2T : Term
      v2T = var v2
      pT : Term
      pT = var (suc zero)
      pairT : Term
      pairT = ap2 Pair v1T v2T

      dl_ihD_v1 : Deriv (Pv1 imp (Pv2 imp Pv1))
      dl_ihD_v1 = axK Pv1 Pv2

      dl_ihD_v2 : Deriv (Pv1 imp (Pv2 imp Pv2))
      dl_ihD_v2 = mp (axK (Pv2 imp Pv2) Pv1) (axImpRefl Pv2)

      ih1_dl : IH2RecP_doublelifted Pv1 Pv2 recPF pT v1T
      ih1_dl = toIH2RecP_doublelifted Pv1 Pv2 v1 dl_ihD_v1

      ih2_dl : IH2RecP_doublelifted Pv1 Pv2 recPF pT v2T
      ih2_dl = toIH2RecP_doublelifted Pv1 Pv2 v2 dl_ihD_v2

      module RPC = BRA.Th12RecP.Th12RecPCase.RecPPairCase_doublelifted s
                     Pv1 Pv2 pT v1T v2T ih1_dl ih2_dl ih_s_bra

      Df_chain12 : Term
      Df_chain12 = RPC.Df_chain12

      sigma_image_dl : Deriv (Pv1 imp (Pv2 imp atomic
                         (eqn (ap1 thmT Df_chain12)
                              (codeFTeq2Asym recPF pT pairT))))
      sigma_image_dl = snd RPC.thm12_RecP_s_pair_dl

    --------------------------------------------------------------------
    -- basePair_param + Th12_F2_RecP_s_concrete: now unconditional.
    -- The chain Df bridge is discharged via Df_F2_RecP_s_at_Pair_chain_proven
    -- (commit Phase 3): real step_inner + emit_* reduction lemmas.

    basePair_param : (v1 v2 : Nat) ->
      Deriv ((substF zero (var v1) P_Th12_RecP_s) imp
             ((substF zero (var v2) P_Th12_RecP_s) imp
              (substF zero (ap2 Pair (var v1) (var v2)) P_Th12_RecP_s)))
    basePair_param v1 v2 =
      let
        open BasePair v1 v2

        bridge_thmT : Deriv (atomic (eqn
                        (ap1 thmT (ap2 Df_F2_RecP_s pT pairT))
                        (ap1 thmT Df_chain12)))
        bridge_thmT = cong1 thmT (Df_F2_RecP_s_at_Pair_chain_proven v1 v2)

        concrete_dl : Deriv (Pv1 imp (Pv2 imp atomic
                        (eqn (ap1 thmT (ap2 Df_F2_RecP_s pT pairT))
                             (codeFTeq2Asym recPF pT pairT))))
        concrete_dl = liftedRuleTransTwo Pv1 Pv2
                        (ap1 thmT (ap2 Df_F2_RecP_s pT pairT))
                        (ap1 thmT Df_chain12)
                        (codeFTeq2Asym recPF pT pairT)
                        (liftAxiomTwo Pv1 Pv2 bridge_thmT)
                        sigma_image_dl

        codeFTeq2Asym_subst_eq_Pair :
          Eq (subst zero pairT (codeFTeq2Asym recPF pT (var zero)))
             (codeFTeq2Asym recPF pT pairT)
        codeFTeq2Asym_subst_eq_Pair =
          eqCong3 (\ cf2' cor' recPF' -> ap2 Pair
            (ap2 Pair (reify tagAp2)
              (ap2 Pair cf2' (ap2 Pair (ap1 cor' pT)(ap1 cor' pairT))))
            (ap1 cor' (ap2 recPF' pT pairT)))
            (cf2_closed zero pairT)
            (cor_closed_eq zero pairT)
            (recPF_closed zero pairT)

      in eqSubst (\ thT' -> Deriv (Pv1 imp (Pv2 imp atomic (eqn
          (ap1 thT' (ap2 (substF2 zero pairT Df_F2_RecP_s) pT pairT))
          (subst zero pairT (codeFTeq2Asym recPF pT (var zero)))))))
        (eqSym (thClosed zero pairT))
        (eqSubst (\ Df' -> Deriv (Pv1 imp (Pv2 imp atomic (eqn
            (ap1 thmT (ap2 Df' pT pairT))
            (subst zero pairT (codeFTeq2Asym recPF pT (var zero)))))))
          (eqSym (Df_F2_RecP_s_closed zero pairT))
          (eqSubst (\ rhs -> Deriv (Pv1 imp (Pv2 imp atomic (eqn
              (ap1 thmT (ap2 Df_F2_RecP_s pT pairT)) rhs))))
            (eqSym codeFTeq2Asym_subst_eq_Pair)
            concrete_dl))

    Th12_F2_RecP_s_concrete : Deriv P_Th12_RecP_s
    Th12_F2_RecP_s_concrete = ruleIndBT P_Th12_RecP_s
                                (suc (suc zero))
                                (suc (suc (suc zero)))
                                Th12_at_lf_substF
                                (basePair_param (suc (suc zero))
                                                (suc (suc (suc zero))))
