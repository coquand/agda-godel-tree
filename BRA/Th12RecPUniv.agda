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
  ( tagAxRecPLf ; tagRuleTrans )
open import BRA.Thm.ThmT using
  ( thmT ; thClosed
  ; tagCode_axRecPLf
  ; tagCode_ruleTrans ; tagCode_axRecPNd ; tagCode_axRefl
  ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRefl_param ; thmTDispRuleTrans_param )
import BRA.Th12RecP

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

  -- step_inner : Fun2 for the RecP step.  At runtime, RecP step_inner p (Pair v1 v2)
  -- = step_inner (Pair p (Pair v1 v2))(Pair (RecP step_inner p v1)(RecP step_inner p v2)).
  --
  -- For the architectural scaffold, step_inner is taken as a parameter
  -- of WithClosure (the full ~150-200 LoC Fan-of-combinators is mechanical
  -- engineering deferred via parameters).
  --
  -- For now, we use a stub step_inner that emits O at the chain content
  -- position.  The CALLER's WithClosure parameters will provide the
  -- actual BRA-equality reductions and chain proofs.

  step_inner : Fun2
  step_inner = Const  -- ap2 Const a b = a; emits orig (Pair p (Pair v1 v2)).
                     -- Stub; real step_inner emits the chain content.

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
    (Th12_at_lf_concrete_at : (p : Term) ->
       Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s p O))
                          (codeFTeq2Asym recPF p O))))
    where

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
