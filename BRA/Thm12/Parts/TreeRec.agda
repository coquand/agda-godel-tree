{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.TreeRec   (Theorem 12 case for g = treeRec f s, binary).
--
-- Unified tree-recursor (subsumes Rec / RecP at the architectural level):
--
--   axTreeRecLf f s p           : ap2 (treeRec f s) p O           = ap1 f p
--   axTreeRecNd f s p a b       : ap2 (treeRec f s) p (Pair a b)
--                                   = ap2 s (Pair p (Pair a b))
--                                           (Pair (ap2 (treeRec f s) p a)
--                                                 (ap2 (treeRec f s) p b))
--
-- Construction module (rev2): instead of taking `apf_corLemma` (the
-- IH-on-f-bridge-on-cor) as a parameter, we now take the IH-on-f
-- itself (Df_f, proof_f) and chain at the leaf via parDispRuleTrans
-- with parEncAxTreeRecLf.  This matches the "Step 1" cleaner construction
-- in BRA/NEXT-SESSION-TREEREC-INTERNAL.md.
--
-- Parameters:
--
--   * f : Fun1, s : Fun2 (the original Fun2 we're proving Theorem 12 for).
--   * Df_f : Fun1, proof_f : (q : Term) -> ...  -- IH-on-f from thm12_F1 f.
--   * D2_treeRec_NN_fun : Fun2 (the chain-Df at Pair-input case).
--   * D_correct2_treeRec_NN_pt : pointwise correctness at  Pair-input.
--
-- Removed parameters (now derived internally):
--
--   * apf_corLemma : derived as part of the leaf chain via proof_f.
--   * D2_treeRec_NN_fun_closed : derived from BRA.SubstClosure.Fun2_closed.
--   * treeRec_fs_closed : derived from BRA.SubstClosure.Fun2_closed.

module BRA.Thm12.Parts.TreeRec where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxTreeRecLf ; tagRuleTrans)
open import BRA.Thm.ThmT using (thmT ; tagCode_axTreeRecLf
                                 ; tagCode_ruleTrans ; thClosed)
open import BRA.SubstClosure
  using (substF1_KT_of_reify ; subst_reify ; Fun1_closed ; Fun2_closed)
open import BRA.Thm12.Param.AxTreeRecLf
  using (parEncAxTreeRecLf ; parOutAxTreeRecLf ; parDispAxTreeRecLf)
open import BRA.Thm12.Param.RuleTrans
  using (parEncRuleTrans ; parDispRuleTrans)

------------------------------------------------------------------------
-- The codeFTeq2 spec for treeRec f s.

codeFTeq2_treeRec_fs : (f : Fun1) (s : Fun2) -> Term -> Term -> Term
codeFTeq2_treeRec_fs f s p x =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 (treeRec f s)))
                        (ap2 Pair (ap1 cor p) (ap1 cor x))))
    (ap1 cor (ap2 (treeRec f s) p x))

------------------------------------------------------------------------
-- Construction module: parametric over f, s, the IH-on-f, the Pair-case
-- chain Fun2 + its pointwise correctness, and an x-closure for the
-- universal wrapper's outer ruleInst.

module Construction
  (f : Fun1)
  (s : Fun2)
  -- IH-on-f from thm12_F1 f.
  (Df_f : Fun1)
  (proof_f : (q : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 Df_f q))
                       (ap2 Pair
                         (ap2 Pair (reify tagAp1)
                                   (ap2 Pair (reify (codeF1 f)) (ap1 cor q)))
                         (ap1 cor (ap1 f q))))))
  -- Pair-case chain Fun2.
  (D2_treeRec_NN_fun : Fun2)
  (D_correct2_treeRec_NN_pt : (p a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_NN_fun p (ap2 Pair a b)))
                       (codeFTeq2_treeRec_fs f s p (ap2 Pair a b)))))
  where

  ----------------------------------------------------------------------
  -- Closures derived structurally from Fun_closed.

  private
    Df_f_closed : (k : Nat) (r : Term) -> Eq (substF1 k r Df_f) Df_f
    Df_f_closed k r = Fun1_closed k r Df_f

    D2_treeRec_NN_fun_closed : (k : Nat) (r : Term) ->
      Eq (substF2 k r D2_treeRec_NN_fun) D2_treeRec_NN_fun
    D2_treeRec_NN_fun_closed k r = Fun2_closed k r D2_treeRec_NN_fun

    treeRec_fs_closed : (k : Nat) (r : Term) ->
      Eq (substF2 k r (treeRec f s)) (treeRec f s)
    treeRec_fs_closed k r = Fun2_closed k r (treeRec f s)

  ----------------------------------------------------------------------
  -- Building blocks for D2_treeRec_fs.

  private
    fT : Term
    fT = reify (codeF1 f)

    sT : Term
    sT = reify (codeF2 s)

    -- ap2 lfPayloadInner p x = ap2 Pair sT (ap1 cor p)
    lfPayloadInner : Fun2
    lfPayloadInner = Fan (Lift (KT sT)) (Lift cor) Pair

    -- ap2 lfPayload p x = ap2 Pair fT (ap2 Pair sT (ap1 cor p))
    lfPayload : Fun2
    lfPayload = Fan (Lift (KT fT)) lfPayloadInner Pair

    -- ap2 lfTreeRecPart p x = parEncAxTreeRecLf fT sT (cor p).
    lfTreeRecPart : Fun2
    lfTreeRecPart = Fan (Lift (KT tagCode_axTreeRecLf)) lfPayload Pair

    -- ap2 lfDfFPart p x = ap1 Df_f p (the IH-on-f applied to p).
    lfDfFPart : Fun2
    lfDfFPart = Lift Df_f

    -- ap2 lfChainPair p x = Pair (parEncAxTreeRecLf fT sT (cor p)) (ap1 Df_f p).
    lfChainPair : Fun2
    lfChainPair = Fan lfTreeRecPart lfDfFPart Pair

    -- ap2 lfPart p x = parEncRuleTrans (parEncAxTreeRecLf fT sT (cor p)) (ap1 Df_f p)
    --                = Pair tagCode_ruleTrans (Pair (parEncAxTreeRecLf fT sT (cor p)) (ap1 Df_f p)).
    lfPart : Fun2
    lfPart = Fan (Lift (KT tagCode_ruleTrans)) lfChainPair Pair

    -- ap2 dispatchFun p x = Pair (lfPart p x) (D2_treeRec_NN_fun p x).
    dispatchFun : Fun2
    dispatchFun = Fan lfPart D2_treeRec_NN_fun Pair

  D2_treeRec_fs : Fun2
  D2_treeRec_fs = Fan (Post Snd Pair) dispatchFun IfLf

  ----------------------------------------------------------------------
  -- Substitution-closure of D2_treeRec_fs.  Derived from Fun2_closed.

  D2_treeRec_fs_closed : (k : Nat) (r : Term) ->
    Eq (substF2 k r D2_treeRec_fs) D2_treeRec_fs
  D2_treeRec_fs_closed k r = Fun2_closed k r D2_treeRec_fs

  ----------------------------------------------------------------------
  -- Helper reductions.

  private
    -- ap2 (Post Snd Pair) p x = x
    postSndPair_eval : (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Post Snd Pair) p x) x))
    postSndPair_eval p x =
      let e1 : Deriv (atomic (eqn (ap2 (Post Snd Pair) p x)
                                   (ap1 Snd (ap2 Pair p x))))
          e1 = axPost Snd Pair p x
          e2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair p x)) x))
          e2 = axSnd p x
      in ruleTrans e1 e2

    -- ap2 (Lift (KT (reify v))) p x = reify v
    liftKTtree_eval : (v : Tree) (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Lift (KT (reify v))) p x) (reify v)))
    liftKTtree_eval v p x =
      ruleTrans (axLift (KT (reify v)) p x) (axKT v p)

    liftCor_eval : (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Lift cor) p x) (ap1 cor p)))
    liftCor_eval p x = axLift cor p x

    liftDfF_eval : (p x : Term) ->
      Deriv (atomic (eqn (ap2 (Lift Df_f) p x) (ap1 Df_f p)))
    liftDfF_eval p x = axLift Df_f p x

  ----------------------------------------------------------------------
  -- Reductions:
  --   ap2 D2_treeRec_fs p O = parEncRuleTrans (parEncAxTreeRecLf fT sT (cor p)) (ap1 Df_f p)
  --   ap2 D2_treeRec_fs p (Pair v1 v2) = ap2 D2_treeRec_NN_fun p (Pair v1 v2)

  private
    -- Build  parEncAxTreeRecLf fT sT (cor p)  via the lfTreeRecPart Fan tower.
    lfTreeRecPart_red : (p x : Term) ->
      Deriv (atomic (eqn (ap2 lfTreeRecPart p x)
                          (parEncAxTreeRecLf fT sT (ap1 cor p))))
    lfTreeRecPart_red p x =
      let
          a1 : Deriv (atomic (eqn (ap2 lfTreeRecPart p x)
                                   (ap2 Pair (ap2 (Lift (KT tagCode_axTreeRecLf)) p x)
                                              (ap2 lfPayload p x))))
          a1 = axFan (Lift (KT tagCode_axTreeRecLf)) lfPayload Pair p x

          a2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axTreeRecLf)) p x)
                                   tagCode_axTreeRecLf))
          a2 = liftKTtree_eval (natCode tagAxTreeRecLf) p x

          b1 : Deriv (atomic (eqn (ap2 lfPayload p x)
                                   (ap2 Pair (ap2 (Lift (KT fT)) p x)
                                              (ap2 lfPayloadInner p x))))
          b1 = axFan (Lift (KT fT)) lfPayloadInner Pair p x

          b2 : Deriv (atomic (eqn (ap2 (Lift (KT fT)) p x) fT))
          b2 = liftKTtree_eval (codeF1 f) p x

          c1 : Deriv (atomic (eqn (ap2 lfPayloadInner p x)
                                   (ap2 Pair (ap2 (Lift (KT sT)) p x)
                                              (ap2 (Lift cor) p x))))
          c1 = axFan (Lift (KT sT)) (Lift cor) Pair p x

          c2 : Deriv (atomic (eqn (ap2 (Lift (KT sT)) p x) sT))
          c2 = liftKTtree_eval (codeF2 s) p x

          c3 : Deriv (atomic (eqn (ap2 (Lift cor) p x) (ap1 cor p)))
          c3 = liftCor_eval p x

          c4 : Deriv (atomic (eqn (ap2 lfPayloadInner p x)
                                   (ap2 Pair sT (ap1 cor p))))
          c4 = ruleTrans c1
                (ruleTrans (congL Pair (ap2 (Lift cor) p x) c2)
                           (congR Pair sT c3))

          b3 : Deriv (atomic (eqn (ap2 lfPayload p x)
                                   (ap2 Pair fT (ap2 Pair sT (ap1 cor p)))))
          b3 = ruleTrans b1
                (ruleTrans (congL Pair (ap2 lfPayloadInner p x) b2)
                           (congR Pair fT c4))

      in ruleTrans a1
           (ruleTrans (congL Pair (ap2 lfPayload p x) a2)
                      (congR Pair tagCode_axTreeRecLf b3))

    lfChainPair_red : (p x : Term) ->
      Deriv (atomic (eqn (ap2 lfChainPair p x)
                          (ap2 Pair (parEncAxTreeRecLf fT sT (ap1 cor p))
                                    (ap1 Df_f p))))
    lfChainPair_red p x =
      let
          a1 : Deriv (atomic (eqn (ap2 lfChainPair p x)
                                   (ap2 Pair (ap2 lfTreeRecPart p x)
                                              (ap2 lfDfFPart p x))))
          a1 = axFan lfTreeRecPart lfDfFPart Pair p x

          a2 : Deriv (atomic (eqn (ap2 lfDfFPart p x) (ap1 Df_f p)))
          a2 = liftDfF_eval p x

          a3 : Deriv (atomic (eqn (ap2 lfTreeRecPart p x)
                                   (parEncAxTreeRecLf fT sT (ap1 cor p))))
          a3 = lfTreeRecPart_red p x
      in ruleTrans a1
           (ruleTrans (congL Pair (ap2 lfDfFPart p x) a3)
                      (congR Pair (parEncAxTreeRecLf fT sT (ap1 cor p)) a2))

    lfPart_red : (p x : Term) ->
      Deriv (atomic (eqn (ap2 lfPart p x)
                          (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                            (ap1 Df_f p))))
    lfPart_red p x =
      let
          a1 : Deriv (atomic (eqn (ap2 lfPart p x)
                                   (ap2 Pair (ap2 (Lift (KT tagCode_ruleTrans)) p x)
                                              (ap2 lfChainPair p x))))
          a1 = axFan (Lift (KT tagCode_ruleTrans)) lfChainPair Pair p x

          a2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) p x)
                                   tagCode_ruleTrans))
          a2 = liftKTtree_eval (natCode tagRuleTrans) p x

          a3 : Deriv (atomic (eqn (ap2 lfChainPair p x)
                                   (ap2 Pair (parEncAxTreeRecLf fT sT (ap1 cor p))
                                              (ap1 Df_f p))))
          a3 = lfChainPair_red p x
      in ruleTrans a1
           (ruleTrans (congL Pair (ap2 lfChainPair p x) a2)
                      (congR Pair tagCode_ruleTrans a3))

  D2_treeRec_fs_reduce_O : (p : Term) ->
    Deriv (atomic (eqn (ap2 D2_treeRec_fs p O)
                       (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                         (ap1 Df_f p))))
  D2_treeRec_fs_reduce_O p =
    let
        a1 : Deriv (atomic (eqn (ap2 D2_treeRec_fs p O)
                                 (ap2 IfLf (ap2 (Post Snd Pair) p O)
                                            (ap2 dispatchFun p O))))
        a1 = axFan (Post Snd Pair) dispatchFun IfLf p O

        a2 : Deriv (atomic (eqn (ap2 (Post Snd Pair) p O) O))
        a2 = postSndPair_eval p O

        a3 : Deriv (atomic (eqn (ap2 IfLf (ap2 (Post Snd Pair) p O)
                                          (ap2 dispatchFun p O))
                                 (ap2 IfLf O (ap2 dispatchFun p O))))
        a3 = congL IfLf (ap2 dispatchFun p O) a2

        c1 : Deriv (atomic (eqn (ap2 dispatchFun p O)
                                 (ap2 Pair (ap2 lfPart p O)
                                            (ap2 D2_treeRec_NN_fun p O))))
        c1 = axFan lfPart D2_treeRec_NN_fun Pair p O

        c2 : Deriv (atomic (eqn (ap2 lfPart p O)
                                 (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                   (ap1 Df_f p))))
        c2 = lfPart_red p O

        c3 : Deriv (atomic (eqn (ap2 dispatchFun p O)
                                 (ap2 Pair
                                   (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                     (ap1 Df_f p))
                                   (ap2 D2_treeRec_NN_fun p O))))
        c3 = ruleTrans c1
              (congL Pair (ap2 D2_treeRec_NN_fun p O) c2)

        a4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 dispatchFun p O))
                                 (ap2 IfLf O (ap2 Pair
                                   (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                     (ap1 Df_f p))
                                   (ap2 D2_treeRec_NN_fun p O)))))
        a4 = congR IfLf O c3

        a5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair
                                  (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                    (ap1 Df_f p))
                                  (ap2 D2_treeRec_NN_fun p O)))
                                 (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                   (ap1 Df_f p))))
        a5 = axIfLfL (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                       (ap1 Df_f p))
                     (ap2 D2_treeRec_NN_fun p O)

    in ruleTrans a1 (ruleTrans a3 (ruleTrans a4 a5))

  D2_treeRec_fs_reduce_Nd : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 D2_treeRec_fs p (ap2 Pair v1 v2))
                       (ap2 D2_treeRec_NN_fun p (ap2 Pair v1 v2))))
  D2_treeRec_fs_reduce_Nd p v1 v2 =
    let x = ap2 Pair v1 v2

        a1 : Deriv (atomic (eqn (ap2 D2_treeRec_fs p x)
                                 (ap2 IfLf (ap2 (Post Snd Pair) p x)
                                            (ap2 dispatchFun p x))))
        a1 = axFan (Post Snd Pair) dispatchFun IfLf p x

        a2 : Deriv (atomic (eqn (ap2 (Post Snd Pair) p x) x))
        a2 = postSndPair_eval p x

        a3 : Deriv (atomic (eqn (ap2 IfLf (ap2 (Post Snd Pair) p x)
                                          (ap2 dispatchFun p x))
                                 (ap2 IfLf x (ap2 dispatchFun p x))))
        a3 = congL IfLf (ap2 dispatchFun p x) a2

        c1 : Deriv (atomic (eqn (ap2 dispatchFun p x)
                                 (ap2 Pair (ap2 lfPart p x)
                                            (ap2 D2_treeRec_NN_fun p x))))
        c1 = axFan lfPart D2_treeRec_NN_fun Pair p x

        a4 : Deriv (atomic (eqn (ap2 IfLf x (ap2 dispatchFun p x))
                                 (ap2 IfLf x (ap2 Pair (ap2 lfPart p x)
                                                        (ap2 D2_treeRec_NN_fun p x)))))
        a4 = congR IfLf x c1

        a5 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair v1 v2)
                                          (ap2 Pair (ap2 lfPart p x)
                                                     (ap2 D2_treeRec_NN_fun p x)))
                                 (ap2 D2_treeRec_NN_fun p x)))
        a5 = axIfLfN v1 v2 (ap2 lfPart p x) (ap2 D2_treeRec_NN_fun p x)

    in ruleTrans a1 (ruleTrans a3 (ruleTrans a4 a5))

  ----------------------------------------------------------------------
  -- Pointwise correctness at x = O via parDispRuleTrans on (parEncAxTreeRecLf,
  -- ap1 Df_f p), with the matching middle component
  --   Pair tagAp1 (Pair fT (cor p)).

  D_correct2_treeRec_fs_O : (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p O))
                       (codeFTeq2_treeRec_fs f s p O)))
  D_correct2_treeRec_fs_O p =
    let
        -- thmT(D2 p O) = thmT(parEncRuleTrans (parEncAxTreeRecLf ...) (Df_f p)).
        r_thmT : Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p O))
                                     (ap1 thmT (parEncRuleTrans
                                                  (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                  (ap1 Df_f p)))))
        r_thmT = cong1 thmT (D2_treeRec_fs_reduce_O p)

        -- y1's image: (encoded LHS treeRec p O, Pair tagAp1 (Pair fT (cor p))).
        u1_y1 : Term
        u1_y1 = ap2 Pair (reify tagAp2)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                       (ap2 Pair fT sT))
                            (ap2 Pair (ap1 cor p) O))
        u2_y1 : Term
        u2_y1 = ap2 Pair (reify tagAp1) (ap2 Pair fT (ap1 cor p))

        d_y1 : Deriv (atomic (eqn (ap1 thmT (parEncAxTreeRecLf fT sT (ap1 cor p)))
                                    (ap2 Pair u1_y1 u2_y1)))
        d_y1 = parDispAxTreeRecLf fT sT (ap1 cor p)

        -- y2's image: (Pair tagAp1 (Pair fT (cor p)), cor (f p))   -- via proof_f.
        u1_Df : Term
        u1_Df = ap2 Pair (reify tagAp1) (ap2 Pair fT (ap1 cor p))
        u2_Df : Term
        u2_Df = ap1 cor (ap1 f p)

        d_Df : Deriv (atomic (eqn (ap1 thmT (ap1 Df_f p))
                                    (ap2 Pair u1_Df u2_Df)))
        d_Df = proof_f p

        -- Shape proof: Fst (parEncAxTreeRecLf fT sT (cor p)) = tagCode_axTreeRecLf
        --            = Pair O (...rest of natCode tagAxTreeRecLf...).
        y1_shape : Deriv (atomic (eqn (ap1 Fst (parEncAxTreeRecLf fT sT (ap1 cor p)))
                                        (ap2 Pair O _)))
        y1_shape = axFst tagCode_axTreeRecLf _

        -- parDispRuleTrans composes y1, y2 at the matching u2 = u3 = u1_Df.
        d_chain : Deriv (atomic (eqn
              (ap1 thmT (parEncRuleTrans
                          (parEncAxTreeRecLf fT sT (ap1 cor p))
                          (ap1 Df_f p)))
              (ap2 Pair u1_y1 u2_Df)))
        d_chain = parDispRuleTrans
                    (parEncAxTreeRecLf fT sT (ap1 cor p))
                    (ap1 Df_f p)
                    u1_y1 u2_y1 u1_Df u2_Df
                    _ _
                    y1_shape d_y1 d_Df

        -- Bridge u1_y1 to codeFTeq2_TR's encoded LHS: rewrite trailing  O  to  cor O .
        cor_O : Deriv (atomic (eqn (ap1 cor O) O))
        cor_O = axRecLf stepCor

        bL_innerPair : Deriv (atomic (eqn (ap2 Pair (ap1 cor p) O)
                                            (ap2 Pair (ap1 cor p) (ap1 cor O))))
        bL_innerPair = congR Pair (ap1 cor p) (ruleSym cor_O)

        bL_secondPair : Deriv (atomic (eqn
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                       (ap2 Pair fT sT))
                            (ap2 Pair (ap1 cor p) O))
                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                            (ap2 Pair (ap1 cor p) (ap1 cor O)))))
        bL_secondPair = congR Pair (reify (codeF2 (treeRec f s))) bL_innerPair

        bL : Deriv (atomic (eqn u1_y1
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 (treeRec f s)))
                                      (ap2 Pair (ap1 cor p) (ap1 cor O))))))
        bL = congR Pair (reify tagAp2) bL_secondPair

        -- Bridge u2_Df = cor (f p) to cor (treeRec f s p O) via cong1 cor (ruleSym axTreeRecLf).
        recLf_eq : Deriv (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))
        recLf_eq = axTreeRecLf f s p

        bR : Deriv (atomic (eqn u2_Df (ap1 cor (ap2 (treeRec f s) p O))))
        bR = ruleSym (cong1 cor recLf_eq)

        -- Combine bridges on the outer Pair.
        bridge1 : Deriv (atomic (eqn (ap2 Pair u1_y1 u2_Df)
                                       (ap2 Pair
                                         (ap2 Pair (reify tagAp2)
                                                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                                                             (ap2 Pair (ap1 cor p) (ap1 cor O))))
                                         u2_Df)))
        bridge1 = congL Pair u2_Df bL

        bridge2 : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 (treeRec f s)))
                                        (ap2 Pair (ap1 cor p) (ap1 cor O))))
                    u2_Df)
                  (codeFTeq2_treeRec_fs f s p O)))
        bridge2 = congR Pair
                    (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 (treeRec f s)))
                                        (ap2 Pair (ap1 cor p) (ap1 cor O))))
                    bR

    in ruleTrans r_thmT (ruleTrans d_chain (ruleTrans bridge1 bridge2))

  D_correct2_treeRec_fs_Nd : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p (ap2 Pair v1 v2)))
                       (codeFTeq2_treeRec_fs f s p (ap2 Pair v1 v2))))
  D_correct2_treeRec_fs_Nd p v1 v2 =
    let r_thmT = cong1 thmT (D2_treeRec_fs_reduce_Nd p v1 v2)
    in ruleTrans r_thmT (D_correct2_treeRec_NN_pt p v1 v2)

  ----------------------------------------------------------------------
  -- Universal proof via ruleIndBT on x.

  private
    v1IndNat : Nat
    v1IndNat = suc (suc zero)
    v2IndNat : Nat
    v2IndNat = suc (suc (suc zero))

  P_Th12_treeRec : Formula
  P_Th12_treeRec =
    atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) (var zero)))
                (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))

  ----------------------------------------------------------------------
  -- Bridge: from a Deriv at (var 1, r) for x, to substF zero r P_Th12_treeRec.

  private
    lhs_eq : (r : Term) ->
      Eq (subst zero r (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) (var zero))))
         (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) r))
    lhs_eq r =
      eqTrans (eqCong (\ F -> ap1 F (ap2 (substF2 zero r D2_treeRec_fs) (var (suc zero)) r))
                       (thClosed zero r))
              (eqCong (\ D -> ap1 thmT (ap2 D (var (suc zero)) r))
                       (D2_treeRec_fs_closed zero r))

    inner_corPair_eq : (r : Term) ->
      Eq (subst zero r (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor (var zero))))
         (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor r))
    inner_corPair_eq r =
      eqTrans (eqCong (\ C -> ap2 Pair (ap1 C (var (suc zero)))
                                        (ap1 (substF1 zero r cor) r))
                       (cor_closed zero r))
              (eqCong (\ C -> ap2 Pair (ap1 cor (var (suc zero))) (ap1 C r))
                       (cor_closed zero r))

    second_pair_eq : (r : Term) ->
      Eq (subst zero r (ap2 Pair (reify (codeF2 (treeRec f s)))
                                  (ap2 Pair (ap1 cor (var (suc zero)))
                                            (ap1 cor (var zero)))))
         (ap2 Pair (reify (codeF2 (treeRec f s)))
                   (ap2 Pair (ap1 cor (var (suc zero)))
                             (ap1 cor r)))
    second_pair_eq r =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst zero r
                                  (ap2 Pair (ap1 cor (var (suc zero)))
                                            (ap1 cor (var zero)))))
                       (subst_reify zero r (codeF2 (treeRec f s))))
              (eqCong (\ P -> ap2 Pair (reify (codeF2 (treeRec f s))) P)
                       (inner_corPair_eq r))

    encoded_lhs_eq : (r : Term) ->
      Eq (subst zero r (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor (var zero))))))
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                             (ap2 Pair (ap1 cor (var (suc zero)))
                                       (ap1 cor r))))
    encoded_lhs_eq r =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst zero r
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor (var zero))))))
                       (subst_reify zero r tagAp2))
              (eqCong (\ Q -> ap2 Pair (reify tagAp2) Q)
                       (second_pair_eq r))

    cor_treeRec_eq : (r : Term) ->
      Eq (subst zero r (ap1 cor (ap2 (treeRec f s) (var (suc zero)) (var zero))))
         (ap1 cor (ap2 (treeRec f s) (var (suc zero)) r))
    cor_treeRec_eq r =
      eqTrans (eqCong (\ C -> ap1 C (ap2 (substF2 zero r (treeRec f s))
                                          (var (suc zero)) r))
                       (cor_closed zero r))
              (eqCong (\ TR -> ap1 cor (ap2 TR (var (suc zero)) r))
                       (treeRec_fs_closed zero r))

    rhs_eq : (r : Term) ->
      Eq (subst zero r (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))
         (codeFTeq2_treeRec_fs f s (var (suc zero)) r)
    rhs_eq r =
      eqTrans (eqCong (\ X -> ap2 Pair X
                                (subst zero r
                                  (ap1 cor (ap2 (treeRec f s) (var (suc zero)) (var zero)))))
                       (encoded_lhs_eq r))
              (eqCong (\ Y -> ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor r))))
                                Y)
                       (cor_treeRec_eq r))

    P_concrete_at : Term -> Formula
    P_concrete_at r =
      atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) r))
                  (codeFTeq2_treeRec_fs f s (var (suc zero)) r))

    formula_eq : (r : Term) ->
      Eq (substF zero r P_Th12_treeRec) (P_concrete_at r)
    formula_eq r =
      eqTrans (eqCong (\ L -> atomic (eqn L
                                (subst zero r
                                  (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))))
                       (lhs_eq r))
              (eqCong (\ R -> atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) r)) R))
                       (rhs_eq r))

    to_substF : (r : Term) -> Deriv (P_concrete_at r) ->
                Deriv (substF zero r P_Th12_treeRec)
    to_substF r prf = eqSubst Deriv (eqSym (formula_eq r)) prf

  private
    base_O_subst : Deriv (substF zero O P_Th12_treeRec)
    base_O_subst = to_substF O (D_correct2_treeRec_fs_O (var (suc zero)))

    pairInd : Term
    pairInd = ap2 Pair (var v1IndNat) (var v2IndNat)

    step_subst : Deriv (substF zero pairInd P_Th12_treeRec)
    step_subst = to_substF pairInd
                   (D_correct2_treeRec_fs_Nd (var (suc zero))
                                              (var v1IndNat) (var v2IndNat))

    step_imp_inner :
      Deriv (substF zero (var v2IndNat) P_Th12_treeRec imp
             substF zero pairInd P_Th12_treeRec)
    step_imp_inner =
      mp (axK (substF zero pairInd P_Th12_treeRec)
              (substF zero (var v2IndNat) P_Th12_treeRec))
         step_subst

    step_imp :
      Deriv (substF zero (var v1IndNat) P_Th12_treeRec imp
             (substF zero (var v2IndNat) P_Th12_treeRec imp
              substF zero pairInd P_Th12_treeRec))
    step_imp =
      mp (axK (substF zero (var v2IndNat) P_Th12_treeRec imp
               substF zero pairInd P_Th12_treeRec)
              (substF zero (var v1IndNat) P_Th12_treeRec))
         step_imp_inner

  D_correct2_treeRec_fs_univ : Deriv P_Th12_treeRec
  D_correct2_treeRec_fs_univ =
    ruleIndBT P_Th12_treeRec v1IndNat v2IndNat base_O_subst step_imp

  ----------------------------------------------------------------------
  -- Universal  (p x : Term) -> Deriv ...  wrapper, with NO closure
  -- assumption on (p, x).
  --
  -- Pair-encoding ruleInst trick: pick a fresh var index  bigNat = 2 ,
  -- which is fresh in  P_Th12_treeRec  (whose only free vars are
  -- 0 and 1).  Three ruleInsts:
  --
  --   1.  ruleInst zero  (Snd (var bigNat))   -- inserts  Snd (var 2)  at x-slot.
  --   2.  ruleInst (suc zero)  (Fst (var bigNat))   -- inserts  Fst (var 2)  at p-slot.
  --   3.  ruleInst bigNat  (Pair p x)         -- inserts  (Pair p x)  at  var 2 .
  --
  -- The walk in step 2 goes through  Snd (var 2)  but  natEq 2 1 = false ,
  -- so it's identity on the inserted Snd.  The walk in step 3 finds
  -- var 2  inside  Fst (var 2)  and  Snd (var 2)  and substitutes
  -- (Pair p x)  there -- but never walks INTO  (Pair p x) .  So neither
  -- p  nor  x  is ever walked by a substitution.
  --
  -- Final formula has  Fst (Pair p x)  and  Snd (Pair p x)  at the slots,
  -- which we bridge to  p  and  x  via  axFst , axSnd  at the Deriv level.

  private
    bigNat : Nat
    bigNat = suc (suc zero)

    bigT : Term
    bigT = var bigNat

    fstBigT : Term
    fstBigT = ap1 Fst bigT

    sndBigT : Term
    sndBigT = ap1 Snd bigT

  -- Reduction of subst (suc zero) fstBigT applied to:
  --   sndBigT          -- identity (natEq 2 1 = false).
  --   reify t          -- identity (subst_reify).
  --   ap1 cor U        -- ap1 cor (subst (suc zero) fstBigT U).
  --   ap2 (treeRec f s) U V  -- treeRec_fs_closed.
  --   thmT, D2_treeRec_fs    -- thClosed, D2_treeRec_fs_closed.

  private
    -- subst (suc zero) fstBigT (var (suc zero)) = fstBigT  (definitional).
    -- subst (suc zero) fstBigT sndBigT = sndBigT  (definitional).

    -- Step 2 (subst (suc zero) fstBigT) Eq lemma:
    --   subst (suc zero) fstBigT (P_concrete_at sndBigT)
    --   = P_pair_at fstBigT sndBigT
    -- where  P_pair_at pT xT = atomic (eqn (thmT (D2 pT xT)) (codeFTeq2_TR f s pT xT)) .

    P_pair_at : Term -> Term -> Formula
    P_pair_at pT xT =
      atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs pT xT))
                  (codeFTeq2_treeRec_fs f s pT xT))

    -- subst (suc zero) fstBigT (LHS at (var 1, sndBigT))
    --   = thmT (D2 fstBigT sndBigT) .
    step2_lhs_eq :
      Eq (subst (suc zero) fstBigT
            (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) sndBigT)))
         (ap1 thmT (ap2 D2_treeRec_fs fstBigT sndBigT))
    step2_lhs_eq =
      eqTrans (eqCong (\ F -> ap1 F (ap2 (substF2 (suc zero) fstBigT D2_treeRec_fs)
                                          fstBigT sndBigT))
                       (thClosed (suc zero) fstBigT))
              (eqCong (\ D -> ap1 thmT (ap2 D fstBigT sndBigT))
                       (D2_treeRec_fs_closed (suc zero) fstBigT))

    -- subst (suc zero) fstBigT (Pair (cor (var 1)) (cor sndBigT))
    --   = Pair (cor fstBigT) (cor sndBigT) .
    step2_corPair_eq :
      Eq (subst (suc zero) fstBigT
            (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor sndBigT)))
         (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))
    step2_corPair_eq =
      eqTrans (eqCong (\ C -> ap2 Pair (ap1 C fstBigT)
                                        (ap1 (substF1 (suc zero) fstBigT cor) sndBigT))
                       (cor_closed (suc zero) fstBigT))
              (eqCong (\ C -> ap2 Pair (ap1 cor fstBigT) (ap1 C sndBigT))
                       (cor_closed (suc zero) fstBigT))

    -- subst (suc zero) fstBigT (Pair codeF2_TR (Pair (cor (var 1)) (cor sndBigT)))
    --   = Pair codeF2_TR (Pair (cor fstBigT) (cor sndBigT)) .
    step2_secondPair_eq :
      Eq (subst (suc zero) fstBigT
            (ap2 Pair (reify (codeF2 (treeRec f s)))
                      (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor sndBigT))))
         (ap2 Pair (reify (codeF2 (treeRec f s)))
                   (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT)))
    step2_secondPair_eq =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst (suc zero) fstBigT
                                  (ap2 Pair (ap1 cor (var (suc zero)))
                                            (ap1 cor sndBigT))))
                       (subst_reify (suc zero) fstBigT (codeF2 (treeRec f s))))
              (eqCong (\ Q -> ap2 Pair (reify (codeF2 (treeRec f s))) Q)
                       step2_corPair_eq)

    step2_encoded_lhs_eq :
      Eq (subst (suc zero) fstBigT
            (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 (treeRec f s)))
                                (ap2 Pair (ap1 cor (var (suc zero)))
                                          (ap1 cor sndBigT)))))
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                             (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
    step2_encoded_lhs_eq =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst (suc zero) fstBigT
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor sndBigT)))))
                       (subst_reify (suc zero) fstBigT tagAp2))
              (eqCong (\ Q -> ap2 Pair (reify tagAp2) Q) step2_secondPair_eq)

    step2_corTreeRec_eq :
      Eq (subst (suc zero) fstBigT
            (ap1 cor (ap2 (treeRec f s) (var (suc zero)) sndBigT)))
         (ap1 cor (ap2 (treeRec f s) fstBigT sndBigT))
    step2_corTreeRec_eq =
      eqTrans (eqCong (\ C -> ap1 C (ap2 (substF2 (suc zero) fstBigT (treeRec f s))
                                          fstBigT sndBigT))
                       (cor_closed (suc zero) fstBigT))
              (eqCong (\ TR -> ap1 cor (ap2 TR fstBigT sndBigT))
                       (treeRec_fs_closed (suc zero) fstBigT))

    step2_rhs_eq :
      Eq (subst (suc zero) fstBigT
            (codeFTeq2_treeRec_fs f s (var (suc zero)) sndBigT))
         (codeFTeq2_treeRec_fs f s fstBigT sndBigT)
    step2_rhs_eq =
      eqTrans (eqCong (\ X -> ap2 Pair X
                                (subst (suc zero) fstBigT
                                  (ap1 cor (ap2 (treeRec f s) (var (suc zero)) sndBigT))))
                       step2_encoded_lhs_eq)
              (eqCong (\ Y -> ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
                                Y)
                       step2_corTreeRec_eq)

    step2_formula_eq :
      Eq (substF (suc zero) fstBigT (P_concrete_at sndBigT))
         (P_pair_at fstBigT sndBigT)
    step2_formula_eq =
      eqTrans (eqCong (\ L -> atomic (eqn L
                                (subst (suc zero) fstBigT
                                  (codeFTeq2_treeRec_fs f s (var (suc zero)) sndBigT))))
                       step2_lhs_eq)
              (eqCong (\ R -> atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs fstBigT sndBigT)) R))
                       step2_rhs_eq)

  ----------------------------------------------------------------------
  -- Step 3 reduction:  subst bigNat (Pair p x)  on  P_pair_at fstBigT sndBigT
  -- = P_pair_at (Fst (Pair p x)) (Snd (Pair p x)).

  private
    step3_FstBig_eq : (pT : Term) ->
      Eq (subst bigNat pT fstBigT) (ap1 Fst pT)
    step3_FstBig_eq pT =
      eqCong (\ F -> ap1 F pT) (Fun1_closed bigNat pT Fst)

    step3_SndBig_eq : (pT : Term) ->
      Eq (subst bigNat pT sndBigT) (ap1 Snd pT)
    step3_SndBig_eq pT =
      eqCong (\ F -> ap1 F pT) (Fun1_closed bigNat pT Snd)

    step3_lhs_eq : (pT : Term) ->
      Eq (subst bigNat pT (ap1 thmT (ap2 D2_treeRec_fs fstBigT sndBigT)))
         (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pT) (ap1 Snd pT)))
    step3_lhs_eq pT =
      eqTrans (eqCong (\ F -> ap1 F (ap2 (substF2 bigNat pT D2_treeRec_fs)
                                          (subst bigNat pT fstBigT)
                                          (subst bigNat pT sndBigT)))
                       (thClosed bigNat pT))
              (eqTrans (eqCong (\ D -> ap1 thmT (ap2 D
                                          (subst bigNat pT fstBigT)
                                          (subst bigNat pT sndBigT)))
                                (D2_treeRec_fs_closed bigNat pT))
                       (eqTrans (eqCong (\ A -> ap1 thmT (ap2 D2_treeRec_fs A
                                                  (subst bigNat pT sndBigT)))
                                          (step3_FstBig_eq pT))
                                (eqCong (\ B -> ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pT) B))
                                          (step3_SndBig_eq pT))))

    step3_corPair_eq : (pT : Term) ->
      Eq (subst bigNat pT (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT)))
         (ap2 Pair (ap1 cor (ap1 Fst pT)) (ap1 cor (ap1 Snd pT)))
    step3_corPair_eq pT =
      eqTrans (eqCong (\ C -> ap2 Pair (ap1 C (subst bigNat pT fstBigT))
                                        (ap1 (substF1 bigNat pT cor) (subst bigNat pT sndBigT)))
                       (cor_closed bigNat pT))
              (eqTrans (eqCong (\ C -> ap2 Pair (ap1 cor (subst bigNat pT fstBigT))
                                                  (ap1 C (subst bigNat pT sndBigT)))
                                (cor_closed bigNat pT))
                       (eqTrans (eqCong (\ A -> ap2 Pair (ap1 cor A)
                                                          (ap1 cor (subst bigNat pT sndBigT)))
                                          (step3_FstBig_eq pT))
                                (eqCong (\ B -> ap2 Pair (ap1 cor (ap1 Fst pT)) (ap1 cor B))
                                          (step3_SndBig_eq pT))))

    step3_secondPair_eq : (pT : Term) ->
      Eq (subst bigNat pT
            (ap2 Pair (reify (codeF2 (treeRec f s)))
                      (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
         (ap2 Pair (reify (codeF2 (treeRec f s)))
                   (ap2 Pair (ap1 cor (ap1 Fst pT)) (ap1 cor (ap1 Snd pT))))
    step3_secondPair_eq pT =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst bigNat pT
                                  (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
                       (subst_reify bigNat pT (codeF2 (treeRec f s))))
              (eqCong (\ Q -> ap2 Pair (reify (codeF2 (treeRec f s))) Q)
                       (step3_corPair_eq pT))

    step3_encoded_lhs_eq : (pT : Term) ->
      Eq (subst bigNat pT
            (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 (treeRec f s)))
                                (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT)))))
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                             (ap2 Pair (ap1 cor (ap1 Fst pT)) (ap1 cor (ap1 Snd pT)))))
    step3_encoded_lhs_eq pT =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst bigNat pT
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor fstBigT)
                                                      (ap1 cor sndBigT)))))
                       (subst_reify bigNat pT tagAp2))
              (eqCong (\ Q -> ap2 Pair (reify tagAp2) Q) (step3_secondPair_eq pT))

    step3_corTreeRec_eq : (pT : Term) ->
      Eq (subst bigNat pT (ap1 cor (ap2 (treeRec f s) fstBigT sndBigT)))
         (ap1 cor (ap2 (treeRec f s) (ap1 Fst pT) (ap1 Snd pT)))
    step3_corTreeRec_eq pT =
      eqTrans (eqCong (\ C -> ap1 C (ap2 (substF2 bigNat pT (treeRec f s))
                                          (subst bigNat pT fstBigT)
                                          (subst bigNat pT sndBigT)))
                       (cor_closed bigNat pT))
              (eqTrans (eqCong (\ TR -> ap1 cor (ap2 TR
                                          (subst bigNat pT fstBigT)
                                          (subst bigNat pT sndBigT)))
                                (treeRec_fs_closed bigNat pT))
                       (eqTrans (eqCong (\ A -> ap1 cor (ap2 (treeRec f s) A
                                                  (subst bigNat pT sndBigT)))
                                          (step3_FstBig_eq pT))
                                (eqCong (\ B -> ap1 cor (ap2 (treeRec f s) (ap1 Fst pT) B))
                                          (step3_SndBig_eq pT))))

    step3_rhs_eq : (pT : Term) ->
      Eq (subst bigNat pT (codeFTeq2_treeRec_fs f s fstBigT sndBigT))
         (codeFTeq2_treeRec_fs f s (ap1 Fst pT) (ap1 Snd pT))
    step3_rhs_eq pT =
      eqTrans (eqCong (\ X -> ap2 Pair X
                                (subst bigNat pT
                                  (ap1 cor (ap2 (treeRec f s) fstBigT sndBigT))))
                       (step3_encoded_lhs_eq pT))
              (eqCong (\ Y -> ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (ap1 Fst pT))
                                                      (ap1 cor (ap1 Snd pT)))))
                                Y)
                       (step3_corTreeRec_eq pT))

    step3_formula_eq : (pT : Term) ->
      Eq (substF bigNat pT (P_pair_at fstBigT sndBigT))
         (P_pair_at (ap1 Fst pT) (ap1 Snd pT))
    step3_formula_eq pT =
      eqTrans (eqCong (\ L -> atomic (eqn L
                                (subst bigNat pT
                                  (codeFTeq2_treeRec_fs f s fstBigT sndBigT))))
                       (step3_lhs_eq pT))
              (eqCong (\ R -> atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pT)
                                                                       (ap1 Snd pT))) R))
                       (step3_rhs_eq pT))

  ----------------------------------------------------------------------
  -- Final Deriv-level bridge:  P_pair_at (Fst (Pair p x)) (Snd (Pair p x))
  --   ~~> P_pair_at p x  via  axFst p x  +  axSnd p x .

  private
    pairBridgeEqLHS : (p x : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst (ap2 Pair p x))
                                                        (ap1 Snd (ap2 Pair p x))))
                          (ap1 thmT (ap2 D2_treeRec_fs p x))))
    pairBridgeEqLHS p x =
      cong1 thmT
        (ruleTrans (congL D2_treeRec_fs (ap1 Snd (ap2 Pair p x)) (axFst p x))
                   (congR D2_treeRec_fs p (axSnd p x)))

    pairBridgeEqCorP : (p x : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair p x))) (ap1 cor p)))
    pairBridgeEqCorP p x = cong1 cor (axFst p x)

    pairBridgeEqCorX : (p x : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap1 Snd (ap2 Pair p x))) (ap1 cor x)))
    pairBridgeEqCorX p x = cong1 cor (axSnd p x)

    pairBridgeEqCorTR : (p x : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap2 (treeRec f s) (ap1 Fst (ap2 Pair p x))
                                                       (ap1 Snd (ap2 Pair p x))))
                          (ap1 cor (ap2 (treeRec f s) p x))))
    pairBridgeEqCorTR p x =
      cong1 cor
        (ruleTrans (congL (treeRec f s) (ap1 Snd (ap2 Pair p x)) (axFst p x))
                   (congR (treeRec f s) p (axSnd p x)))

    -- Bridge the encoded LHS:
    --   Pair tagAp2 (Pair codeF2_TR (Pair (cor (Fst (Pair p x))) (cor (Snd (Pair p x)))))
    --   = Pair tagAp2 (Pair codeF2_TR (Pair (cor p) (cor x)))
    pairBridgeEncoded : (p x : Term) ->
      Deriv (atomic (eqn
        (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                            (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair p x)))
                                      (ap1 cor (ap1 Snd (ap2 Pair p x))))))
        (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                            (ap2 Pair (ap1 cor p) (ap1 cor x))))))
    pairBridgeEncoded p x =
      let inner_corPair :
              Deriv (atomic (eqn
                (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair p x)))
                          (ap1 cor (ap1 Snd (ap2 Pair p x))))
                (ap2 Pair (ap1 cor p) (ap1 cor x))))
          inner_corPair =
            ruleTrans (congL Pair (ap1 cor (ap1 Snd (ap2 Pair p x))) (pairBridgeEqCorP p x))
                      (congR Pair (ap1 cor p) (pairBridgeEqCorX p x))

          second_pair :
              Deriv (atomic (eqn
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair p x)))
                                    (ap1 cor (ap1 Snd (ap2 Pair p x)))))
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor p) (ap1 cor x)))))
          second_pair = congR Pair (reify (codeF2 (treeRec f s))) inner_corPair
      in congR Pair (reify tagAp2) second_pair

    -- Bridge the full RHS  codeFTeq2_treeRec_fs f s (Fst pPx) (Snd pPx) = ... f s p x.
    pairBridgeRHS : (p x : Term) ->
      Deriv (atomic (eqn (codeFTeq2_treeRec_fs f s
                            (ap1 Fst (ap2 Pair p x)) (ap1 Snd (ap2 Pair p x)))
                          (codeFTeq2_treeRec_fs f s p x)))
    pairBridgeRHS p x =
      ruleTrans (congL Pair
                   (ap1 cor (ap2 (treeRec f s) (ap1 Fst (ap2 Pair p x))
                                                 (ap1 Snd (ap2 Pair p x))))
                   (pairBridgeEncoded p x))
                (congR Pair
                   (ap2 Pair (reify tagAp2)
                             (ap2 Pair (reify (codeF2 (treeRec f s)))
                                       (ap2 Pair (ap1 cor p) (ap1 cor x))))
                   (pairBridgeEqCorTR p x))

  D_correct2_treeRec_fs : (p x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p x))
                       (codeFTeq2_treeRec_fs f s p x)))
  D_correct2_treeRec_fs p x =
    let
        -- Stage 1: ruleInst zero -> sndBigT.
        stage1_raw : Deriv (substF zero sndBigT P_Th12_treeRec)
        stage1_raw = ruleInst zero sndBigT D_correct2_treeRec_fs_univ

        stage1 : Deriv (P_concrete_at sndBigT)
        stage1 = eqSubst Deriv (formula_eq sndBigT) stage1_raw

        -- Stage 2: ruleInst (suc zero) -> fstBigT.
        stage2_raw : Deriv (substF (suc zero) fstBigT (P_concrete_at sndBigT))
        stage2_raw = ruleInst (suc zero) fstBigT stage1

        stage2 : Deriv (P_pair_at fstBigT sndBigT)
        stage2 = eqSubst Deriv step2_formula_eq stage2_raw

        -- Stage 3: ruleInst bigNat -> Pair p x.
        pairPX : Term
        pairPX = ap2 Pair p x

        stage3_raw : Deriv (substF bigNat pairPX (P_pair_at fstBigT sndBigT))
        stage3_raw = ruleInst bigNat pairPX stage2

        stage3 : Deriv (P_pair_at (ap1 Fst pairPX) (ap1 Snd pairPX))
        stage3 = eqSubst Deriv (step3_formula_eq pairPX) stage3_raw

        -- Final Deriv-level bridge using axFst, axSnd.
        --   stage3 : Deriv (eqn (thmT (D2 (Fst pPx) (Snd pPx))) (codeFTeq2 ... (Fst pPx) (Snd pPx)))
        --   Want : Deriv (eqn (thmT (D2 p x)) (codeFTeq2 ... p x)).
        --
        -- ruleTrans  ((thmT (D2 p x)) -> (thmT (D2 (Fst pPx) (Snd pPx))))
        --           ((thmT (D2 (Fst pPx) (Snd pPx))) -> (codeFTeq2 (Fst pPx) (Snd pPx)))
        --           ((codeFTeq2 (Fst pPx) (Snd pPx)) -> (codeFTeq2 p x))
        --   = (thmT (D2 p x)) -> (codeFTeq2 p x).

        bridge_lhs_back : Deriv (atomic (eqn
          (ap1 thmT (ap2 D2_treeRec_fs p x))
          (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pairPX) (ap1 Snd pairPX)))))
        bridge_lhs_back = ruleSym (pairBridgeEqLHS p x)

        bridge_rhs_forward : Deriv (atomic (eqn
          (codeFTeq2_treeRec_fs f s (ap1 Fst pairPX) (ap1 Snd pairPX))
          (codeFTeq2_treeRec_fs f s p x)))
        bridge_rhs_forward = pairBridgeRHS p x

    in ruleTrans bridge_lhs_back (ruleTrans stage3 bridge_rhs_forward)

------------------------------------------------------------------------
-- Top-level convenience alias.

Df_F2_treeRec :
  (f : Fun1) (s : Fun2)
  (Df_f : Fun1)
  (proof_f : (q : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 Df_f q))
                       (ap2 Pair
                         (ap2 Pair (reify tagAp1)
                                   (ap2 Pair (reify (codeF1 f)) (ap1 cor q)))
                         (ap1 cor (ap1 f q))))))
  (D2_treeRec_NN_fun : Fun2)
  (D_correct2_treeRec_NN_pt : (p a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_NN_fun p (ap2 Pair a b)))
                       (codeFTeq2_treeRec_fs f s p (ap2 Pair a b)))))
  -> Fun2
Df_F2_treeRec f s Df_f proof_f D2NN D_NN_pt =
  Construction.D2_treeRec_fs f s Df_f proof_f D2NN D_NN_pt
