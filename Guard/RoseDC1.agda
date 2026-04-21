{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RoseDC1 -- Rose's Lemma 2 (DC1) as a per-primitive encoder
-- library.
--
-- Layer 3 of the Rose/Ryan Goedel II plan (see NEXT-SESSION-IMPT-GODELII.md).
--
-- Rose's Lemma 2 says: for every PR function  f  in our primitive
-- vocabulary, there is an encoding function  p_f  such that given
-- the values of  f 's arguments, the term  p_f args  is a proof-
-- encoding that internally resolves (under  thmT hCode ) to
-- codeEqn (eqn (f args) (f args's computed value)) .
--
-- We already have this result in full generality -- it is Theorem 14
-- (v3), implemented in  Guard.Thm14EV3  as a family of  ProofE3
-- records.  Each  thm14EV3Ax*  record carries
--   * a specific Term  encT rec   (the encoding)
--   * a Deriv proof that  ap1 (thmT hCode) (encT rec) = reify (codeEqn ..) .
--
-- This module re-exports those records under Rose-style names:
--   * p_<f>     : ... -> Term                (the encoding itself)
--   * p_<f>Corr : ... -> Deriv .. (thmT-reduction to codeEqn ..)
-- for every computation axiom + structural combinator.  No new proofs
-- -- just a Rose-flavoured facade.
--
-- The structural combinators (sym/trans/cong1/congL/congR) take
-- ProofE3 arguments rather than raw Terms, since producing a new
-- encoding requires access to the caller's  pa/pb  split (which a bare
-- Term/Prov3 does not expose).

module Guard.RoseDC1 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.Thm14EV3

------------------------------------------------------------------------
-- Every encoder depends on the ambient hypothesis  H  whose code is
-- embedded into  thmT .  We parameterise by  H  via a module.

module RoseEncoders (H : Equation) where

  private
    hCode : Term
    hCode = reify (codeEqn H)

  --------------------------------------------------------------------
  -- Computation-axiom encoders
  --
  -- For each computation axiom, we expose the encoding Term and the
  -- correctness Deriv directly.

  -- axI

  p_I : (t : Term) -> Term
  p_I t = encT (thm14EV3AxI H t)

  p_ICorr : (t : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_I t))
                   (reify (codeEqn (eqn (ap1 I t) t))))
  p_ICorr t = corr (thm14EV3AxI H t)

  -- axFst

  p_Fst : (a b : Term) -> Term
  p_Fst a b = encT (thm14EV3AxFst H a b)

  p_FstCorr : (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Fst a b))
                   (reify (codeEqn (eqn (ap1 Fst (ap2 Pair a b)) a))))
  p_FstCorr a b = corr (thm14EV3AxFst H a b)

  -- axSnd

  p_Snd : (a b : Term) -> Term
  p_Snd a b = encT (thm14EV3AxSnd H a b)

  p_SndCorr : (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Snd a b))
                   (reify (codeEqn (eqn (ap1 Snd (ap2 Pair a b)) b))))
  p_SndCorr a b = corr (thm14EV3AxSnd H a b)

  -- axConst

  p_Const : (a b : Term) -> Term
  p_Const a b = encT (thm14EV3AxConst H a b)

  p_ConstCorr : (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Const a b))
                   (reify (codeEqn (eqn (ap2 Const a b) a))))
  p_ConstCorr a b = corr (thm14EV3AxConst H a b)

  -- axComp

  p_Comp : (f g : Fun1) (t : Term) -> Term
  p_Comp f g t = encT (thm14EV3AxComp H f g t)

  p_CompCorr : (f g : Fun1) (t : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Comp f g t))
                   (reify (codeEqn (eqn (ap1 (Comp f g) t)
                                        (ap1 f (ap1 g t))))))
  p_CompCorr f g t = corr (thm14EV3AxComp H f g t)

  -- axComp2

  p_Comp2 : (h : Fun2) (f g : Fun1) (t : Term) -> Term
  p_Comp2 h f g t = encT (thm14EV3AxComp2 H h f g t)

  p_Comp2Corr : (h : Fun2) (f g : Fun1) (t : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Comp2 h f g t))
                   (reify (codeEqn (eqn (ap1 (Comp2 h f g) t)
                                        (ap2 h (ap1 f t) (ap1 g t))))))
  p_Comp2Corr h f g t = corr (thm14EV3AxComp2 H h f g t)

  -- axLift

  p_Lift : (f : Fun1) (a b : Term) -> Term
  p_Lift f a b = encT (thm14EV3AxLift H f a b)

  p_LiftCorr : (f : Fun1) (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Lift f a b))
                   (reify (codeEqn (eqn (ap2 (Lift f) a b) (ap1 f a)))))
  p_LiftCorr f a b = corr (thm14EV3AxLift H f a b)

  -- axPost

  p_Post : (f : Fun1) (h : Fun2) (a b : Term) -> Term
  p_Post f h a b = encT (thm14EV3AxPost H f h a b)

  p_PostCorr : (f : Fun1) (h : Fun2) (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Post f h a b))
                   (reify (codeEqn (eqn (ap2 (Post f h) a b)
                                        (ap1 f (ap2 h a b))))))
  p_PostCorr f h a b = corr (thm14EV3AxPost H f h a b)

  -- axFan

  p_Fan : (h1 h2 h : Fun2) (a b : Term) -> Term
  p_Fan h1 h2 h a b = encT (thm14EV3AxFan H h1 h2 h a b)

  p_FanCorr : (h1 h2 h : Fun2) (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_Fan h1 h2 h a b))
                   (reify (codeEqn (eqn (ap2 (Fan h1 h2 h) a b)
                                        (ap2 h (ap2 h1 a b)
                                               (ap2 h2 a b))))))
  p_FanCorr h1 h2 h a b = corr (thm14EV3AxFan H h1 h2 h a b)

  -- axKT

  p_KT : (t x : Term) -> Term
  p_KT t x = encT (thm14EV3AxKT H t x)

  p_KTCorr : (t x : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_KT t x))
                   (reify (codeEqn (eqn (ap1 (KT t) x) t))))
  p_KTCorr t x = corr (thm14EV3AxKT H t x)

  -- axRecLf / axRecNd

  p_RecLf : (z : Term) (s : Fun2) -> Term
  p_RecLf z s = encT (thm14EV3AxRecLf H z s)

  p_RecLfCorr : (z : Term) (s : Fun2) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_RecLf z s))
                   (reify (codeEqn (eqn (ap1 (Rec z s) O) z))))
  p_RecLfCorr z s = corr (thm14EV3AxRecLf H z s)

  p_RecNd : (z : Term) (s : Fun2) (a b : Term) -> Term
  p_RecNd z s a b = encT (thm14EV3AxRecNd H z s a b)

  p_RecNdCorr : (z : Term) (s : Fun2) (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_RecNd z s a b))
                   (reify (codeEqn
                     (eqn (ap1 (Rec z s) (ap2 Pair a b))
                          (ap2 s (ap2 Pair a b)
                                 (ap2 Pair (ap1 (Rec z s) a)
                                           (ap1 (Rec z s) b)))))))
  p_RecNdCorr z s a b = corr (thm14EV3AxRecNd H z s a b)

  --------------------------------------------------------------------
  -- axIfLfL / axIfLfN

  p_IfLfL : (a b : Term) -> Term
  p_IfLfL a b = encT (thm14EV3AxIfLfL H a b)

  p_IfLfLCorr : (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_IfLfL a b))
                   (reify (codeEqn
                     (eqn (ap2 IfLf O (ap2 Pair a b)) a))))
  p_IfLfLCorr a b = corr (thm14EV3AxIfLfL H a b)

  p_IfLfN : (x y a b : Term) -> Term
  p_IfLfN x y a b = encT (thm14EV3AxIfLfN H x y a b)

  p_IfLfNCorr : (x y a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_IfLfN x y a b))
                   (reify (codeEqn
                     (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))))
  p_IfLfNCorr x y a b = corr (thm14EV3AxIfLfN H x y a b)

  --------------------------------------------------------------------
  -- axTreeEq{LL,LN,NL,NN}

  p_TreeEqLL : Term
  p_TreeEqLL = encT (thm14EV3AxTreeEqLL H)

  p_TreeEqLLCorr : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) p_TreeEqLL)
                   (reify (codeEqn (eqn (ap2 TreeEq O O) O))))
  p_TreeEqLLCorr = corr (thm14EV3AxTreeEqLL H)

  p_TreeEqLN : (a b : Term) -> Term
  p_TreeEqLN a b = encT (thm14EV3AxTreeEqLN H a b)

  p_TreeEqLNCorr : (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_TreeEqLN a b))
                   (reify (codeEqn
                     (eqn (ap2 TreeEq O (ap2 Pair a b))
                          (ap2 Pair O O)))))
  p_TreeEqLNCorr a b = corr (thm14EV3AxTreeEqLN H a b)

  p_TreeEqNL : (a b : Term) -> Term
  p_TreeEqNL a b = encT (thm14EV3AxTreeEqNL H a b)

  p_TreeEqNLCorr : (a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_TreeEqNL a b))
                   (reify (codeEqn
                     (eqn (ap2 TreeEq (ap2 Pair a b) O)
                          (ap2 Pair O O)))))
  p_TreeEqNLCorr a b = corr (thm14EV3AxTreeEqNL H a b)

  p_TreeEqNN : (a1 a2 b1 b2 : Term) -> Term
  p_TreeEqNN a1 a2 b1 b2 = encT (thm14EV3AxTreeEqNN H a1 a2 b1 b2)

  p_TreeEqNNCorr : (a1 a2 b1 b2 : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_TreeEqNN a1 a2 b1 b2))
                   (reify (codeEqn
                     (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                          (ap2 IfLf (ap2 TreeEq a1 b1)
                                    (ap2 Pair (ap2 TreeEq a2 b2)
                                              (ap2 Pair O O)))))))
  p_TreeEqNNCorr a1 a2 b1 b2 = corr (thm14EV3AxTreeEqNN H a1 a2 b1 b2)

  --------------------------------------------------------------------
  -- RecP

  p_RecPLf : (s : Fun2) (p : Term) -> Term
  p_RecPLf s p = encT (thm14EV3AxRecPLf H s p)

  p_RecPLfCorr : (s : Fun2) (p : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_RecPLf s p))
                   (reify (codeEqn (eqn (ap2 (RecP s) p O) O))))
  p_RecPLfCorr s p = corr (thm14EV3AxRecPLf H s p)

  p_RecPNd : (s : Fun2) (p a b : Term) -> Term
  p_RecPNd s p a b = encT (thm14EV3AxRecPNd H s p a b)

  p_RecPNdCorr : (s : Fun2) (p a b : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) (p_RecPNd s p a b))
                   (reify (codeEqn
                     (eqn (ap2 (RecP s) p (ap2 Pair a b))
                          (ap2 s (ap2 Pair p (ap2 Pair a b))
                                 (ap2 Pair (ap2 (RecP s) p a)
                                           (ap2 (RecP s) p b)))))))
  p_RecPNdCorr s p a b = corr (thm14EV3AxRecPNd H s p a b)

  --------------------------------------------------------------------
  -- Structural-rule encoders: sym / trans / cong1 / congL / congR /
  -- inst / axRefl / hyp / F .
  --
  -- These take ProofE3 arguments (not Terms) because producing a new
  -- encoding needs the  pa/pb  split of the sub-encoding.  Each is a
  -- one-line re-export of the corresponding thm14EV3 combinator.

  p_Refl : (t : Term) -> ProofE3 H (eqn t t)
  p_Refl t = thm14EV3Refl H t

  p_HypE : ProofE3 H H
  p_HypE = thm14EV3Hyp H

  p_Sym : {t u : Term} -> ProofE3 H (eqn t u) -> ProofE3 H (eqn u t)
  p_Sym = thm14EV3Sym

  p_Trans : {t u v : Term} ->
    ProofE3 H (eqn t u) -> ProofE3 H (eqn u v) ->
    ProofE3 H (eqn t v)
  p_Trans = thm14EV3Trans

  p_Cong1 : {t u : Term} (f : Fun1) ->
    ProofE3 H (eqn t u) -> ProofE3 H (eqn (ap1 f t) (ap1 f u))
  p_Cong1 = thm14EV3Cong1

  p_CongL : {t u : Term} (g : Fun2) (x : Term) ->
    ProofE3 H (eqn t u) -> ProofE3 H (eqn (ap2 g t x) (ap2 g u x))
  p_CongL = thm14EV3CongL

  p_CongR : {t u : Term} (g : Fun2) (x : Term) ->
    ProofE3 H (eqn t u) -> ProofE3 H (eqn (ap2 g x t) (ap2 g x u))
  p_CongR = thm14EV3CongR

  p_Inst : {l r' : Term} (x : Nat) (t : Term) ->
    ProofE3 H (eqn l r') ->
    ProofE3 H (substEq x t (eqn l r'))
  p_Inst = thm14EV3Inst

  --------------------------------------------------------------------
  -- The master DC1: any Deriv is encodable as a ProofE3.

  p_dc1 : {eq : Equation} -> Deriv H eq -> ProofE3 H eq
  p_dc1 = thm14EV3

------------------------------------------------------------------------
-- Summary
--
-- RoseEncoders H  exposes, for every primitive and every structural
-- rule of Deriv:
--
--   p_<ax>      : ... -> Term                 (the encoding)
--   p_<ax>Corr  : ... -> Deriv ...            (thmT hCode correctness)
--   p_Sym, p_Trans, p_Cong1, p_CongL, p_CongR, p_Inst, p_Refl, p_HypE
--               : ProofE3 combinators
--   p_dc1       : Deriv H eq -> ProofE3 H eq  (master DC1)
--
-- Every entry is a one-line re-export of an existing  thm14EV3*
-- definition; no new proofs.  Compiles under --safe --without-K
-- --exact-split, no postulates, no holes.
