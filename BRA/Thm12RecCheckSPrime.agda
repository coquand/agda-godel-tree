{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12RecCheckSPrime
--
-- Step 1 (of the Theorem 12 Rec parametric path):  construct  s' : Fun2
-- such that  ap2 s' (Pair a b) (Pair pf_a pf_b)  BRA-reduces to the
-- chain Term  Df_chain12345  used by  RecOSPairCaseFull .
--
-- Then  D_R = Rec z' s'  with
--   z' = parEncAxRecLf O sT  (the leaf chain Term, from thm12_RecOS_O ).
-- At  ap1 D_R O = z'  (axRecLf), so the leaf case Df aligns.
-- At  ap1 D_R (Pair a b) BRA-reduces (via axRecNd + s'-reduction) to
-- Df_chain12345(a, b, pf_a, pf_b)  where pf_a = ap1 D_R a, pf_b = ap1 D_R b.
--
-- This file delivers  s' , the reduction lemma  s'_red , and the
-- composite  D_R  with its base/step BRA-reduction lemmas.
-- Universal closure via ruleIndBT + SKI is downstream (steps 2-4).
--
-- No postulates, no holes.

module BRA.Thm12RecCheckSPrime where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axRecLf ; tagCode_axRecNd ; tagCode_axPost ; tagCode_axSnd
  ; tagCode_ruleTrans ; tagCode_congL ; tagCode_congR )
open import BRA.Thm.Tag using
  ( tagAxRecLf ; tagAxRecNd ; tagAxPost ; tagAxSnd
  ; tagRuleTrans ; tagCongL ; tagCongR )
open import BRA.Thm12RecCheck using (sBin ; D_Rec_OS_F)

------------------------------------------------------------------------
-- Constants and projections.

private
  sT : Term
  sT = reify (codeF2 sBin)

  cf : Term
  cf = reify (codeF1 D_Rec_OS_F)

  pCT : Term
  pCT = reify (codeF2 Pair)

  cSnd : Term
  cSnd = reify (codeF1 Snd)

  tagAp1T : Term
  tagAp1T = reify tagAp1

  tagAp2T : Term
  tagAp2T = reify tagAp2

------------------------------------------------------------------------
-- Fun2 building blocks.
--
--   constF t  : Fun2 producing  t  regardless of inputs (for canonical
--               t = reify v ; reduces via  axLift + axKT ).
--   pairF f g : Fun2 producing  ap2 Pair (f a b) (g a b) (axFan).

constF : Term -> Fun2
constF t = Lift (KT t)

pairF : Fun2 -> Fun2 -> Fun2
pairF f g = Fan f g Pair

-- Input projections at  (orig=Pair a b, recs=Pair pf_a pf_b) :

projFstOrig : Fun2
projFstOrig = Lift Fst              -- = Fst orig = a

projSndOrig : Fun2
projSndOrig = Lift Snd              -- = Snd orig = b

corFstOrig : Fun2
corFstOrig = Lift (Comp cor Fst)    -- = cor (Fst orig) = cor a = cv_a

corSndOrig : Fun2
corSndOrig = Lift (Comp cor Snd)    -- = cor (Snd orig) = cor b = cv_b

projFstRecs : Fun2
projFstRecs = Post Fst sBin         -- = Fst (sBin orig recs) = Fst recs = pf_a

projSndRecs : Fun2
projSndRecs = Post Snd sBin         -- = Snd recs = pf_b

corFstRecs : Fun2
corFstRecs = Post (Comp cor Fst) sBin  -- = cor (Fst recs) = cor pf_a

corSndRecs : Fun2
corSndRecs = Post (Comp cor Snd) sBin  -- = cor (Snd recs) = cor pf_b

------------------------------------------------------------------------
-- Mid-level Fun2's encoding the X, Y, mkAp1T-cv subterms.

-- F_mkAp1T_cv_a : produces  mkAp1T cf cv_a = ap2 Pair tagAp1T (ap2 Pair cf cv_a) .

F_mkAp1T_cv_a : Fun2
F_mkAp1T_cv_a = pairF (constF tagAp1T) (pairF (constF cf) corFstOrig)

F_mkAp1T_cv_b : Fun2
F_mkAp1T_cv_b = pairF (constF tagAp1T) (pairF (constF cf) corSndOrig)

-- F_X : produces  X = mkAp2T pCT cv_a cv_b = ap2 Pair tagAp2T (ap2 Pair pCT (ap2 Pair cv_a cv_b)) .

F_X : Fun2
F_X = pairF (constF tagAp2T) (pairF (constF pCT) (pairF corFstOrig corSndOrig))

-- F_Y : produces  Y = mkAp2T pCT (mkAp1T cf cv_a) (mkAp1T cf cv_b) .

F_Y : Fun2
F_Y = pairF (constF tagAp2T) (pairF (constF pCT) (pairF F_mkAp1T_cv_a F_mkAp1T_cv_b))

------------------------------------------------------------------------
-- Df_E_i sub-encoders.

F_Df_E1 : Fun2
F_Df_E1 = pairF (constF tagCode_axRecNd)
            (pairF (constF O)
              (pairF (constF sT) (pairF corFstOrig corSndOrig)))

F_Df_E2 : Fun2
F_Df_E2 = pairF (constF tagCode_axPost)
            (pairF (constF cSnd)
              (pairF (constF pCT) (pairF F_X F_Y)))

F_Df_E3 : Fun2
F_Df_E3 = pairF (constF tagCode_axSnd) (pairF F_X F_Y)

F_Df_E4 : Fun2
F_Df_E4 = pairF (constF tagCode_congL)
            (pairF (constF pCT) (pairF projFstRecs F_mkAp1T_cv_b))

F_Df_E5 : Fun2
F_Df_E5 = pairF (constF tagCode_congR)
            (pairF (constF pCT) (pairF projSndRecs corFstRecs))

------------------------------------------------------------------------
-- Chain-composition encoders.

F_chain12 : Fun2
F_chain12 = pairF (constF tagCode_ruleTrans) (pairF F_Df_E1 F_Df_E2)

F_chain123 : Fun2
F_chain123 = pairF (constF tagCode_ruleTrans) (pairF F_chain12 F_Df_E3)

F_chain1234 : Fun2
F_chain1234 = pairF (constF tagCode_ruleTrans) (pairF F_chain123 F_Df_E4)

F_chain12345 : Fun2
F_chain12345 = pairF (constF tagCode_ruleTrans) (pairF F_chain1234 F_Df_E5)

------------------------------------------------------------------------
-- s' : the step Fun2 of D_R = Rec z' s' .

s' : Fun2
s' = F_chain12345

------------------------------------------------------------------------
-- z' : the leaf-case chain Term of D_R = Rec z' s' .

z' : Term
z' = ap2 Pair tagCode_axRecLf (ap2 Pair O sT)
-- = parEncAxRecLf O sT  (matches Df from  thm12_RecOS_O ).

------------------------------------------------------------------------
-- D_R : the universal Theorem-12 witness functor.

D_R : Fun1
D_R = Rec z' s'

------------------------------------------------------------------------
-- Helper reduction lemmas.

-- pairF_red : Fan-applied reduces to Pair-of-results.

pairF_red :
  (f g : Fun2) (a b a' b' : Term) ->
  Deriv (atomic (eqn (ap2 f a b) a')) ->
  Deriv (atomic (eqn (ap2 g a b) b')) ->
  Deriv (atomic (eqn (ap2 (pairF f g) a b) (ap2 Pair a' b')))
pairF_red f g a b a' b' f_red g_red =
  ruleTrans (axFan f g Pair a b)
            (ruleTrans (congL Pair (ap2 g a b) f_red)
                       (congR Pair a' g_red))

-- constF_red : constF (reify v) applied at any (a, b) reduces to reify v.

constF_red :
  (v : Tree) (a b : Term) ->
  Deriv (atomic (eqn (ap2 (constF (reify v)) a b) (reify v)))
constF_red v a b = ruleTrans (axLift (KT (reify v)) a b) (axKT v a)


------------------------------------------------------------------------
-- Projection reduction lemmas at  (a, b) = (Pair α β, Pair pf_α pf_β) .
-- ( α = a , β = b , pf_α = pf_a , pf_β = pf_b ; renamed locally to
-- avoid Agda capturing globals.)

module ProjRed (α β pf_α pf_β : Term) where

  origT : Term
  origT = ap2 Pair α β

  recsT : Term
  recsT = ap2 Pair pf_α pf_β

  -- sBin_red : ap2 sBin orig recs = recs   (= Pair pf_α pf_β)

  sBin_red : Deriv (atomic (eqn (ap2 sBin origT recsT) recsT))
  sBin_red = ruleTrans (axPost Snd Pair origT recsT) (axSnd origT recsT)

  projFstOrig_red : Deriv (atomic (eqn (ap2 projFstOrig origT recsT) α))
  projFstOrig_red = ruleTrans (axLift Fst origT recsT) (axFst α β)

  projSndOrig_red : Deriv (atomic (eqn (ap2 projSndOrig origT recsT) β))
  projSndOrig_red = ruleTrans (axLift Snd origT recsT) (axSnd α β)

  corFstOrig_red : Deriv (atomic (eqn (ap2 corFstOrig origT recsT) (ap1 cor α)))
  corFstOrig_red =
    ruleTrans (axLift (Comp cor Fst) origT recsT)
              (ruleTrans (axComp cor Fst origT) (cong1 cor (axFst α β)))

  corSndOrig_red : Deriv (atomic (eqn (ap2 corSndOrig origT recsT) (ap1 cor β)))
  corSndOrig_red =
    ruleTrans (axLift (Comp cor Snd) origT recsT)
              (ruleTrans (axComp cor Snd origT) (cong1 cor (axSnd α β)))

  projFstRecs_red : Deriv (atomic (eqn (ap2 projFstRecs origT recsT) pf_α))
  projFstRecs_red =
    ruleTrans (axPost Fst sBin origT recsT)
              (ruleTrans (cong1 Fst sBin_red) (axFst pf_α pf_β))

  projSndRecs_red : Deriv (atomic (eqn (ap2 projSndRecs origT recsT) pf_β))
  projSndRecs_red =
    ruleTrans (axPost Snd sBin origT recsT)
              (ruleTrans (cong1 Snd sBin_red) (axSnd pf_α pf_β))

  corFstRecs_red : Deriv (atomic (eqn (ap2 corFstRecs origT recsT) (ap1 cor pf_α)))
  corFstRecs_red =
    ruleTrans (axPost (Comp cor Fst) sBin origT recsT)
              (ruleTrans (cong1 (Comp cor Fst) sBin_red)
                         (ruleTrans (axComp cor Fst recsT)
                                    (cong1 cor (axFst pf_α pf_β))))

  corSndRecs_red : Deriv (atomic (eqn (ap2 corSndRecs origT recsT) (ap1 cor pf_β)))
  corSndRecs_red =
    ruleTrans (axPost (Comp cor Snd) sBin origT recsT)
              (ruleTrans (cong1 (Comp cor Snd) sBin_red)
                         (ruleTrans (axComp cor Snd recsT)
                                    (cong1 cor (axSnd pf_α pf_β))))

  ----------------------------------------------------------------------
  -- Mid-level term values (bind once for readability of the chain).

  cv_a : Term
  cv_a = ap1 cor α

  cv_b : Term
  cv_b = ap1 cor β

  mkAp1T_cv_a_T : Term
  mkAp1T_cv_a_T = ap2 Pair tagAp1T (ap2 Pair cf cv_a)

  mkAp1T_cv_b_T : Term
  mkAp1T_cv_b_T = ap2 Pair tagAp1T (ap2 Pair cf cv_b)

  X_T : Term
  X_T = ap2 Pair tagAp2T (ap2 Pair pCT (ap2 Pair cv_a cv_b))

  Y_T : Term
  Y_T = ap2 Pair tagAp2T (ap2 Pair pCT (ap2 Pair mkAp1T_cv_a_T mkAp1T_cv_b_T))

  cor_pf_a : Term
  cor_pf_a = ap1 cor pf_α

  cor_pf_b : Term
  cor_pf_b = ap1 cor pf_β

  ----------------------------------------------------------------------
  -- Reductions for the mid-level Fun2's.

  mkAp1T_cv_a_red :
    Deriv (atomic (eqn (ap2 F_mkAp1T_cv_a origT recsT) mkAp1T_cv_a_T))
  mkAp1T_cv_a_red =
    pairF_red (constF tagAp1T) (pairF (constF cf) corFstOrig)
              origT recsT tagAp1T (ap2 Pair cf cv_a)
      (constF_red tagAp1 origT recsT)
      (pairF_red (constF cf) corFstOrig origT recsT cf cv_a
        (constF_red (codeF1 D_Rec_OS_F) origT recsT)
        corFstOrig_red)

  mkAp1T_cv_b_red :
    Deriv (atomic (eqn (ap2 F_mkAp1T_cv_b origT recsT) mkAp1T_cv_b_T))
  mkAp1T_cv_b_red =
    pairF_red (constF tagAp1T) (pairF (constF cf) corSndOrig)
              origT recsT tagAp1T (ap2 Pair cf cv_b)
      (constF_red tagAp1 origT recsT)
      (pairF_red (constF cf) corSndOrig origT recsT cf cv_b
        (constF_red (codeF1 D_Rec_OS_F) origT recsT)
        corSndOrig_red)

  X_red : Deriv (atomic (eqn (ap2 F_X origT recsT) X_T))
  X_red =
    pairF_red (constF tagAp2T) (pairF (constF pCT) (pairF corFstOrig corSndOrig))
              origT recsT tagAp2T (ap2 Pair pCT (ap2 Pair cv_a cv_b))
      (constF_red tagAp2 origT recsT)
      (pairF_red (constF pCT) (pairF corFstOrig corSndOrig) origT recsT
                  pCT (ap2 Pair cv_a cv_b)
        (constF_red (codeF2 Pair) origT recsT)
        (pairF_red corFstOrig corSndOrig origT recsT cv_a cv_b
          corFstOrig_red corSndOrig_red))

  Y_red : Deriv (atomic (eqn (ap2 F_Y origT recsT) Y_T))
  Y_red =
    pairF_red (constF tagAp2T) (pairF (constF pCT) (pairF F_mkAp1T_cv_a F_mkAp1T_cv_b))
              origT recsT tagAp2T (ap2 Pair pCT (ap2 Pair mkAp1T_cv_a_T mkAp1T_cv_b_T))
      (constF_red tagAp2 origT recsT)
      (pairF_red (constF pCT) (pairF F_mkAp1T_cv_a F_mkAp1T_cv_b) origT recsT
                  pCT (ap2 Pair mkAp1T_cv_a_T mkAp1T_cv_b_T)
        (constF_red (codeF2 Pair) origT recsT)
        (pairF_red F_mkAp1T_cv_a F_mkAp1T_cv_b origT recsT mkAp1T_cv_a_T mkAp1T_cv_b_T
          mkAp1T_cv_a_red mkAp1T_cv_b_red))

  ----------------------------------------------------------------------
  -- Target Df_E_i Terms (matching RecOSPairCaseFull's chain components).

  Df_E1_T : Term
  Df_E1_T = ap2 Pair tagCode_axRecNd
              (ap2 Pair O (ap2 Pair sT (ap2 Pair cv_a cv_b)))

  Df_E2_T : Term
  Df_E2_T = ap2 Pair tagCode_axPost
              (ap2 Pair cSnd (ap2 Pair pCT (ap2 Pair X_T Y_T)))

  Df_E3_T : Term
  Df_E3_T = ap2 Pair tagCode_axSnd (ap2 Pair X_T Y_T)

  Df_E4_T : Term
  Df_E4_T = ap2 Pair tagCode_congL
              (ap2 Pair pCT (ap2 Pair pf_α mkAp1T_cv_b_T))

  Df_E5_T : Term
  Df_E5_T = ap2 Pair tagCode_congR
              (ap2 Pair pCT (ap2 Pair pf_β cor_pf_a))

  Df_chain12_T : Term
  Df_chain12_T = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1_T Df_E2_T)

  Df_chain123_T : Term
  Df_chain123_T = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain12_T Df_E3_T)

  Df_chain1234_T : Term
  Df_chain1234_T = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain123_T Df_E4_T)

  Df_chain12345_T : Term
  Df_chain12345_T = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1234_T Df_E5_T)

  ----------------------------------------------------------------------
  -- Reductions for Df_E_i.

  Df_E1_red : Deriv (atomic (eqn (ap2 F_Df_E1 origT recsT) Df_E1_T))
  Df_E1_red =
    pairF_red (constF tagCode_axRecNd) _ origT recsT
              tagCode_axRecNd (ap2 Pair O (ap2 Pair sT (ap2 Pair cv_a cv_b)))
      (constF_red (natCode tagAxRecNd) origT recsT)
      (pairF_red (constF O) _ origT recsT O (ap2 Pair sT (ap2 Pair cv_a cv_b))
        (constF_red lf origT recsT)
        (pairF_red (constF sT) _ origT recsT sT (ap2 Pair cv_a cv_b)
          (constF_red (codeF2 sBin) origT recsT)
          (pairF_red corFstOrig corSndOrig origT recsT cv_a cv_b
            corFstOrig_red corSndOrig_red)))

  Df_E2_red : Deriv (atomic (eqn (ap2 F_Df_E2 origT recsT) Df_E2_T))
  Df_E2_red =
    pairF_red (constF tagCode_axPost) _ origT recsT
              tagCode_axPost (ap2 Pair cSnd (ap2 Pair pCT (ap2 Pair X_T Y_T)))
      (constF_red (natCode tagAxPost) origT recsT)
      (pairF_red (constF cSnd) _ origT recsT cSnd (ap2 Pair pCT (ap2 Pair X_T Y_T))
        (constF_red (codeF1 Snd) origT recsT)
        (pairF_red (constF pCT) _ origT recsT pCT (ap2 Pair X_T Y_T)
          (constF_red (codeF2 Pair) origT recsT)
          (pairF_red F_X F_Y origT recsT X_T Y_T X_red Y_red)))

  Df_E3_red : Deriv (atomic (eqn (ap2 F_Df_E3 origT recsT) Df_E3_T))
  Df_E3_red =
    pairF_red (constF tagCode_axSnd) _ origT recsT
              tagCode_axSnd (ap2 Pair X_T Y_T)
      (constF_red (natCode tagAxSnd) origT recsT)
      (pairF_red F_X F_Y origT recsT X_T Y_T X_red Y_red)

  Df_E4_red : Deriv (atomic (eqn (ap2 F_Df_E4 origT recsT) Df_E4_T))
  Df_E4_red =
    pairF_red (constF tagCode_congL) _ origT recsT
              tagCode_congL (ap2 Pair pCT (ap2 Pair pf_α mkAp1T_cv_b_T))
      (constF_red (natCode tagCongL) origT recsT)
      (pairF_red (constF pCT) _ origT recsT pCT (ap2 Pair pf_α mkAp1T_cv_b_T)
        (constF_red (codeF2 Pair) origT recsT)
        (pairF_red projFstRecs F_mkAp1T_cv_b origT recsT pf_α mkAp1T_cv_b_T
          projFstRecs_red mkAp1T_cv_b_red))

  Df_E5_red : Deriv (atomic (eqn (ap2 F_Df_E5 origT recsT) Df_E5_T))
  Df_E5_red =
    pairF_red (constF tagCode_congR) _ origT recsT
              tagCode_congR (ap2 Pair pCT (ap2 Pair pf_β cor_pf_a))
      (constF_red (natCode tagCongR) origT recsT)
      (pairF_red (constF pCT) _ origT recsT pCT (ap2 Pair pf_β cor_pf_a)
        (constF_red (codeF2 Pair) origT recsT)
        (pairF_red projSndRecs corFstRecs origT recsT pf_β cor_pf_a
          projSndRecs_red corFstRecs_red))

  ----------------------------------------------------------------------
  -- Chain composition reductions.

  Df_chain12_red : Deriv (atomic (eqn (ap2 F_chain12 origT recsT) Df_chain12_T))
  Df_chain12_red =
    pairF_red (constF tagCode_ruleTrans) _ origT recsT
              tagCode_ruleTrans (ap2 Pair Df_E1_T Df_E2_T)
      (constF_red (natCode tagRuleTrans) origT recsT)
      (pairF_red F_Df_E1 F_Df_E2 origT recsT Df_E1_T Df_E2_T Df_E1_red Df_E2_red)

  Df_chain123_red : Deriv (atomic (eqn (ap2 F_chain123 origT recsT) Df_chain123_T))
  Df_chain123_red =
    pairF_red (constF tagCode_ruleTrans) _ origT recsT
              tagCode_ruleTrans (ap2 Pair Df_chain12_T Df_E3_T)
      (constF_red (natCode tagRuleTrans) origT recsT)
      (pairF_red F_chain12 F_Df_E3 origT recsT Df_chain12_T Df_E3_T
                 Df_chain12_red Df_E3_red)

  Df_chain1234_red : Deriv (atomic (eqn (ap2 F_chain1234 origT recsT) Df_chain1234_T))
  Df_chain1234_red =
    pairF_red (constF tagCode_ruleTrans) _ origT recsT
              tagCode_ruleTrans (ap2 Pair Df_chain123_T Df_E4_T)
      (constF_red (natCode tagRuleTrans) origT recsT)
      (pairF_red F_chain123 F_Df_E4 origT recsT Df_chain123_T Df_E4_T
                 Df_chain123_red Df_E4_red)

  Df_chain12345_red : Deriv (atomic (eqn (ap2 F_chain12345 origT recsT) Df_chain12345_T))
  Df_chain12345_red =
    pairF_red (constF tagCode_ruleTrans) _ origT recsT
              tagCode_ruleTrans (ap2 Pair Df_chain1234_T Df_E5_T)
      (constF_red (natCode tagRuleTrans) origT recsT)
      (pairF_red F_chain1234 F_Df_E5 origT recsT Df_chain1234_T Df_E5_T
                 Df_chain1234_red Df_E5_red)

  ----------------------------------------------------------------------
  -- The main reduction lemma:  ap2 s' origT recsT  =  Df_chain12345_T .

  s'_red : Deriv (atomic (eqn (ap2 s' origT recsT) Df_chain12345_T))
  s'_red = Df_chain12345_red

------------------------------------------------------------------------
-- Top-level BRA-reduction lemmas for D_R.
--
-- At leaf input  x = O :   ap1 D_R O  =  z'   (axRecLf).
-- At Pair input  x = Pair a b :  ap1 D_R (Pair a b)  =  Df_chain12345 ,
--   provided pf_α = ap1 D_R a, pf_β = ap1 D_R b  (= recursive sub-apps
--   automatically supplied by  axRecNd ).

D_R_at_O : Deriv (atomic (eqn (ap1 D_R O) z'))
D_R_at_O = axRecLf z' s'

D_R_at_Pair :
  (a b : Term) ->
  let pf_a : Term
      pf_a = ap1 D_R a
      pf_b : Term
      pf_b = ap1 D_R b
      open ProjRed a b pf_a pf_b
  in Deriv (atomic (eqn (ap1 D_R (ap2 Pair a b)) Df_chain12345_T))
D_R_at_Pair a b =
  let pf_a : Term
      pf_a = ap1 D_R a
      pf_b : Term
      pf_b = ap1 D_R b
      open ProjRed a b pf_a pf_b
      step1 : Deriv (atomic (eqn (ap1 D_R (ap2 Pair a b))
                                  (ap2 s' (ap2 Pair a b) (ap2 Pair pf_a pf_b))))
      step1 = axRecNd z' s' a b
  in ruleTrans step1 s'_red
