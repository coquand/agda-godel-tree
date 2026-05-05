{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12RecCheck
--
-- Architectural validation for Theorem 12 (asymmetric) at the Rec
-- case.  See BRA/NEXT-SESSION-REC-CHECK.md for the design.
--
-- Concrete functor under test:
--
--     D_Rec_OS_F = Rec O sBin       where  sBin = Post Snd Pair .
--
-- This is the simplest non-trivial recursive functor that needs cross
-- IHs in the Pair-case chain:
--
--     ap2 sBin a b   =  ap1 Snd (ap2 Pair a b)   =  b   (axPost + axSnd)
--
-- so  Rec O sBin (Pair a b) = sBin (Pair a b) (Pair (Rec... a) (Rec... b))
--                            = Pair (Rec... a) (Rec... b)
-- (it acts as identity on canonical trees, recursively).
--
-- We deliver:
--
--   1.  thm12_RecOS_O    : Theorem 12 at concrete  x = O .
--                          Fully proved via parDispAxRecLf + cor reductions.
--
--   2.  RecOSPairCaseChain v1 v2 . chain123
--                        : the encoded chain through three pure-dispatcher
--                          stages (parDispAxRecNd + parDispAxPost +
--                          parDispAxSnd, composed via parDispRuleTrans),
--                          giving thmT(Df_chain123) = Pair (mkAp1T cf X) Y
--                          where X = encoded "Pair (cor v1) (cor v2)" and
--                          Y = encoded "Pair (Rec... cor v1) (Rec... cor v2)".
--
--   3.  Diagnostic of the cross-IH stage:  see comments after
--       RecOSPairCaseChain .  The cross-IH propagation through inner
--       ap2 Pair positions of  Y  hits a shape-proof gap on
--       parDispCongL / parDispCongR .  Two routes to resolve are
--       documented; both are tractable.
--
-- NOT delivered:
--
--   * The cross-IH-using extension of chain123 to a full Pair-case
--     proof (blocked on parDispCongL/CongR shape requirement; see
--     diagnostic below).
--
--   * The single  D_Rec_OS = Rec z' s'  Fun1 expression that, applied
--     at  x , reduces (in BRA) to the chain Term whose thmT-image
--     matches a Sigma-form  Df_term .  Constructing  s'  as a literal
--     Fun2 expression (Fan / Lift / KT / projections) is ~80-120 LoC
--     of mechanical engineering.  This is engineering, NOT
--     architectural.
--
--   * The universal closure  D_correct_RecOS : (x : Term) -> Deriv
--     (...)  via  ruleIndBT .  Requires SKI internalisation of the
--     Pair case.
--
-- No postulates, no holes.  Typechecks in ~0.3s.

module BRA.Thm12RecCheck where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axRecLf ; tagCode_axRecNd
  ; tagCode_axPost ; tagCode_axSnd
  ; tagCode_ruleTrans ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRecLf_param ; thmTDispAxRecNd_param
  ; thmTDispAxPost_param ; thmTDispAxSnd_param
  ; thmTDispRuleTrans_param ; thmTDispCongL_param ; thmTDispCongR_param )

------------------------------------------------------------------------
-- The recursive functor under test.

sBin : Fun2
sBin = Post Snd Pair

D_Rec_OS_F : Fun1
D_Rec_OS_F = Rec O sBin

------------------------------------------------------------------------
-- The Theorem-12 (asymmetric) spec, packaged as Sigma.

T12Spec1 : Term -> Set
T12Spec1 x =
  Sigma Term (\ Df ->
    Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq1Asym D_Rec_OS_F x))))

------------------------------------------------------------------------
-- Leaf case:  Theorem 12 at  x = O .
--
-- Df_term = parEncAxRecLf O sT  (encoded "axRecLf O sBin" payload).
-- thmTDispAxRecLf_param dispatches it to  parOutAxRecLf O sT
-- = Pair (mkAp1T cf O) O, where  cf = reify (codeF1 (Rec O sBin)) .
-- Bridge to codeFTeq1Asym (Rec O sBin) O via cor reductions:
--   LHS : mkAp1T cf O  ->  mkAp1T cf (cor O)            (cor O = O)
--   RHS : O            ->  cor (Rec O sBin O)
--          via  axRecLf O sBin + cong1 cor + axRecLf O stepCor .

thm12_RecOS_O : T12Spec1 O
thm12_RecOS_O =
  let
    sT : Term
    sT = reify (codeF2 sBin)

    cf : Term
    cf = reify (codeF1 D_Rec_OS_F)

    -- The Df_term is the encoding of "axRecLf was applied at z=O, s=sBin".
    Df_term : Term
    Df_term = ap2 Pair tagCode_axRecLf (ap2 Pair O sT)

    -- Dispatch produces the encoded equation "Rec O sBin O = O".
    -- thmTDispAxRecLf_param's output structure (with zT=O):
    --   Pair (Pair tagAp1 (Pair (Pair tagAxRec' (Pair O sT)) O)) O
    -- which is definitionally  Pair (mkAp1T cf O) O  (since cf reduces
    -- to  Pair tagAxRec' (Pair O sT) , the natCode 32 head plus payload).

    disp : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (ap2 Pair (ap2 Pair (reify tagAp1)
                                            (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                                (ap2 Pair O sT))
                                                      O))
                                          O)))
    disp = thmTDispAxRecLf_param O sT

    -- LHS bridge:  the inner  O  needs to come from  cor O .
    cor_O : Deriv (atomic (eqn (ap1 cor O) O))
    cor_O = axRecLf O stepCor

    bL_inner : Deriv (atomic (eqn
                (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                    (ap2 Pair O sT))
                          O)
                (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                    (ap2 Pair O sT))
                          (ap1 cor O))))
    bL_inner = congR Pair
                 (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                           (ap2 Pair O sT))
                 (ruleSym cor_O)

    bL : Deriv (atomic (eqn
            (ap2 Pair (reify tagAp1)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                          (ap2 Pair O sT))
                                O))
            (mkAp1T cf (ap1 cor O))))
    bL = congR Pair (reify tagAp1) bL_inner

    -- RHS bridge:  O  ->  cor (Rec O sBin O) .
    --   axRecLf O sBin       : Rec O sBin O = O
    --   cong1 cor            : cor (Rec O sBin O) = cor O
    --   axRecLf O stepCor    : cor O = O
    --   compose + ruleSym    : O = cor (Rec O sBin O) .

    bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 D_Rec_OS_F O)) O))
    bR_combined = ruleTrans (cong1 cor (axRecLf O sBin)) cor_O

    bR : Deriv (atomic (eqn O (ap1 cor (ap1 D_Rec_OS_F O))))
    bR = ruleSym bR_combined

    -- Outer Pair bridges.

    step_LHS : Deriv (atomic (eqn
                (ap2 Pair (ap2 Pair (reify tagAp1)
                            (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                (ap2 Pair O sT))
                                      O))
                          O)
                (ap2 Pair (mkAp1T cf (ap1 cor O)) O)))
    step_LHS = congL Pair O bL

    step_RHS : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T cf (ap1 cor O)) O)
                (ap2 Pair (mkAp1T cf (ap1 cor O))
                          (ap1 cor (ap1 D_Rec_OS_F O)))))
    step_RHS = congR Pair (mkAp1T cf (ap1 cor O)) bR

    bridge_total : Deriv (atomic (eqn
                    (ap2 Pair (ap2 Pair (reify tagAp1)
                                (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                    (ap2 Pair O sT))
                                          O))
                              O)
                    (codeFTeq1Asym D_Rec_OS_F O)))
    bridge_total = ruleTrans step_LHS step_RHS

    final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                (codeFTeq1Asym D_Rec_OS_F O)))
    final = ruleTrans disp bridge_total

  in mkSigma Df_term final

------------------------------------------------------------------------
-- Pair case (PARTIAL):  Theorem 12 at  x = Pair v1 v2 .
--
-- We attempt the encoded chain through three pure-dispatcher stages
-- (no cross-IH yet):
--
--   E1 : parDispAxRecNd at zT=O, sT=sT, aT=cor v1, bT=cor v2
--        Gives encoded "Rec O sBin (Pair (cor v1) (cor v2))
--                     = sBin (Pair (cor v1) (cor v2))
--                            (Pair (Rec... (cor v1)) (Rec... (cor v2)))".
--   E2 : parDispAxPost Snd Pair X Y where X = mkAp2T pCT cv1 cv2,
--                                    Y = mkAp2T pCT (mkAp1T cf cv1) (mkAp1T cf cv2)
--        Gives encoded "Post Snd Pair X Y = Snd (Pair X Y)".
--   E3 : parDispAxSnd X Y
--        Gives encoded "Snd (Pair X Y) = Y".
--
-- chain123 = parDispRuleTrans^2 (E1, E2, E3) gives a single Df whose
-- thmT-image is  Pair (mkAp1T cf X) Y  -- i.e., the encoded equation
-- "Rec O sBin (encoded Pair (cor v1) (cor v2)) = mkAp2T pCT (mkAp1T cf cv1) (mkAp1T cf cv2)".
--
-- This is the seed of the chain; the cross-IH propagation comes next.

module RecOSPairCaseChain (v1 v2 : Nat) where

  v1T : Term
  v1T = var v1

  v2T : Term
  v2T = var v2

  cv1 : Term
  cv1 = ap1 cor v1T

  cv2 : Term
  cv2 = ap1 cor v2T

  sT : Term
  sT = reify (codeF2 sBin)

  cf : Term
  cf = reify (codeF1 D_Rec_OS_F)

  pCT : Term
  pCT = reify (codeF2 Pair)

  cSnd : Term
  cSnd = reify (codeF1 Snd)

  X : Term
  X = ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cv1 cv2))
  -- = mkAp2T pCT cv1 cv2

  Y : Term
  Y = ap2 Pair (reify tagAp2)
        (ap2 Pair pCT (ap2 Pair (mkAp1T cf cv1) (mkAp1T cf cv2)))
  -- = mkAp2T pCT (mkAp1T cf cv1) (mkAp1T cf cv2)

  ----------------------------------------------------------------------
  -- E1 : parDispAxRecNd at zT=O, sT=sT, aT=cv1, bT=cv2.
  -- E1's image: Pair u1_E1 u2_E1, with
  --   u1_E1 = mkAp1T cf X  (= the LHS subterm of parOutAxRecNd)
  --   u2_E1 = mkAp2T sT X Y  (= the RHS subterm)

  Df_E1 : Term
  Df_E1 = ap2 Pair tagCode_axRecNd
              (ap2 Pair O (ap2 Pair sT (ap2 Pair cv1 cv2)))

  u1_E1 : Term
  u1_E1 = mkAp1T cf X

  u2_E1 : Term
  u2_E1 = ap2 Pair (reify tagAp2) (ap2 Pair sT (ap2 Pair X Y))
  -- = mkAp2T sT X Y

  E1 : Deriv (atomic (eqn (ap1 thmT Df_E1) (ap2 Pair u1_E1 u2_E1)))
  E1 = thmTDispAxRecNd_param O sT cv1 cv2

  ----------------------------------------------------------------------
  -- E2 : parDispAxPost Snd Pair X Y.
  -- E2's image: Pair u2_E1 u2_E2, with
  --   u2_E2 = mkAp1T cSnd (mkAp2T pCT X Y)

  Df_E2 : Term
  Df_E2 = ap2 Pair tagCode_axPost
              (ap2 Pair cSnd (ap2 Pair pCT (ap2 Pair X Y)))

  u2_E2 : Term
  u2_E2 = mkAp1T cSnd (mkAp2T pCT X Y)

  E2 : Deriv (atomic (eqn (ap1 thmT Df_E2) (ap2 Pair u2_E1 u2_E2)))
  E2 = thmTDispAxPost_param Snd Pair X Y

  ----------------------------------------------------------------------
  -- E3 : parDispAxSnd X Y.
  -- E3's image: Pair u2_E2 Y.

  Df_E3 : Term
  Df_E3 = ap2 Pair tagCode_axSnd (ap2 Pair X Y)

  E3 : Deriv (atomic (eqn (ap1 thmT Df_E3) (ap2 Pair u2_E2 Y)))
  E3 = thmTDispAxSnd_param X Y

  ----------------------------------------------------------------------
  -- chain12 : parDispRuleTrans (Df_E1, Df_E2) gives a single Df whose
  -- image is Pair u1_E1 u2_E2.
  --
  -- Shape proof for Df_E1 : Fst (Pair tagCode_axRecNd _) = tagCode_axRecNd
  -- = reify (natCode tagAxRecNd) = Pair O (reify (natCode (suc^{-1} tagAxRecNd))).

  shape_E1 : Deriv (atomic (eqn (ap1 Fst Df_E1) tagCode_axRecNd))
  shape_E1 = axFst tagCode_axRecNd _

  Df_chain12 : Term
  Df_chain12 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1 Df_E2)

  chain12 : Deriv (atomic (eqn (ap1 thmT Df_chain12)
                                (ap2 Pair u1_E1 u2_E2)))
  chain12 = thmTDispRuleTrans_param Df_E1 Df_E2 u1_E1 u2_E1 u2_E1 u2_E2
              _ _ shape_E1 E1 E2

  ----------------------------------------------------------------------
  -- chain123 : compose chain12 with E3.

  shape_chain12 : Deriv (atomic (eqn (ap1 Fst Df_chain12) tagCode_ruleTrans))
  shape_chain12 = axFst tagCode_ruleTrans _

  Df_chain123 : Term
  Df_chain123 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain12 Df_E3)

  chain123 : Deriv (atomic (eqn (ap1 thmT Df_chain123)
                                 (ap2 Pair u1_E1 Y)))
  chain123 = thmTDispRuleTrans_param Df_chain12 Df_E3 u1_E1 u2_E2 u2_E2 Y
               _ _ shape_chain12 chain12 E3

  -- chain123 establishes : thmT(Df_chain123) = Pair (mkAp1T cf X) Y
  --                       = encoded "Rec O sBin (encoded Pair cv1 cv2) = Y" .
  --
  -- Architectural significance: the chain composition through pure
  -- dispatchers (parDispAxRecNd + parDispAxPost + parDispAxSnd) using
  -- parDispRuleTrans typechecks and produces the expected thmT-image.
  -- The composition is purely mechanical: each shape proof is
  --  axFst tagCode_X _  for known tag.  No subtleties.

------------------------------------------------------------------------
-- Bundled-IH spec:  Theorem-12 IH packaged with an  Fst-shape witness.
--
-- parDispCongL / parDispCongR  require a  Fst-shape proof on their
-- y_h_T  argument (the inner sub-encoding).  When the cross-IH is
-- supplied externally, we ask the provider to bundle that shape proof
-- alongside the thmT-image.  The natural choice in practice is for
-- the IH-Df to be  parEncRuleTrans-headed  (head =  tagCode_ruleTrans
-- = Pair O ...), so  axFst tagCode_ruleTrans _  fills in the witness.

record IH1 (x : Term) : Set where
  field
    Df    : Term
    fstL  : Term  -- left  child of  Fst Df  (= x'   in parDispCongL/R)
    fstR  : Term  -- right child of  Fst Df  (= y_h' in parDispCongL/R)
    shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
    image : Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq1Asym D_Rec_OS_F x)))

------------------------------------------------------------------------
-- Helper: cor-reduction at  ap2 Pair a b .
--
-- cor (Pair a b) = mkAp2T pCT (cor a) (cor b)
-- via  axRecNd O stepCor a b  +  stepCorRed .

cor_red_pair : (a b : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap2 Pair a b))
                     (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 Pair))
                         (ap2 Pair (ap1 cor a) (ap1 cor b))))))
cor_red_pair a b =
  ruleTrans (axRecNd O stepCor a b)
            (stepCorRed (ap2 Pair a b)
                        (ap2 Pair (ap1 cor a) (ap1 cor b)))

------------------------------------------------------------------------
-- Pair case (full): Theorem 12 at  Pair v1 v2 , parametric in
-- bundled-IH inputs at  v1, v2 .
--
-- Chain layout (continuing chain123 from RecOSPairCaseChain):
--
--   E4 : parDispCongL Pair Df_IH_v1 (mkAp1T cf cv2)
--        -- rewrites first slot of Y from  mkAp1T cf cv1  to  cor (Rec... v1) .
--   E5 : parDispCongR Pair (cor (Rec... v1)) Df_IH_v2
--        -- rewrites second slot from  mkAp1T cf cv2  to  cor (Rec... v2) .
--   chain12345 = chain123  +  E4  +  E5  via  parDispRuleTrans .
--   Final bridge: BRA-level cong rewrites bridging
--     Pair (mkAp1T cf X) (mkAp2T pCT (cor (Rec... v1)) (cor (Rec... v2)))
--   to
--     codeFTeq1Asym D_Rec_OS_F (Pair v1 v2) .

module RecOSPairCaseFull
  (v1T v2T : Term)
  (ih_v1 : IH1 v1T)
  (ih_v2 : IH1 v2T)
  where

  pairT : Term
  pairT = ap2 Pair v1T v2T

  cv1 : Term
  cv1 = ap1 cor v1T

  cv2 : Term
  cv2 = ap1 cor v2T

  sT : Term
  sT = reify (codeF2 sBin)

  cf : Term
  cf = reify (codeF1 D_Rec_OS_F)

  pCT : Term
  pCT = reify (codeF2 Pair)

  cSnd : Term
  cSnd = reify (codeF1 Snd)

  X : Term
  X = ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cv1 cv2))
  -- = mkAp2T pCT cv1 cv2

  Y : Term
  Y = ap2 Pair (reify tagAp2)
        (ap2 Pair pCT (ap2 Pair (mkAp1T cf cv1) (mkAp1T cf cv2)))
  -- = mkAp2T pCT (mkAp1T cf cv1) (mkAp1T cf cv2)

  ----------------------------------------------------------------------
  -- IH access.

  Df_IH_v1 : Term
  Df_IH_v1 = IH1.Df ih_v1

  ih_v1_LHS : Term
  ih_v1_LHS = mkAp1T cf cv1
  -- = first slot of  codeFTeq1Asym D_Rec_OS_F v1T .

  rec_v1 : Term
  rec_v1 = ap1 D_Rec_OS_F v1T

  ih_v1_RHS : Term
  ih_v1_RHS = ap1 cor rec_v1
  -- = second slot of  codeFTeq1Asym D_Rec_OS_F v1T .

  ih_v1_image : Deriv (atomic (eqn (ap1 thmT Df_IH_v1)
                                    (ap2 Pair ih_v1_LHS ih_v1_RHS)))
  ih_v1_image = IH1.image ih_v1

  Df_IH_v2 : Term
  Df_IH_v2 = IH1.Df ih_v2

  ih_v2_LHS : Term
  ih_v2_LHS = mkAp1T cf cv2

  rec_v2 : Term
  rec_v2 = ap1 D_Rec_OS_F v2T

  ih_v2_RHS : Term
  ih_v2_RHS = ap1 cor rec_v2

  ih_v2_image : Deriv (atomic (eqn (ap1 thmT Df_IH_v2)
                                    (ap2 Pair ih_v2_LHS ih_v2_RHS)))
  ih_v2_image = IH1.image ih_v2

  ----------------------------------------------------------------------
  -- Stages E1..E3 (re-stated from RecOSPairCaseChain).

  Df_E1 : Term
  Df_E1 = ap2 Pair tagCode_axRecNd
              (ap2 Pair O (ap2 Pair sT (ap2 Pair cv1 cv2)))

  u1_E1 : Term
  u1_E1 = mkAp1T cf X

  u2_E1 : Term
  u2_E1 = ap2 Pair (reify tagAp2) (ap2 Pair sT (ap2 Pair X Y))
  -- = mkAp2T sT X Y

  E1 : Deriv (atomic (eqn (ap1 thmT Df_E1) (ap2 Pair u1_E1 u2_E1)))
  E1 = thmTDispAxRecNd_param O sT cv1 cv2

  Df_E2 : Term
  Df_E2 = ap2 Pair tagCode_axPost
              (ap2 Pair cSnd (ap2 Pair pCT (ap2 Pair X Y)))

  u2_E2 : Term
  u2_E2 = mkAp1T cSnd (mkAp2T pCT X Y)

  E2 : Deriv (atomic (eqn (ap1 thmT Df_E2) (ap2 Pair u2_E1 u2_E2)))
  E2 = thmTDispAxPost_param Snd Pair X Y

  Df_E3 : Term
  Df_E3 = ap2 Pair tagCode_axSnd (ap2 Pair X Y)

  E3 : Deriv (atomic (eqn (ap1 thmT Df_E3) (ap2 Pair u2_E2 Y)))
  E3 = thmTDispAxSnd_param X Y

  Df_chain12 : Term
  Df_chain12 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1 Df_E2)

  shape_E1 : Deriv (atomic (eqn (ap1 Fst Df_E1) tagCode_axRecNd))
  shape_E1 = axFst tagCode_axRecNd _

  chain12 : Deriv (atomic (eqn (ap1 thmT Df_chain12) (ap2 Pair u1_E1 u2_E2)))
  chain12 = thmTDispRuleTrans_param Df_E1 Df_E2 u1_E1 u2_E1 u2_E1 u2_E2
              _ _ shape_E1 E1 E2

  Df_chain123 : Term
  Df_chain123 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain12 Df_E3)

  shape_chain12 : Deriv (atomic (eqn (ap1 Fst Df_chain12) tagCode_ruleTrans))
  shape_chain12 = axFst tagCode_ruleTrans _

  chain123 : Deriv (atomic (eqn (ap1 thmT Df_chain123) (ap2 Pair u1_E1 Y)))
  chain123 = thmTDispRuleTrans_param Df_chain12 Df_E3 u1_E1 u2_E2 u2_E2 Y
               _ _ shape_chain12 chain12 E3

  ----------------------------------------------------------------------
  -- E4 : parDispCongL Pair Df_IH_v1 (mkAp1T cf cv2)
  -- Rewrites the first slot of  Y  using  ih_v1 .

  Df_E4 : Term
  Df_E4 = ap2 Pair tagCode_congL
              (ap2 Pair pCT (ap2 Pair Df_IH_v1 (mkAp1T cf cv2)))

  Y_after_v1 : Term
  Y_after_v1 = ap2 Pair (reify tagAp2)
                 (ap2 Pair pCT (ap2 Pair ih_v1_RHS (mkAp1T cf cv2)))
  -- = mkAp2T pCT ih_v1_RHS (mkAp1T cf cv2)
  -- = mkAp2T pCT (cor (Rec... v1)) (mkAp1T cf cv2)

  E4 : Deriv (atomic (eqn (ap1 thmT Df_E4) (ap2 Pair Y Y_after_v1)))
  E4 = thmTDispCongL_param Pair (mkAp1T cf cv2) Df_IH_v1
         ih_v1_LHS ih_v1_RHS
         (IH1.fstR ih_v1) (IH1.fstL ih_v1)
         (IH1.shape ih_v1) ih_v1_image

  ----------------------------------------------------------------------
  -- chain1234 = chain123  +  E4 .

  Df_chain1234 : Term
  Df_chain1234 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain123 Df_E4)

  shape_chain123 : Deriv (atomic (eqn (ap1 Fst Df_chain123) tagCode_ruleTrans))
  shape_chain123 = axFst tagCode_ruleTrans _

  chain1234 : Deriv (atomic (eqn (ap1 thmT Df_chain1234)
                                  (ap2 Pair u1_E1 Y_after_v1)))
  chain1234 = thmTDispRuleTrans_param Df_chain123 Df_E4 u1_E1 Y Y Y_after_v1
                _ _ shape_chain123 chain123 E4

  ----------------------------------------------------------------------
  -- E5 : parDispCongR Pair (cor (Rec... v1)) Df_IH_v2 .
  -- Rewrites the second slot of  Y_after_v1  using  ih_v2 .

  Df_E5 : Term
  Df_E5 = ap2 Pair tagCode_congR
              (ap2 Pair pCT (ap2 Pair Df_IH_v2 ih_v1_RHS))

  Y_full : Term
  Y_full = ap2 Pair (reify tagAp2)
             (ap2 Pair pCT (ap2 Pair ih_v1_RHS ih_v2_RHS))
  -- = mkAp2T pCT (cor (Rec... v1)) (cor (Rec... v2))

  E5 : Deriv (atomic (eqn (ap1 thmT Df_E5) (ap2 Pair Y_after_v1 Y_full)))
  E5 = thmTDispCongR_param Pair ih_v1_RHS Df_IH_v2
         ih_v2_LHS ih_v2_RHS
         (IH1.fstR ih_v2) (IH1.fstL ih_v2)
         (IH1.shape ih_v2) ih_v2_image

  ----------------------------------------------------------------------
  -- chain12345 = chain1234  +  E5 .

  Df_chain12345 : Term
  Df_chain12345 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1234 Df_E5)

  shape_chain1234 : Deriv (atomic (eqn (ap1 Fst Df_chain1234) tagCode_ruleTrans))
  shape_chain1234 = axFst tagCode_ruleTrans _

  chain12345 : Deriv (atomic (eqn (ap1 thmT Df_chain12345)
                                   (ap2 Pair u1_E1 Y_full)))
  chain12345 = thmTDispRuleTrans_param Df_chain1234 Df_E5
                 u1_E1 Y_after_v1 Y_after_v1 Y_full
                 _ _ shape_chain1234 chain1234 E5

  ----------------------------------------------------------------------
  -- BRA-level outer bridge:
  --   Pair u1_E1 Y_full   =   codeFTeq1Asym D_Rec_OS_F pairT
  --
  -- LHS subterm:  mkAp1T cf X  =  mkAp1T cf (cor pairT)
  -- via cong on the cor reduction at Pair v1 v2 (used backwards).
  --
  -- RHS subterm:  mkAp2T pCT (cor (Rec... v1)) (cor (Rec... v2))
  --             =  cor (Rec O sBin pairT)
  -- via:
  --   step1 :  mkAp2T pCT (cor X1) (cor X2)  =  cor (Pair X1 X2)
  --            (ruleSym of cor reduction at Pair (Rec... v1) (Rec... v2)).
  --   step2 :  cor (Pair (Rec... v1) (Rec... v2))  =  cor (Rec O sBin pairT)
  --            (cong1 cor of axRecNd + axPost + axSnd chain).

  -- BRA-level reduction:  Rec O sBin (Pair v1 v2) = Pair (Rec... v1) (Rec... v2) .

  rec_eval : Deriv (atomic (eqn (ap1 D_Rec_OS_F pairT)
                                 (ap2 Pair rec_v1 rec_v2)))
  rec_eval =
    let s1 : Deriv (atomic (eqn (ap1 D_Rec_OS_F pairT)
                                 (ap2 sBin pairT (ap2 Pair rec_v1 rec_v2))))
        s1 = axRecNd O sBin v1T v2T

        s2 : Deriv (atomic (eqn (ap2 sBin pairT (ap2 Pair rec_v1 rec_v2))
                                 (ap1 Snd (ap2 Pair pairT (ap2 Pair rec_v1 rec_v2)))))
        s2 = axPost Snd Pair pairT (ap2 Pair rec_v1 rec_v2)

        s3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair pairT (ap2 Pair rec_v1 rec_v2)))
                                 (ap2 Pair rec_v1 rec_v2)))
        s3 = axSnd pairT (ap2 Pair rec_v1 rec_v2)

    in ruleTrans s1 (ruleTrans s2 s3)

  -- LHS bridge:  mkAp1T cf X  ->  mkAp1T cf (cor pairT) .

  inner_LHS : Deriv (atomic (eqn X (ap1 cor pairT)))
  inner_LHS = ruleSym (cor_red_pair v1T v2T)

  bridge_LHS : Deriv (atomic (eqn u1_E1 (mkAp1T cf (ap1 cor pairT))))
  bridge_LHS = congR Pair (reify tagAp1) (congR Pair cf inner_LHS)

  -- RHS bridge:  Y_full  ->  cor (Rec O sBin pairT) .

  step1_RHS : Deriv (atomic (eqn Y_full
                              (ap1 cor (ap2 Pair rec_v1 rec_v2))))
  step1_RHS = ruleSym (cor_red_pair rec_v1 rec_v2)

  step2_RHS : Deriv (atomic (eqn (ap1 cor (ap2 Pair rec_v1 rec_v2))
                                  (ap1 cor (ap1 D_Rec_OS_F pairT))))
  step2_RHS = cong1 cor (ruleSym rec_eval)

  bridge_RHS : Deriv (atomic (eqn Y_full (ap1 cor (ap1 D_Rec_OS_F pairT))))
  bridge_RHS = ruleTrans step1_RHS step2_RHS

  -- Outer bridge.

  outer_bridge : Deriv (atomic (eqn (ap2 Pair u1_E1 Y_full)
                                     (codeFTeq1Asym D_Rec_OS_F pairT)))
  outer_bridge =
    ruleTrans (congL Pair Y_full bridge_LHS)
              (congR Pair (mkAp1T cf (ap1 cor pairT)) bridge_RHS)

  ----------------------------------------------------------------------
  -- Final theorem.

  thm12_RecOS_pair :
    Sigma Term (\ Df ->
      Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq1Asym D_Rec_OS_F pairT))))
  thm12_RecOS_pair = mkSigma Df_chain12345 (ruleTrans chain12345 outer_bridge)

------------------------------------------------------------------------
-- Architectural conclusion (UPDATED).
--
--   * Leaf case:    thm12_RecOS_O                  --  PROVED.
--   * Pair case:    RecOSPairCaseFull.thm12_RecOS_pair  --  PROVED
--                   (parametric in IH1-bundled cross-IHs at v1, v2).
--
-- Together these establish the asymmetric Theorem 12 for  Rec O sBin  at
-- both shape cases (O and  Pair v1 v2 ), using the encoded chain
-- composition through  parDispAxRecNd + parDispAxPost + parDispAxSnd
-- + parDispCongL (with cross-IH at v1) + parDispCongR (with cross-IH
-- at v2), plus a final BRA-level bridge through  cor  reductions.
--
-- The architectural claim from NEXT-SESSION-REC-CHECK.md (claim 5):
--   "Cross-IH structural circularity for Rec is resolved by
--    D_Rec_zs = Rec z' s'.  The recursive sub-applications appear
--    automatically in the second argument to s' via axRecNd."
-- is VERIFIED at this concrete instance.  The recursive sub-encodings
-- mkAp1T cf (cor v_i)  appear in chain123's RHS via parDispAxRecNd ,
-- and are bridged to  cor (Rec O sBin v_i)  by parDispCongL/CongR
-- threading the cross-IH images.
--
-- Remaining engineering (NOT architectural):
--
--   * The single  D_Rec_OS = Rec z' s'  Fun1 expression that, at
--     x = pairT , reduces (in BRA) to a chain Term whose thmT-image
--     matches  thm12_RecOS_pair 's  Df_chain12345 .  Constructing  s'
--     as a literal Fun2 expression (Fan / Lift / KT / projections) is
--     ~80-120 LoC of mechanical engineering.  The SHAPE of  s'  follows
--     directly from  Df_chain12345 : it is a tree of  parEncRuleTrans
--     /parEncCongL/parEncCongR /parEncAxRecNd / parEncAxPost / parEncAxSnd
--     constructors with inputs projected from  orig=Pair a b  (via
--     Lift Fst, Lift Snd, Lift (Comp cor Fst), Lift (Comp cor Snd)) and
--     recs=Pair pf_a pf_b  (via Lift Fst, Lift Snd).  See the
--     RecRefactorPlan.agda PROTOTYPE pattern.
--
--   * The universal closure  D_correct_RecOS : (x : Term) -> Deriv
--     (...)  via  ruleIndBT .  At the universal level, the cross-IH
--     Df is  ap1 D_Rec_OS (var v_i) , which is NOT Pair-headed
--     directly.  Two routes:
--     (a) Construct D_Rec_OS so that ap1 D_Rec_OS x reduces (BRA-eq)
--         to a chain Term whose Fst is statically tagCode_ruleTrans
--         (equivalent to Pair O ...); use this BRA-eq Deriv as the
--         shape proof in IH1.shape via eqSubst.
--     (b) SKI internalisation of RecOSPairCaseFull's body at
--         v1, v2 = ruleIndBT's free variables; produces a closed
--         step Deriv directly.
--
-- Both are tractable; both follow the already-proved  thm12_RecOS_pair
-- as the structural template.

------------------------------------------------------------------------
-- Architectural conclusion.
--
-- The leaf case typechecks (verifies parDispAxRecLf + cor-reduction
-- bridge composition).  The Pair case follows the identical pattern
-- composed via parDispRuleTrans threading through parDispAxRecNd +
-- parDispAxPost + parDispAxSnd + parDispCongL + parDispCongR + ih_v1
-- + ih_v2 + cor reductions.
--
-- The construction has NO architectural obstruction: every step is
-- a single dispatcher whose signature is already exported from
-- BRA.Thm.ThmT and the cross-IH inputs are consumed at  parDispCong*
-- positions exactly as Thm12LiftComp.PostCase does for f = Snd, h = Pair.
--
-- The remaining work is:
--   (a) ~400-500 LoC of mechanical chain composition for the Pair
--       case (Sigma form).
--   (b) ~80-120 LoC for the  s' : Fun2  expression that lifts the
--       Sigma-form Df_term to a  D_Rec_OS = Rec z' s'  Fun1 form.
--   (c) ~50-100 LoC for SKI internalisation of the Pair case Deriv-
--       with-IH-inputs, producing a closed step Deriv for ruleIndBT.
--
-- All three are tractable; none change the Theorem 12 architecture.
